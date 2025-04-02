open Std
open Local_store

let { Logger.log } = Logger.for_section "Mtyper"

let index_changelog = Local_store.s_table Stamped_hashtable.create_changelog ()

type index_tbl =
  (Shape.Uid.t * Longident.t Location.loc, unit) Stamped_hashtable.t

(* Forward ref to be filled by analysis.Occurrences *)
let index_items :
    (index:index_tbl ->
    stamp:int ->
    Mconfig.t ->
    [ `Impl of Typedtree.structure_item list
    | `Intf of Typedtree.signature_item list ] ->
    unit)
    ref =
  ref (fun ~index:_ ~stamp:_ _config _item -> ())
let set_index_items f = index_items := f

type ('p, 't) item =
  { parsetree_item : 'p;
    typedtree_items : 't list * Types.signature_item list;
    part_snapshot : Types.snapshot;
    part_stamp : int;
    part_uid : int;
    part_env : Env.t;
    part_rev_sg : Types.signature_item list;
    part_errors : exn list;
    part_checks : Typecore.delayed_check list;
    part_warnings : Warnings.state
  }

type typedtree =
  [ `Interface of Typedtree.signature | `Implementation of Typedtree.structure ]

type typedtree_items =
  | Interface_items of
      { items : (Parsetree.signature_item, Typedtree.signature_item) item list;
        psig_modalities : Parsetree.modalities;
        sig_modalities : Mode.Modality.Value.Const.t;
        sig_sloc : Location.t
      }
  | Implementation_items of
      (Parsetree.structure_item, Typedtree.structure_item) item list

type typer_cache_stats = Miss | Hit of { reused : int; typed : int }

type 'a cache_result =
  { env : Env.t;
    snapshot : Types.snapshot;
    ident_stamp : int;
    uid_stamp : int;
    value : 'a;
    index : (Shape.Uid.t * Longident.t Location.loc, unit) Stamped_hashtable.t
  }

let cache : typedtree_items option cache_result option ref = s_ref None

let fresh_env config =
  let env0 = Typer_raw.fresh_env () in
  let env0 = Extension.register Mconfig.(config.merlin.extensions) env0 in
  let snap0 = Btype.snapshot () in
  let stamp0 = Ident.get_currentstamp () in
  let uid0 = Shape.Uid.get_current_stamp () in
  (env0, snap0, stamp0, uid0)

let get_cache config =
  match !cache with
  | Some ({ snapshot; _ } as c) when Types.is_valid snapshot -> c
  | Some _ | None ->
    let env, snapshot, ident_stamp, uid_stamp = fresh_env config in
    let index = Stamped_hashtable.create !index_changelog 256 in
    { env; snapshot; ident_stamp; uid_stamp; value = None; index }

let return_and_cache status =
  cache := Some { status with value = Some status.value };
  status

type result =
  { config : Mconfig.t;
    initial_env : Env.t;
    initial_snapshot : Types.snapshot;
    initial_stamp : int;
    stamp : int;
    initial_uid_stamp : int;
    typedtree : typedtree_items;
    index : (Shape.Uid.t * Longident.t Location.loc, unit) Stamped_hashtable.t;
    cache_stat : typer_cache_stats
  }

let initial_env res = res.initial_env

let get_cache_stat res = res.cache_stat

let compatible_prefix_rev result_items tree_items =
  let rec aux acc = function
    | ritem :: ritems, pitem :: pitems
      when Types.is_valid ritem.part_snapshot
           && compare ritem.parsetree_item pitem = 0 ->
      aux (ritem :: acc) (ritems, pitems)
    | _, pitems ->
      let reused = List.length acc in
      let typed = List.length pitems in
      let cache_stat = Hit { reused; typed } in
      log ~title:"compatible_prefix" "reusing %d items, %d new items to type"
        reused typed;
      (acc, pitems, cache_stat)
  in
  aux [] (result_items, tree_items)

(*  TODO @xvw 
    - type [completion] needs to be changed for whatever type you defined to describe how far the typer must go. 
    - type [partial] should also change adequatly.
*)
type partial =
  { msg : Domain_msg.msg; shared : unit Shared.t; comp : Domain_msg.completion }

let make_partial ?position msg shared =
  let comp =
    match position with
    | None -> Domain_msg.All
    | Some (line, column) -> Domain_msg.Partial { line; column }
  in
  { msg; shared; comp }

exception
  Cancel_struc of (Parsetree.structure_item, Typedtree.structure_item) item list

let continue_typing comp get_location item =
  match comp with
  | Domain_msg.All -> true
  | Partial { line; column } -> (
    let loc = get_location item in
    let start = loc.Location.loc_start in
    match Int.compare line start.pos_lnum with
    | 0 -> Int.compare column (Lexing.column start) >= 0
    | i -> i >= 0)

let type_structure caught { msg; shared; comp } env sg parsetree =
  (*  TODO @xvw *)
  let continue_typing = continue_typing comp (fun i -> i.Parsetree.pstr_loc) in

  let rec loop env sg parsetree acc =
    (match Atomic.get msg.Domain_msg.from_main with
    | `Empty -> ()
    | `Waiting ->
      while Atomic.get msg.Domain_msg.from_main == `Waiting do
        Domain.cpu_relax ()
      done
    | `Closing -> raise Domain_msg.Closing
    | `Cancel ->
      (* Cancel_struct is catched by type_implementation *)
      raise (Cancel_struc acc));

    Shared.lock shared;
    match parsetree with
    | parsetree_item :: rest ->
      let items, sg', part_env =
        Typemod.merlin_type_structure env sg [ parsetree_item ]
      in
      let typedtree_items =
        (items.Typedtree.str_items, items.Typedtree.str_type)
      in
      let part_rev_sg = List.rev_append sg' sg in
      let item =
        { parsetree_item;
          typedtree_items;
          part_env;
          part_rev_sg;
          part_snapshot = Btype.snapshot ();
          part_stamp = Ident.get_currentstamp ();
          part_uid = Shape.Uid.get_current_stamp ();
          part_errors = !caught;
          part_checks = !Typecore.delayed_checks;
          part_warnings = Warnings.backup ()
        }
      in
      Shared.unlock shared;
      (*  TODO @xvw *)
      if not (continue_typing parsetree_item) then (env, rest, item :: acc)
      else loop part_env part_rev_sg rest (item :: acc)
    | [] ->
      Shared.unlock shared;
      (env, [], List.rev acc)
  in
  loop env sg parsetree []

exception
  Cancel_sig of (Parsetree.signature_item, Typedtree.signature_item) item list

let type_signature caught { msg; shared; comp } env sg psg_modalities psg_loc parsetree =
  (*  TODO @xvw *)
  let continue_typing = continue_typing comp (fun i -> i.Parsetree.psig_loc) in

let rec loop env sg parsetree acc =
  (match Atomic.get msg.Domain_msg.from_main with
  | `Empty -> ()
  | `Waiting ->
    while Atomic.get msg.Domain_msg.from_main == `Waiting do
      Domain.cpu_relax ()
    done
  | `Closing -> raise Domain_msg.Closing
  | `Cancel ->
    (* Cancel_sig is catched by type_interface *)
    raise (Cancel_sig acc));

    Shared.lock shared;

    match parsetree with
    | parsetree_item :: rest ->
      let { Typedtree.sig_final_env = part_env; sig_items; sig_type; sig_modalities = _; sig_sloc = _ } =
        Typemod.merlin_transl_signature env sg
        (Ast_helper.Sg.mk ~loc:psg_loc ~modalities:psg_modalities
           [ parsetree_item ])
      in
      let part_rev_sg = List.rev_append sig_type sg in
      let item =
        { parsetree_item;
          typedtree_items = (sig_items, sig_type);
          part_env;
          part_rev_sg;
          part_snapshot = Btype.snapshot ();
          part_stamp = Ident.get_currentstamp ();
          part_uid = Shape.Uid.get_current_stamp ();
          part_errors = !caught;
          part_checks = !Typecore.delayed_checks;
          part_warnings = Warnings.backup ()
        }
      in
      Shared.unlock shared;
      (*  TODO @xvw *)
      if not (continue_typing parsetree_item) then (env, rest, item :: acc)
      else loop part_env part_rev_sg rest (item :: acc)
    | [] ->
      Shared.unlock shared;
      (env, [], List.rev acc)
  in
  loop env sg parsetree []

open Effect
open Effect.Deep

type _ Effect.t +=
  | Internal_partial :
      typedtree_items cache_result * typer_cache_stats
      -> unit t
  | Partial : result -> unit t

let type_implementation config caught partial parsetree =
  let { env; snapshot; ident_stamp; uid_stamp; value = prefix; index; _ } =
    get_cache config
  in
  let rev_prefix, parsetree_suffix, cache_stats =
    match prefix with
    | Some (Implementation_items items) -> compatible_prefix_rev items parsetree
    | Some (Interface_items _) | None -> ([], parsetree, Miss)
  in
  let env', sg', snap', stamp', uid_stamp', warn' =
    match rev_prefix with
    | [] -> (env, [], snapshot, ident_stamp, uid_stamp, Warnings.backup ())
    | x :: _ ->
      caught := x.part_errors;
      Typecore.delayed_checks := x.part_checks;
      ( x.part_env,
        x.part_rev_sg,
        x.part_snapshot,
        x.part_stamp,
        x.part_uid,
        x.part_warnings )
  in
  Btype.backtrack snap';
  Warnings.restore warn';
  Env.cleanup_functor_caches ~stamp:stamp';
  let stamp = List.length rev_prefix - 1 in
  Stamped_hashtable.backtrack !index_changelog ~stamp;
  Env.cleanup_usage_tables ~stamp:uid_stamp';
  Shape.Uid.restore_stamp uid_stamp';
  let aux preprocessed_suffix suffix =
    let () =
      List.iteri
        ~f:(fun i { typedtree_items = items, _; _ } ->
          let stamp = stamp + i + 1 in
          !index_items ~index ~stamp config (`Impl items))
        suffix
    in
    let value =
      Implementation_items (List.rev_append rev_prefix (preprocessed_suffix @ suffix))
    in
    return_and_cache { env; snapshot; ident_stamp; uid_stamp; value; index }
  in
  try
    match partial.comp with
    | All ->
      let _, _, suffix = type_structure caught partial env' sg' parsetree_suffix in
      (aux [] suffix, cache_stats)
    | Partial _ ->
      let nenv, nparsetree, first_suffix =
        type_structure caught partial env' sg' parsetree_suffix
      in
      let partial_result = aux [] first_suffix in
      perform (Internal_partial (partial_result, cache_stats));
      let _, _, second_suffix =
        type_structure caught { partial with comp = All } nenv sg' nparsetree
      in
      (aux first_suffix second_suffix, cache_stats)
  with Cancel_struc suffix ->
    (* Caching before cancellation *)
    aux [] suffix |> ignore;
    raise Domain_msg.Cancel

let type_interface config caught partial (parsetree : Parsetree.signature) =
  let { env; snapshot; ident_stamp; uid_stamp; value = prefix; index; _ } =
    get_cache config
  in
  let rev_prefix, parsetree_suffix, cache_stats =
    match prefix with
    | Some
        (Interface_items
          { items; psig_modalities; sig_modalities = _; sig_sloc = _ })
    (* only use the cached items if they were typed using the same modalities on the sig *)
      when List.equal
             ~eq:(fun
                 { Location.txt = Parsetree.Modality a; loc = _ }
                 { Location.txt = Parsetree.Modality b; loc = _ }
               -> String.equal a b)
             psig_modalities parsetree.psg_modalities ->
      compatible_prefix_rev items parsetree.psg_items
    | Some (Interface_items _) | Some (Implementation_items _) | None ->
      ([], parsetree.psg_items, Miss)
  in
  let env', sg', snap', stamp', uid_stamp', warn' =
    match rev_prefix with
    | [] -> (env, [], snapshot, ident_stamp, uid_stamp, Warnings.backup ())
    | x :: _ ->
      caught := x.part_errors;
      Typecore.delayed_checks := x.part_checks;
      ( x.part_env,
        x.part_rev_sg,
        x.part_snapshot,
        x.part_stamp,
        x.part_uid,
        x.part_warnings )
  in
  Btype.backtrack snap';
  Warnings.restore warn';
  Env.cleanup_functor_caches ~stamp:stamp';
  let stamp = List.length rev_prefix in
  Stamped_hashtable.backtrack !index_changelog ~stamp;
  Env.cleanup_usage_tables ~stamp:uid_stamp';
  Shape.Uid.restore_stamp uid_stamp';
  let aux preprocessed_suffix suffix =
    let () =
      List.iteri
        ~f:(fun i { typedtree_items = items, _; _ } ->
          let stamp = stamp + i + 1 in
          !index_items ~index ~stamp config (`Intf items))
        suffix
    in
    (* transl an empty signature to get the sig_modalities and sig_sloc *)
    let ({ sig_final_env = _;
          sig_items = _;
          sig_type = _;
          sig_modalities;
          sig_sloc
        }
          : Typedtree.signature) =
      Typemod.merlin_transl_signature Env.empty []
        (Ast_helper.Sg.mk ~modalities:parsetree.psg_modalities
          ~loc:parsetree.psg_loc [])
    in
    let value =
      Interface_items 
        { items = List.rev_append rev_prefix (preprocessed_suffix @ suffix);
          sig_modalities;
          psig_modalities = parsetree.psg_modalities;
          sig_sloc
        }
    in
    return_and_cache { env; snapshot; ident_stamp; uid_stamp; value; index }
  in
  try
    match partial.comp with
    | All ->
      let _, _, suffix = type_signature caught partial env' sg' parsetree.psg_modalities parsetree.psg_loc parsetree_suffix in
      (aux [] suffix, cache_stats)
    | Partial _ ->
      let nenv, nparsetree, first_suffix =
        type_signature caught partial env' sg' parsetree.psg_modalities parsetree.psg_loc parsetree_suffix
      in
      let partial_result = aux [] first_suffix in
      perform (Internal_partial (partial_result, cache_stats));
      let _, _, second_suffix =
        type_signature caught { partial with comp = All } nenv sg' parsetree.psg_modalities parsetree.psg_loc nparsetree
      in
      (aux first_suffix second_suffix, cache_stats)
  with Cancel_sig suffix ->
    (* Caching before cancellation *)
    aux [] suffix |> ignore;
    raise Domain_msg.Cancel

let run config partial parsetree =
  if not (Env.check_state_consistency ()) then (
    (* Resetting the local store will clear the load_path cache.
       Save it now, reset the store and then restore the path. *)
    let { Load_path.visible; hidden } = Load_path.get_paths () in
    (* Same story with the registered parameters. *)
    let parameters = Env.parameters () in
    Mocaml.flush_caches ();
    Local_store.reset ();
    Load_path.reset ();
    Load_path.(init ~auto_include:no_auto_include ~visible ~hidden);
    List.iter ~f:Env.register_parameter parameters);
  let caught = ref [] in
  Msupport.catch_errors Mconfig.(config.ocaml.warnings) caught @@ fun () ->
  Typecore.reset_delayed_checks ();

  let aux cached_result cache_stat =
    let stamp = Ident.get_currentstamp () in
    Typecore.reset_delayed_checks ();
    { config;
      initial_env = cached_result.env;
      initial_snapshot = cached_result.snapshot;
      initial_stamp = cached_result.ident_stamp;
      stamp;
      initial_uid_stamp = cached_result.uid_stamp;
      typedtree = cached_result.value;
      index = cached_result.index;
      cache_stat
    }
  in
  Effect.Deep.match_with
    (function
      | `Implementation parsetree ->
        type_implementation config caught partial parsetree
      | `Interface parsetree ->
        type_interface config caught partial parsetree)
    parsetree
    { retc = (fun (cached_result, cache_stat) -> aux cached_result cache_stat);
      exnc = raise;
      effc = fun (type a) (eff : a Effect.t) ->
        match eff with
        | Internal_partial (cached_result, cache_stat) ->
          Some (fun (k : (a, _) Effect.Deep.continuation) ->
            let r = aux cached_result cache_stat in
            perform (Partial r);
            continue k ()
          )
        | _ -> None
    }

let get_env ?pos:_ t =
  Option.value ~default:t.initial_env
    (match t.typedtree with
    | Implementation_items l ->
      Option.map ~f:(fun x -> x.part_env) (List.last l)
    | Interface_items
        { items = l; sig_modalities = _; psig_modalities = _; sig_sloc = _ } ->
      Option.map ~f:(fun x -> x.part_env) (List.last l))

let get_errors t =
  let errors, checks =
    Option.value ~default:([], [])
      (let f x = (x.part_errors, x.part_checks) in
       match t.typedtree with
       | Implementation_items l -> Option.map ~f (List.last l)
       | Interface_items l -> Option.map ~f (List.last l.items))
  in
  let caught = ref errors in
  Typecore.delayed_checks := checks;
  Msupport.catch_errors
    Mconfig.(t.config.ocaml.warnings)
    caught Typecore.force_delayed_checks;
  Typecore.reset_delayed_checks ();
  !caught

let get_typedtree t =
  let split_items l =
    let typd, typs = List.split (List.map ~f:(fun x -> x.typedtree_items) l) in
    (List.concat typd, List.concat typs)
  in
  match t.typedtree with
  | Implementation_items l ->
    let str_items, str_type = split_items l in
    `Implementation { Typedtree.str_items; str_type; str_final_env = get_env t }
  | Interface_items { items = l; psig_modalities = _; sig_modalities; sig_sloc }
    ->
    let sig_items, sig_type = split_items l in
    `Interface
      { Typedtree.sig_items;
        sig_type;
        sig_final_env = get_env t;
        sig_modalities;
        sig_sloc
      }

let get_index t = t.index

let get_stamp t = t.stamp

let node_at ?(skip_recovered = false) ?let_pun_behavior t pos_cursor =
  let node = Mbrowse.of_typedtree (get_typedtree t) in
  log ~title:"node_at" "Node: %s" (Mbrowse.print () node);
  let rec select = function
    (* If recovery happens, the incorrect node is kept and a recovery node
       is introduced, so the node to check for recovery is the second one. *)
    | (_, _) :: ((_, node') :: _ as ancestors) when Mbrowse.is_recovered node'
      -> select ancestors
    | l -> l
  in
  match Mbrowse.deepest_before ?let_pun_behavior pos_cursor [ node ] with
  | [] -> [ (get_env t, Browse_raw.Dummy) ]
  | path when skip_recovered -> select path
  | path ->
    log ~title:"node_at" "Deepest before %s" (Mbrowse.print () path);
    path
