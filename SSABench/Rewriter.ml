open SSA
open Camlcoq
open Maps
open Registers

(* SSA function augmented with extra bookkeeping for use-def chains and previous
   instruction lookup *)

type t = {
  code : code;
  (* Map from nodes to previous node in the program order *)
  prev_nodes : node PTree.t;
  (* Map from registers to nodes using their value *)
  du_chain : node list PTree.t;
  (* Map from regs to the node defining them *)
  reg_defs : node PTree.t;
}

let get_instr rw (node : node) : instruction option =
  PTree.get node rw.code

let get_code rw : code = rw.code

(* Get the reg defined by an instruction *)
let instr_reg instr : reg option =
  match instr with
  | Iop (_, _, dest, _)
  | Iload (_, _, _, dest, _)
  | Icall (_, _, _, dest, _) -> Some dest
  | Ibuiltin _ -> assert false
  | _ -> None

(* Get the registers used by an instruction *)
let instr_args instr : reg list =
  match instr with
  | Iop (_, args, _, _)
  | Iload (_, _, args, _, _)
  | Istore (_, _, args, _, _)
  | Icall (_, _, args, _, _)
  | Itailcall (_, _, args)
  | Icond (_, args, _, _) -> args
  | Ijumptable (arg, _) -> [arg]
  | Ibuiltin (_, args, _, _) -> assert false
  | Ireturn arg -> Option.to_list arg
  | _ -> []

(* Get the single successor of an instruction if there is one *)
let instr_succ instr : node option =
  match SSA.successors_instr instr with
    | [succ] -> Some succ
    | [] -> None
    (* we don't support ops with multiple successors for now *)
    | _ -> assert false 

(* Get the nodes that use a given reg *)
let users rw reg : node list =
  PTree.get reg rw.du_chain |> Option.value ~default:[]

(* Get the reg defining a node if there is one *)
let definition rw reg : node option = PTree.get reg rw.reg_defs

(* Remove node from the du_chains of its args *)
let remove_from_du node instr du_chain : node list PTree.t =
  let remove du_chain reg =
    match PTree.get reg du_chain with
    | None -> du_chain
    | Some chain ->
      match List.filter (fun n -> not (P.eq n node)) chain with
      | [] -> PTree.remove reg du_chain
      | new_chain -> PTree.set reg new_chain du_chain
  in
  List.fold_left remove du_chain (instr_args instr)

(* Add node to the du_chains of its args *)
let add_to_du node instr du_chain : node list PTree.t =
  let add du_chain reg =
    let uses = PTree.get reg du_chain |> Option.value ~default:[] in
    PTree.set reg (node :: uses) du_chain
  in
  List.fold_left add du_chain (instr_args instr)

(* Construct a rewriter with its metadata over a function body *)
let from_code (code : code) : t =
  let initial = {
    code;
    prev_nodes = PTree.empty;
    du_chain = PTree.empty;
    reg_defs = PTree.empty;
  } in

  let add_node rw node instr =
    let set_ref tree idx =
      match idx with
      | Some n -> PTree.set n node tree
      | None -> tree
    in

    (* If node transitions to succ, set node as succ's prev_node *)
    let prev_nodes = set_ref rw.prev_nodes (instr_succ instr) in
    let du_chain = add_to_du node instr rw.du_chain in
    let reg_defs =
      match instr_reg instr with
      | Some reg -> PTree.set reg node rw.reg_defs
      | None -> rw.reg_defs
    in

    { rw with prev_nodes; du_chain; reg_defs }
  in
  PTree.fold add_node code initial

(* Detach a node from the control flow - this doesn't remove its users from
   the DU chain. The node must have a successor node in the control flow *)
let detach_node node rw : t =
  let instr = get_instr rw node |> Option.get in

  (* we don't support ops without a single successor for now *)
  let succ = instr_succ instr |> Option.get in

  (* Update prev_nodes for this node and successor *)
  let prev_node = PTree.get node rw.prev_nodes |> Option.get in
  let prev_nodes =
    rw.prev_nodes
    |> PTree.remove node
    |> PTree.set succ prev_node
  in

  let map_succ = function
    | n when P.eq n node -> succ
    | n -> n
  in

  (* It is assumed that any instruction passed here is a predecessor of node
     and thus if it has just one successor it must be node *)
  let map_instr = function
    | Inop _ -> Inop succ
    | Iop (o, a, r, _) -> Iop (o, a, r, succ)
    | Iload (m, ad, a, r, _) -> Iload (m, ad, a, r, succ)
    | Istore (m, ad, a, r, _) -> Istore (m, ad, a, r, succ)
    | Icall (s, i, a, r, _) -> Icall (s, i, a, r, succ)
    | Ibuiltin (e, a, r, _) -> Ibuiltin (e, a, r, succ)
    | Icond (c, a, ifso, ifnot) -> Icond (c, a, map_succ ifso, map_succ ifnot)
    | Ijumptable (a, s) -> Ijumptable (a, List.map map_succ s)
    | i -> i
  in

  (* Update prev instruction to point at new successor *)
  let code =
    get_instr rw prev_node
    |> Option.get
    |> map_instr
    |> fun new_instr -> PTree.set prev_node new_instr rw.code
  in
  { rw with code; prev_nodes }

(* Erase a node from the function, detaching it and updating the
   def-use chain and reg definition map *)
let erase_node node rw : t =
  let rw = detach_node node rw in

  let instr = get_instr rw node |> Option.get in
  let reg = instr_reg instr in

  let remove_reg ptree =
    match reg with
    | None -> ptree
    | Some reg -> PTree.remove reg ptree
  in

  let du_chain =
    rw.du_chain
    |> remove_reg
    |> remove_from_du node instr
  in

  let reg_defs = remove_reg rw.reg_defs in
  let code = PTree.remove node rw.code in

  { rw with code; du_chain; reg_defs }

let erase_node_if_unused node rw : t =
  match (users rw node) with
  | [] -> erase_node node rw
  | _ -> rw

(* Map the args of an instruction from old_node to new_node *)
let map_instr_args old_reg new_reg instr : instruction =
  let map_one = function
    | n when P.eq n old_reg -> new_reg
    | n -> n
  in
  let map = List.map map_one in
  match instr with
  | Inop n -> Inop n
  | Iop (o, args, r, n) -> Iop (o, map args, r, n)
  | Iload (m, a, args, r, n) -> Iload (m, a, map args, r, n)
  | Istore (m, a, args, r, n) -> Istore (m, a, map args, r, n)
  | Icall (s, i, args, r, n) -> Icall (s, i, map args, r, n)
  | Itailcall (s, f, args) -> Itailcall (s, f, map args)
  | Ibuiltin (e, args, r, n) -> assert false
  | Icond (c, args, s, n) -> Icond (c, map args, s, n)
  | Ijumptable (arg, s) -> Ijumptable (map_one arg, s)
  | Ireturn arg -> Ireturn (Option.map map_one arg)

(* Replace a node defining a value with a different one, erasing the old one.
   This updates the nodes using the old node to instead use the reg defined
   by the new one.
   Returns the new rewriter as well as the list of nodes that used the result
   of the old node. *)
let replace_node old_node new_node rw : t * node list =
  let old_instr = get_instr rw old_node |> Option.get in
  let new_instr = get_instr rw new_node |> Option.get in
  let old_reg = instr_reg old_instr |> Option.get in
  let new_reg = instr_reg new_instr |> Option.get in
  let old_node_users = users rw old_reg in
  let new_node_users = users rw new_reg in

  (* Update the users of the old node to instead use the new node *)
  let update_user code user =
    PTree.get user code
    |> Option.get
    |> map_instr_args old_reg new_reg
    |> fun instr -> PTree.set user instr code
  in
  let code = List.fold_left update_user rw.code old_node_users in

  (* TODO: dedup the use list *)

  (* Add the users of the old node to the users of the new node *)
  let combined_users = List.append old_node_users new_node_users in
  let du_chain = PTree.set new_reg combined_users rw.du_chain in

  let rw = { rw with code; du_chain } in
  let rw = erase_node old_node rw in
  (rw, old_node_users)

(* Replace an operation node with a new operation in place, writing to the
   same register and with the same successor *)
let replace_node_inplace node new_instr rw : t =
  let old_instr = get_instr rw node |> Option.get in

  let new_instr =
    match (old_instr, new_instr) with
    | (Iop (_, _, res, next), Iop (op, args, _, _)) -> Iop (op, args, res, next)
    | _ -> assert false
  in

  let du_chain =
    rw.du_chain
    |> remove_from_du node old_instr
    |> add_to_du node new_instr
  in

  let code = PTree.set node new_instr rw.code in

  { rw with du_chain; code }
