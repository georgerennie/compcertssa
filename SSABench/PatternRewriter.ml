open SSA
open Maps

(* A pattern rewriter based on the Buffed implementation. Note that this
   currently doesn't support phi nodes *)

module Worklist =
  struct
    (* Ocaml linked lists don't allow O(1) access so we can't implement the
       worklist as in lean. Instead, we allow O(1) deletion by tracking which
       nodes are still considered to be in the stack, at the cost of a lookup
       on pop. The stack therefore is mainly used for ordering *)
    type t = {
      stack : node list;
      node_in_stack : unit PTree.t;
    }

    let empty = {
      stack = [];
      node_in_stack = PTree.empty;
    }

    let push node wl : t =
      let stack = node :: wl.stack in
      let node_in_stack = PTree.set node () wl.node_in_stack in
      { stack; node_in_stack }

    let push_list (nodes : node list) wl : t =
      List.fold_left (fun acc node -> push node acc) wl nodes

    let rec pop wl : (t * node) option =
      match wl.stack with
      | [] -> None
      | x :: xs ->
        match PTree.get x wl.node_in_stack with
        | Some _ ->
          Some ({ stack = xs; node_in_stack = PTree.remove x wl.node_in_stack }, x)
        | None -> pop { wl with stack = xs }

    let remove node wl : t =
      { wl with node_in_stack = PTree.remove node wl.node_in_stack }

    (* adds all nodes in the code to a new worklist *)
    let from_code (code : code) : t =
      PTree.fold (fun wl node _ -> push node wl) code empty
  end

type t = {
  ctx : Rewriter.t;
  wl : Worklist.t;
  changed : bool;
}

let from_rewriter (ctx : Rewriter.t) : t =
  { ctx; wl = Worklist.from_code (Rewriter.get_code ctx); changed = false }

let get_instr rw node : instruction option =
  Rewriter.get_instr rw.ctx node

(* Get the reg defining a node *)
let definition rw reg : node option =
  Rewriter.definition rw.ctx reg

(* Erase an unused node. The caller must confirm it is unused.
   This detaches it, erases it and removes it from worklists *)
let erase_node node rw : t =
  let ctx = Rewriter.erase_node node rw.ctx in
  let wl = Worklist.remove node rw.wl in
  { ctx; wl; changed = true }

let erase_node_if_unused node rw : t =
  match (Rewriter.users rw.ctx node) with
  | [] -> erase_node node rw
  | _ -> rw

(* Replace all uses of the output of an op with the output of another, and
   remove that node *)
let replace_node old_node new_node rw : t =
  let (ctx, old_node_users) = Rewriter.replace_node old_node new_node rw.ctx in
  let wl = Worklist.push_list old_node_users rw.wl in
  { ctx; wl; changed = true }

(* Replaces an operation node with a new operation that must drive the same register *)
let replace_node_inplace node new_instr rw : t =
  let wl = Worklist.push_list (Rewriter.users rw.ctx node) rw.wl in
  { ctx = Rewriter.replace_node_inplace node new_instr rw.ctx; wl; changed = true }

type rewrite_pattern = t -> node -> t option

let worklist_pop rw : (t * node) option =
  Worklist.pop rw.wl |> Option.map (fun (wl, n) -> ({ rw with wl }, n))

(* Apply the given rewrite pattern to all operations in the function.
   Return the new context, and a boolean indicating whether any changes were made. *)
let apply_once_in_code (pattern : rewrite_pattern) (ctx : Rewriter.t) : (Rewriter.t * bool) =
  let rw = from_rewriter ctx in
  let rec go rw =
    match worklist_pop rw with
    | None -> rw.ctx, rw.changed
    | Some (rw, node) -> go (pattern rw node |> Option.value ~default:rw)
  in
  go rw

let rec apply_in_code (pattern : rewrite_pattern) (ctx : Rewriter.t) : Rewriter.t =
  match apply_once_in_code pattern ctx with
  | ctx, false -> ctx
  | ctx, true -> apply_in_code pattern ctx
