open AST
open SSA
open Camlcoq
open Maps
open Op
open Registers
open Printf

let (let*) o f = Option.bind o f
let (let+) o f = Option.map f o

(* SSA function augmented with extra bookkeeping for use-def chains and previous
   instruction lookup *)
module Rewriter =
  struct
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

  end

(* A pattern rewriter based on the Buffed implementation. Note that this
   currently doesn't support phi nodes *)
module PatternRewriter =
  struct
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

    let apply_in_code (pattern : rewrite_pattern) (code : code) : code =
      let rec go ctx =
        match apply_once_in_code pattern ctx with
        | ctx, false -> Rewriter.get_code ctx
        | ctx, true -> go ctx
      in
      go (Rewriter.from_code code)

    let apply_in_function (pattern : rewrite_pattern) (fn : coq_function) : coq_function =
      { fn with fn_code = apply_in_code pattern fn.fn_code }
  end

module FnBuilder =
  struct
    type t = {
      f : coq_function;
      insertion_index : P.t;
    }

    let add (instr_fn : reg -> node -> instruction) b : t * reg =
      let index = b.insertion_index in
      let next_index = P.succ index in
      let instr = instr_fn index next_index in
      let fn_code = PTree.set index instr b.f.fn_code in
      ({ f = { b.f with fn_code }; insertion_index = next_index }, index)

    let empty : t =
      let initial_index = P.one in
      {
        f = {
          fn_sig = {
            sig_args = [];
            sig_res = Tret Tint;
            sig_cc = cc_default;
          };
          fn_params = [];
          fn_stacksize = coqint_of_camlint 0l;
          fn_code = PTree.empty;
          fn_phicode = PTree.empty;
          fn_entrypoint = initial_index;
          fn_ext_params = [];
          fn_dom_test = fun _ _ -> assert false;
        };
        insertion_index = initial_index
      }
      (* SCCP requires all operations to be reached via edges so the first op
         ends up needing to be a no-op *)
      |> add (fun _ next -> Inop next)
      |> fst

    let int_const const b : t * reg =
      b |> add (fun r n -> Iop (Ointconst (coqint_of_camlint const), [], r, n))

    let return (r : reg) b : coq_function =
      b
      |> add (fun _ _ -> Ireturn (Some r))
      |> fun (b, _) -> b.f

  end

let add_tree_benchmark i init_const add_const =
  let (b, root) =
    FnBuilder.empty
    |> FnBuilder.int_const init_const
  in
  let rec go b acc = function
    | 0 -> b |> FnBuilder.return acc
    | i ->
      let (b, const) = b |> FnBuilder.int_const add_const in
      let (b, acc) = b |> FnBuilder.add (fun r n -> Iop (Oadd, [const; acc], r, n)) in
      go b acc (i - 1)
  in
  go b root i

let add_zero_benchmark i = add_tree_benchmark i 42l 0l
let add_const_benchmark i = add_tree_benchmark i 42l 1l

let mul2_tree_benchmark n root =
  let (b, root) =
    FnBuilder.empty
    |> FnBuilder.int_const root
  in
  let rec go b acc = function
    | 0 -> b |> FnBuilder.return acc
    | i ->
      let (b, const) = b |> FnBuilder.int_const 2l in
      let (b, acc) = b |> FnBuilder.add (fun r n -> Iop (Omul, [acc; const], r, n)) in
      go b acc (i - 1)
  in
  go b root n

let add_zero_folding_pattern (rw : PatternRewriter.t) node : PatternRewriter.t option =
  let* instr = PatternRewriter.get_instr rw node in
  let* (lhs_reg, rhs_reg) =
    match instr with
    | Iop (Oadd, [lhs; rhs], _, _) -> Some (lhs, rhs)
    | _ -> None
  in
  let* lhs = PatternRewriter.definition rw lhs_reg in
  let* rhs = PatternRewriter.definition rw rhs_reg in

  (* Get the left hand side and check it is constant 0 *)
  let* lhs_instr = PatternRewriter.get_instr rw lhs in
  let* const0 =
    match lhs_instr with
    | Iop (Ointconst n, [], _, _) when Z.eq n Z.zero -> Some ()
    | _ -> None
  in

  rw
  |> PatternRewriter.replace_node node rhs
  |> PatternRewriter.erase_node_if_unused lhs
  |> Option.some

let mul2_strength_red_pattern (rw : PatternRewriter.t) node : PatternRewriter.t option =
  let* instr = PatternRewriter.get_instr rw node in
  let* (lhs_reg, rhs_reg, reg, next) =
    match instr with
    | Iop (Omul, [lhs; rhs], reg, next) -> Some (lhs, rhs, reg, next)
    | _ -> None
  in
  let* lhs = PatternRewriter.definition rw lhs_reg in
  let* rhs = PatternRewriter.definition rw rhs_reg in

  (* Get the right hand side and check it is constant 2 *)
  let* rhs_instr = PatternRewriter.get_instr rw rhs in
  let* const2 =
    match rhs_instr with
    | Iop (Ointconst n, [], _, _) when Z.eq n (Z.of_uint 2) -> Some ()
    | _ -> None
  in

  let new_node = Iop (Oadd, [lhs; lhs], reg, next) in

  rw
  |> PatternRewriter.replace_node_inplace node new_node
  |> PatternRewriter.erase_node_if_unused rhs
  |> Option.some

let add_const_folding_pattern (rw : PatternRewriter.t) node : PatternRewriter.t option =
  let* instr = PatternRewriter.get_instr rw node in
  let* (lhs_reg, rhs_reg, reg, next) =
    match instr with
    | Iop (Oadd, [lhs; rhs], reg, next) -> Some (lhs, rhs, reg, next)
    | _ -> None
  in
  let* lhs = PatternRewriter.definition rw lhs_reg in
  let* rhs = PatternRewriter.definition rw rhs_reg in

  let get_const node =
    match PatternRewriter.get_instr rw node with
    | Some (Iop (Ointconst n, [], _, _)) -> Some n
    | _ -> None
  in

  let* lhs_val = get_const lhs in
  let* rhs_val = get_const rhs in
  let new_val = Z.add lhs_val rhs_val in

  rw
  |> PatternRewriter.replace_node_inplace node (Iop (Ointconst new_val, [], reg, next))
  |> PatternRewriter.erase_node_if_unused lhs
  |> PatternRewriter.erase_node_if_unused rhs
  |> Option.some

let rewrite_add_zero = PatternRewriter.apply_in_function add_zero_folding_pattern
let rewrite_add_const = PatternRewriter.apply_in_function add_const_folding_pattern
let rewrite_mul2_red = PatternRewriter.apply_in_function mul2_strength_red_pattern

let time name f =
  let t = Unix.gettimeofday () in
  let res = f () in
  printf "%s time (s): %.10f\n" name (Unix.gettimeofday () -. t);
  res

let run_bench name n =
  printf "CompCertSSA benchmark %s %d\n" name n;

  let run create rewrite show =
    let benchmark = time "create" (fun () -> create n) in
    let rewritten = time "rewrite" (fun () -> rewrite benchmark) in
    if show then PrintSSA.print_function stdout P.one rewritten
  in

  match name with
  | "add-zero" -> run add_zero_benchmark rewrite_add_zero true
  | "add-zero-sccp" -> run add_zero_benchmark SCCPopt.transf_function false
  | "constant-folding" -> run add_const_benchmark rewrite_add_const true
  | "constant-folding-sccp" -> run add_const_benchmark SCCPopt.transf_function false
  | "mul2-reduce" -> run (fun n -> mul2_tree_benchmark n 42l) rewrite_mul2_red false
  | s -> printf "Unrecognised benchmark %s\n" s

let _ =
  (* The compcert driver sets this and it seems to improve perf ~30% *)
  Gc.set {
    (Gc.get()) with
      Gc.minor_heap_size = 524288; (* 512k *)
      Gc.major_heap_increment = 4194304 (* 4M *)
  };

  match Sys.argv with
  | [|_; bench|] -> run_bench bench 50000
  | [|_; bench; n|] -> run_bench bench (int_of_string n)
  | _ -> printf "Usage: ssabench [benchmark <n>]\n"
