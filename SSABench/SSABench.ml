open SSA
open Camlcoq
open Op
open Printf

let (let*) o f = Option.bind o f
let (let+) o f = Option.map f o

module Pattern =
  struct
    let add_constant_folding (rw : PatternRewriter.t) node : PatternRewriter.t option =
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

    let add_zero_folding (rw : PatternRewriter.t) node : PatternRewriter.t option =
      let* instr = PatternRewriter.get_instr rw node in
      let* (lhs_reg, rhs_reg) =
        match instr with
        | Iop (Oadd, [lhs; rhs], _, _) -> Some (lhs, rhs)
        | _ -> None
      in
      let* lhs = PatternRewriter.definition rw lhs_reg in
      let* rhs = PatternRewriter.definition rw rhs_reg in

      (* Get the right hand side and check it is constant 0 *)
      let* rhs_instr = PatternRewriter.get_instr rw rhs in
      let* const0 =
        match rhs_instr with
        | Iop (Ointconst n, [], _, _) when Z.eq n Z.zero -> Some ()
        | _ -> None
      in

      rw
      |> PatternRewriter.replace_node node lhs
      |> PatternRewriter.erase_node_if_unused rhs
      |> Option.some

    let mul_two_reduce (rw : PatternRewriter.t) node : PatternRewriter.t option =
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

  end

(* Rewrites as above but without using the PatternRewriter interface, instead
   applying the rewrites in custom locations *)
module CustomRewriter =
  struct
    type pattern = Rewriter.t -> node -> Rewriter.t option

    let add_zero_folding (rw : Rewriter.t) node : Rewriter.t option =
      let* instr = Rewriter.get_instr rw node in
      let* (lhs_reg, rhs_reg) =
        match instr with
        | Iop (Oadd, [lhs; rhs], _, _) -> Some (lhs, rhs)
        | _ -> None
      in
      let* lhs = Rewriter.definition rw lhs_reg in
      let* rhs = Rewriter.definition rw rhs_reg in

      (* Get the left hand side and check it is constant 0 *)
      let* lhs_instr = Rewriter.get_instr rw lhs in
      let* const0 =
        match lhs_instr with
        | Iop (Ointconst n, [], _, _) when Z.eq n Z.zero -> Some ()
        | _ -> None
      in

      let (rw, _) = rw |> Rewriter.replace_node node rhs in
      rw
      |> Rewriter.erase_node_if_unused lhs
      |> Option.some

    let rewrite_first (fn : coq_function) (op : operation) (pat : pattern) : coq_function =
      let rw = Rewriter.from_code fn.fn_code in
      let rec first_node node : node option =
        let* instr = Rewriter.get_instr rw node in
        match instr with
        | Iop (op, _, _, _) -> Option.some node
        | _ -> let* next = Rewriter.instr_succ instr in first_node next
      in
      let node = first_node fn.fn_entrypoint |> Option.get in

      let fn_code =
        pat rw node
        |> Option.value ~default:rw
        |> Rewriter.get_code
      in
      { fn with fn_code }

  end

module Program =
  struct

    (* Create a program that looks like:
       func @main() -> int {
         %0 = arith.constant [root] : int
         %1 = arith.constant [inc] : int
         %2 = [opcode] %0, %1 : int
         %3 = arith.constant [inc] : int
         %4 = [opcode] %2, %3 : int
         ... *)
    let const_fold_tree op n root inc : coq_function =
      let b = FnBuilder.empty in
      let (b, root_node) = b |> FnBuilder.int_const root in
      let rec go b acc = function
        | 0 -> b |> FnBuilder.return acc
        | i ->
          let (b, const) = b |> FnBuilder.int_const inc in
          let (b, acc) = b |> FnBuilder.add (fun r n -> Iop (op, [acc; const], r, n)) in
          go b acc (i - 1)
      in
      go b root_node n

    let add_zero_tree n = const_fold_tree Oadd n 42l 0l
    let add_one_tree n = const_fold_tree Oadd n 42l 1l
    let mul_two_tree n = const_fold_tree Omul n 42l 2l

    (* Create a program that looks like:
       func @main() -> int {
         %0 = arith.constant 3 : int
         %reuse = arith.constant inc : int
         %2 = arith.addi %reuse, %0 : int
         %3 = arith.addi %reuse, %2 : int
         ... *)
    let const_reuse_tree op n root inc : coq_function =
      let b = FnBuilder.empty in
      let (b, root) = b |> FnBuilder.int_const root in
      let (b, reuse) = b |> FnBuilder.int_const inc in

      let rec go b acc = function
        | 0 -> b |> FnBuilder.return acc
        | i ->
          let (b, acc) = b |> FnBuilder.add (fun r n -> Iop (op, [acc; reuse], r, n)) in
          go b acc (i - 1)
      in
      go b root n

    let add_zero_reuse_tree n = const_reuse_tree Oadd n 42l 0l

    (* Create a program that looks like:
       func @main() -> int {
         %0 = arith.constant [lhs] : int
         %1 = arith.constant [rhs] : int
         %reuse = [opcode] %0, %1 : int
         %3 = [opcode] %reuse, %reuse : int
         %4 = [opcode] %3, %reuse : int
         %5 = [opcode] %4, %reuse : int
        ... *)
    let const_lots_of_reuse_tree op n lhs rhs =
      let b = FnBuilder.empty in
      let (b, lhs_node) = b |> FnBuilder.int_const lhs in
      let (b, rhs_node) = b |> FnBuilder.int_const rhs in
      let (b, reuse) = b |> FnBuilder.add (fun r n -> Iop (op, [lhs_node; rhs_node], r, n)) in

      let rec go b acc = function
        | 0 -> b |> FnBuilder.return acc
        | i ->
          let (b, acc) = b |> FnBuilder.add (fun r n -> Iop (op, [acc; reuse], r, n)) in
          go b acc (i - 1)
      in
      go b reuse n

    let add_zero_lots_of_reuse_tree n = const_lots_of_reuse_tree Oadd n 42l 0l

  end

module Rewrite =
  struct
    let add_constant_folding = PatternRewriter.apply_in_function Pattern.add_constant_folding
    let add_zero_folding = PatternRewriter.apply_in_function Pattern.add_zero_folding
    let mul_two_reduce = PatternRewriter.apply_in_function Pattern.mul_two_reduce
    let add_zero_first_add fn = CustomRewriter.rewrite_first fn Oadd CustomRewriter.add_zero_folding
  end

let time name f =
  let t = Unix.gettimeofday () in
  let res = f () in
  printf "%s time (s): %.10f\n" name (Unix.gettimeofday () -. t);
  res

let run n create rewrite print : coq_function =
  let benchmark = time "create" (fun () -> create n) in
  let rewritten = time "rewrite" (fun () -> rewrite benchmark) in
  if print then PrintSSA.print_function stdout P.one rewritten;
  rewritten


let run_benchmark name n : coq_function =
  printf "CompCertSSA benchmark %s %d\n" name n;

  match name with
  | "constant-folding" ->             run n Program.add_one_tree                Rewrite.add_constant_folding true
  | "add-zero" ->                     run n Program.add_zero_tree               Rewrite.add_zero_folding     true
  | "add-zero-reuse" ->               run n Program.add_zero_reuse_tree         Rewrite.add_zero_folding     true
  | "add-zero-once-operand-reused" -> run n Program.add_zero_reuse_tree         Rewrite.add_zero_first_add   false
  | "add-zero-one-operation-reuse" -> run n Program.add_zero_lots_of_reuse_tree Rewrite.add_zero_first_add   false
  | "mul2-reduce" ->                  run n Program.mul_two_tree                Rewrite.mul_two_reduce       false
  | "add-zero-sccp" ->                run n Program.add_zero_tree               SCCPopt.transf_function      false
  | "constant-folding-sccp" ->        run n Program.add_one_tree                SCCPopt.transf_function      false
  | _ -> failwith "Unrecognised benchmark\n"

let _ =
  (* The compcert driver sets this and it seems to improve perf ~30% *)
  Gc.set {
    (Gc.get()) with
      Gc.minor_heap_size = 524288; (* 512k *)
      Gc.major_heap_increment = 4194304 (* 4M *)
  };

  match Sys.argv with
  | [|_; bench|] -> run_benchmark bench 50000 |> ignore
  | [|_; bench; n|] -> run_benchmark bench (int_of_string n) |> ignore
  | _ -> printf "Usage: ssabench [benchmark <n>]\n"
