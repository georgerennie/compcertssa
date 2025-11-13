open SSA
open Camlcoq
open Op
open Printf

let (let*) o f = Option.bind o f
let (let+) o f = Option.map f o

let time name f =
  let t = Unix.gettimeofday () in
  let res = f () in
  printf "%s time (s): %.10f\n" name (Unix.gettimeofday () -. t);
  res

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
module Custom =
  struct
    type pattern = Rewriter.t -> node -> Rewriter.t option

    let add_constant_folding (rw : Rewriter.t) node : Rewriter.t option =
      let* instr = Rewriter.get_instr rw node in
      let* (lhs_reg, rhs_reg, reg, next) =
        match instr with
        | Iop (Oadd, [lhs; rhs], reg, next) -> Some (lhs, rhs, reg, next)
        | _ -> None
      in
      let* lhs = Rewriter.definition rw lhs_reg in
      let* rhs = Rewriter.definition rw rhs_reg in

      let get_const node =
        match Rewriter.get_instr rw node with
        | Some (Iop (Ointconst n, [], _, _)) -> Some n
        | _ -> None
      in

      let* lhs_val = get_const lhs in
      let* rhs_val = get_const rhs in
      let new_val = Z.add lhs_val rhs_val in

      rw
      |> Rewriter.replace_node_inplace node (Iop (Ointconst new_val, [], reg, next))
      |> Rewriter.erase_node_if_unused lhs
      |> Rewriter.erase_node_if_unused rhs
      |> Option.some

    let add_zero_folding (rw : Rewriter.t) node : Rewriter.t option =
      let* instr = Rewriter.get_instr rw node in
      let* (lhs_reg, rhs_reg) =
        match instr with
        | Iop (Oadd, [lhs; rhs], _, _) -> Some (lhs, rhs)
        | _ -> None
      in
      let* lhs = Rewriter.definition rw lhs_reg in
      let* rhs = Rewriter.definition rw rhs_reg in

      (* Get the right hand side and check it is constant 0 *)
      let* rhs_instr = Rewriter.get_instr rw rhs in
      let* const0 =
        match rhs_instr with
        | Iop (Ointconst n, [], _, _) when Z.eq n Z.zero -> Some ()
        | _ -> None
      in

      let (rw, _) = rw |> Rewriter.replace_node node lhs in
      rw
      |> Rewriter.erase_node_if_unused rhs
      |> Option.some

    let mul_two_reduce (rw : Rewriter.t) node : Rewriter.t option =
      let* instr = Rewriter.get_instr rw node in
      let* (lhs_reg, rhs_reg, reg, next) =
        match instr with
        | Iop (Omul, [lhs; rhs], reg, next) -> Some (lhs, rhs, reg, next)
        | _ -> None
      in
      let* lhs = Rewriter.definition rw lhs_reg in
      let* rhs = Rewriter.definition rw rhs_reg in

      (* Get the right hand side and check it is constant 2 *)
      let* rhs_instr = Rewriter.get_instr rw rhs in
      let* const2 =
        match rhs_instr with
        | Iop (Ointconst n, [], _, _) when Z.eq n (Z.of_uint 2) -> Some ()
        | _ -> None
      in

      let new_node = Iop (Oadd, [lhs; lhs], reg, next) in

      rw
      |> Rewriter.replace_node_inplace node new_node
      |> Rewriter.erase_node_if_unused rhs
      |> Option.some

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
         %0 = arith.constant [root] : int
         %reuse = arith.constant [inc]: int
         %2 = [opcode] %0, %reuse : int
         %3 = [opcode] %2, %reuse : int
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

let rewrite_worklist (fn : coq_function) pattern =
  let ctx = time "chain" (fun () -> Rewriter.from_code fn.fn_code) in
  let ctx = PatternRewriter.apply_in_code pattern ctx in
  { fn with fn_code = Rewriter.get_code ctx }

let rewrite_first (fn : coq_function) (op : operation) (pat : Custom.pattern) : coq_function =
  let rw = time "chain" (fun () -> Rewriter.from_code fn.fn_code) in
  let rec first_node node : node option =
    let* instr = Rewriter.get_instr rw node in
    match instr with
    | Iop (o, _, _, _) when o = op -> Option.some node
    | _ -> let* next = Rewriter.instr_succ instr in first_node next
  in
  let node = first_node fn.fn_entrypoint |> Option.get in

  let fn_code =
    pat rw node
    |> Option.value ~default:rw
    |> Rewriter.get_code
  in
  { fn with fn_code }

let rewrite_first_add (fn : coq_function) (pat : Custom.pattern) : coq_function =
  rewrite_first fn Oadd pat

let rewrite_forwards (fn : coq_function) (pat : Custom.pattern) : coq_function =
  let rw = time "chain" (fun () -> Rewriter.from_code fn.fn_code) in

  let rec go rw node =
    Option.value ~default:rw @@
    let* instr = Rewriter.get_instr rw node in
    let+ next = Rewriter.instr_succ instr in

    let rw = Option.value ~default:rw (pat rw node) in
    go rw next
  in

  let rw = go rw fn.fn_entrypoint in
  { fn with fn_code = Rewriter.get_code rw }

let stringify (fn : coq_function) : string =
  (* From https://stackoverflow.com/a/20576176 *)
  let (ind, outd) = Unix.pipe () in
  let (inc, outc) = (Unix.in_channel_of_descr ind, Unix.out_channel_of_descr outd) in
  PrintSSA.print_function outc P.one fn;
  Out_channel.close outc;
  In_channel.input_all inc

let run n create rewrite_driver rewrite_pattern print : coq_function =
  let benchmark = time "create" (fun () -> create n) in
  let rewritten = time "rewrite" (fun () -> rewrite_driver benchmark rewrite_pattern) in
  if print then PrintSSA.print_function stdout P.one rewritten;
  rewritten

let run_sccp n create : coq_function =
  let benchmark = time "create" (fun () -> create n) in
  let rewritten = time "rewrite" (fun () -> SCCPopt.transf_function benchmark) in
  rewritten

let run_bench name n : coq_function =
  printf "CompCertSSA benchmark %s %d\n" name n;

  let open Program in

  match name with
  | "add-fold-worklist" ->            run n add_one_tree                rewrite_worklist   Pattern.add_constant_folding true
  | "add-zero-worklist" ->            run n add_zero_tree               rewrite_worklist   Pattern.add_zero_folding     true
  | "add-zero-reuse-worklist" ->      run n add_zero_reuse_tree         rewrite_worklist   Pattern.add_zero_folding     true
  | "mul-two-worklist" ->             run n mul_two_tree                rewrite_worklist   Pattern.mul_two_reduce      false

  | "add-fold-forwards" ->            run n add_one_tree                rewrite_forwards   Custom.add_constant_folding  true
  | "add-zero-forwards" ->            run n add_zero_tree               rewrite_forwards   Custom.add_zero_folding      true
  | "add-zero-reuse-forwards" ->      run n add_zero_reuse_tree         rewrite_forwards   Custom.add_zero_folding      true
  | "mul-two-forwards" ->             run n mul_two_tree                rewrite_forwards   Custom.mul_two_reduce       false

  | "add-zero-reuse-first" ->         run n add_zero_reuse_tree         rewrite_first_add  Custom.add_zero_folding     false
  | "add-zero-lots-of-reuse-first" -> run n add_zero_lots_of_reuse_tree rewrite_first_add  Custom.add_zero_folding     false

  | "add-fold-sccp" ->                run_sccp n add_one_tree
  | "add-zero-sccp" ->                run_sccp n add_zero_tree
  | _ -> failwith "Unrecognised benchmark\n"

let test () =
  let expect fns expected =
    let split = Str.split (Str.regexp "[\n\t ]+") in
    let expected_split = split expected in

    let test_one fn =
      let actual = stringify fn in
      let actual_split = split actual in

      if not (actual_split = expected_split) then (
        printf "expected:\n{|%s|}\n" expected;
        printf "actual:\n{|%s|}\n" actual;
        failwith "Test mismatch"
      )
    in

    List.map test_one fns |> ignore
  in

  expect [(run_bench "add-fold-worklist" 10); (run_bench "add-fold-forwards" 10)]
{|$1() {
        goto 1
   23:  return x22
   22:  x22 = 52
        goto 23
    1:  goto 22
}|};

  expect [(run_bench "add-zero-worklist" 10); (run_bench "add-zero-forwards" 10)]
{|$1() {
        goto 1
   23:  return x2
    2:  x2 = 42
        goto 23
    1:  goto 2
}|};

  expect [(run_bench "mul-two-worklist" 10); (run_bench "mul-two-forwards" 10)]
{|$1() {
        goto 1
   23:  return x22
   22:  x22 = x20 + x20
        goto 23
   20:  x20 = x18 + x18
        goto 22
   18:  x18 = x16 + x16
        goto 20
   16:  x16 = x14 + x14
        goto 18
   14:  x14 = x12 + x12
        goto 16
   12:  x12 = x10 + x10
        goto 14
   10:  x10 = x8 + x8
        goto 12
    8:  x8 = x6 + x6
        goto 10
    6:  x6 = x4 + x4
        goto 8
    4:  x4 = x2 + x2
        goto 6
    2:  x2 = 42
        goto 4
    1:  goto 2
}|};

  expect [(Program.add_zero_reuse_tree 5)]
{|$1() {
        goto 1
    9:  return x8
    8:  x8 = x7 + x3
        goto 9
    7:  x7 = x6 + x3
        goto 8
    6:  x6 = x5 + x3
        goto 7
    5:  x5 = x4 + x3
        goto 6
    4:  x4 = x2 + x3
        goto 5
    3:  x3 = 0
        goto 4
    2:  x2 = 42
        goto 3
    1:  goto 2
}|};

  expect [(run_bench "add-zero-reuse-worklist" 10); (run_bench "add-zero-reuse-forwards" 10)]
{|$1() {
        goto 1
   14:  return x2
    2:  x2 = 42
        goto 14
    1:  goto 2
}|};

  expect [(run_bench "add-zero-reuse-first" 5)]
{|$1() {
        goto 1
    9:  return x8
    8:  x8 = x7 + x3
        goto 9
    7:  x7 = x6 + x3
        goto 8
    6:  x6 = x5 + x3
        goto 7
    5:  x5 = x2 + x3
        goto 6
    3:  x3 = 0
        goto 5
    2:  x2 = 42
        goto 3
    1:  goto 2
}|};

  expect [(Program.add_zero_lots_of_reuse_tree 5)]
{|$1() {
        goto 1
   10:  return x9
    9:  x9 = x8 + x4
        goto 10
    8:  x8 = x7 + x4
        goto 9
    7:  x7 = x6 + x4
        goto 8
    6:  x6 = x5 + x4
        goto 7
    5:  x5 = x4 + x4
        goto 6
    4:  x4 = x2 + x3
        goto 5
    3:  x3 = 0
        goto 4
    2:  x2 = 42
        goto 3
    1:  goto 2
}|};

  expect [(run_bench "add-zero-lots-of-reuse-first" 5)]
{|$1() {
        goto 1
   10:  return x9
    9:  x9 = x8 + x2
        goto 10
    8:  x8 = x7 + x2
        goto 9
    7:  x7 = x6 + x2
        goto 8
    6:  x6 = x5 + x2
        goto 7
    5:  x5 = x2 + x2
        goto 6
    2:  x2 = 42
        goto 5
    1:  goto 2
}|};

  printf "All tests passed!\n"

let _ =
  (* The compcert driver sets this and it seems to improve perf ~30% *)
  Gc.set {
    (Gc.get()) with
      Gc.minor_heap_size = 524288; (* 512k *)
      Gc.major_heap_increment = 4194304 (* 4M *)
  };

  match Sys.argv with
  | [|_; "test"|] -> test ()
  | [|_; bench|] -> run_bench bench 50000 |> ignore
  | [|_; bench; n|] -> run_bench bench (int_of_string n) |> ignore
  | _ -> printf "Usage: ssabench [benchmark <n>]\n"
