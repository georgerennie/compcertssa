open AST
open SSA
open Camlcoq
open Maps
open Op
open Registers

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
