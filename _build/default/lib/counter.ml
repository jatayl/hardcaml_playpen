open Hardcaml
open Hardcaml.Signal
(* open Hardcaml_waveterm *)

module I = struct
  type 'a t = { clock : 'a; clear : 'a; incr : 'a }
  [@@deriving sexp_of, hardcaml]
end

module O = struct
  type 'a t = { dout : 'a [@bits 8] } [@@deriving sexp_of, hardcaml]
end

let create (i : _ I.t) =
  {
    O.dout =
      reg_fb (Reg_spec.create ~clock:i.clock ~clear:i.clear ())
        ~enable:i.incr ~width:8 ~f:(fun d -> d +:. 1);
  }

let counter_with_wire (i : _ I.t) =
  let w = wire 8 in
  let dout =
    reg
      (Reg_spec.create ~clock:i.clock ~clear:i.clear ())
      ~enable:i.incr (w +:. 1)
  in
  w <== dout;
  { O.dout }

let counter_with_always (i : _ I.t) =
  let dout =
    Always.Variable.reg
    (Reg_spec.create ~clock:i.clock ())
    ~enable:vdd
    ~width:8
  in
  Always.(compile [
    if_ i.clear
      [ dout <-- 0;]
      [ when_ i.incr [dout <- dout.value +:. 1]]
  ]);
  { O.dout = dout.value }

module Simulator = Cyclesim.With_interface (I) (O)

let testbench (create_design_fn : t I.t -> t O.t) =
  let sim = Simulator.create create_design_fn in
  let inputs : _ I.t = Cyclesim.inputs sim in
  let outputs : _ O.t = Cyclesim.outputs sim in

  let step ~clear ~incr =
    inputs.clear := if clear = 1 then Bits.vdd else Bits.gnd;
    inputs.incr := if incr = 1 then Bits.vdd else Bits.gnd;
    Stdio.printf "dout='%s'\n" (Bits.to_string !(outputs.dout));
    Cyclesim.cycle sim
  in

  step ~clear:0 ~incr:0;
  step ~clear:0 ~incr:1;
  step ~clear:0 ~incr:1;
  step ~clear:1 ~incr:0;
  step ~clear:0 ~incr:0;
  step ~clear:0 ~incr:0
