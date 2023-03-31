open Base

let rec umul_base a b =
  if b = 0 then 0
  else
    let partial_product = if b land 1 = 1 then a else 0 in
    partial_product + umul_base (a lsl 1) (b lsr 1)

open Hardcaml
open Hardcaml.Bits

let rec umul_bits_helper a b =
  if to_int b = 0 then zero (width a)
  else
    let partial_product = mux2 b.:[0, 0] a (zero (width a)) in
    partial_product +: umul_bits_helper (sll a 1) (srl b 1)

let umul_bits a b = umul_bits_helper (uresize a (width a + width b)) b

open Hardcaml.Signal

let partial_product a b0 = mux2 b0 a (zero (width a))

let running_sum first sum a b0 =
  let sum = mux2 first (zero (width sum)) sum in
  ue sum +: ue (partial_product a b0)

let running_sum_reg spec first a b0 =
  let sum_w = wire (width a) -- "running_sum" in
  let running_sum = running_sum first sum_w a b0 -- "running_sum_next" in

  let running_sum_bit_out = lsb running_sum in
  let running_sum = msbs running_sum in

  let sum = reg spec ~enable:vdd running_sum in
  sum_w <== sum;
  (sum, running_sum_bit_out)

let computed_bits spec width bit =
  reg_fb spec ~width ~f:(fun d -> bit @: msbs d)

let umul_sequential clock first a b_width b0 =
  let spec = Reg_spec.create ~clock () in
  let running_sum, computed_bit = running_sum_reg spec first a b0 in
  let computed_bits = computed_bits spec b_width computed_bit in
  running_sum @: computed_bits

let create_circuit a_width b_width =
  let clock = input "clock" 1 in
  let first = input "first" 1 in
  let a = input "a" a_width in
  let b0 = input "b0" 1 in
  let result = umul_sequential clock first a b_width b0 in
  Circuit.create_exn ~name:"umul" [ output "result" result ]

module Waveform = Hardcaml_waveterm.Waveform

let create_sim circuit =
  let sim = Cyclesim.create ~config:Cyclesim.Config.trace_all circuit in
  let waves, sim = Waveform.create sim in
  let first = Cyclesim.in_port sim "first" in
  let a = Cyclesim.in_port sim "a" in
  let b0 = Cyclesim.in_port sim "b0" in
  let result = Cyclesim.out_port sim "result" in
  (waves, sim, first, a, b0, result)

let test a_in b_in =
  let open Bits in
  let waves, sim, first, a, b0, result =
    create_circuit (width a_in) (width b_in) |> create_sim
  in
  let step iteration =
    first := if iteration = 0 then vdd else gnd;
    b0 := b_in.:[iteration, iteration];
    Cyclesim.cycle sim
  in
  a := a_in;
  for i = 0 to width b_in - 1 do
    step i
  done;
  let result = !result in
  Cyclesim.cycle sim;
  (waves, result)
