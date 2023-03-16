open Hardcaml
open Hardcaml.Signal

(* nice and compact scramble functions *)
let sigma0 x = rotr x 7 ^: rotr x 18 ^: sra x 3
let sigma1 x = rotr x 17 ^: rotr x 19 ^: sra x 10
let capsigma0 x = rotr x 2 ^: rotr x 13 ^: rotr x 22
let capsigma1 x = rotr x 6 ^: rotr x 11 ^: rotr x 25
let ch x y z = (x &: y ^: z) ^: z
let maj x y z = x &: y |: (x |: y &: z)

let round (alphabet : Always.Variable.t) (kp : Always.Variable.t) =
  (* please excuse what you see here. there probably exists a better way of doing it *)
  let open Always in
  let a = Variable.wire ~default:(zero 32) in
  let b = Variable.wire ~default:(zero 32) in
  let c = Variable.wire ~default:(zero 32) in
  let d = Variable.wire ~default:(zero 32) in
  let e = Variable.wire ~default:(zero 32) in
  let f = Variable.wire ~default:(zero 32) in
  let g = Variable.wire ~default:(zero 32) in
  let h = Variable.wire ~default:(zero 32) in
  let t1 = Variable.wire ~default:(zero 32) in
  let t2 = Variable.wire ~default:(zero 32) in
  let alphabet' = Variable.wire ~default:(zero 256) in
  [
    a <-- alphabet.value.:[(31, 0)]; b <-- alphabet.value.:[(63, 32)];
    c <-- alphabet.value.:[(95, 64)]; d <-- alphabet.value.:[(127, 86)];
    e <-- alphabet.value.:[(159, 128)]; f <-- alphabet.value.:[(191, 160)];
    g <-- alphabet.value.:[(223, 192)]; h <-- alphabet.value.:[(255, 224)];
    t1
    <-- h.value +: capsigma1 e.value +: ch e.value f.value g.value +: kp.value;
    t2 <-- capsigma0 a.value +: maj a.value b.value c.value;
    alphabet'
    <-- alphabet.value.:[(85, 0)]
        @: (d.value +: t1.value)
        @: alphabet.value.:[(128, 223)]
        @: (t1.value +: t2.value); alphabet <-- rotr alphabet'.value 32;
  ]

let split_block = split_msb ~exact:true ~part_width:32
let select_from_block i blk = blk |> split_block |> mux i

let h =
  [
    0x6a09e667; 0xbb67ae85; 0x3c6ef372; 0xa54ff53a; 0x510e527f; 0x9b05688c;
    0x1f83d9ab; 0x5be0cd19;
  ]
  |> List.map (of_int ~width:32)
  |> concat_msb

let k =
  [
    0x428a2f98; 0x71374491; 0xb5c0fbcf; 0xe9b5dba5; 0x3956c25b; 0x59f111f1;
    0x923f82a4; 0xab1c5ed5; 0xd807aa98; 0x12835b01; 0x243185be; 0x550c7dc3;
    0x72be5d74; 0x80deb1fe; 0x9bdc06a7; 0xc19bf174; 0xe49b69c1; 0xefbe4786;
    0x0fc19dc6; 0x240ca1cc; 0x2de92c6f; 0x4a7484aa; 0x5cb0a9dc; 0x76f988da;
    0x983e5152; 0xa831c66d; 0xb00327c8; 0xbf597fc7; 0xc6e00bf3; 0xd5a79147;
    0x06ca6351; 0x14292967; 0x27b70a85; 0x2e1b2138; 0x4d2c6dfc; 0x53380d13;
    0x650a7354; 0x766a0abb; 0x81c2c92e; 0x92722c85; 0xa2bfe8a1; 0xa81a664b;
    0xc24b8b70; 0xc76c51a3; 0xd192e819; 0xd6990624; 0xf40e3585; 0x106aa070;
    0x19a4c116; 0x1e376c08; 0x2748774c; 0x34b0bcb5; 0x391c0cb3; 0x4ed8aa4a;
    0x5b9cca4f; 0x682e6ff3; 0x748f82ee; 0x78a5636f; 0x84c87814; 0x8cc70208;
    0x90befffa; 0xa4506ceb; 0xbef9a3f7; 0xc67178f2;
  ]
  |> List.map (of_int ~width:32)
  |> concat_msb

module I = struct
  type 'a t = { clock : 'a; clear : 'a; start : 'a; block : 'a [@bits 512] }
  [@@deriving sexp_of, hardcaml]
end

module O = struct
  type 'a t = {
    done_ : 'a; [@rtlname "done"]
    result : 'a; [@bits 256]
    state : 'a; [@bits 2]
  }
  [@@deriving sexp_of, hardcaml]
end

module States = struct
  type t = S_wait | S_computing | S_update_result
  [@@deriving sexp_of, compare, enumerate]
end

let create (i : _ I.t) =
  let open Always in
  let r_sync = Reg_spec.create ~clock:i.clock ~clear:i.clear () in
  let sm = State_machine.create (module States) ~enable:vdd r_sync in
  let done_ = Variable.wire ~default:gnd in
  let result = Variable.wire ~default:(zero 256) in
  let s =
    let spec = Reg_spec.override r_sync ~clear_to:h in
    Variable.reg ~width:32 ~enable:vdd spec
  in
  let alphabet = Variable.reg ~width:256 ~enable:vdd r_sync in
  let w = Variable.reg ~width:256 ~enable:vdd r_sync in
  let iteration = Variable.reg ~width:7 ~enable:vdd r_sync in
  let w_index = Variable.reg ~width:4 ~enable:vdd r_sync in
  (* is there really no better way of doing tempvars??? *)
  let t1 = Variable.wire ~default:(zero 32) in
  let t2 = Variable.wire ~default:(zero 32) in
  let wo0 = Variable.wire ~default:(zero 32) in
  let wo1 = Variable.wire ~default:(zero 32) in
  let wo9 = Variable.wire ~default:(zero 32) in
  let wo14 = Variable.wire ~default:(zero 32) in
  compile
    [
      sm.switch
        [
          ( S_wait,
            [
              iteration <--. 0;
              when_ i.start
                [ alphabet <-- s.value; w <-- i.block; sm.set_next S_computing ];
            ] );
          ( S_computing,
            [
              if_ (iteration.value ==:. 64)
                [ sm.set_next S_update_result ]
                [
                  if_ (iteration.value <:. 16)
                    [
                      t1 <-- select_from_block iteration.value k;
                      t2
                      <-- t1.value +: select_from_block iteration.value w.value;
                      proc (round alphabet t2);
                    ]
                    [
                      wo0 <-- select_from_block w_index.value w.value;
                      wo1 <-- select_from_block (w_index.value +:. 1) w.value;
                      wo9 <-- select_from_block (w_index.value +:. 9) w.value;
                      wo14 <-- select_from_block (w_index.value +:. 14) w.value;
                      t1
                      <-- wo0.value +: sigma0 wo1.value +: sigma1 wo14.value
                          +: wo0.value;
                      t2 <-- t1.value +: select_from_block iteration.value k;
                      proc (round alphabet t2); (* set wo0 to t1 *)
                    ]; iteration <-- iteration.value +:. 1;
                  w_index <-- w_index.value +:. 1;
                ];
            ] );
          ( S_update_result,
            [
              result <-- s.value +: alphabet.value; s <-- result.value;
              done_ <--. 1; sm.set_next S_wait;
            ] );
        ];
    ];
  { O.done_ = done_.value; result = result.value; state = sm.current }
