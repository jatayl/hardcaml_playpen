open Hardcaml
open Hardcaml.Signal

(* nice and compact scramble functions *)
let sigma0 x = rotr x 7 ^: rotr x 18 ^: sra x 3
let sigma1 x = rotr x 17 ^: rotr x 19 ^: sra x 10
let capsigma0 x = rotr x 2 ^: rotr x 13 ^: rotr x 22
let capsigma1 x = rotr x 6 ^: rotr x 11 ^: rotr x 25
let ch x y z = (x &: y ^: z) ^: z
let maj x y z = x &: y |: (x |: y &: z)

let round a b c d e f g h kp =
  let t1 = h +: capsigma1 e +: ch e f g +: kp in
  let t2 = capsigma0 a +: maj a b c in
  (d +: t1, t1 +: t2)

let extract_word_from_block i blk = (sll blk (i * 32)).:[(0, 32)]

let h =
  [|
    0x6a09e667; 0xbb67ae85; 0x3c6ef372; 0xa54ff53a; 0x510e527f; 0x9b05688c;
    0x1f83d9ab; 0x5be0cd19;
  |]
  |> Array.map (of_int ~width:32)

let k =
  [|
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
  |]
  |> Array.map (of_int ~width:32)

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
  let r_sync = Reg_spec.create ~clock:i.clock () in
  let sm = State_machine.create (module States) ~enable:vdd r_sync in
  let done_ = Variable.wire ~default:gnd in
  let result = Variable.wire ~default:(zero 256) in
  let _s =
    Array.init 16 (fun i ->
        (* when cleared, will use initial state h *)
        let spec = Reg_spec.override r_sync ~clear_to:h.(i) in
        Variable.reg ~width:32 ~enable:vdd spec)
  in
  let w = Array.init 16 (fun _ -> Variable.reg ~width:32 ~enable:vdd r_sync) in
  let iteration = Variable.wire ~default:(zero 6) in
  compile
    [
      sm.switch
        [
          ( S_wait,
            [ iteration <--. 0; when_ i.start [ sm.set_next S_computing ] ] );
          ( S_computing,
            [
              if_ (iteration.value ==:. 64)
                [ sm.set_next S_update_result ]
                [
                  if_ (iteration.value <:. 16)
                    [
                      (* this is quite ugly *)
                      w.(to_int iteration.value)
                      <-- extract_word_from_block
                            (to_int iteration.value) i.block;
                    ]
                    [];
                ];
            ] ); (S_update_result, []);
        ];
    ];
  { O.done_ = done_.value; result = result.value; state = sm.current }
