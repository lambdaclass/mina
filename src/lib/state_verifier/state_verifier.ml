(* let read_whole_file filename =
     (* open_in_bin works correctly on Unix and Windows *)
     let ch = open_in_bin filename in
     let s = really_input_string ch (in_channel_length ch) in
     close_in ch ; s
   let proof = read_whole_file "../../../../proof.txt"
   let decoded_proof = Mina_block.Precomputed.Proof.of_bin_string proof *)

let serialized_block =
  Mina_block.External_transition_precomputed.sample_block_json

let block = Yojson.Safe.from_string serialized_block

match block with
| Ok block_inner -> print_endline block_inner
| _ -> ()

(* let () = print_endline block *)

(*
   Verifier.verify_blockchain_snarks verifier, to_verify
*)
