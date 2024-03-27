(* let read_whole_file filename =
     (* open_in_bin works correctly on Unix and Windows *)
     let ch = open_in_bin filename in
     let s = really_input_string ch (in_channel_length ch) in
     close_in ch ; s
   let proof = read_whole_file "../../../../proof.txt"
   let decoded_proof = Mina_block.Precomputed.Proof.of_bin_string proof *)

let serialized_block =
  Mina_block.External_transition_precomputed.sample_block_json

let json_block = Yojson.Safe.from_string serialized_block

let result = Mina_block.Precomputed.of_yojson json_block

let block = Result.get_ok result

let state = block.protocol_state

let proof = block.protocol_state_proof

let blockchain = Blockchain_snark.Blockchain.create ~state ~proof

(* let proof = Mina_block.Precomputed.protocol_state_proof block *)

(* let header = Mina_block.Precomputed.header block *)

let () = print_endline block

(*
   Verifier.verify_blockchain_snarks verifier, to_verify
*)
