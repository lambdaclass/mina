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

let convert_to_stable_v1 (block_abs : Mina_block.Precomputed) : Mina_block.Precomputed.Stable.V1.t =
  let scheduled_time = block_abs.scheduled_time in
  let protocol_state = block_abs.protocol_state in
  let protocol_state_proof = block_abs.protocol_state_proof in
  let staged_ledger_diff = block_abs.staged_ledger_diff in
  let delta_transition_chain_proof = block_abs.delta_transition_chain_proof in
  { Mina_block.Precomputed.Stable.V1.scheduled_time
  ; protocol_state
  ; protocol_state_proof
  ; staged_ledger_diff
  ; delta_transition_chain_proof
  }

let v1_block = convert_to_stable_v1 block

(* let state = block.protocol_state

   let proof = block.protocol_state_proof *)

let blockchain = Blockchain_snark.Blockchain.create ~state ~proof

(* let proof = Mina_block.Precomputed.protocol_state_proof block *)

(* let header = Mina_block.Precomputed.header block *)

let () = print_endline block

(*
   Verifier.verify_blockchain_snarks verifier, to_verify
*)
