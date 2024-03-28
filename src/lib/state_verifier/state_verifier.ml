open Core
(* open Async *)

let serialized_block =
  Mina_block.External_transition_precomputed.sample_block_json

let json_block = Yojson.Safe.from_string serialized_block

let result = Mina_block.Precomputed.of_yojson json_block

let block =
  match result with
  | Ok block ->
      block
  | Error err ->
      failwithf "Could not read block: %s" err ()

let state : Mina_state.Protocol_state.Value.Stable.Latest.t =
  block.protocol_state

let proof = block.protocol_state_proof

let lalala = Blockchain_snark.verify state proof

let blockchain = Blockchain_snark.Blockchain.create ~state ~proof

(* let () = Parallel.init_master () *)

let logger = Logger.create ()

(* let conf_dir = Cli_lib.Flag.conf_dir *)

let verifier =
  Async.Thread_safe.block_on_async_exn (fun () ->
      Verifier.create ~logger
        ~proof_level:Genesis_constants.Proof_level.compiled
        ~constraint_constants:Genesis_constants.Constraint_constants.compiled
        ~pids:(Child_processes.Termination.create_pid_table ())
        ~conf_dir:None )

let verification_result =
  Async.Thread_safe.block_on_async_exn (fun () ->
      Verifier.verify_blockchain_snarks verifier [ blockchain ] )

let () =
  match verification_result with
  | Ok true ->
      print_endline "Proof verified successfully"
  | Ok false ->
      print_endline "Proof did not verify"
  | Error _err ->
      print_endline "Failed while verifying proofs:\n"
