open Core
open Async

let serialized_block =
  Mina_block.External_transition_precomputed.sample_block_json

let json_block = Yojson.Safe.from_string serialized_block

let result = Mina_block.Precomputed.of_yojson json_block

let block = Result.get_ok result

let state : Mina_state.Protocol_state.Value.Stable.Latest.t =
  block.protocol_state

let proof = block.protocol_state_proof

let _blockchain = Blockchain_snark.Blockchain.create ~state ~proof

let logger = Logger.create ()

let conf_dir = Cli_lib.Flag.conf_dir

let verifier =
  Verifier.create ~logger ~proof_level:Genesis_constants.Proof_level.compiled
    ~constraint_constants:Genesis_constants.Constraint_constants.compiled
    ~pids:(Pid.Table.create ()) ~conf_dir:(Some conf_dir)

let () = print_endline "State verified successfully"

(*
   Verifier.verify_blockchain_snarks verifier, to_verify
*)
