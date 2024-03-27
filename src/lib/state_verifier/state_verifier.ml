open Core
open Async

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

let blockchain = Blockchain_snark.Blockchain.create ~state ~proof

let logger = Logger.create ()

let conf_dir = Cli_lib.Flag.conf_dir

let%bind verifier =
  Verifier.create~logger ~proof_level:Genesis_constants.Proof_level.compiled
    ~constraint_constants:Genesis_constants.Constraint_constants.compiled
    ~pids:(Child_processes.Termination.create_pid_table ())
    ~conf_dir:None in
  let%bind result = (Verifier.verify_blockchain_snarks verifier, [ blockchain ])
in
match result with
| Ok true -> 
  printf "Proofs verified successfully" ;
  exit 0
| Ok false ->
  printf "Proofs failed to verify" ;
  exit 1
| Error err ->
  printf "Failed while verifying proofs:\n%s"
    (Error.to_string_hum err) ;
  exit 2;
