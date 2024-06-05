let read_whole_file filename =
  (* open_in_bin works correctly on Unix and Windows *)
  let ch = open_in_bin filename in
  let s = really_input_string ch (in_channel_length ch) in
  close_in ch ; s

let () = read_whole_file "merkle_root.txt"
         |> Mina_base.Ledger_hash.of_base58_check_exn
         |> Snark_params.Tick.Field.to_string
         |> Printf.printf "%s"
