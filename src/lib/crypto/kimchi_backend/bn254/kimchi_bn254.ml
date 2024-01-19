module Basic = Kimchi_bn254_basic

module Bn254_based_plonk = struct
  module Field = Bn254_based_plonk.Field
  module Curve = Bn254_based_plonk.Curve
  module Bigint = Bn254_based_plonk.Bigint

  let field_size = Bn254_based_plonk.field_size

  module Verification_key = Bn254_based_plonk.Verification_key
  module R1CS_constraint_system = Bn254_based_plonk.R1CS_constraint_system
  module Keypair = Bn254_based_plonk.Keypair
  module Proving_key = Bn254_based_plonk.Proving_key
  module Proof = Bn254_based_plonk.Proof
end

module Bn254 = struct
  module Fp = Bn254.Bn254_fp
  module Fq = Bn254.Bn254_fq
  module Curve = Bn254.Bn254_curve
end
