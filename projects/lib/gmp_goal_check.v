From  Require Import gmp_goal gmp_proof_auto gmp_proof_manual_tmp.

Module VC_Correctness : VC_Correct.
  Include gmp_proof_auto.
  Include gmp_proof_manual_tmp.
End VC_Correctness.
