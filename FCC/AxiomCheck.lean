import FCC.Paper

/-!
# Axiom audit

`#print axioms` for every headline result: the Lean kernel prints the axioms a
proof actually depends on.  For this development the expected set is the
mathlib-standard trusted base

* `propext`, `Quot.sound`, `Classical.choice`,

and nothing else.  In particular `sorryAx` (an unfinished proof) and the
`native_decide` trust axioms must never appear in a headline result;
`scripts/axioms_check.ps1` enforces the allowlist and fails on `sorryAx`.

Every name here must also appear in `scripts/headline_theorems.txt` (the
manifest is checked in both directions, so a headline result cannot be added or
dropped silently).  The list grows as the formalization does: the
paper-independent base layer, the phase-1a counting lemmas, and the
paper-example checks of `FCC/Paper.lean`, and — from phase 3.2 on — the paper
results that are actually proved (`#theorem 2#` first).
-/

namespace FCC

#print axioms wt_zero
#print axioms wt_le_wt_add_hammingDist
#print axioms mem_ball_self
#print axioms card_word
#print axioms hammingDist_eq_card_diffSet
#print axioms ball_eq_biUnion_sphere
#print axioms disjoint_sphere
#print axioms ball_eq_univ_of_le
#print axioms card_ball_univ
#print axioms ex6_cdrm_matches
#print axioms ex7_drm_matches
#print axioms ex6_no_length_two
#print axioms ex6_length_three

-- Phase 3.2 (the paper's own theorems, in paper order):
-- §II (the (f,t)-FCC bounds of [1]):
#print axioms optimalRedundancy_ge_drm
#print axioms two_mul_le_optimalRedundancy
#print axioms optimalRedundancy_le_fdm
#print axioms optimalRedundancy_eq_fdm
-- §IV (with data protection):
#print axioms optimalRedundancyData_eq_N_drmData
#print axioms optimalRedundancyData_ge_N_subset
#print axioms two_mul_le_optimalRedundancyData
#print axioms optimalRedundancyData_ge_Nconst_sub
#print axioms N_drmData_le_N_cdrm_add
#print axioms optimalRedundancyData_le_N_cdrm_add
#print axioms N_cdrm_le_Nconst
#print axioms two_step_redundancy_bounds

end FCC
