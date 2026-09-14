import FCC.Examples

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
dropped silently).  The list grows as the formalization does: it currently holds
the paper-independent base layer and the phase-1a counting lemmas.
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

namespace Examples

#print axioms ex6_cdrm_matches
#print axioms ex7_drm_matches
#print axioms ex6_no_length_two
#print axioms ex6_length_three

end Examples

end FCC
