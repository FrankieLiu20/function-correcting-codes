import FCC.Basic

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
the paper-independent base layer.
-/

namespace FCC

#print axioms wt_zero
#print axioms wt_le_wt_add_hammingDist
#print axioms mem_ball_self

end FCC
