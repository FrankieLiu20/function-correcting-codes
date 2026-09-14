import FCC.Balls
import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.ZMod.Basic

/-!
# Internal scaffolding

Helpers that are **not** part of the paper.  At the moment this is only the
alphabet used by the `decide` checks in `FCC/Paper.lean`.

The checks use `Bool` as `F₂` rather than `ZMod 2`, because `decide` needs an
alphabet whose `DecidableEq` the kernel can reduce.
`Mathlib.Algebra.Ring.BooleanRing` makes `Bool` the field with two elements
(`false = 0`, `true = 1`, `+` = xor), so all the combinatorial definitions of
`FCC/Paper.lean` — which need only a finite alphabet with a zero — instantiate.
(The *linear* definitions of §VII need an honest `[Field F]` and are therefore
checked with `ZMod 2`/`Fin` in the examples that need them.)

Everything here may be renamed, reorganised or deleted; the deliverable is
`FCC/Paper.lean`.
-/

namespace FCC

/-- `(internal, test scaffolding — no paper item)` — `F₂` for the `decide`
checks. -/
abbrev F₂ := Bool

end FCC
