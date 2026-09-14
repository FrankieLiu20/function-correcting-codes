import FCC.Balls
import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.ZMod.Basic

/-!
# Internal scaffolding

Helpers that are **not** part of the paper: the alphabet used by the `decide`
checks in `FCC/Paper.lean`, and the temporary transcriptions of `#definition 7#`
and `#definition 11#` that those checks are stated against.  Everything here may
be renamed, reorganised or deleted; the deliverable is `FCC/Paper.lean`.

Two implementation notes (see `DEVLOG.md`, 2026-09-14):

* the checks use `Bool` as `F₂` rather than `ZMod 2`, because `decide` needs an
  alphabet whose `DecidableEq` the kernel can reduce (`Mathlib.Algebra.Ring.
  BooleanRing` makes `Bool` the field with two elements: `false = 0`,
  `true = 1`, `+` = xor);
* the transcriptions `cdrmPaper`/`drmDataPaper` restate §III/§IV definitions for
  one fixed example; when the real definitions land in phase 1c the checks in
  `FCC/Paper.lean` are rewritten against them and this file shrinks.
-/

namespace FCC

/-- `(internal, test scaffolding — no paper item)` — `F₂` for the `decide`
checks. -/
abbrev F₂ := Bool

/-- `#definition 7#` (§III) — the coded distance requirement matrix (CDRM),
transcribed for a fixed example, with the codomain of `f` specialised to `ℕ`.

The real declaration is `cdrm`, which arrives in phase 1d. -/
def cdrmPaper {k ℓ : ℕ} (f : Word F₂ k → ℕ) (C : Word F₂ k → Word F₂ ℓ) (tf : ℕ)
    (u : Fin 4 → Word F₂ k) : Fin 4 → Fin 4 → ℕ :=
  fun i j =>
    if f (u i) = f (u j) then 0
    else max (2 * tf + 1 - hammingDist (C (u i)) (C (u j))) 0

/-- `#definition 11#` (§IV) — the distance requirement matrix for an
`(f, t_d, t_f)`-FCC, transcribed for a fixed example.

Note the three cases: the diagonal is `0`, equal function values use the
`2t_d+1` row, and different function values use the `2t_f+1` row.  The real
declaration is `drmData` (phase 1c). -/
def drmDataPaper {k M : ℕ} (f : Word F₂ k → ℕ) (td tf : ℕ) (u : Fin M → Word F₂ k) :
    Fin M → Fin M → ℕ :=
  fun i j =>
    if u i = u j then 0
    else if f (u i) = f (u j) then max (2 * td + 1 - hammingDist (u i) (u j)) 0
    else max (2 * tf + 1 - hammingDist (u i) (u j)) 0

end FCC
