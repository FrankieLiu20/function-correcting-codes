import FCC.Balls
import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.ZMod.Basic

/-!
# Regression tests: the paper's worked examples

The paper's Examples 1–17 are illustrations, not theorems, so they are not part
of the statement catalogue (`PLAN.md` §1.2).  They are, however, the cheapest
possible check that our *transcription conventions* agree with the paper: every
test below is a closed statement about an explicit finite object, discharged by
`decide`.

What each group pins down:

* `ball`/`sphere` sizes — the radius convention of §I-E and the first values of
  the count `Σ_{i≤t} C(n,i)(q-1)^i`;
* `ex6*` — Definition 7 (the coded distance requirement matrix, CDRM), the
  `[6,3,3]` code of Example 6, its `D`-code `{000,110,101,011}` and the claim
  `N(D) = 3`: no `D`-code of length 2 exists, one of length 3 does;
* `ex7*` — Definition 11 (the DRM with data protection) against the paper's 8×8
  matrix for `f = wt` on `F₂³`, `t_d = 1`, `t_f = 2`.  This is the check that
  pins "equal function value ⇒ the `2t_d+1` row, different ⇒ the `2t_f+1` row";
* `ex10*` — the `[7,4,3]` Hamming code of Example 10 (minimum distance 3).

Two implementation notes, both recorded in `DEVLOG.md`:

* **The alphabet of the tests is `Bool`, not `ZMod 2`.**  `Bool` with xor is
  `F₂` (mathlib's `BooleanRing Bool`: `false = 0`, `true = 1`, `+` = xor), and
  its `DecidableEq` is reducible by the kernel.  `ZMod 2`'s is not, so `decide`
  gets stuck on `hammingDist` over `ZMod 2`.  The library itself keeps the
  general-field statements (`Word F n` for `[Field F]`), where the proofs use
  mathlib lemmas rather than `decide`.
* **The encoders are explicit linear forms** (`u 0 + u 1 + …`) rather than
  `u ↦ uG`: the generator-matrix convention is exercised in phase 1f, when the
  library actually has linear codes.

The local transcriptions `cdrmPaper`/`drmDataPaper` restate Definitions 7 and 11
for a fixed example.  When those definitions land in phase 1c this file is
rewritten to use them.
-/

namespace FCC

namespace Examples

/-- `F₂` for the regression tests (see the module docstring). -/
abbrev F₂ := Bool

section RegressionTests

-- The kernel unfolds these `decide` proofs completely; the 256-candidate search
-- in `ex6_no_length_two` needs more than the default recursion depth of 1000.
set_option maxRecDepth 100000

/-! ## 1. Hamming balls, spheres and the message space -/

/-- `B(0,1)` in `F₂³` has `1 + 3 = 4` elements (§I-E). -/
theorem ball_f2_3_one : (ball (0 : Word F₂ 3) 1).card = 4 := by decide

/-- `B(0,2)` in `F₂³` has `1 + 3 + 3 = 7` elements. -/
theorem ball_f2_3_two : (ball (0 : Word F₂ 3) 2).card = 7 := by decide

/-- `B(0,3)` in `F₂³` is the whole space, because `n = 3 ≤ t`. -/
theorem ball_f2_3_three : (ball (0 : Word F₂ 3) 3).card = 8 := by decide

/-- `B(0,1)` in `(Fin 3)²` has `1 + 2·2 = 5` elements: the `(q-1)^i` factor. -/
theorem ball_fin3_2_one : (ball (0 : Word (Fin 3) 2) 1).card = 5 := by decide

/-- The sphere of radius 1 in `F₂³` has `3` elements. -/
theorem sphere_f2_3_one : (sphere (0 : Word F₂ 3) 1).card = 3 := by decide

/-- The message space `F₂³` has `q^k = 8` elements. -/
theorem card_word_f2_3 : Fintype.card (Word F₂ 3) = 8 := by decide

/-! ## 2. Example 6: the `[6,3,3]` code, its CDRM and its `D`-code -/

/-- The encoder of the `[6,3,3]` code of Example 6, i.e. `u ↦ uG` for the
generator matrix with rows `100110, 010101, 001011` (systematic form). -/
def ex6Enc (u : Word F₂ 3) : Word F₂ 6 :=
  ![u 0, u 1, u 2, u 0 + u 1, u 0 + u 2, u 1 + u 2]

/-- The four information vectors of Example 6: `000, 100, 011, 111`. -/
def ex6Rep : Fin 4 → Word F₂ 3 :=
  ![![false, false, false], ![true, false, false], ![false, true, true],
    ![true, true, true]]

/-- Definition 7 (CDRM), transcribed for a fixed example, with the codomain of
`f` specialised to `ℕ`. -/
def cdrmPaper {k ℓ : ℕ} (f : Word F₂ k → ℕ) (C : Word F₂ k → Word F₂ ℓ) (tf : ℕ)
    (u : Fin 4 → Word F₂ k) : Fin 4 → Fin 4 → ℕ :=
  fun i j =>
    if f (u i) = f (u j) then 0
    else max (2 * tf + 1 - hammingDist (C (u i)) (C (u j))) 0

/-- The CDRM printed in Example 6. -/
def ex6CDRM : Fin 4 → Fin 4 → ℕ :=
  ![![0, 2, 1, 2], ![2, 0, 2, 1], ![1, 2, 0, 2], ![2, 1, 2, 0]]

/-- The codewords of Example 6, as printed. -/
theorem ex6_codewords :
    ex6Enc ![false, false, false] = ![false, false, false, false, false, false] ∧
      ex6Enc ![true, false, false] = ![true, false, false, true, true, false] ∧
      ex6Enc ![false, true, true] = ![false, true, true, true, true, false] ∧
      ex6Enc ![true, true, true] = ![true, true, true, false, false, false] := by
  decide

/-- `[6,3,3]`: every non-zero codeword has weight at least 3. -/
theorem ex6_min_dist : ∀ u : Word F₂ 3, u ≠ 0 → 3 ≤ wt (ex6Enc u) := by
  decide

/-- The transcribed Definition 7 reproduces the matrix printed in Example 6. -/
theorem ex6_cdrm_matches :
    ∀ i j : Fin 4, cdrmPaper (fun u => wt u) ex6Enc 2 ex6Rep i j = ex6CDRM i j := by
  decide

/-- The `D`-code `{000,110,101,011}` of Example 6. -/
def ex6Dcode : Fin 4 → Word F₂ 3 :=
  ![![false, false, false], ![true, true, false], ![true, false, true],
    ![false, true, true]]

/-- That `D`-code satisfies every entry of the CDRM. -/
theorem ex6_dcode_valid :
    ∀ i j : Fin 4, i ≠ j → ex6CDRM i j ≤ hammingDist (ex6Dcode i) (ex6Dcode j) := by
  decide

/-- `N(D) = 3` for Example 6's CDRM: no `D`-code of length 2 exists. -/
theorem ex6_no_length_two :
    ¬∃ p : Fin 4 → Word F₂ 2,
      ∀ i j : Fin 4, i ≠ j → ex6CDRM i j ≤ hammingDist (p i) (p j) := by
  decide

/-- `N(D) = 3` for Example 6's CDRM: a `D`-code of length 3 exists. -/
theorem ex6_length_three :
    ∃ p : Fin 4 → Word F₂ 3,
      ∀ i j : Fin 4, i ≠ j → ex6CDRM i j ≤ hammingDist (p i) (p j) :=
  ⟨ex6Dcode, by decide⟩

/-! ## 3. Example 7: the DRM with data protection for `f = wt` on `F₂³` -/

/-- Definition 11 (DRM with data protection), transcribed for a fixed example.

Note the three cases: the diagonal is `0`, equal function values use the
`2t_d+1` row, and different function values use the `2t_f+1` row. -/
def drmDataPaper {k M : ℕ} (f : Word F₂ k → ℕ) (td tf : ℕ) (u : Fin M → Word F₂ k) :
    Fin M → Fin M → ℕ :=
  fun i j =>
    if u i = u j then 0
    else if f (u i) = f (u j) then max (2 * td + 1 - hammingDist (u i) (u j)) 0
    else max (2 * tf + 1 - hammingDist (u i) (u j)) 0

/-- The information vectors of Example 7, in the paper's order
`000, 100, 010, 001, 110, 101, 011, 111`. -/
def ex7Vec : Fin 8 → Word F₂ 3 :=
  ![![false, false, false], ![true, false, false], ![false, true, false],
    ![false, false, true], ![true, true, false], ![true, false, true],
    ![false, true, true], ![true, true, true]]

/-- The 8×8 DRM printed in Example 7 (`t_d = 1`, `t_f = 2`). -/
def ex7DRM : Fin 8 → Fin 8 → ℕ :=
  ![![0, 4, 4, 4, 3, 3, 3, 2], ![4, 0, 1, 1, 4, 4, 2, 3], ![4, 1, 0, 1, 4, 2, 4, 3],
    ![4, 1, 1, 0, 2, 4, 4, 3], ![3, 4, 4, 2, 0, 1, 1, 4], ![3, 4, 2, 4, 1, 0, 1, 4],
    ![3, 2, 4, 4, 1, 1, 0, 4], ![2, 3, 3, 3, 4, 4, 4, 0]]

/-- The transcribed Definition 11 reproduces the 8×8 matrix of Example 7. -/
theorem ex7_drm_matches :
    ∀ i j : Fin 8, drmDataPaper (fun u => wt u) 1 2 ex7Vec i j = ex7DRM i j := by
  decide

/-! ## 4. Example 10: the `[7,4,3]` Hamming code -/

/-- The encoder of the `[7,4,3]` Hamming code of Example 10 (`u ↦ uG` for the
generator matrix printed there, in systematic form). -/
def ex10Enc (u : Word F₂ 4) : Word F₂ 7 :=
  ![u 0, u 1, u 2, u 3, u 0 + u 1 + u 3, u 0 + u 2 + u 3, u 1 + u 2 + u 3]

/-- `[7,4,3]`: every non-zero codeword has weight at least 3. -/
theorem ex10_min_dist : ∀ u : Word F₂ 4, u ≠ 0 → 3 ≤ wt (ex10Enc u) := by
  decide

/-- The code has `2^4 = 16` codewords (sanity check on the encoder). -/
theorem ex10_card_codewords : (Finset.univ.image ex10Enc).card = 16 := by decide

end RegressionTests

end Examples

end FCC
