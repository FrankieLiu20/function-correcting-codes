import FCC.Definitions
import FCC.Basic
import FCC.Balls
import FCC.Internal
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Order.Lattice.Nat

/-!
# `FCC/Paper.lean` — the paper, in paper order

**This is the main file.**  Every numbered item of

> C. Rajput, B. S. Rajan, R. Freij-Hollanti, C. Hollanti,
> "Function-Correcting Codes With Data Protection",
> IEEE Trans. Inform. Theory **72**(7), pp. 4860–4880, 2026,
> DOI 10.1109/TIT.2026.3692458

appears here exactly once, **in the order the paper presents it**: its
definitions, examples, theorems, lemmas and corollaries.  Reading this file from
top to bottom is reading the paper's formalization.  The docstring of every item
opens with the paper's own number (`#definition 5#`, `#theorem 2#`, …) followed by
a paraphrase of the paper's wording, so that the file can be compared with the
PDF line by line.

Everything that is *not* a numbered item of the paper — arithmetic about words,
the counting lemmas, the temporary transcriptions used by the example checks —
lives in the helper modules this file imports, and carries an
`(internal, §…)` docstring instead of a paper number:

| Module | Contents |
| --- | --- |
| `FCC/Definitions.lean` | §I-E notation: `Word` (= `F_q^n`), `wt`, `ball` |
| `FCC/Basic.lean` | internal lemmas about words and weights |
| `FCC/Balls.lean` | internal counting lemmas (spheres and balls) |
| `FCC/Internal.lean` | internal scaffolding for the example checks |

Helpers may be reorganised, renamed and renumbered freely — they are not the
deliverable.  The deliverable is this file.

**Status.**  Items marked `TODO` below are not written yet.  `PLAN.md` §1.1 is
the same inventory with a per-item status column, and
`scripts/consistency_check.ps1` reports which rows are still unstated:
definitions arrive in phase 1, every statement in phase 2, proofs in phase 3
(one numbered item per working session).  Of the paper's 17 examples, only the
ones that serve as convention tests are formalized (`#example 6#`,
`#example 7#`, `#example 10#`); the rest are prose illustrations.
-/

-- The `decide` checks of the examples (e.g. the search over 256 candidate
-- `D`-codes in `ex6_no_length_two`) need a deeper kernel recursion limit than
-- the default.
set_option maxRecDepth 100000

namespace FCC

/-! ## §I-E — Notation and conventions

The paper's notation layer is `FCC/Definitions.lean`:

* `Word F n` is `F_q^n` (an arbitrary finite field `F`, so `q = Fintype.card F`);
* `hammingDist` is mathlib's Hamming distance `d(·,·)`;
* `wt u` is `wt(u)`, the number of non-zero entries;
* `ball u t` is the Hamming ball `B(u,t) = {x | d(x,u) ≤ t}`.

The full dictionary is `Notation.md` §2.
-/

/-! ## §II — Preliminaries

Definitions 1–5 are below (phase 1, done).  The numbered *results* of this
section are still to come: `#lemma 1#` (external), `#corollary 1#`,
`#theorem 1#`, `#corollary 2#`, `#corollary 3#` (external).
-/

section Combinatorial

variable {F : Type*} [Fintype F] [DecidableEq F] {α : Type*} [DecidableEq α]

/-- `#definition 1#` (§II) — an `(f,t)`-function correcting code: "a systematic
encoding `C : F_q^k → F_q^{k+r}` is defined as an `(f,t)`-FCC if, for any
`u₁, u₂ ∈ F_q^k` such that `f(u₁) ≠ f(u₂)`, the following condition holds:
`d(C(u₁), C(u₂)) ≥ 2t + 1`". -/
def IsFCC {k r : ℕ} (f : Word F k → α) (C : Word F k → Word F (k + r)) (t : ℕ) : Prop :=
  IsSystematic C ∧ ∀ u v, f u ≠ f v → 2 * t + 1 ≤ hammingDist (C u) (C v)

/-- `#definition 1#` (§II) — the optimal redundancy `r_f(k,t)`: "the minimum of
`r` for which there exists an `(f,t)`-FCC with an encoding function
`C : F_q^k → F_q^{k+r}`". -/
noncomputable def optimalRedundancy {k : ℕ} (f : Word F k → α) (t : ℕ) : ℕ :=
  sInf {r : ℕ | ∃ C : Word F k → Word F (k + r), IsFCC f C t}

/-- `#definition 2#` (§II) — the distance requirement matrix (DRM):
`[D_f(t, u₁,…,u_M)]_{i,j} = max(2t+1 − d(u_i,u_j), 0)` if `f(u_i) ≠ f(u_j)`, and
`0` otherwise. -/
def drm {k M : ℕ} (f : Word F k → α) (t : ℕ) (u : Fin M → Word F k) : Fin M → Fin M → ℕ :=
  fun i j => if f (u i) = f (u j) then 0
    else max (2 * t + 1 - hammingDist (u i) (u j)) 0

/-- `#definition 3#` (§II) — an irregular-distance code (`D`-code): a family
`p₁,…,p_M` of words such that `d(p_i, p_j) ≥ [D]_{i,j}` for all `i ≠ j` (the
paper's "there is an ordering of `P`" is the indexing of this family). -/
def IsDCode {M : ℕ} (D : Fin M → Fin M → ℕ) (r : ℕ) : Prop :=
  ∃ p : Fin M → Word F r, ∀ i j, i ≠ j → D i j ≤ hammingDist (p i) (p j)

/-- `#definition 3#` (§II) — `N(D)`: "the smallest integer `r` such that there
exists a `D`-code of length `r`" (`0` if no `D`-code exists at all; the `N`-API,
including existence, is phase 3.0). -/
noncomputable def N {M : ℕ} (D : Fin M → Fin M → ℕ) : ℕ :=
  sInf {r : ℕ | IsDCode (F := F) D r}

/-- `#definition 3#` (§II) — `N(M,D)`: the minimum length of an error-correcting
code with `M` codewords and minimum distance at least `D`, i.e. `N` of the
constant matrix. -/
noncomputable def Nconst (M D : ℕ) : ℕ := N (F := F) (fun _ _ : Fin M => D)

/-- `#definition 4#` (§II) — the distance between function values:
`d(fᵢ, fⱼ) = min{d(u₁,u₂) | f(u₁) = fᵢ, f(u₂) = fⱼ}`.  The minimum over an empty
family (an empty preimage) is `0`; every use below is for values in `Im(f)`. -/
noncomputable def fDist {k : ℕ} (f : Word F k → α) (a b : α) : ℕ :=
  sInf {d : ℕ | ∃ u v : Word F k, f u = a ∧ f v = b ∧ hammingDist u v = d}

/-- `#definition 5#` (§II) — the function distance matrix (FDM): the `E × E`
matrix (`E = |Im(f)|`) with entries `max(2t+1 − d(fᵢ,fⱼ), 0)` off the diagonal
and `0` on it.  We index it by the image values themselves. -/
noncomputable def fdm {k : ℕ} (f : Word F k → α) (t : ℕ) : α → α → ℕ :=
  fun a b => if a = b then 0 else max (2 * t + 1 - fDist f a b) 0

/-! ### Example 1 (`#example 1#`) — the DRM of a function on `F₂²` -/

/-- `#example 1#` (§II) — the function `f : F₂² → {0,1,2}` with `f(00) = 0`,
`f(01) = f(10) = 1`, `f(11) = 2`. -/
def ex1F (u : Word F₂ 2) : Fin 3 :=
  match u 0, u 1 with
  | false, false => 0
  | false, true => 1
  | true, false => 1
  | true, true => 2

/-- `#example 1#` (§II) — the information vectors `u₁ = 00, u₂ = 01, u₃ = 10`,
`u₄ = 11` in the paper's order.  (The same four messages, in the same order, are
used by `#example 2#` and `#example 4#`.) -/
def ex1Vec : Fin 4 → Word F₂ 2 :=
  ![![false, false], ![false, true], ![true, false], ![true, true]]

/-- `#example 1#` (§II) — the DRM printed in the paper. -/
def ex1DRM : Fin 4 → Fin 4 → ℕ :=
  ![![0, 2, 2, 1], ![2, 0, 0, 2], ![2, 0, 0, 2], ![1, 2, 2, 0]]

/-- `#example 1#` (§II) — `drm` reproduces the printed matrix. -/
theorem ex1_drm_matches : ∀ i j : Fin 4, drm ex1F 1 ex1Vec i j = ex1DRM i j := by
  decide

/-! ### Example 2 (`#example 2#`) — the `D`-code of `#example 1#` and its FCC -/

/-- `#example 2#` (§II) — the `D`-code `{000, 110, 110, 101}` (the repeat is in the
paper: two messages with the same `f`-value may share a redundancy vector). -/
def ex2Dcode : Fin 4 → Word F₂ 3 :=
  ![![false, false, false], ![true, true, false], ![true, true, false], ![true, false, true]]

/-- `#example 2#` (§II) — that `D`-code satisfies the DRM of `#example 1#`. -/
theorem ex2_dcode_valid :
    ∀ i j : Fin 4, i ≠ j → ex1DRM i j ≤ hammingDist (ex2Dcode i) (ex2Dcode j) := by
  decide

/-- `#example 2#` (§II) — `N(D) = 3` for that DRM: no `D`-code of length 2 exists,
while the one above has length 3 (so the two decidable facts below pin `N(D) = 3`
once the `N`-API of phase 3.0 is available). -/
theorem ex2_no_length_two :
    ¬∃ p : Fin 4 → Word F₂ 2,
      ∀ i j : Fin 4, i ≠ j → ex1DRM i j ≤ hammingDist (p i) (p j) := by
  decide

/-- `#example 2#` (§II) — the `(f,1)`-FCC `{(u_i, p_i)}` obtained from that
`D`-code; it is systematic by construction. -/
def ex2Enc (i : Fin 4) : Word F₂ 5 :=
  ![ex1Vec i 0, ex1Vec i 1, ex2Dcode i 0, ex2Dcode i 1, ex2Dcode i 2]

/-- `#example 2#` (§II) — the codewords are `{00000, 01110, 10110, 11101}`, with
the message in the first two coordinates. -/
theorem ex2_codewords :
    ex2Enc 0 = ![false, false, false, false, false] ∧
      ex2Enc 1 = ![false, true, true, true, false] ∧
      ex2Enc 2 = ![true, false, true, true, false] ∧
      ex2Enc 3 = ![true, true, true, false, true] := by
  decide

/-- `#example 2#` (§II) — the code is an `(f,1)`-FCC: codewords of messages with
different `f`-values are at distance at least `2·1 + 1 = 3`. -/
theorem ex2_is_fcc :
    ∀ i j : Fin 4, ex1F (ex1Vec i) ≠ ex1F (ex1Vec j) →
      3 ≤ hammingDist (ex2Enc i) (ex2Enc j) := by
  decide

/-! ### Example 4 (`#example 4#`) — the same function protection, two data
protections -/

/-- `#example 4#` (§III) — the function `f(00) = 0`, `f(u) = 1` for `u ≠ 00`. -/
def ex4F (u : Word F₂ 2) : Bool := u 0 || u 1

/-- `#example 4#` (§III) — the first code of the example, `{0000, 0111, 1011, 1111}`. -/
def ex4Code₁ : Fin 4 → Word F₂ 4 :=
  ![![false, false, false, false], ![false, true, true, true], ![true, false, true, true],
    ![true, true, true, true]]

/-- `#example 4#` (§III) — the second code, `{0000, 0111, 1011, 1101}`. -/
def ex4Code₂ : Fin 4 → Word F₂ 4 :=
  ![![false, false, false, false], ![false, true, true, true], ![true, false, true, true],
    ![true, true, false, true]]

/-- `#example 4#` (§III) — "both of the following codes achieve the same level of
functional error correction" for `t_f = 1`. -/
theorem ex4_both_fcc :
    (∀ i j : Fin 4, ex4F (ex1Vec i) ≠ ex4F (ex1Vec j) →
        3 ≤ hammingDist (ex4Code₁ i) (ex4Code₁ j)) ∧
      ∀ i j : Fin 4, ex4F (ex1Vec i) ≠ ex4F (ex1Vec j) →
        3 ≤ hammingDist (ex4Code₂ i) (ex4Code₂ j) := by
  decide

/-- `#example 4#` (§III) — "the first code has a minimum distance of 1, while the
second code has a minimum distance of 2, allowing for single-error detection in
the data". -/
theorem ex4_min_dists :
    (∀ i j : Fin 4, i ≠ j → 1 ≤ hammingDist (ex4Code₁ i) (ex4Code₁ j)) ∧
      (∃ i j : Fin 4, i ≠ j ∧ hammingDist (ex4Code₁ i) (ex4Code₁ j) = 1) ∧
      (∀ i j : Fin 4, i ≠ j → 2 ≤ hammingDist (ex4Code₂ i) (ex4Code₂ j)) ∧
      ∃ i j : Fin 4, i ≠ j ∧ hammingDist (ex4Code₂ i) (ex4Code₂ j) = 2 := by
  decide

/-! ### §III — A construction procedure for FCCs with data protection -/

/-- `#definition 6#` (§III) — an `(f : d_d, d_f)`-FCC: "an encoding
`C_f : F_q^k → F_q^{k+r}` ... if, for any `u₁, u₂` with `u₁ ≠ u₂`,
`d(C_f(u₁), C_f(u₂)) ≥ d_d`, and for any `u₁, u₂` with `f(u₁) ≠ f(u₂)`,
`d(C_f(u₁), C_f(u₂)) ≥ d_f`, where `d_d ≤ d_f`".

The encoding is systematic, as in `#definition 1#` and throughout §III-A; the
paper's statement of this definition does not repeat that word, so the choice is
recorded in `Notation.md` §3.5 — it is what `#theorem 2#`'s proof uses. -/
def IsFCCData {k r : ℕ} (f : Word F k → α) (C : Word F k → Word F (k + r))
    (dd df : ℕ) : Prop :=
  IsSystematic C ∧ (∀ u v, u ≠ v → dd ≤ hammingDist (C u) (C v)) ∧
    ∀ u v, f u ≠ f v → df ≤ hammingDist (C u) (C v)

/-- `#definition 7#` (§III) — the coded distance requirement matrix (CDRM):
like the DRM of `#definition 2#`, but the distances are taken between the
*codewords* `c_u = uG` rather than between the messages. -/
def cdrm {k ℓ M : ℕ} (f : Word F k → α) (C : Word F k → Word F ℓ) (tf : ℕ)
    (u : Fin M → Word F k) : Fin M → Fin M → ℕ :=
  fun i j => if f (u i) = f (u j) then 0
    else max (2 * tf + 1 - hammingDist (C (u i)) (C (u j))) 0

/-- `#definition 8#` (§III) — the coded distance between function values:
`d_C(fᵢ, fⱼ) = min{d(c_{u₁}, c_{u₂}) | f(u₁) = fᵢ, f(u₂) = fⱼ}`. -/
noncomputable def codedFDist {k ℓ : ℕ} (f : Word F k → α) (C : Word F k → Word F ℓ)
    (a b : α) : ℕ :=
  sInf {d : ℕ | ∃ u v : Word F k, f u = a ∧ f v = b ∧ hammingDist (C u) (C v) = d}

/-- `#definition 9#` (§III) — the coded function distance matrix (CFDM): the
`E × E` matrix with entries `max(2t_f+1 − d_C(fᵢ,fⱼ), 0)` off the diagonal and
`0` on it, indexed here by the image values. -/
noncomputable def cfdm {k ℓ : ℕ} (f : Word F k → α) (C : Word F k → Word F ℓ) (tf : ℕ) :
    α → α → ℕ :=
  fun a b => if a = b then 0 else max (2 * tf + 1 - codedFDist f C a b) 0

/-! ## §III — A construction procedure for FCCs with data protection

TODO: `#definition 6#`, `#definition 7#`, `#definition 8#`, `#definition 9#`.

The construction method of §III-A itself carries no number; it is formalized
through `#theorem 5#` and `#corollary 4#` (§IV) together with the concrete
constructions of §VI–§VII.
-/

/-! ## §IV — Bounds for optimal redundancy for FCCs with data protection

Definitions 10–11 are below.  Still to come: `#theorem 2#` (the central identity
`r_f(k,t_d,t_f) = N(D_f(t_d,t_f : u₁,…,u_{q^k}))`), `#theorem 3#`–`#theorem 7#`,
`#remark 1#`.
-/

/-- `#definition 10#` (§IV) — the optimal redundancy with data protection
`r_f(k : d_d, d_f)` = `r_f(k, t_d, t_f)`: "the minimum value of `r` for which
there exists an `(f : d_d, d_f)`-FCC with an encoding function
`C_f : F_q^k → F_q^{k+r}`". -/
noncomputable def optimalRedundancyData {k : ℕ} (f : Word F k → α) (dd df : ℕ) : ℕ :=
  sInf {r : ℕ | ∃ C : Word F k → Word F (k + r), IsFCCData f C dd df}

/-- `#definition 11#` (§IV) — the distance requirement matrix for an
`(f, t_d, t_f)`-FCC: entries `max(2t_d+1 − d(u_i,u_j), 0)` when `u_i ≠ u_j` and
`f(u_i) = f(u_j)`, entries `max(2t_f+1 − d(u_i,u_j), 0)` when `f(u_i) ≠ f(u_j)`,
and `0` otherwise (in particular on the diagonal). -/
def drmData {k M : ℕ} (f : Word F k → α) (td tf : ℕ) (u : Fin M → Word F k) :
    Fin M → Fin M → ℕ :=
  fun i j =>
    if u i = u j then 0
    else if f (u i) = f (u j) then max (2 * td + 1 - hammingDist (u i) (u j)) 0
    else max (2 * tf + 1 - hammingDist (u i) (u j)) 0

/-! ### Example 6 (`#example 6#`) — the `[6,3,3]` two-step construction -/

/-- `#example 6#` (§IV) — the encoder of the `[6,3,3]` code, i.e. `u ↦ uG` for the
generator matrix with rows `100110, 010101, 001011` (systematic form). -/
def ex6Enc (u : Word F₂ 3) : Word F₂ 6 :=
  ![u 0, u 1, u 2, u 0 + u 1, u 0 + u 2, u 1 + u 2]

/-- `#example 6#` (§IV) — the four information vectors `000, 100, 011, 111`. -/
def ex6Rep : Fin 4 → Word F₂ 3 :=
  ![![false, false, false], ![true, false, false], ![false, true, true],
    ![true, true, true]]

/-- `#example 6#` (§IV) — the CDRM as printed. -/
def ex6CDRM : Fin 4 → Fin 4 → ℕ :=
  ![![0, 2, 1, 2], ![2, 0, 2, 1], ![1, 2, 0, 2], ![2, 1, 2, 0]]

/-- `#example 6#` (§IV) — the codewords as printed. -/
theorem ex6_codewords :
    ex6Enc ![false, false, false] = ![false, false, false, false, false, false] ∧
      ex6Enc ![true, false, false] = ![true, false, false, true, true, false] ∧
      ex6Enc ![false, true, true] = ![false, true, true, true, true, false] ∧
      ex6Enc ![true, true, true] = ![true, true, true, false, false, false] := by
  decide

/-- `#example 6#` (§IV) — `[6,3,3]`: every non-zero codeword has weight at least 3. -/
theorem ex6_min_dist : ∀ u : Word F₂ 3, u ≠ 0 → 3 ≤ wt (ex6Enc u) := by
  decide

/-- `#example 6#` (§IV) — the transcription of `#definition 7#` reproduces the
matrix printed in the example.  This is the check that pins our reading of the
CDRM against the paper. -/
theorem ex6_cdrm_matches :
    ∀ i j : Fin 4, cdrm (fun u => wt u) ex6Enc 2 ex6Rep i j = ex6CDRM i j := by
  decide

/-- `#example 6#` (§IV) — the `D`-code `{000,110,101,011}`. -/
def ex6Dcode : Fin 4 → Word F₂ 3 :=
  ![![false, false, false], ![true, true, false], ![true, false, true],
    ![false, true, true]]

/-- `#example 6#` (§IV) — that `D`-code satisfies every entry of the CDRM. -/
theorem ex6_dcode_valid :
    ∀ i j : Fin 4, i ≠ j → ex6CDRM i j ≤ hammingDist (ex6Dcode i) (ex6Dcode j) := by
  decide

/-- `#example 6#` (§IV) — `N(D) = 3`: no `D`-code of length 2 exists. -/
theorem ex6_no_length_two :
    ¬∃ p : Fin 4 → Word F₂ 2,
      ∀ i j : Fin 4, i ≠ j → ex6CDRM i j ≤ hammingDist (p i) (p j) := by
  decide

/-- `#example 6#` (§IV) — `N(D) = 3`: a `D`-code of length 3 exists. -/
theorem ex6_length_three :
    ∃ p : Fin 4 → Word F₂ 3,
      ∀ i j : Fin 4, i ≠ j → ex6CDRM i j ≤ hammingDist (p i) (p j) :=
  ⟨ex6Dcode, by decide⟩

/-! ### Example 7 (`#example 7#`) — the DRM with data protection for `f = wt` -/

/-- `#example 7#` (§IV) — the information vectors, in the paper's order
`000, 100, 010, 001, 110, 101, 011, 111`. -/
def ex7Vec : Fin 8 → Word F₂ 3 :=
  ![![false, false, false], ![true, false, false], ![false, true, false],
    ![false, false, true], ![true, true, false], ![true, false, true],
    ![false, true, true], ![true, true, true]]

/-- `#example 7#` (§IV) — the 8×8 DRM as printed (`t_d = 1`, `t_f = 2`). -/
def ex7DRM : Fin 8 → Fin 8 → ℕ :=
  ![![0, 4, 4, 4, 3, 3, 3, 2], ![4, 0, 1, 1, 4, 4, 2, 3], ![4, 1, 0, 1, 4, 2, 4, 3],
    ![4, 1, 1, 0, 2, 4, 4, 3], ![3, 4, 4, 2, 0, 1, 1, 4], ![3, 4, 2, 4, 1, 0, 1, 4],
    ![3, 2, 4, 4, 1, 1, 0, 4], ![2, 3, 3, 3, 4, 4, 4, 0]]

/-- `#example 7#` (§IV) — the transcription of `#definition 11#` reproduces the
8×8 matrix printed in the example.  This is the check that pins "equal function
value ⇒ the `2t_d+1` row, different ⇒ the `2t_f+1` row, diagonal `0`". -/
theorem ex7_drm_matches :
    ∀ i j : Fin 8, drmData (fun u => wt u) 1 2 ex7Vec i j = ex7DRM i j := by
  decide

/-! ## §V — Non-existence of strict `(f : d_d, d_f)`-FCCs

Definition 12 is below.  Still to come: `#theorem 8#`, `#theorem 9#`,
`#theorem 10#`, `#corollary 7#`, `#lemma 2#`, `#theorem 11#`, `#corollary 8#`.
-/

/-- `#definition 12#` (§V) — the minimum-distance graph `G(C)`: "the graph whose
vertex set is `C` and two distinct vertices `c₁, c₂ ∈ C` are adjacent if and only
if `d(c₁, c₂) = d_min(C)`, where `d_min(C)` denotes the minimum distance of the
code `C`". -/
def minDistGraph {n : ℕ} (C : Finset (Word F n)) : SimpleGraph (Word F n) where
  Adj x y := x ≠ y ∧ x ∈ C ∧ y ∈ C ∧ hammingDist x y = minDist C
  symm := ⟨fun x y ⟨hxy, hx, hy, hd⟩ =>
    ⟨hxy.symm, hy, hx, by rwa [hammingDist_comm]⟩⟩
  loopless := ⟨fun x ⟨hxx, _⟩ => hxx rfl⟩

/-! ## §VI — Function-correcting codes for specific functions

Definitions 13–15 are below.  Still to come: `#lemma 3#`, `#corollary 9#`–
`#corollary 12#`, `#lemma 4#` (external), `#lemma 5#`, `#theorem 12#`,
`#lemma 6#`.
-/

/-- `#definition 13#` (§VI-A) — the function ball: "the function ball of a
function `f : F_q^k → Im(f)` with radius `ρ` around `u ∈ F_q^k` is defined as
`B_f(u,ρ) = {f(u') | u' ∈ F_q^k and d(u,u') ≤ ρ}`". -/
def functionBall {k : ℕ} (f : Word F k → α) (u : Word F k) (ρ : ℕ) : Finset α :=
  (ball u ρ).image f

/-- `#definition 14#` (§VI-A) — a `ρ`-locally binary function: "a function `f` is
said to be a `ρ`-locally binary function if `|B_f(u,ρ)| ≤ 2` for all
`u ∈ F_q^k`". -/
def IsLocallyBinary {k : ℕ} (f : Word F k → α) (ρ : ℕ) : Prop :=
  ∀ u, (functionBall f u ρ).card ≤ 2

/-- `#definition 15#` (§VI-B) — a `(ρ,λ)`-bounded function: "a function `f` is
said to be a `(ρ,λ)`-bounded function if `|B_f(u,ρ)| ≤ λ` for all
`u ∈ F_q^k`".  (The paper's `λ` is called `lam` in Lean, where `λ` is the lambda
binder.) -/
def IsLocallyBounded {k : ℕ} (f : Word F k → α) (ρ lam : ℕ) : Prop :=
  ∀ u, (functionBall f u ρ).card ≤ lam

end Combinatorial

/-! ### Example 10 (`#example 10#`) — the `[7,4,3]` Hamming code -/

/-- `#example 10#` (§VI-A) — the encoder of the `[7,4,3]` Hamming code (`u ↦ uG`
for the generator matrix printed there, in systematic form). -/
def ex10Enc (u : Word F₂ 4) : Word F₂ 7 :=
  ![u 0, u 1, u 2, u 3, u 0 + u 1 + u 3, u 0 + u 2 + u 3, u 1 + u 2 + u 3]

/-- `#example 10#` (§VI-A) — `[7,4,3]`: every non-zero codeword has weight ≥ 3. -/
theorem ex10_min_dist : ∀ u : Word F₂ 4, u ≠ 0 → 3 ≤ wt (ex10Enc u) := by
  decide

/-- `#example 10#` (§VI-A) — the code has `2^4 = 16` codewords (sanity check on
the encoder). -/
theorem ex10_card_codewords : (Finset.univ.image ex10Enc).card = 16 := by decide

/-! ## §VII — Linear `(f : d_d, d_f)`-FCC

Definitions 16–18 are below.  Still to come: `#lemma 7#`, `#lemma 8#`,
`#lemma 9#`, `#lemma 10#`, `#theorem 13#`.
-/

section Linear

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {α : Type*} [DecidableEq α]

/-- `#definition 16#` (§VII) — a linear `(f : d_d, d_f)`-FCC: "a subspace `C` of
the vector space `F_q^n` with dimension `k` is called a linear
`(f : d_d, d_f)`-FCC if (1) weight of any non-zero codeword in `C` is at least
`d_d`, (2) for any `c₁ = (u₁,p₁), c₂ = (u₂,p₂) ∈ C` such that `f(u₁) ≠ f(u₂)`, we
have `d(c₁,c₂) ≥ d_f`". -/
def IsLinearFCC {k r : ℕ} (f : Word F k → α) (C : Submodule F (Word F (k + r)))
    (dd df : ℕ) : Prop :=
  Module.finrank F C = k ∧ (∀ c ∈ C, c ≠ 0 → dd ≤ wt c) ∧
    ∀ c₁ ∈ C, ∀ c₂ ∈ C, f (msgPart c₁) ≠ f (msgPart c₂) → df ≤ hammingDist c₁ c₂

/-- `(internal, §VII)` — the message part of a codeword of `C`, as a linear map;
`D_f` in `#definition 18#` is the kernel of `f` composed with this map. -/
def msgPartLinear {k r : ℕ} (C : Submodule F (Word F (k + r))) : C →ₗ[F] Word F k where
  toFun c := msgPart (c : Word F (k + r))
  map_add' x y := by funext i; rfl
  map_smul' a x := by funext i; rfl

/-- `#definition 17#` (§VII) — the coset code `C/D`: "the coset code `C/D` is the
collection of all cosets of `D` in `C`", `C/D = {v + D | v ∈ C}`.  (We keep the
cosets as subsets of `C` rather than passing to the quotient `C ⧸ D`.) -/
abbrev CosetCode {F : Type*} [Field F] {n : ℕ} (C : Submodule F (Word F n))
    (D : Submodule F C) : Set (Set C) :=
  Set.range (fun x : C => {y : C | x - y ∈ D})

/-- `#definition 17#` (§VII) — the coset distance of `z` modulo `D`:
`min{d(c₁,c₂) | c₁ ∈ z + D, c₂ ∈ D}`.  By `#lemma 8#` this equals
`min_{d ∈ D} wt(z + d)`, which is the form used here. -/
noncomputable def cosetDist (D : Submodule F (Word F n)) (z : Word F n) : ℕ :=
  sInf {w : ℕ | ∃ d ∈ D, w = wt (z + d)}

/-- `#definition 17#` (§VII) — the minimum distance of the coset code:
`d(C/D) = min{d(c₁,c₂) | c₁ ∈ u+D, c₂ ∈ v+D}` over pairs `u,v ∈ C` with
`u − v ∉ D`, i.e. over pairs of distinct cosets. -/
noncomputable def cosetCodeMinDist (C : Submodule F (Word F n)) (D : Submodule F C) : ℕ :=
  sInf {w : ℕ |
    ∃ x : C, ∃ y : C, (x - y) ∉ D ∧
      w = cosetDist (D.map C.subtype) ((x - y : C) : Word F n)}

/-- `#definition 18#` (§VII) — the subcode `D_f = {c = (u,p) ∈ C | u ∈ ker f}` of a
linear `(f : d_d, d_f)`-FCC for a *linear* function `f`, i.e. the kernel of
`f ∘ (message part)` restricted to `C`. -/
def kernelSubcode {k r : ℕ} (f : Word F k →ₗ[F] Word F r)
    (C : Submodule F (Word F (k + r))) : Submodule F C :=
  (LinearMap.ker f).comap (msgPartLinear C)

/-- `#definition 18#` (§VII) — the equivalent form of a linear
`(f : d_d, d_f)`-FCC for a linear function: "`d(C) ≥ d_d` and `d(C/D_f) ≥ d_f`,
where `D_f = {c = (u,p) ∈ C | u ∈ ker f}`". -/
def IsLinearFCCKernel {k r : ℕ} (f : Word F k →ₗ[F] Word F r)
    (C : Submodule F (Word F (k + r))) (dd df : ℕ) : Prop :=
  (∀ c ∈ C, c ≠ 0 → dd ≤ wt c) ∧ df ≤ cosetCodeMinDist C (kernelSubcode f C)

end Linear

/-! ## §VIII — Extension of bounds from error-correcting codes to FCCs

TODO: `#lemma 11#`, `#lemma 12#` (external), `#lemma 13#`, `#theorem 14#`,
`#theorem 15#`, `#corollary 13#`, `#theorem 16#`, `#corollary 14#`.
-/

/-! ## §IX — Conclusion

Not formalized: §IX contains no definitions or theorems, only a summary and
outlook.
-/

/-! ## Appendix — Counting the number of vectors in the union of balls

TODO: `#theorem 17#`, `#lemma 14#`, `#theorem 18#`, `#theorem 19#`.
-/

end FCC
