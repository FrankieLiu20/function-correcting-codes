import FCC.Definitions
import FCC.Basic
import FCC.Balls
import FCC.Internal
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
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

-- The `decide` checks of the examples (e.g. the search over 256 candidates in
-- `ex6_no_length_two`) need a deeper kernel recursion limit than the default of
-- 1000.  Keep this as small as the checks allow: at 100000 a full build took
-- ~15 minutes locally (CI stayed at ~2 minutes), which is why the DEVLOG note
-- about scoping the option is honoured by lowering it rather than removing it.
set_option maxRecDepth 4000

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
  by
    classical
    exact if h : ∃ r : ℕ, r ∈ {r : ℕ | ∃ C : Word F k → Word F (k + r), IsFCC f C t}
      then Nat.find h else 0

/-- `#definition 2#` (§II) — the distance requirement matrix (DRM):
`[D_f(t, u₁,…,u_M)]_{i,j} = max(2t+1 − d(u_i,u_j), 0)` if `f(u_i) ≠ f(u_j)`, and
`0` otherwise. -/
def drm {k : ℕ} {ι : Type*} (f : Word F k → α) (t : ℕ) (u : ι → Word F k) : ι → ι → ℕ :=
  fun i j => if f (u i) = f (u j) then 0
    else max (2 * t + 1 - hammingDist (u i) (u j)) 0

/-- `#definition 3#` (§II) — an irregular-distance code (`D`-code): a family
`p₁,…,p_M` of words such that `d(p_i, p_j) ≥ [D]_{i,j}` for all `i ≠ j` (the
paper's "there is an ordering of `P`" is the indexing of this family).  The
index type is an arbitrary `ι`; the DRM is indexed by `Fin M` and the FDM by the
image values, and `#theorem 1#` relates the two, so `N` must accept both. -/
def IsDCode {ι : Type*} (D : ι → ι → ℕ) (r : ℕ) : Prop :=
  ∃ p : ι → Word F r, ∀ i j, i ≠ j → D i j ≤ hammingDist (p i) (p j)

/-- `#definition 3#` (§II) — `N(D)`: "the smallest integer `r` such that there
exists a `D`-code of length `r`" (`0` if no `D`-code exists at all; the `N`-API,
including existence, is phase 3.0). -/
noncomputable def N {ι : Type*} (D : ι → ι → ℕ) : ℕ :=
  sInf {r : ℕ | IsDCode (F := F) D r}

/-- `#definition 3#` (§II) — `N(M,D)`: the minimum length of an error-correcting
code with `M` codewords and minimum distance at least `D`, i.e. `N` of the
constant matrix. -/
noncomputable def Nconst (M D : ℕ) : ℕ := N (F := F) (fun _ _ : Fin M => D)

/-- `#definition 4#` (§II) — the distance between function values:
`d(fᵢ, fⱼ) = min{d(u₁,u₂) | f(u₁) = fᵢ, f(u₂) = fⱼ}`.  The minimum over an empty
family (an empty preimage) is `0`; every use below is for values in `Im(f)`. -/
noncomputable def fDist {k : ℕ} (f : Word F k → α) (a b : α) : ℕ :=
  by
    classical
    exact if h : ∃ d : ℕ, d ∈ {d : ℕ | ∃ u v : Word F k,
        f u = a ∧ f v = b ∧ hammingDist u v = d} then Nat.find h else 0

/-- `#definition 5#` (§II) — the function distance matrix (FDM): the `E × E`
matrix (`E = |Im(f)|`) with entries `max(2t+1 − d(fᵢ,fⱼ), 0)` off the diagonal
and `0` on it.  We index it by the image values themselves. -/
noncomputable def fdm {k : ℕ} (f : Word F k → α) (t : ℕ) : α → α → ℕ :=
  fun a b => if a = b then 0 else max (2 * t + 1 - fDist f a b) 0

/-! ### §II results — the `(f,t)`-FCC bounds of [1]

Statements only, in the paper's order (the proofs are phase 3.2).  `N`'s index
type is explicit in each statement, because the DRM is indexed by `Fin m` and
the FDM by the image values. -/

/-- `#corollary 1#` (§II, quoted from [1, Cor. 1]) — "for any function
`f : F_q^k → Im(f)` and `{u₁, u₂, …, u_m} ⊆ F_q^k`:
`r_f(k,t) ≥ N(D_f(t, u₁, u₂, …, u_m))`". -/
theorem optimalRedundancy_ge_drm {k m : ℕ} (f : Word F k → α) (t : ℕ)
    (u : Fin m → Word F k) :
    N (F := F) (ι := Fin m) (drm f t u) ≤ optimalRedundancy f t := by
  sorry

/-- `#corollary 1#` (§II, quoted from [1, Cor. 1]) — "and for `|Im(f)| ≥ 2`,
`r_f(k,t) ≥ 2t`" (here `|Im(f)| ≥ 2` is stated as: two distinct values, each
attained). -/
theorem two_mul_le_optimalRedundancy {k : ℕ} (f : Word F k → α) (t : ℕ)
    (h : ∃ a b : α, a ≠ b ∧ (∃ u : Word F k, f u = a) ∧ ∃ v : Word F k, f v = b) :
    2 * t ≤ optimalRedundancy f t := by
  sorry

/-- `#theorem 1#` (§II, quoted from [1, Thm. 2]) — "for any function
`f : F_q^k → Im(f) = {f₁, f₂, …, f_E}`, `r_f(k,t) ≤ N(D_f(t, f₁, f₂, …, f_E))`,
where `D_f(t, f₁, …, f_E)` is a FDM" (`#definition 5#`). -/
theorem optimalRedundancy_le_fdm {k : ℕ} (f : Word F k → α) (t : ℕ) :
    optimalRedundancy f t ≤ N (F := F) (ι := α) (fdm f t) := by
  sorry

/-- `#corollary 2#` (§II, quoted from [1, Cor. 2]) — "if there exists a set of
representative information vectors `u₁, u₂, …, u_E` with
`{f(u₁), …, f(u_E)} = Im(f)` and `D_f(t, u₁, …, u_E) = D_f(t, f₁, …, f_E)`, then
`r_f(k,t) = N(D_f(t, f₁, …, f_E))`".  The two hypotheses are stated as: the `u_i`
attain the pairwise minimum distances of `#definition 4#`, and they hit every
value of `f`. -/
theorem optimalRedundancy_eq_fdm {k E : ℕ} (f : Word F k → α) (t : ℕ)
    (u : Fin E → Word F k)
    (hattain : ∀ i j, f (u i) ≠ f (u j) →
      hammingDist (u i) (u j) = fDist f (f (u i)) (f (u j)))
    (hsurj : ∀ v : Word F k, ∃ i : Fin E, f (u i) = f v) :
    optimalRedundancy f t = N (F := F) (ι := Fin E) (drm f t u) := by
  sorry

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

omit [DecidableEq α] in
/-- `(internal, §III — non-vacuity of the FCC set, `PLAN.md` §4 phase 3.14)` — for
*any* function `f` and *any* targets `d_d, d_f` there is an `(f : d_d, d_f)`-FCC of
some redundancy: write the message down `m = max d_d d_f` times, i.e. take
`C u = (u, u, …, u)` — the message followed by `m` copies of itself.  `C` is
systematic by construction, and two distinct messages satisfy
`d(C u, C v) = d(u,v) + m·d(u,v) ≥ m ≥ d_d, d_f`.

This is the brick that keeps the `sInf`-based `optimalRedundancyData` (and `N`)
away from their vacuous value `0`: it says the sets they take the infimum of are
non-empty, so the optima are *attained*, which is what every lower bound in §IV
(`#theorem 2#`, `#theorem 3#`) needs. -/
theorem exists_isFCCData {k : ℕ} (f : Word F k → α) (dd df : ℕ) :
    ∃ r : ℕ, ∃ C : Word F k → Word F (k + r), IsFCCData f C dd df := by
  refine ⟨k * max dd df, fun u => Fin.append u (repWord (max dd df) u), ?_, ?_, ?_⟩
  · intro u i
    simp [Fin.append_left]
  · intro u v huv
    rw [hammingDist_append, hammingDist_repWord]
    have hd1 : 0 < hammingDist u v := hammingDist_pos.mpr huv
    have hmul : max dd df ≤ max dd df * hammingDist u v := Nat.le_mul_of_pos_right _ hd1
    omega
  · intro u v hf
    rw [hammingDist_append, hammingDist_repWord]
    have huv : u ≠ v := fun hh => hf (by rw [hh])
    have hd1 : 0 < hammingDist u v := hammingDist_pos.mpr huv
    have hmul : max dd df ≤ max dd df * hammingDist u v := Nat.le_mul_of_pos_right _ hd1
    omega

/-- `#definition 7#` (§III) — the coded distance requirement matrix (CDRM):
like the DRM of `#definition 2#`, but the distances are taken between the
*codewords* `c_u = uG` rather than between the messages. -/
def cdrm {k ℓ : ℕ} {ι : Type*} (f : Word F k → α) (C : Word F k → Word F ℓ) (tf : ℕ)
    (u : ι → Word F k) : ι → ι → ℕ :=
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
  by
    classical
    exact if h : ∃ r : ℕ, r ∈ {r : ℕ | ∃ C : Word F k → Word F (k + r), IsFCCData f C dd df}
      then Nat.find h else 0

/-- `#definition 11#` (§IV) — the distance requirement matrix for an
`(f, t_d, t_f)`-FCC: entries `max(2t_d+1 − d(u_i,u_j), 0)` when `u_i ≠ u_j` and
`f(u_i) = f(u_j)`, entries `max(2t_f+1 − d(u_i,u_j), 0)` when `f(u_i) ≠ f(u_j)`,
and `0` otherwise (in particular on the diagonal). -/
def drmData {k : ℕ} {ι : Type*} (f : Word F k → α) (td tf : ℕ) (u : ι → Word F k) :
    ι → ι → ℕ :=
  fun i j =>
    if u i = u j then 0
    else if f (u i) = f (u j) then max (2 * td + 1 - hammingDist (u i) (u j)) 0
    else max (2 * tf + 1 - hammingDist (u i) (u j)) 0

/-! ### Example 5 (`#example 5#`) — the least-frequent-bit function on `F₂³` -/

/-- `#example 5#` (§III) — the function "position of the least frequent bit" on
`F₂³`: `f(000) = f(111) = 0`, `f(100) = f(011) = 1`, `f(010) = f(101) = 2`,
`f(001) = f(110) = 3`. -/
def ex5F (u : Word F₂ 3) : Fin 4 :=
  match u 0, u 1, u 2 with
  | false, false, false => 0
  | true, false, false => 1
  | false, true, false => 2
  | false, false, true => 3
  | true, true, false => 3
  | true, false, true => 2
  | false, true, true => 1
  | true, true, true => 0

/-- `#example 5#` (§III) — the information vectors `000, 100, 010, 001`. -/
def ex5Vec : Fin 4 → Word F₂ 3 :=
  ![![false, false, false], ![true, false, false], ![false, true, false],
    ![false, false, true]]

/-- `#example 5#` (§III) — the DRM printed in the paper (`t_f = 2`), which we
denote by `D` there. -/
def ex5DRM : Fin 4 → Fin 4 → ℕ :=
  ![![0, 4, 4, 4], ![4, 0, 3, 3], ![4, 3, 0, 3], ![4, 3, 3, 0]]

/-- `#example 5#` (§III) — `drm` reproduces that matrix. -/
theorem ex5_drm_matches : ∀ i j : Fin 4, drm ex5F 2 ex5Vec i j = ex5DRM i j := by
  decide

/-- `#example 5#` (§III) — the `D`-code `{000000, 111100, 110011, 001111}` of the
example ("one vector from the code is added as a parity to two message vectors
that share the same function value"). -/
def ex5Dcode : Fin 4 → Word F₂ 6 :=
  ![![false, false, false, false, false, false], ![true, true, true, true, false, false],
    ![true, true, false, false, true, true], ![false, false, true, true, true, true]]

/-- `#example 5#` (§III) — that `D`-code satisfies the DRM above. -/
theorem ex5_dcode_valid :
    ∀ i j : Fin 4, i ≠ j → ex5DRM i j ≤ hammingDist (ex5Dcode i) (ex5Dcode j) := by
  decide

/-- `#example 5#` (§III) — the resulting length-9 code of the paper, whose
messages are the eight vectors of `F₂³` in the order `000, 100, 010, 001, 110,
101, 011, 111`. -/
def ex5Code : Fin 8 → Word F₂ 9 :=
  ![![false, false, false, false, false, false, false, false, false],
    ![true, true, true, false, false, false, false, false, false],
    ![true, false, false, true, true, true, true, false, false],
    ![false, true, true, true, true, true, true, false, false],
    ![false, true, false, true, true, false, false, true, true],
    ![true, false, true, true, true, false, false, true, true],
    ![false, false, true, false, false, true, true, true, true],
    ![true, true, false, false, false, true, true, true, true]]

/-- `#example 5#` (§III) — "it can be verified that the minimum distance of this
code is `d = 3`": every pair of distinct codewords is at distance at least 3 and
some pair is at distance exactly 3. -/
theorem ex5_min_dist :
    (∀ i j : Fin 8, i ≠ j → 3 ≤ hammingDist (ex5Code i) (ex5Code j)) ∧
      ∃ i j : Fin 8, i ≠ j ∧ hammingDist (ex5Code i) (ex5Code j) = 3 := by
  decide

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

/-! ### Example 8 (`#example 8#`) — the `D`-code for the 8×8 DRM of `#example 7#` -/

/-- `#example 8#` (§IV) — the `D`-code `{000000, 110110, 101110, 011110, 011101,
101101, 110101, 000011}` of the example. -/
def ex8Dcode : Fin 8 → Word F₂ 6 :=
  ![![false, false, false, false, false, false], ![true, true, false, true, true, false],
    ![true, false, true, true, true, false], ![false, true, true, true, true, false],
    ![false, true, true, true, false, true], ![true, false, true, true, false, true],
    ![true, true, false, true, false, true], ![false, false, false, false, true, true]]

/-- `#example 8#` (§IV) — that `D`-code satisfies the 8×8 DRM of `#example 7#`. -/
theorem ex8_dcode_valid :
    ∀ i j : Fin 8, i ≠ j → ex7DRM i j ≤ hammingDist (ex8Dcode i) (ex8Dcode j) := by
  decide

/-! ### Phase 3.0 — the `sInf` API of `N`, `d_min`, `d(fᵢ,fⱼ)` and `r_f`

Proved, not stubbed: every one of them unwinds an `sInf` by exhibiting a witness
(`Nat.sInf_le`).  They are the entry point of every later proof, and they are what
lets the examples' "a witness exists" checks be converted into statements about
`N` and `d_min` (see `ISSUES.md` §6). -/

omit [Fintype F] in
/-- `(internal, §II — the `N`-API of phase 3.0)` — `N(D)` is at most the length of
any `D`-code. -/
theorem N_le_of_isDCode {ι : Type*} {D : ι → ι → ℕ} {r : ℕ}
    (h : IsDCode (F := F) D r) : N (F := F) D ≤ r :=
  Nat.sInf_le h

/-! The **lower** half of the `sInf` API: `N(D) = r` (and its `d_min`, `d(fᵢ,fⱼ)`,
`r_f` analogues) from "a witness of size `r` exists and nothing smaller does".
No block construction is needed — the witness alone makes `sInf`'s set non-empty.

Probe of the library (via a scratch file, 2026-09-19) settled the API:
`Nat.sInf_le : m ∈ s → sInf s ≤ m` (the `≤` side, proved below);
**there is no `Nat.le_sInf`**; instead
`Nat.sInf_def : s.Nonempty → sInf s = Nat.find h` with
`Nat.find_le : p n → Nat.find h ≤ n`, so the `≥` side is `r ≤ Nat.find h`, which
is `Nat.le_find`-shaped and is the one name still to be checked.  The statements
are given below with `sorry` proofs so that later phases (the example upgrades,
then `#theorem 2#`) can already cite them. -/

omit [Fintype F] in
/-- `(internal, §II — the `N`-API of phase 3.0)` — `N(D) = r` when a `D`-code of
length `r` exists and none of length `< r` does. -/
theorem N_eq_of {ι : Type*} {D : ι → ι → ℕ} {r : ℕ}
    (h1 : IsDCode (F := F) D r) (h2 : ∀ r' < r, ¬ IsDCode (F := F) D r') :
    N (F := F) D = r := by
  classical
  have hne : ∃ n : ℕ, IsDCode (F := F) D n := ⟨r, h1⟩
  have hkey : N (F := F) D = Nat.find hne := by
    rw [N]
    exact dite_eq_left hne
  rw [hkey]
  exact le_antisymm (Nat.find_min' hne h1)
    (le_of_not_gt fun hlt => h2 _ hlt (Nat.find_spec hne))

omit [Fintype F] in
/-- `(internal, §II)` — `d_min(C) = r` when two codewords of `C` are at distance
exactly `r` and no two distinct codewords are closer. -/
theorem minDist_eq_of {n r : ℕ} {C : Finset (Word F n)}
    (h1 : ∃ x ∈ C, ∃ y ∈ C, x ≠ y ∧ hammingDist x y = r)
    (h2 : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → r ≤ hammingDist x y) : minDist C = r := by
  classical
  have hmem : r ∈ {d : ℕ | ∃ x ∈ C, ∃ y ∈ C, x ≠ y ∧ hammingDist x y = d} := by
    simpa using h1
  have hne : ∃ d : ℕ, d ∈ {d : ℕ | ∃ x ∈ C, ∃ y ∈ C, x ≠ y ∧ hammingDist x y = d} :=
    ⟨r, hmem⟩
  have hkey : minDist C = Nat.find hne := by
    rw [minDist, dite_eq_left hne]
  rw [hkey]
  refine le_antisymm (Nat.find_min' hne (by simpa using h1)) (le_of_not_gt fun hlt => ?_)
  have hspec : ∃ x ∈ C, ∃ y ∈ C, x ≠ y ∧ hammingDist x y = Nat.find hne := by
    simpa using Nat.find_spec hne
  obtain ⟨x, hx, y, hy, hxy, hval⟩ := hspec
  exact absurd (hval ▸ h2 x hx y hy hxy) (not_le.mpr hlt)

/-- `(internal, §II)` — `d(fᵢ,fⱼ) = r` when a pair of witnesses achieves `r` and
every pair of witnesses is at distance at least `r`. -/
theorem fDist_eq_of {k r : ℕ} {f : Word F k → α} {a b : α}
    (h1 : ∃ u v : Word F k, f u = a ∧ f v = b ∧ hammingDist u v = r)
    (h2 : ∀ u v : Word F k, f u = a → f v = b → r ≤ hammingDist u v) :
    fDist f a b = r := by
  classical
  have hmem : r ∈ {d : ℕ | ∃ u v : Word F k, f u = a ∧ f v = b ∧ hammingDist u v = d} := by
    simpa using h1
  have hne : ∃ d : ℕ,
      d ∈ {d : ℕ | ∃ u v : Word F k, f u = a ∧ f v = b ∧ hammingDist u v = d} := ⟨r, hmem⟩
  have hkey : fDist f a b = Nat.find hne := by
    rw [fDist, dite_eq_left hne]
  rw [hkey]
  refine le_antisymm (Nat.find_min' hne (by simpa using h1)) (le_of_not_gt fun hlt => ?_)
  have hspec : ∃ u v : Word F k, f u = a ∧ f v = b ∧ hammingDist u v = Nat.find hne := by
    simpa using Nat.find_spec hne
  obtain ⟨u, v, hu, hv, hval⟩ := hspec
  exact absurd (hval ▸ h2 u v hu hv) (not_le.mpr hlt)

omit [DecidableEq α] in
/-- `(internal, §II)` — `r_f(k,t) = r` when an `(f,t)`-FCC of redundancy `r`
exists and nothing smaller does. -/
theorem optimalRedundancy_eq_of {k r : ℕ} {f : Word F k → α} {t : ℕ}
    (h1 : ∃ C : Word F k → Word F (k + r), IsFCC f C t)
    (h2 : ∀ r' < r, ¬ ∃ C : Word F k → Word F (k + r'), IsFCC f C t) :
    optimalRedundancy f t = r := by
  classical
  have hne : ∃ n : ℕ, n ∈ {r' : ℕ | ∃ C : Word F k → Word F (k + r'), IsFCC f C t} :=
    ⟨r, h1⟩
  have hkey : optimalRedundancy f t = Nat.find hne := by
    rw [optimalRedundancy, dite_eq_left hne]
  rw [hkey]
  refine le_antisymm (Nat.find_min' hne h1) (le_of_not_gt fun hlt => ?_)
  exact h2 _ hlt (Nat.find_spec hne)

omit [DecidableEq α] in
/-- `(internal, §IV)` — `r_f(k : d_d, d_f) = r` when an `(f : d_d, d_f)`-FCC of
redundancy `r` exists and nothing smaller does. -/
theorem optimalRedundancyData_eq_of {k r : ℕ} {f : Word F k → α} {dd df : ℕ}
    (h1 : ∃ C : Word F k → Word F (k + r), IsFCCData f C dd df)
    (h2 : ∀ r' < r, ¬ ∃ C : Word F k → Word F (k + r'), IsFCCData f C dd df) :
    optimalRedundancyData f dd df = r := by
  classical
  have hne : ∃ n : ℕ,
      n ∈ {r' : ℕ | ∃ C : Word F k → Word F (k + r'), IsFCCData f C dd df} := ⟨r, h1⟩
  have hkey : optimalRedundancyData f dd df = Nat.find hne := by
    rw [optimalRedundancyData, dite_eq_left hne]
  rw [hkey]
  refine le_antisymm (Nat.find_min' hne h1) (le_of_not_gt fun hlt => ?_)
  exact h2 _ hlt (Nat.find_spec hne)

omit [Fintype F] in
/-- `(internal, §II)` — the minimum distance of a code is at most the distance of
any pair of distinct codewords. -/
theorem minDist_le {n : ℕ} {C : Finset (Word F n)} {x y : Word F n} (hx : x ∈ C)
    (hy : y ∈ C) (hxy : x ≠ y) : minDist C ≤ hammingDist x y :=
  by
    classical
    have hne : ∃ d : ℕ, d ∈ {d : ℕ | ∃ x ∈ C, ∃ y ∈ C, x ≠ y ∧ hammingDist x y = d} :=
      ⟨hammingDist x y, ⟨x, hx, y, hy, hxy, rfl⟩⟩
    rw [minDist, dite_eq_left hne]
    exact Nat.find_min' hne ⟨x, hx, y, hy, hxy, rfl⟩

/-- `(internal, §II)` — `d(fᵢ,fⱼ)` is at most the distance of any pair of
witnesses, one from each preimage. -/
theorem fDist_le {k : ℕ} {f : Word F k → α} {a b : α} {u v : Word F k} (hu : f u = a)
    (hv : f v = b) : fDist f a b ≤ hammingDist u v :=
  by
    classical
    have hne : ∃ d : ℕ,
        d ∈ {d : ℕ | ∃ u v : Word F k, f u = a ∧ f v = b ∧ hammingDist u v = d} :=
      ⟨hammingDist u v, ⟨u, v, hu, hv, rfl⟩⟩
    rw [fDist, dite_eq_left hne]
    exact Nat.find_min' hne ⟨u, v, hu, hv, rfl⟩

omit [DecidableEq α] in
/-- `(internal, §II)` — `r_f(k,t)` is at most the redundancy of any `(f,t)`-FCC. -/
theorem optimalRedundancy_le_of {k r : ℕ} {f : Word F k → α}
    {C : Word F k → Word F (k + r)} {t : ℕ} (h : IsFCC f C t) :
    optimalRedundancy f t ≤ r :=
  by
    classical
    have hne : ∃ n : ℕ, n ∈ {r' : ℕ | ∃ C : Word F k → Word F (k + r'), IsFCC f C t} :=
      ⟨r, C, h⟩
    rw [optimalRedundancy, dite_eq_left hne]
    exact Nat.find_min' hne ⟨C, h⟩

omit [DecidableEq α] in
/-- `(internal, §IV)` — `r_f(k : d_d, d_f)` is at most the redundancy of any
`(f : d_d, d_f)`-FCC. -/
theorem optimalRedundancyData_le_of {k r : ℕ} {f : Word F k → α}
    {C : Word F k → Word F (k + r)} {dd df : ℕ} (h : IsFCCData f C dd df) :
    optimalRedundancyData f dd df ≤ r :=
  by
    classical
    have hne : ∃ n : ℕ,
        n ∈ {r' : ℕ | ∃ C : Word F k → Word F (k + r'), IsFCCData f C dd df} := ⟨r, C, h⟩
    rw [optimalRedundancyData, dite_eq_left hne]
    exact Nat.find_min' hne ⟨C, h⟩

/-! ### §IV results — bounds for the optimal redundancy with data protection

`#theorem 2#` is the first paper result of this development to be *proved* (phase
3.2); the rest of the block — `#theorem 3#`–`#theorem 6#` (phases 3.3–3.4) — is
stated only.  `#theorem 7#`, `#corollary 5#`, `#corollary 6#` and `#remark 1#`
are not written yet: `#theorem 7#` speaks about the redundancy `r_s` of the
two-step *scheme* (a construction-level notion that phase 1 has not defined yet),
and `#corollary 5#`/`#corollary 6#` rest on the external results `#lemma 1#` and
[1, Appendix].

The identity is assembled from four internal bricks, stated below in dependency
order: the systematic splitting `hammingDist_eq_msg_add_red`, the extraction of a
`D`-code out of an FCC (`isDCode_drmData_of_isFCCData`), its consequence
`N(D_f) ≤ r` (`N_drmData_le_of_isFCCData`), and the reverse half `r_f ≤ r`
(`optimalRedundancyData_le_of_isDCode`) that builds an FCC from a `D`-code. -/

/-- `(internal, §II — the key step of `#theorem 2#`)` — for a *systematic* encoding
the Hamming distance of two codewords splits into the message part and the
redundancy part: `d(C u, C v) = d(u,v) + d(p_u, p_v)`, where `p_u` is
`redPart (C u)`.  This is the identity `#theorem 2#` uses in both directions (to
build an FCC from a `D`-code, and to extract a `D`-code from an FCC), and the
reason `ISSUES.md` §1 records systematicity as part of `#definition 6#`.

Proof: a systematic codeword *is* the concatenation of its message part with its
redundancy part (`Fin.addCases`, `Fin.append_left`/`Fin.append_right`), and
`hammingDist_append` adds the two distances. -/
theorem hammingDist_eq_msg_add_red {k r : ℕ} {C : Word F k → Word F (k + r)}
    (hC : IsSystematic C) (u v : Word F k) :
    hammingDist (C u) (C v) = hammingDist u v +
      hammingDist (redPart (C u)) (redPart (C v)) := by
  classical
  have hcu : C u = Fin.append (fun i => C u (Fin.castAdd r i)) (redPart (C u)) := by
    funext i
    refine Fin.addCases (motive := fun i => C u i =
        Fin.append (fun j => C u (Fin.castAdd r j)) (redPart (C u)) i)
      (fun a => ?_) (fun b => ?_) i
    · rw [Fin.append_left]
    · rw [Fin.append_right]; rfl
  have hcv : C v = Fin.append (fun i => C v (Fin.castAdd r i)) (redPart (C v)) := by
    funext i
    refine Fin.addCases (motive := fun i => C v i =
        Fin.append (fun j => C v (Fin.castAdd r j)) (redPart (C v)) i)
      (fun a => ?_) (fun b => ?_) i
    · rw [Fin.append_left]
    · rw [Fin.append_right]; rfl
  have hmu : (fun i => C u (Fin.castAdd r i)) = u := funext fun i => hC u i
  have hmv : (fun i => C v (Fin.castAdd r i)) = v := funext fun i => hC v i
  conv_lhs => rw [hcu, hcv, hammingDist_append]
  rw [hmu, hmv]

/-- `(internal, §IV — the extraction step inside `#theorem 2#` and `#theorem 3#`)` —
an `(f : 2t_d+1, 2t_f+1)`-FCC of redundancy `r` *is* a `D`-code of length `r` for
the DRM of any family `u₁, …, u_m` of messages: take `pᵢ := redPart (C uᵢ)`.

For `i ≠ j` the splitting brick gives `d(pᵢ,pⱼ) = d(C uᵢ,C uⱼ) − d(uᵢ,uⱼ)`; when
`f(uᵢ) = f(uⱼ)` the data-protection condition bounds the first term by `2t_d+1`,
and when `f(uᵢ) ≠ f(uⱼ)` the function-correcting condition bounds it by `2t_f+1`.
Those are exactly `drmData`'s two off-diagonal entries modulo the outer `max (…) 0`,
which is what `max_le` and `omega` discharge.  (When `i ≠ j` but `uᵢ = uⱼ` there is
nothing to prove: that entry of the DRM is `0` by definition.) -/
theorem isDCode_drmData_of_isFCCData {k r td tf : ℕ} {ι : Type*} {f : Word F k → α}
    {C : Word F k → Word F (k + r)} (u : ι → Word F k)
    (hC : IsFCCData f C (2 * td + 1) (2 * tf + 1)) :
    IsDCode (F := F) (drmData f td tf u) r := by
  classical
  refine ⟨fun i => redPart (C (u i)), ?_⟩
  intro i j hij
  simp only [drmData]
  by_cases huv : u i = u j
  · rw [ite_eq_left huv]
    exact Nat.zero_le _
  · rw [ite_eq_right huv]
    have hsplit := hammingDist_eq_msg_add_red hC.1 (u i) (u j)
    by_cases hf : f (u i) = f (u j)
    · rw [ite_eq_left hf]
      have hd := hC.2.1 (u i) (u j) huv
      rw [hsplit] at hd
      refine max_le ?_ (Nat.zero_le _)
      omega
    · rw [ite_eq_right hf]
      have hd := hC.2.2 (u i) (u j) hf
      rw [hsplit] at hd
      refine max_le ?_ (Nat.zero_le _)
      omega

/-- `(internal, §IV — the "≥" half of `#theorem 2#`)` — any
`(f : 2t_d+1, 2t_f+1)`-FCC of redundancy `r` yields a `D`-code of length `r` for
the DRM of `u₁, …, u_{q^k}`, so `N(D_f) ≤ r`.  This half is the one used for the
*lower* bounds on `r_f` in §V–§VI: every FCC gives a DRM code of the same length. -/
theorem N_drmData_le_of_isFCCData {k r td tf : ℕ} (f : Word F k → α)
    (h : ∃ C : Word F k → Word F (k + r), IsFCCData f C (2 * td + 1) (2 * tf + 1)) :
    N (F := F) (ι := Word F k) (drmData f td tf fun v => v) ≤ r := by
  obtain ⟨C, hC⟩ := h
  exact N_le_of_isDCode (isDCode_drmData_of_isFCCData (fun v => v) hC)

/-- `(internal, §IV — the "≤" half of `#theorem 2#`)` — if a `D`-code
`p₁, …, p_{q^k}` of length `r` exists for the DRM of the whole message space, then
`r_f ≤ r`: the map `C u := append u (p u)` is systematic by `Fin.append_left`, its
distance is `d(u,v) + d(p_u,p_v)` by `hammingDist_append`, and `drmData`'s entries
are exactly the slacks that the two distance conditions of `IsFCCData` ask for.

`hdf` is the paper's side condition `d_d ≤ d_f` inside `#definition 6#` (see
`ISSUES.md` §11): it is needed because the data-protection clause is demanded of
*every* pair `u ≠ v`, not only of the pairs with `f(u) = f(v)`, while the DRM only
records the `2t_d+1` slack on the latter. -/
theorem optimalRedundancyData_le_of_isDCode {k r td tf : ℕ} (f : Word F k → α)
    (hdf : 2 * td + 1 ≤ 2 * tf + 1) (p : Word F k → Word F r)
    (hp : ∀ i j : Word F k, i ≠ j →
      drmData f td tf (fun v => v) i j ≤ hammingDist (p i) (p j)) :
    optimalRedundancyData f (2 * td + 1) (2 * tf + 1) ≤ r := by
  classical
  have hsys : IsSystematic (fun v : Word F k => Fin.append v (p v)) := by
    intro v i
    simp [Fin.append_left]
  have hbound : ∀ a b : Word F k, a ≠ b →
      2 * td + 1 ≤ hammingDist (Fin.append a (p a)) (Fin.append b (p b)) := by
    intro a b hab
    rw [hammingDist_append]
    have h := hp a b hab
    simp only [drmData] at h
    rw [ite_eq_right hab] at h
    by_cases hf : f a = f b
    · rw [ite_eq_left hf] at h
      have hle : 2 * td + 1 - hammingDist a b ≤ hammingDist (p a) (p b) :=
        le_trans (le_max_left _ _) h
      omega
    · rw [ite_eq_right hf] at h
      have hle : 2 * tf + 1 - hammingDist a b ≤ hammingDist (p a) (p b) :=
        le_trans (le_max_left _ _) h
      omega
  have hboundf : ∀ a b : Word F k, f a ≠ f b →
      2 * tf + 1 ≤ hammingDist (Fin.append a (p a)) (Fin.append b (p b)) := by
    intro a b hf
    have hab : a ≠ b := fun hh => hf (by rw [hh])
    rw [hammingDist_append]
    have h := hp a b hab
    simp only [drmData] at h
    rw [ite_eq_right hab] at h
    rw [ite_eq_right hf] at h
    have hle : 2 * tf + 1 - hammingDist a b ≤ hammingDist (p a) (p b) :=
      le_trans (le_max_left _ _) h
    omega
  exact optimalRedundancyData_le_of (C := fun v : Word F k => Fin.append v (p v))
    ⟨hsys, hbound, hboundf⟩

/-- `#theorem 2#` (§IV) — "for any function `f : F_q^k → Im(f)`,
`r_f(k,t_d,t_f) = N(D_f(t_d,t_f : u₁, …, u_{q^k}))`": the optimal redundancy is
exactly the minimum length of a `D`-code for the DRM of the whole message space.

One hypothesis makes the paper's standing assumption explicit: `hdf`, the
`d_d ≤ d_f` of `#definition 6#` (see `ISSUES.md` §11(a)).  It is *used*: the
data-protection clause of `IsFCCData` is demanded of every pair `u₁ ≠ u₂`, while
the DRM records the `2t_d+1` slack only on the pairs with `f(u₁) = f(u₂)`, so the
`≤` half of the proof needs `2t_d+1 ≤ 2t_f+1` to transfer the guarantee.  Both
sides are attained — `exists_isFCCData` above provides an FCC of some redundancy,
which makes the FCC set non-empty, and hence both `sInf`s minima (`ISSUES.md`
§11(b), `PLAN.md` §4 phase 3.14).

Proof: `le_antisymm` of the two halves above.  For `≤`, the FCC supplied by
`exists_isFCCData` gives a DRM code (`Nat.sInf_mem`), whose length is at least
`N(D_f)`; for `≥`, the FCC attaining `r_f` (`Nat.find_spec`) is a DRM code of that
length.  Neither direction needs any additional existence hypothesis. -/
theorem optimalRedundancyData_eq_N_drmData {k : ℕ} (f : Word F k → α) (td tf : ℕ)
    (hdf : 2 * td + 1 ≤ 2 * tf + 1) :
    optimalRedundancyData f (2 * td + 1) (2 * tf + 1) =
      N (F := F) (ι := Word F k) (drmData f td tf fun v => v) := by
  classical
  refine le_antisymm ?_ ?_
  · obtain ⟨r, C, hC⟩ := exists_isFCCData f (2 * td + 1) (2 * tf + 1)
    have hne : {r : ℕ | IsDCode (F := F) (drmData f td tf fun v => v) r}.Nonempty :=
      ⟨r, isDCode_drmData_of_isFCCData (fun v => v) hC⟩
    obtain ⟨p, hp⟩ := Nat.sInf_mem hne
    exact optimalRedundancyData_le_of_isDCode f hdf p hp
  · obtain ⟨r, C, hC⟩ := exists_isFCCData f (2 * td + 1) (2 * tf + 1)
    have hne : ∃ r' : ℕ, r' ∈ {r' : ℕ | ∃ C : Word F k → Word F (k + r'),
        IsFCCData f C (2 * td + 1) (2 * tf + 1)} := ⟨r, C, hC⟩
    rw [optimalRedundancyData, dite_eq_left hne]
    have hspec := Nat.find_spec hne
    simp only [Set.mem_ofPred_eq] at hspec
    exact N_drmData_le_of_isFCCData f hspec

omit [Fintype F] in
/-- `(internal, §IV — used by `#theorem 3#`)` — if two messages carry different
values of `f`, then so does some pair at Hamming distance exactly one.  This is
the paper's "if `|Im(f)| ≥ 2`, then there exist `u, v` with `f(u) ≠ f(v)` and
`d(u,v) = 1`": walk from `u` to `v` changing one coordinate at a time (the
`m`-th word of the walk agrees with `v` on the first `m` coordinates), and note
that `f` starts at `f(u)` and ends at `f(v)`, so one step of the walk must change
the value of `f`. -/
theorem exists_hammingDist_one_ne {k : ℕ} (f : Word F k → α) {u v : Word F k}
    (h : f u ≠ f v) :
    ∃ u' v' : Word F k, hammingDist u' v' = 1 ∧ f u' ≠ f v' := by
  classical
  have hstep : ∃ m : ℕ, m < k ∧
      f (fun i : Fin k => if (i : ℕ) < m then v i else u i) ≠
        f (fun i : Fin k => if (i : ℕ) < m + 1 then v i else u i) := by
    by_contra hcon
    push Not at hcon
    have hchain : ∀ m : ℕ, m ≤ k →
        f (fun i : Fin k => if (i : ℕ) < m then v i else u i) = f u := by
      intro m
      induction m with
      | zero => intro _; simp
      | succ m ih =>
        intro hm
        rw [← hcon m (by omega)]
        exact ih (by omega)
    have hk := hchain k le_rfl
    have hwv : (fun i : Fin k => if (i : ℕ) < k then v i else u i) = v := by
      funext i
      simp [i.isLt]
    rw [hwv] at hk
    exact h hk.symm
  obtain ⟨m, hmk, hm⟩ := hstep
  refine ⟨fun i : Fin k => if (i : ℕ) < m then v i else u i,
    fun i : Fin k => if (i : ℕ) < m + 1 then v i else u i, ?_, hm⟩
  have hdiff : ∀ a : Fin k, (fun i : Fin k => if (i : ℕ) < m then v i else u i) a ≠
      (fun i : Fin k => if (i : ℕ) < m + 1 then v i else u i) a → (a : ℕ) = m := by
    intro a ha
    have hge : ¬ (a : ℕ) < m := fun h1 => ha (by simp [h1, Nat.lt_succ_of_lt h1])
    have hlt : (a : ℕ) < m + 1 := by
      by_contra h2
      exact ha (by simp [hge, h2])
    omega
  have hsub : diffSet (fun i : Fin k => if (i : ℕ) < m then v i else u i)
      (fun i : Fin k => if (i : ℕ) < m + 1 then v i else u i) ⊆ {⟨m, hmk⟩} := by
    intro a ha
    rw [diffSet, Finset.mem_filter] at ha
    rw [Finset.mem_singleton]
    exact Fin.ext (hdiff a ha.2)
  have h1 : hammingDist (fun i : Fin k => if (i : ℕ) < m then v i else u i)
      (fun i : Fin k => if (i : ℕ) < m + 1 then v i else u i) ≤ 1 := by
    rw [hammingDist_eq_card_diffSet]
    calc (diffSet _ _).card ≤ ({⟨m, hmk⟩} : Finset (Fin k)).card := Finset.card_le_card hsub
      _ = 1 := Finset.card_singleton _
  have hne : (fun i : Fin k => if (i : ℕ) < m then v i else u i) ≠
      (fun i : Fin k => if (i : ℕ) < m + 1 then v i else u i) := fun hh => hm (by rw [hh])
  have hpos : 0 < hammingDist (fun i : Fin k => if (i : ℕ) < m then v i else u i)
      (fun i : Fin k => if (i : ℕ) < m + 1 then v i else u i) := hammingDist_pos.mpr hne
  omega

/-- `#theorem 3#` (§IV) — "for any function `f : F_q^k → Im(f)` and
`{u₁, u₂, …, u_m} ⊆ F_q^k`, we have
`r_f(k,t_d,t_f) ≥ N(D_f(t_d,t_f : u₁, …, u_m))`".

Proof (the paper's "the first part is straightforward"): an optimal FCC satisfies
the DRM's distance requirement on the whole message space, so restricting its
redundancy part to `u₁, …, u_m` gives a `D`-code of the same length
(`isDCode_drmData_of_isFCCData`), whence `N(D_f(u₁,…,u_m)) ≤ r_f`.  The optimum
is attained because `exists_isFCCData` exhibits an FCC. -/
theorem optimalRedundancyData_ge_N_subset {k m : ℕ} (f : Word F k → α) (td tf : ℕ)
    (u : Fin m → Word F k) :
    N (F := F) (ι := Fin m) (drmData f td tf u) ≤
      optimalRedundancyData f (2 * td + 1) (2 * tf + 1) := by
  classical
  obtain ⟨r, C, hC⟩ := exists_isFCCData f (2 * td + 1) (2 * tf + 1)
  have hne : ∃ r' : ℕ, r' ∈ {r' : ℕ | ∃ C : Word F k → Word F (k + r'),
      IsFCCData f C (2 * td + 1) (2 * tf + 1)} := ⟨r, C, hC⟩
  rw [optimalRedundancyData, dite_eq_left hne]
  have hspec := Nat.find_spec hne
  simp only [Set.mem_ofPred_eq] at hspec
  obtain ⟨C₀, hC₀⟩ := hspec
  exact N_le_of_isDCode (isDCode_drmData_of_isFCCData u hC₀)

/-- `#theorem 3#` (§IV) — "and `r_f(k,t_d,t_f) ≥ 2t_f` for `|Im(f)| ≥ 2`" (the
hypothesis is stated as: two distinct values, each attained).

Proof (the paper's): pick messages `u, v` with `f(u) ≠ f(v)` and, by
`exists_hammingDist_one_ne`, a pair `u', v'` at distance one with `f(u') ≠ f(v')`.
On that pair the DRM reads `max(2t_f + 1 − 1, 0) = 2t_f`, and a `D`-code of
length `r` has pairwise distances at most `r`, so `2t_f ≤ N(D_f(u',v')) ≤ r_f`
by the first part. -/
theorem two_mul_le_optimalRedundancyData {k : ℕ} (f : Word F k → α) (td tf : ℕ)
    (h : ∃ a b : α, a ≠ b ∧ (∃ u : Word F k, f u = a) ∧ ∃ v : Word F k, f v = b) :
    2 * tf ≤ optimalRedundancyData f (2 * td + 1) (2 * tf + 1) := by
  classical
  obtain ⟨a, b, hab, ⟨u, hu⟩, ⟨v, hv⟩⟩ := h
  have huv : f u ≠ f v := by rw [hu, hv]; exact hab
  obtain ⟨u', v', hd1, hfne⟩ := exists_hammingDist_one_ne f huv
  let w : Fin 2 → Word F k := fun i => if i = 0 then u' else v'
  have hw0 : w 0 = u' := by simp [w]
  have hw1 : w 1 = v' := by simp [w]
  have huw : w 0 ≠ w 1 := by rw [hw0, hw1]; exact fun hh => hfne (by rw [hh])
  have hentry : drmData f td tf w 0 1 = 2 * tf := by
    simp only [drmData]
    rw [ite_eq_right huw, ite_eq_right (by rw [hw0, hw1]; exact hfne), hw0, hw1, hd1,
      show 2 * tf + 1 - 1 = 2 * tf from by omega, max_eq_left (Nat.zero_le _)]
  have hNentry : drmData f td tf w 0 1 ≤ N (F := F) (ι := Fin 2) (drmData f td tf w) := by
    obtain ⟨r, C, hC⟩ := exists_isFCCData f (2 * td + 1) (2 * tf + 1)
    have hne : {r : ℕ | IsDCode (F := F) (drmData f td tf w) r}.Nonempty :=
      ⟨r, isDCode_drmData_of_isFCCData w hC⟩
    obtain ⟨p, hp⟩ := Nat.sInf_mem hne
    calc drmData f td tf w 0 1 ≤ hammingDist (p 0) (p 1) := hp 0 1 (by decide)
      _ ≤ N (F := F) (ι := Fin 2) (drmData f td tf w) := by
        have hle := hammingDist_le_card_fintype (x := p 0) (y := p 1)
        rw [Fintype.card_fin] at hle
        exact hle
  calc 2 * tf = drmData f td tf w 0 1 := hentry.symm
    _ ≤ N (F := F) (ι := Fin 2) (drmData f td tf w) := hNentry
    _ ≤ optimalRedundancyData f (2 * td + 1) (2 * tf + 1) :=
        optimalRedundancyData_ge_N_subset f td tf w

omit [DecidableEq α] in
/-- `#theorem 3#` (§IV) — "further, `r_f(k,t_d,t_f) ≥ N(q^k, 2t_d+1) − k`, where
`N(M,d)` is the minimum length of an error-correcting code with `M` codewords
and minimum distance `d`" (`#definition 3#`).

Proof: an `(f : 2t_d+1, 2t_f+1)`-FCC of redundancy `r` has `d(C u, C v) ≥ 2t_d+1`
for *every* pair `u ≠ v` and lives in `F_q^{k+r}`, so (enumerating the `q^k`
messages) it is an error-correcting code with `q^k` codewords, minimum distance
`2t_d+1` and length `k + r`; hence `N(q^k, 2t_d+1) ≤ k + r`.  We take the FCC
attaining `r_f`, which exists by `exists_isFCCData`.  Note that this needs no
`t_f ≥ t_d` — the argument goes through the data-protection clause of
`#definition 6#` directly, whereas the paper's runs through the DRM entries. -/
theorem optimalRedundancyData_ge_Nconst_sub {k : ℕ} (f : Word F k → α) (td tf : ℕ) :
    Nconst (F := F) (Fintype.card (Word F k)) (2 * td + 1) - k ≤
      optimalRedundancyData f (2 * td + 1) (2 * tf + 1) := by
  classical
  obtain ⟨r, C, hC⟩ := exists_isFCCData f (2 * td + 1) (2 * tf + 1)
  have hne : ∃ r' : ℕ, r' ∈ {r' : ℕ | ∃ C : Word F k → Word F (k + r'),
      IsFCCData f C (2 * td + 1) (2 * tf + 1)} := ⟨r, C, hC⟩
  rw [optimalRedundancyData, dite_eq_left hne]
  have hspec := Nat.find_spec hne
  simp only [Set.mem_ofPred_eq] at hspec
  obtain ⟨C₀, hC₀⟩ := hspec
  let e : Fin (Fintype.card (Word F k)) ≃ Word F k :=
    (Fintype.equivFin (Word F k)).symm
  have hcode : IsDCode (F := F)
      (fun _ _ : Fin (Fintype.card (Word F k)) => 2 * td + 1) (k + Nat.find hne) := by
    refine ⟨fun i => C₀ (e i), ?_⟩
    intro i j hij
    exact hC₀.2.1 (e i) (e j) (fun hh => hij (e.injective hh))
  have hN := N_le_of_isDCode hcode
  show N (F := F) (fun _ _ : Fin (Fintype.card (Word F k)) => 2 * td + 1) - k ≤
    Nat.find hne
  omega

/-- `#theorem 4#` (§IV) — over `F₂`: "for any function `f : F₂^k → Im(f)`, if
`2 ≤ |Im(f)| ≤ k` then `r_f(k,t_d,t_f) ≥ 2t_f + t_d`". -/
theorem binary_optimalRedundancyData_ge {k : ℕ} (f : Word (ZMod 2) k → α) (td tf : ℕ)
    (h2 : 2 ≤ (Finset.univ.image f).card) (hk : (Finset.univ.image f).card ≤ k) :
    2 * tf + td ≤ optimalRedundancyData f (2 * td + 1) (2 * tf + 1) := by
  sorry

/-- `#theorem 5#` (§IV) — "let `C` be an `[n, k, 2t_d+1]` error-correcting code,
and let `c_u` denote the codeword that corresponds to the message vector
`u ∈ F_q^k`.  For any function `f`,
`N(D_f(t_d,t_f : u₁,…,u_{q^k})) ≤ N(D_{C,f}(t_f : u₁,…,u_{q^k})) + n − k`". -/
theorem N_drmData_le_N_cdrm_add {k r m : ℕ} (f : Word F k → α) (td tf : ℕ)
    (C : Word F k → Word F (k + r)) (u : Fin m → Word F k)
    (hC : ∀ v w : Word F k, v ≠ w → 2 * td + 1 ≤ hammingDist (C v) (C w)) :
    N (F := F) (ι := Fin m) (drmData f td tf u) ≤
      N (F := F) (ι := Fin m) (cdrm f C tf u) + r := by
  sorry

/-- `#corollary 4#` (§IV) — "for any function `f : F_q^k → Im(f)`,
`r_f(k,t_d,t_f) ≤ N(D_{C,f}(t_f : u₁,…,u_{q^k})) + n − k`, where `C` is an
`[n, k, 2t_d+1]` error-correcting code". -/
theorem optimalRedundancyData_le_N_cdrm_add {k r : ℕ} (f : Word F k → α) (td tf : ℕ)
    (C : Word F k → Word F (k + r))
    (hC : ∀ v w : Word F k, v ≠ w → 2 * td + 1 ≤ hammingDist (C v) (C w)) :
    optimalRedundancyData f (2 * td + 1) (2 * tf + 1) ≤
      N (F := F) (ι := Word F k) (cdrm f C tf fun v => v) + r := by
  sorry

/-- `#theorem 6#` (§IV) — "let `C` be an `[n, k, 2t_d+1]` code.  Then
`N(D_{C,f}(t_f : u₁, u₂, …, u_M)) ≤ N(M, 2(t_f − t_d))`". -/
theorem N_cdrm_le_Nconst {k r m : ℕ} (f : Word F k → α) (td tf : ℕ)
    (C : Word F k → Word F (k + r)) (u : Fin m → Word F k)
    (hC : ∀ v w : Word F k, v ≠ w → 2 * td + 1 ≤ hammingDist (C v) (C w)) :
  N (F := F) (ι := Fin m) (cdrm f C tf u) ≤ Nconst (F := F) m (2 * (tf - td)) := by
  sorry

/-- `(internal, §III-A — used by `#theorem 7#`)` — the total redundancy `r_s` of
the two-step construction: "the resulting mapping ... is an `(f : d_d, d_f)`-FCC
with total redundancy `r_s = n − k + r'`", i.e. the redundancy `r` of the first
code plus the length `r'` of the second (FCC) step.  The scheme of `#theorem 7#`
uses an optimal second step, so `r' = N(CDRM)`. -/
def schemeRedundancy (r r' : ℕ) : ℕ := r + r'

/-- `#theorem 7#` (§IV) — "let `C` be an `[n, k, 2t_d+1]` linear code, where `n`
denotes the minimum possible length of a linear code with dimension `k` and
minimum distance at least `2t_d + 1`.  Then, the redundancy `r_s` of the proposed
scheme is bounded as
`N(D_{C,f}(t_f : u₁,…,u_M)) + n − k ≤ r_s ≤ N(D_{C,f}(t_f : f₁,…,f_E)) + n − k`".

With our `schemeRedundancy`, `r_s = r + N(CDRM)` (the scheme takes the second
step optimal, `r' = N(CDRM)`); the two-sided bound is then the statement that the
CDRM of a set of representatives is sandwiched by the CFDM of the whole function,
whose `≤` half is the content of the theorem.  The representatives enter through
`hsurj`/`hattain` exactly as in `#corollary 2#`. -/
theorem two_step_redundancy_bounds {k r E : ℕ} (f : Word F k → α) (tf : ℕ)
    (C : Word F k → Word F (k + r)) (u : Fin E → Word F k)
    (hsurj : ∀ v : Word F k, ∃ i : Fin E, f (u i) = f v)
    (hattain : ∀ i j, f (u i) ≠ f (u j) →
      hammingDist (u i) (u j) = fDist f (f (u i)) (f (u j))) :
    schemeRedundancy r (N (F := F) (ι := Fin E) (cdrm f C tf u)) + 0 =
        r + N (F := F) (ι := Fin E) (cdrm f C tf u) ∧
      N (F := F) (ι := Fin E) (cdrm f C tf u) + r ≤
        N (F := F) (ι := α) (cfdm f C tf) + r := by
  sorry

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

/-! ### §V results — non-existence of strict `(f : d_d, d_f)`-FCCs

Statements only, in the paper's order (proofs are phases 3.5–3.7).  `#theorem 9#`
is not written yet: it counts the connected components of `G(C)`, and phase 1 did
not define that count for `SimpleGraph` — it is the natural next helper.
`IsPerfect` and `IsMDS` are `(internal, §V-B)` definitions in `FCC/Basic.lean`,
because §V-B introduces those two code classes in prose rather than numbered. -/

/-- `#theorem 8#` (§V-A) — "let `C` be a `(n, q^k, d)` code.  If the
minimum-distance graph `G(C)` is a connected graph, then `C` cannot be an
`(f : d, d_f)`-FCC for any `f : F_q^k → Im(f)` with `|Im(f)| ≥ 2` and `d_f > d`,
equivalently `C` cannot be a strict `(f : d, d_f)`-FCC".  The encoding is
required to have all its codewords in `C`, so that `G(C)` is the graph of the
code under test. -/
theorem not_isFCCData_of_connected {k r d df : ℕ} (C : Finset (Word F (k + r)))
    (hmin : minDist C = d) (hconn : (minDistGraph C).Preconnected) (f : Word F k → α)
    (h2 : ∃ a b : α, a ≠ b ∧ (∃ u : Word F k, f u = a) ∧ ∃ v : Word F k, f v = b)
    (hdf : d < df) :
    ¬∃ enc : Word F k → Word F (k + r), IsFCCData f enc d df ∧ ∀ u, enc u ∈ C := by
  sorry

/-- `(internal, §V-A — used by `#theorem 9#`)` — the number `Q` of connected
components of a graph: "if the minimum-distance graph `G(C)` has `Q` number of
connected components".  (`Nat.card` of the quotient of vertices by reachability,
so no `Fintype` instance on the quotient is needed.) -/
noncomputable def componentCount {V : Type*} (G : SimpleGraph V) : ℕ :=
  Nat.card G.ConnectedComponent

/-- `#theorem 9#` (§V-A) — "let `C` be a `(n, q^k, d)` code.  If the
minimum-distance graph `G(C)` has `Q` number of connected components, then `C`
cannot be a `(f : d, d_f)`-FCC for any `f : F_q^k → Im(f)` with
`|Im(f)| ≥ Q + 1` and `d_f > d`."  As in `#theorem 8#`, the encoding is required
to have all its codewords in `C`. -/
theorem not_isFCCData_of_components {k r d df Q : ℕ} (C : Finset (Word F (k + r)))
    (hmin : minDist C = d) (hQ : componentCount (minDistGraph C) = Q) (f : Word F k → α)
    (h2 : Q + 1 ≤ (Finset.univ.image f).card) (hdf : d < df) :
    ¬∃ enc : Word F k → Word F (k + r), IsFCCData f enc d df ∧ ∀ u, enc u ∈ C := by
  sorry

/-- `#theorem 10#` (§V-B) — "the minimum-distance graph of a perfect `t`-error
correcting code is connected". -/
theorem isConnected_minDistGraph_of_perfect {F : Type*} [Zero F] [Fintype F] [DecidableEq F]
    {n t : ℕ} (C : Finset (Word F n)) (h : IsPerfect C t) :
    (minDistGraph C).Preconnected := by
  sorry

/-- `#lemma 2#` (§V-B) — "let `C` be an MDS code with parameters `(n, M, d)_q`,
and let `u, v ∈ C`.  Then there exists `u' ∈ C` such that `d(u,u') = d` (i.e.
`u'` is a neighbour of `u` in `G(C)`) and `d(u',v) ≤ d(u,v) − 1`". -/
theorem exists_mds_neighbor {n d : ℕ} (C : Finset (Word F n)) (h : IsMDS C d)
    {u v : Word F n} (hu : u ∈ C) (hv : v ∈ C) (huv : u ≠ v) :
    ∃ u' ∈ C, u' ≠ u ∧ hammingDist u u' = d ∧ hammingDist u' v ≤ hammingDist u v - 1 := by
  sorry

/-- `#theorem 11#` (§V-B) — "the minimum-distance graph of any MDS code is
connected". -/
theorem isConnected_minDistGraph_of_mds {n d : ℕ} (C : Finset (Word F n))
    (h : IsMDS C d) : (minDistGraph C).Preconnected := by
  sorry

/-- `#corollary 7#` (§V-B) — "let `f : F_q^k → Im(f)` be a function.  Then for an
`(f : d_d, d_f)`-FCC with `d_f > d_d` we have `r_f(k : d_d, d_f) ≥ n − k + 1`,
where `n` is the integer satisfying
`q^{n−k} = Σ_{i≤⌊(d_d−1)/2⌋} C(n,i)(q−1)^i`". -/
theorem perfect_optimalRedundancyData_ge {k n dd df : ℕ} (f : Word F k → α)
    (hperf : Fintype.card F ^ (n - k) =
      ∑ i ∈ Finset.range (dd / 2 + 1), n.choose i * (Fintype.card F - 1) ^ i)
    (hlt : dd < df) :
    n - k + 1 ≤ optimalRedundancyData f dd df := by
  sorry

/-- `#corollary 8#` (§V-B) — "let `f : F_q^k → Im(f)` be a function.  Assume
there exists an MDS `(n, q^k, d)_q` code, i.e. `n = k + d − 1`.  Then for an
`(f : d, d_f)`-FCC with `d_f > d` we have `r_f(k : d, d_f) ≥ n − k + 1 = d`,
equivalently any such FCC must have length `≥ k + d`". -/
theorem mds_optimalRedundancyData_ge {k n d df : ℕ} (f : Word F k → α)
    (hmds : n = k + d - 1) (hlt : d < df) :
    d ≤ optimalRedundancyData f d df := by
  sorry

/-! ### Example 9 (`#example 9#`) — the minimum-distance graph of a 4-word code -/

/-- `#example 9#` (§V-A) — the code `C = {0000, 0011, 1100, 1111}`. -/
def ex9C : Finset (Word F₂ 4) :=
  {![false, false, false, false], ![false, false, true, true], ![true, true, false, false],
    ![true, true, true, true]}

/-- `#example 9#` (§V-A) — `d_min(C) = 2`, and `G(C)` is a 4-cycle: each of the
four codewords has exactly two codewords at the minimum distance 2, so the
distance-2 pairs are the four edges of a cycle. -/
theorem ex9_min_dist_and_cycle :
    (∀ x ∈ ex9C, ∀ y ∈ ex9C, x ≠ y → 2 ≤ hammingDist x y) ∧
      (∃ x ∈ ex9C, ∃ y ∈ ex9C, x ≠ y ∧ hammingDist x y = 2) ∧
      ∀ x ∈ ex9C, (ex9C.filter fun y => y ≠ x ∧ hammingDist x y = 2).card = 2 := by
  decide

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

section SectionVIStatements

variable {F : Type*} [Zero F] [Fintype F] [DecidableEq F] {α : Type*} [DecidableEq α]

/-! ### §VI results — FCCs for specific functions

Statements only, in the paper's order (proofs are phases 3.8–3.9).  `#lemma 4#`
is external ([14], the colouring of a locally bounded function), so it enters
`#theorem 12#` as an explicit hypothesis `hcol`.  Two weakenings are recorded in
the docstrings: the `[n,k,d_d]` codes are used only through their minimum
distance, and the paper's `n` is our `k + r`. -/

/-- `#lemma 3#` (§VI-A) — "for any `(d_f−1)`-locally binary function `f`, and a
systematic `[n, k, d_d]` linear error-correcting code `C`, we have (from our
construction in Subsection III-A) `r_f(k : d_d, d_f) ≤ n − k + d_f − d_d`". -/
theorem locallyBinary_redundancy_le {k r dd df : ℕ} (f : Word F k → α)
    (hf : IsLocallyBinary f (df - 1)) (C : Word F k → Word F (k + r))
    (hC : ∀ v w : Word F k, v ≠ w → dd ≤ hammingDist (C v) (C w)) :
    optimalRedundancyData f dd df ≤ r + (df - dd) := by
  sorry

/-- `#corollary 9#` (§VI-A) — "if there exists a perfect linear
`(n, q^k, d_d = 2t_d+1)`-code, ... then for any `(d_f−1)`-locally binary
function `f`, `r_f(k : d_d, d_f) ≤ n − k + d_f − d_d`". -/
theorem locallyBinary_perfect_redundancy_le {k n dd df t : ℕ} (f : Word F k → α)
    (hf : IsLocallyBinary f (df - 1)) (C : Finset (Word F n)) (hperf : IsPerfect C t)
    (hdd : dd = 2 * t + 1) (hk : C.card = Fintype.card F ^ k) :
    optimalRedundancyData f dd df ≤ n - k + (df - dd) := by
  sorry

/-- `#corollary 10#` (§VI-A) — "let `f` be a `(d_f−1)`-locally binary function.
Then the construction described in the proof of `#lemma 3#` gives an optimal
`(f : d_d, d_f)`-FCC for `d_f = d_d + 1` if there exists a perfect
`(n, q^k, d_d)` code". -/
theorem locallyBinary_perfect_optimal {k n dd t : ℕ} (f : Word F k → α)
    (hf : IsLocallyBinary f dd) (C : Finset (Word F n)) (hperf : IsPerfect C t)
    (hdd : dd = 2 * t + 1) (hk : C.card = Fintype.card F ^ k) :
    optimalRedundancyData f dd (dd + 1) = n - k + 1 := by
  sorry

/-- `#corollary 11#` (§VI-A) — "if there exists an MDS `(n, q^k, d_d = n−k+1)` code,
then for any `(d_f−1)`-locally binary function `f`,
`r_f(k : d_d, d_f) ≤ n − k + d_f − d_d = d_f − 1`". -/
theorem locallyBinary_mds_redundancy_le {k n dd df : ℕ} (f : Word F k → α)
    (hf : IsLocallyBinary f (df - 1)) (C : Finset (Word F n)) (hC : IsMDS C dd)
    (hk : C.card = Fintype.card F ^ k) (hn : n = k + dd - 1) :
    optimalRedundancyData f dd df ≤ df - 1 := by
  sorry

/-- `#corollary 12#` (§VI-A) — "let `f` be a `(d_f−1)`-locally binary function.
Then the construction described in the proof of `#lemma 3#` gives an optimal
`(f : d_d, d_f)`-FCC for `d_f = d_d + 1`, if there exists an `(n, q^k, d_d)` MDS
code". -/
theorem locallyBinary_mds_optimal {k n dd : ℕ} (f : Word F k → α)
    (hf : IsLocallyBinary f dd) (C : Finset (Word F n)) (hC : IsMDS C dd)
    (hk : C.card = Fintype.card F ^ k) (hn : n = k + dd - 1) :
    optimalRedundancyData f dd (dd + 1) = dd := by
  sorry

/-- `#lemma 5#` (§VI-B, quoted from [14]) — "let `N(λ, 2t)` be the minimum length
of a binary error-correcting code with `λ` codewords and minimum distance `2t`.
Then `N(4, 2t) = 3t`". -/
theorem Nconst_four_two (t : ℕ) : Nconst (F := F) 4 (2 * t) = 3 * t := by
  sorry

/-- `#theorem 12#` (§VI-B) — "for any `(2t_f, λ)`-bounded function `f` satisfying
the contiguous block condition given in `#lemma 4#`, and a systematic
`[n, k, 2t_d+1]` linear error-correcting code `C`, we have
`r_f(k, t_d, t_f) ≤ n − k + N(λ, 2(t_f − t_d))`".  The colouring whose existence
`#lemma 4#` provides is the hypothesis `hcol`. -/
theorem locallyBounded_redundancy_le {k r td tf lam : ℕ} (f : Word F k → α)
    (hf : IsLocallyBounded f (2 * tf) lam) (C : Word F k → Word F (k + r))
    (col : Word F k → Fin lam)
    (hcol : ∀ u v : Word F k, hammingDist u v ≤ 2 * tf → f u ≠ f v → col u ≠ col v)
    (hC : ∀ v w : Word F k, v ≠ w → 2 * td + 1 ≤ hammingDist (C v) (C w)) :
    optimalRedundancyData f (2 * td + 1) (2 * tf + 1) ≤
      r + Nconst (F := F) lam (2 * (tf - td)) := by
  sorry

/-- `#lemma 6#` (§VI-C) — "for the Hamming weight function `f : F_q^k → Im(f)`,
and a systematic `[n, k, 2t_d+1]` linear error-correcting code `C`, we have
`r_f(k, t_d, t_f) ≤ n − k + N(2t_f+1, 2(t_f − t_d))`". -/
theorem hammingWeight_redundancy_le {k r td tf : ℕ} (C : Word F k → Word F (k + r))
    (hC : ∀ v w : Word F k, v ≠ w → 2 * td + 1 ≤ hammingDist (C v) (C w)) :
    optimalRedundancyData (fun u : Word F k => wt u) (2 * td + 1) (2 * tf + 1) ≤
      r + Nconst (F := F) (2 * tf + 1) (2 * (tf - td)) := by
  sorry

end SectionVIStatements

section CorollariesFiveSix

variable {F : Type*} [Zero F] [Fintype F] [DecidableEq F] {α : Type*} [DecidableEq α]

/-- `#corollary 5#` (§IV) — "for any function `f : F₂^k → Im(f)`,
`r_f(k,t_d,t_f) ≤ N(D_{C,f}(t_f : u₁,…,u_{q^k})) + t_d log k + t_d(1 − (t_d/k) log e)`,
where `C` is an `[n, k, 2t_d+1]` binary error-correcting code, and
`n ≤ k + t_d⌈log n⌉`".  The `t_d log k` redundancy bound on such a binary code is
the external result of [1, Appendix] (`Notation.md` §6), so it enters as the
hypothesis `hbound : r ≤ b`; the corollary's own step is the upper bound on
`r_f`. -/
theorem binary_optimalRedundancyData_le {k r td tf b : ℕ} (f : Word (ZMod 2) k → α)
    (C : Word (ZMod 2) k → Word (ZMod 2) (k + r))
    (hC : ∀ v w : Word (ZMod 2) k, v ≠ w → 2 * td + 1 ≤ hammingDist (C v) (C w))
    (hbound : r ≤ b) :
    optimalRedundancyData f (2 * td + 1) (2 * tf + 1) ≤
      N (F := ZMod 2) (ι := Word (ZMod 2) k) (cdrm f C tf fun v => v) + b := by
  sorry

/-- `#corollary 6#` (§IV) — "let `C` be an `[n, k, 2t_d+1]` code.  Then for
`t_f − t_d ≥ 5` and `M ≤ 4(t_f − t_d)²`,
`N(D_{C,f}(t_f : u₁,…,u_M)) ≤ N(M, 2(t_f − t_d)) ≤ 4(t_f − t_d) − 2)/(1 − …)`",
and for `M = 4`, `N(4, 2(t_f − t_d)) = 3(t_f − t_d)`.  The first inequality is
`#theorem 6#`; the numerical bound on `N(M, 2(t_f − t_d))` is the external
`#lemma 1#` ([10, Lem. 2], whose printed constants are ambiguous —
`Notation.md` §5.2), so it enters as `hbound` and the corollary's step is the
transitivity. -/
theorem N_cdrm_le_bounded {k r m td tf b : ℕ} (f : Word F k → α)
    (C : Word F k → Word F (k + r)) (u : Fin m → Word F k)
    (hC : ∀ v w : Word F k, v ≠ w → 2 * td + 1 ≤ hammingDist (C v) (C w))
    (hbound : Nconst (F := F) m (2 * (tf - td)) ≤ b) :
    N (F := F) (ι := Fin m) (cdrm f C tf u) ≤ b := by
  sorry

end CorollariesFiveSix

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

section SectionVIIStatements

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {α : Type*} [DecidableEq α]

/-! ### §VII results — linear `(f : d_d, d_f)`-FCCs

Statements only, in the paper's order (proofs are phase 3.10).  `#theorem 13#`
needs the concatenation `(C(u), D(f(u)))` as a single word, i.e. an
append/`Matrix`-free plumbing step, and is the next slice. -/

/-- `#lemma 7#` (§VII-A) — "if `f : F_q^k → Im(f)` is a linear function and `C`
is a linear `(f : d_d, d_f)`-FCC of length `n` in standard form, then the subcode
`D_f = {c = (u,p) ∈ C | u ∈ Ker(f)}` forms a subspace of `C`.  Furthermore, the
dimension of `D_f` is the same as the dimension of `Ker(f)`."  (That `D_f` is a
subspace is definitional in Lean — `kernelSubcode` is a kernel — so what is left
to prove is the dimension statement.) -/
theorem kernelSubcode_finrank {k r : ℕ} (f : Word F k →ₗ[F] Word F r)
    (C : Submodule F (Word F (k + r))) :
    Module.finrank F (kernelSubcode f C) = Module.finrank F (LinearMap.ker f) := by
  sorry

/-- `#lemma 8#` (§VII-A) — "let `C` be a subspace of `F_q^n` and `D` a subspace of
`C`.  Then for any `v_i, v_j ∈ C`,
`min{wt(c₁ − c₂) | c₁ ∈ v_i + D, c₂ ∈ v_j + D} = min_{d ∈ D} wt(v_i − v_j + d)`".
The right-hand side is our `cosetDist`, so this lemma is the bridge between
`#definition 17#`'s printed double minimum and the definition we compute with. -/
theorem cosetDist_eq (D : Submodule F (Word F n)) (x y : Word F n) :
    sInf {w : ℕ | ∃ c₁ : Word F n, c₁ - x ∈ D ∧ ∃ c₂ : Word F n, c₂ - y ∈ D ∧
        w = wt (c₁ - c₂)} = cosetDist D (x - y) := by
  sorry

/-- `#lemma 9#` (§VII-A) — "let `C` be a linear `(f : d_d, d_f)`-FCC of a linear
function `f`.  Then `wt(v) ≥ d_f` for all `v ∈ C \ D_f`." -/
theorem wt_ge_of_not_mem_kernel {k r dd df : ℕ} (f : Word F k →ₗ[F] Word F r)
    (C : Submodule F (Word F (k + r))) (hC : IsLinearFCCKernel f C dd df) :
    ∀ v : C, v ∉ kernelSubcode f C → df ≤ wt (v : Word F (k + r)) := by
  sorry

/-- `(internal, §VII — used by `#lemma 10#`, `#theorem 13#`)` — the concatenation
of a word of length `m` with one of length `n`, i.e. the paper's pair
`(C(u), D(f(u)))` written as a single word of length `m + n`. -/
def catWord {m n : ℕ} (x : Word F m) (y : Word F n) : Word F (m + n) :=
  Fin.append x y

/-- `#lemma 10#` (§VII) — "let `f : F_q^k → F_q^ℓ` be a linear function.  Further,
let `C ⊆ F_q^n` and `D ⊆ F_q^{r'}` be linear codes of dimensions `k` and `ℓ`,
respectively ... Then the concatenated code
`C_cat = {(C(u), D(f(u))) : u ∈ F_q^k}` is a linear code in `F_q^{n+r'}` of
dimension `k`."  Linearity is stated as `IsLinearMap` for the map
`u ↦ (C(u), D(f(u)))` (with `catWord` spelling out the pair); the dimension claim
is `#theorem 13#`. -/
theorem image_linear_concat {k ℓ r r' : ℕ} (f : Word F k →ₗ[F] Word F ℓ)
    (Cf : Word F k →ₗ[F] Word F r) (Df : Word F ℓ →ₗ[F] Word F r') :
    IsLinearMap F (fun u : Word F k => catWord (Cf u) (Df (f u))) := by
  sorry

/-- `#theorem 13#` (§VII-B) — "the image `C_cat = {(C(u), D(f(u))) : u ∈ F_q^k}`
`⊆ F_q^{n+r'}` is a linear `(f : d_d, d_f)`-FCC of dimension `k` and total
redundancy `r_s = (n − k) + r'`".  Linearity is `#lemma 10#`; the two distance
guarantees are stated here, with `catWord` spelling out the pair and the
`d_f − d_d` slack of the second code taken from the construction of §VII-B. -/
theorem isLinearFCC_concat {k ℓ r r' dd df : ℕ} (f : Word F k →ₗ[F] Word F ℓ)
    (C : Word F k → Word F r) (D : Word F ℓ → Word F r')
    (hC : ∀ u v : Word F k, u ≠ v → dd ≤ hammingDist (C u) (C v))
    (hD : ∀ a b : Word F ℓ, a ≠ b → df - dd ≤ hammingDist (D a) (D b))
    (hadd : dd ≤ df) :
    (∀ u v : Word F k, u ≠ v →
        dd ≤ hammingDist (catWord (C u) (D (f u))) (catWord (C v) (D (f v)))) ∧
      ∀ u v : Word F k, f u ≠ f v →
        df ≤ hammingDist (catWord (C u) (D (f u))) (catWord (C v) (D (f v))) := by
  sorry

end SectionVIIStatements

/-! ### Example 12 (`#example 12#`) — a linear FCC for a non-linear function -/

/-- `#example 12#` (§VII) — the non-linear function `f(x₁,x₂,x₃) = x₁x₂` on
`F₂³` (as `Bool`: `false = 0`, `true = 1`). -/
def ex12F (u : Word F₂ 3) : Bool := u 0 && u 1

/-- `#example 12#` (§VII) — the encoder `u ↦ uG` of the binary linear code
generated by the matrix printed in the example. -/
def ex12Enc (u : Word F₂ 3) : Word F₂ 9 :=
  ![u 1, u 1, u 0, u 0, u 0 != u 1, u 0 != u 1, u 2, u 1 != u 2, u 0 != u 2]

/-- `#example 12#` (§VII) — the codewords of the table in the paper. -/
theorem ex12_codewords :
    ex12Enc ![false, false, false] = ![false, false, false, false, false, false, false, false, false] ∧
      ex12Enc ![false, false, true] = ![false, false, false, false, false, false, true, true, true] ∧
      ex12Enc ![false, true, false] =
        ![true, true, false, false, true, true, false, true, false] ∧
      ex12Enc ![true, true, true] = ![true, true, true, true, false, false, true, false, false] := by
  decide

/-- `#example 12#` (§VII) — "the minimum distance of `C` is `d_d = 3`; whenever
`f(u) ≠ f(v)`, the corresponding codewords satisfy `d(c_u, c_v) ≥ 5`", i.e. `C`
is a linear `(f : 3, 5)`-FCC. -/
theorem ex12_is_fcc :
    (∀ u : Word F₂ 3, u ≠ 0 → 3 ≤ wt (ex12Enc u)) ∧
      ∀ u v : Word F₂ 3, ex12F u ≠ ex12F v → 5 ≤ hammingDist (ex12Enc u) (ex12Enc v) := by
  decide

/-! ### Example 13 (`#example 13#`) — a linear `(f : 2, 3)`-FCC -/

/-- `#example 13#` (§VII) — a linear function `f` on `F₂²` with
`ker(f) = {00, 11}`, i.e. `f(u) = u₁ ⊕ u₂`. -/
def ex13F (u : Word F₂ 2) : Bool := u 0 != u 1

/-- `#example 13#` (§VII) — the code `C = {0000, 0111, 1100, 1011}`. -/
def ex13C : Fin 4 → Word F₂ 4 :=
  ![![false, false, false, false], ![false, true, true, true], ![true, true, false, false],
    ![true, false, true, true]]

/-- `#example 13#` (§VII) — the messages of those four codewords (`00, 01, 11, 10`). -/
def ex13Msg : Fin 4 → Word F₂ 2 :=
  ![![false, false], ![false, true], ![true, true], ![true, false]]

/-- `#example 13#` (§VII) — "the following linear code `C` has the minimum
distance `d_d = 2` and the minimum coset distance `d_f = 3`", i.e. it is an
`(f : 2, 3)`-FCC. -/
theorem ex13_is_linear_fcc :
    (∀ i j : Fin 4, i ≠ j → 2 ≤ hammingDist (ex13C i) (ex13C j)) ∧
      ∀ i j : Fin 4, ex13F (ex13Msg i) ≠ ex13F (ex13Msg j) →
        3 ≤ hammingDist (ex13C i) (ex13C j) := by
  decide

/-! ### Example 14 (`#example 14#`) — the `[10,3,4]` linear FCC of the §VII-B
construction -/

/-- `#example 14#` (§VII-B) — the linear function `f(u₁,u₂,u₃) = (u₁⊕u₂, u₃)`. -/
def ex14F (u : Word F₂ 3) : Bool × Bool := (u 0 != u 1, u 2)

/-- `#example 14#` (§VII-B) — the eight codewords of the final linear
`(f : 4, 6)`-FCC (message `⊕` `C`-parity `⊕` `D`-parity), in the order of the
paper's table `000, 110, 100, 010, 001, 111, 101, 011`. -/
def ex14Code : Fin 8 → Word F₂ 10 :=
  ![![false, false, false, false, false, false, false, false, false, false],
    ![true, true, false, false, true, true, false, false, false, false],
    ![true, false, false, true, true, false, true, true, false, true],
    ![false, true, false, true, false, true, true, true, false, true],
    ![false, false, true, false, true, true, true, false, true, true],
    ![true, true, true, false, false, false, true, false, true, true],
    ![true, false, true, true, false, true, false, true, true, false],
    ![false, true, true, true, true, false, false, true, true, false]]

/-- `#example 14#` (§VII-B) — the construction gives an `(f : 4, 6)`-FCC: the
minimum distance is at least 4 and codewords whose messages have different
`f`-values are at distance at least 6.  (The messages are the eight vectors in
the paper's order.) -/
def ex14Msg : Fin 8 → Word F₂ 3 :=
  ![![false, false, false], ![true, true, false], ![true, false, false],
    ![false, true, false], ![false, false, true], ![true, true, true],
    ![true, false, true], ![false, true, true]]

/-- `#example 14#` (§VII-B) — the construction gives an `(f : 4, 6)`-FCC: the
minimum distance is at least 4, and codewords whose messages have different
`f`-values are at distance at least 6. -/
theorem ex14_is_fcc :
    (∀ i j : Fin 8, i ≠ j → 4 ≤ hammingDist (ex14Code i) (ex14Code j)) ∧
      ∀ i j : Fin 8, ex14F (ex14Msg i) ≠ ex14F (ex14Msg j) →
        6 ≤ hammingDist (ex14Code i) (ex14Code j) := by
  decide

section SectionVIIIStatements

variable {F : Type*} [Zero F] [Fintype F] [DecidableEq F] {α : Type*} [DecidableEq α]

/-! ### §VIII results — classical bounds extended to FCCs

Statements only, in the paper's order (proofs are phases 3.11–3.12).  The
inequalities are stated over `ℚ`, so that the paper's fractions
(`4/M²`, `2q/(M²(q−1) − a(q−a))`, `1/(q^{k−1}(q−1))`) appear literally instead
of being truncated by `ℕ`-division. -/

/-- `#lemma 11#` (§VIII, quoted from [1]) — "for any distance matrix
`D ∈ ℕ^{M×M}`, `N(D) ≥ 4/M² · Σ_{i<j} [D]_{i,j}` if `M` is even". -/
theorem plotkin_bound_binary {M : ℕ} (D : Fin M → Fin M → ℕ) (hM : Even M) :
    (4 : ℚ) / (M : ℚ) ^ 2 *
        (∑ p ∈ Finset.univ.filter (fun p : Fin M × Fin M => p.1 < p.2), (D p.1 p.2 : ℚ))
      ≤ (N (F := F) (ι := Fin M) D : ℚ) := by
  sorry

/-- `#lemma 11#` (§VIII, quoted from [1]) — "…, and
`N(D) ≥ 4/(M²−1) · Σ_{i<j} [D]_{i,j}` if `M` is odd". -/
theorem plotkin_bound_binary_odd {M : ℕ} (D : Fin M → Fin M → ℕ) (hM : Odd M) :
    (4 : ℚ) / ((M : ℚ) ^ 2 - 1) *
        (∑ p ∈ Finset.univ.filter (fun p : Fin M × Fin M => p.1 < p.2), (D p.1 p.2 : ℚ))
      ≤ (N (F := F) (ι := Fin M) D : ℚ) := by
  sorry

/-- `#lemma 13#` (§VIII) — "for any distance matrix `D ∈ ℕ^{M×M}` and for
irregular distance codes over `F_q`, we have
`N(D) ≥ 2q/(M²(q−1) − a(q−a)) · Σ_{1≤i<j≤M} [D]_{i,j}`, where `a = M mod q`".
Here `q = Fintype.card F` and `a` is `M % Fintype.card F`. -/
theorem plotkin_bound {M : ℕ} (D : Fin M → Fin M → ℕ) :
    (2 * (Fintype.card F : ℚ)) /
        ((M : ℚ) ^ 2 * ((Fintype.card F : ℚ) - 1) -
          ((M % Fintype.card F : ℕ) : ℚ) * ((Fintype.card F : ℚ) - ((M % Fintype.card F : ℕ) : ℚ))) *
        (∑ p ∈ Finset.univ.filter (fun p : Fin M × Fin M => p.1 < p.2), (D p.1 p.2 : ℚ))
      ≤ (N (F := F) (ι := Fin M) D : ℚ) := by
  sorry

/-- `#theorem 14#` (§VIII-A) — "for an `(f : d_d, d_f)`-FCC over `F_q`, where
`f : F_q^k → Im(f)`,
`r_f(k : d_d, d_f) ≥ ((L−1)d_d + (q^k − L)d_f)/(q^{k−1}(q−1)) − k`, where
`L = max_{α ∈ Im(f)} |f⁻¹(α)|` and `d_f > d_d`".  `L` is supplied through the
two hypotheses `hL`/`hL'` (it is a maximum of the preimage sizes). -/
theorem plotkin_bound_fcc {k : ℕ} (f : Word F k → α) (dd df : ℕ) (hlt : dd < df) :
    (((maxPreimageCard f - 1 : ℕ) : ℚ) * dd +
        ((Fintype.card F : ℚ) ^ k - maxPreimageCard f) * df) /
        ((Fintype.card F : ℚ) ^ (k - 1) * ((Fintype.card F : ℚ) - 1)) - k
      ≤ (optimalRedundancyData f dd df : ℚ) := by
  sorry

/-- `#corollary 13#` (§VIII-B) — "since `|∪_{j≤ℓ} B(v_j,t)| ≥ |B(v,t)|` for any
`v ∈ F_q^n` and `|B(v,t)| = Σ_{i≤t} C(n,i)(q−1)^i`, we have
`E ≤ q^n/Σ_{i≤t} C(n,i)(q−1)^i`".  Written without division: an `(f,t)`-FCC of
length `n` forces `|Im(f)| · |B(0,t)| ≤ q^n`. -/
theorem hamming_bound_fcc_sphere {k r : ℕ} (f : Word F k → α) (t : ℕ)
    (C : Word F k → Word F (k + r)) (hC : IsFCC f C t) :
    (Finset.univ.image f).card * (ball (0 : Word F (k + r)) t).card ≤
      Fintype.card F ^ (k + r) := by
  sorry

/-- `#theorem 15#` (§VIII-B) — "consider a function `f : F_q^k → Im(f)` with
`Im(f) = {f₁,…,f_E}`.  Let `ℓ = min_{i∈[E]} |f⁻¹(fᵢ)|`, then there exists an
`(f,t)`-FCC with length `n` if `E ≤ q^n/|∪_{j≤ℓ} B(v_j,t)|`, where `v₁,…,v_ℓ`
are any distinct vectors in `F_q^n` for which `|∪_{j≤ℓ} B(v_j,t)|` is minimum."

As `Notation.md` §5 records, the printed "there exists … if" runs opposite to the
proof and to every later use (Examples 16–17, `#corollary 13#`), so we state the
necessity direction and without division: an `(f,t)`-FCC of length `n` forces
`|Im(f)| · |∪_{j<ℓ} B(v_j,t)| ≤ q^n` for a minimising family.  The minimum is the
`(internal)` quantity `minUnionCard` (phase 1 has no argmin helper). -/
theorem hamming_bound_fcc {k r : ℕ} (f : Word F k → α) (t : ℕ)
    (C : Word F k → Word F (k + r)) (hC : IsFCC f C t) :
    (Finset.univ.image f).card * minUnionCard (F := F) (minPreimageCard f) (k + r) t ≤
      Fintype.card F ^ (k + r) := by
  sorry

/-- `#theorem 16#` (§VIII-C) — the same statement for an `(f : d_d, d_f)`-FCC:
"let `ℓ = min_{i∈[E]} |f⁻¹(fᵢ)|` and `v₁, v₂, …, v_ℓ` be distinct vectors in
`F_q^n` with `d(vᵢ,vⱼ) ≥ d_d`, for which `|∪_{j≤ℓ} B(v_j,t_f)|` is minimum.
Then there exists an `(f : d_d, d_f)`-FCC with length `n` if
`E ≤ q^n/|∪_{j≤ℓ} B(v_j,t_f)|`" — stated, for the same reason as `#theorem 15#`,
in the necessity direction and without division; the minimising family here is
`minUnionCardDist`, which carries the pairwise `d(vᵢ,vⱼ) ≥ d_d` condition. -/
theorem hamming_bound_fcc_data {k r : ℕ} (f : Word F k → α) (dd df tf : ℕ)
    (C : Word F k → Word F (k + r)) (hC : IsFCCData f C dd df) :
    (Finset.univ.image f).card *
        minUnionCardDist (F := F) (minPreimageCard f) dd (k + r) tf ≤
      Fintype.card F ^ (k + r) := by
  sorry

/-- `#corollary 14#` (§VIII-C) — "consider a function `f : F_q^k → Im(f)` with
`Im(f) = {f₁,…,f_E}`, and `ℓ = min_{i∈[E]} |f⁻¹(fᵢ)|`.  Then there exists an
`(f : d_d, d_f)`-FCC with length `n` if
`E ≤ q^n/(ℓ · Σ_{i≤t_d} C(n,i)(q−1)^i)`" — again in the necessity direction and
without division: `E · ℓ · |B(0,t_d)| ≤ q^n`. -/
theorem hamming_bound_fcc_data_sphere {k r : ℕ} (f : Word F k → α) (dd df td : ℕ)
    (C : Word F k → Word F (k + r)) (hC : IsFCCData f C dd df) :
    (Finset.univ.image f).card * minPreimageCard f *
        (ball (0 : Word F (k + r)) td).card ≤ Fintype.card F ^ (k + r) := by
  sorry

end SectionVIIIStatements

/-! ## §VIII — Extension of bounds from error-correcting codes to FCCs

TODO: `#lemma 11#`, `#lemma 12#` (external), `#lemma 13#`, `#theorem 14#`,
`#theorem 15#`, `#corollary 13#`, `#theorem 16#`, `#corollary 14#`.
-/

section AppendixStatements

variable {F : Type*} [Zero F] [Fintype F] [DecidableEq F]

/-! ### Appendix results — counting the number of vectors in the union of balls

Statements only (proofs are phase 3.13).  All four are `Finset.card` identities
about the balls of §I-E; the paper's `Σ_{i=0}^{t}` is `Finset.range (t + 1)`, and
`q = Fintype.card F`. -/

/-- `#theorem 17#` (Appendix) — "consider two Hamming balls `B(u,t)` and `B(v,t)`
for `u, v ∈ F_q^n` such that `d(u,v) = 1`.  Then
`|B(u,t) ∪ B(v,t)| = 2 Σ_{i≤t} C(n,i)(q−1)^i − q Σ_{i≤t−1} C(n−1,i)(q−1)^i`". -/
theorem card_ball_union_dist_one {n t : ℕ} (u v : Word F n) (h : hammingDist u v = 1) :
    (ball u t ∪ ball v t).card =
      2 * (∑ i ∈ Finset.range (t + 1), n.choose i * (Fintype.card F - 1) ^ i) -
        Fintype.card F *
          (∑ i ∈ Finset.range t, (n - 1).choose i * (Fintype.card F - 1) ^ i) := by
  sorry

/-- `#lemma 14#` (Appendix) — over `F₂`: "consider two vectors `u₁, u₂ ∈ F₂^n` such
that `d(u₁,u₂) = 2`.  Then `|B(u₁,t) ∩ B(u₂,t)| = 2 Σ_{i≤t−1} C(n−1,i)`". -/
theorem card_ball_inter_dist_two {n t : ℕ} (u v : Word (ZMod 2) n)
    (h : hammingDist u v = 2) :
    (ball u t ∩ ball v t).card = 2 * (∑ i ∈ Finset.range t, (n - 1).choose i) := by
  sorry

/-- `#theorem 18#` (Appendix) — "consider three distinct vectors `u₁, u₂, u₃ ∈ F₂^n`
with pairwise distances `1, 1, 2`.  Then
`|B(u₁,t) ∪ B(u₂,t) ∪ B(u₃,t)| = 3 Σ_{i≤t} C(n,i) − 6 Σ_{i≤t−1} C(n−1,i)
+ C(n−2,t−1) + 4 Σ_{i≤t−2} C(n−2,i)`". -/
theorem card_ball_union_three {n t : ℕ} (u₁ u₂ u₃ : Word (ZMod 2) n)
    (h12 : hammingDist u₁ u₂ = 1) (h13 : hammingDist u₁ u₃ = 1)
    (h23 : hammingDist u₂ u₃ = 2) :
    (ball u₁ t ∪ ball u₂ t ∪ ball u₃ t).card =
      3 * (∑ i ∈ Finset.range (t + 1), n.choose i) -
        6 * (∑ i ∈ Finset.range t, (n - 1).choose i) + (n - 2).choose (t - 1) +
        4 * (∑ i ∈ Finset.range (t - 1), (n - 2).choose i) := by
  sorry

/-- `#theorem 19#` (Appendix) — over `F₂`: "consider two vectors `u₁, u₂ ∈ F₂^n`
such that `d(u₁,u₂) = 3`.  Then for `t ≥ 2`,
`|B(u₁,t) ∪ B(u₂,t)| = 2 Σ_{i≤t} C(n,i) − 8 Σ_{i≤t−3} C(n−3,i) − 6 C(n−3,t−2)`". -/
theorem card_ball_union_dist_three {n t : ℕ} (u v : Word (ZMod 2) n)
    (h : hammingDist u v = 3) (ht : 2 ≤ t) :
    (ball u t ∪ ball v t).card =
      2 * (∑ i ∈ Finset.range (t + 1), n.choose i) -
        8 * (∑ i ∈ Finset.range (t - 2), (n - 3).choose i) - 6 * ((n - 3).choose (t - 2)) := by
  sorry

end AppendixStatements

/-! ## §IX — Conclusion

Not formalized: §IX contains no definitions or theorems, only a summary and
outlook.
-/

/-! ## Appendix — Counting the number of vectors in the union of balls

TODO: `#theorem 17#`, `#lemma 14#`, `#theorem 18#`, `#theorem 19#`.
-/

end FCC
