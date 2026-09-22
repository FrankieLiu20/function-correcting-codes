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
and `0` on it.  We define it on all of `α` (so that it is a total function); it is
meant to be read on the image of `f`, the paper's `f₁, …, f_E`, i.e. on
`Set.range f` — that is the index set every statement using it must take `N` over
(`#theorem 1#`).  Rows for values outside `Im(f)` are junk: their `fDist` is `0`
by the empty-preimage convention above, so their entries are `2t+1` — which is
precisely why the whole-`α` index set is wrong (`ISSUES.md` §12). -/
noncomputable def fdm {k : ℕ} (f : Word F k → α) (t : ℕ) : α → α → ℕ :=
  fun a b => if a = b then 0 else max (2 * t + 1 - fDist f a b) 0

/-- `(internal, §II — the splitting identity behind `#corollary 1#`, `#theorem 1#`,
`#theorem 2#` and `#theorem 5#`)` — for a *systematic* encoding the Hamming distance
of two codewords splits into the message part and the redundancy part:
`d(C u, C v) = d(u,v) + d(p_u, p_v)`, where `p_u` is `redPart (C u)`.  Every
"extract a `D`-code from an FCC" step in this file is this identity plus one of the
FCC's distance conditions.

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

omit [Fintype F] in
/-- `(internal, §II — the `N`-API)` — `N(D)` is at most the length of any `D`-code. -/
theorem N_le_of_isDCode {ι : Type*} {D : ι → ι → ℕ} {r : ℕ}
    (h : IsDCode (F := F) D r) : N (F := F) D ≤ r :=
  Nat.sInf_le h

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
/-- `(internal, §II — non-vacuity of the `(f,t)`-FCC set)` — for any `f` and `t`
there is an `(f,t)`-FCC of some redundancy: write the message down `2t+1` times
(`C u = (u, u, …, u)`), so that any two distinct messages are at distance
`d(u,v) + (2t+1)·d(u,v) ≥ 2t+1`.  This is the §II analogue of
`exists_isFCCData` (§III) and is what makes the `sInf`-based `optimalRedundancy`
attained. -/
theorem exists_isFCC {k : ℕ} (f : Word F k → α) (t : ℕ) :
    ∃ r : ℕ, ∃ C : Word F k → Word F (k + r), IsFCC f C t := by
  refine ⟨k * (2 * t + 1), fun u => Fin.append u (repWord (2 * t + 1) u), ?_, ?_⟩
  · intro u i
    simp [Fin.append_left]
  · intro u v huv
    have huv' : u ≠ v := fun hh => huv (by rw [hh])
    rw [hammingDist_append, hammingDist_repWord]
    have hd1 : 0 < hammingDist u v := hammingDist_pos.mpr huv'
    have hmul : 2 * t + 1 ≤ (2 * t + 1) * hammingDist u v := Nat.le_mul_of_pos_right _ hd1
    omega

/-- `(internal, §II — the extraction step of `#corollary 1#`)` — an `(f,t)`-FCC of
redundancy `r` is a `D`-code of length `r` for the DRM of *any* family
`u₁, …, u_m` of messages: take `pᵢ := redPart (C uᵢ)`.  For `i ≠ j` with
`f(uᵢ) ≠ f(uⱼ)` the FCC condition gives `d(uᵢ,uⱼ) + d(pᵢ,pⱼ) ≥ 2t+1`, i.e.
`d(pᵢ,pⱼ) ≥ max(2t+1 − d(uᵢ,uⱼ), 0)`, which is exactly the DRM entry. -/
theorem isDCode_drm_of_isFCC {k r t : ℕ} {ι : Type*} {f : Word F k → α}
    {C : Word F k → Word F (k + r)} (u : ι → Word F k) (hC : IsFCC f C t) :
    IsDCode (F := F) (drm f t u) r := by
  classical
  refine ⟨fun i => redPart (C (u i)), ?_⟩
  intro i j hij
  simp only [drm]
  by_cases hf : f (u i) = f (u j)
  · rw [ite_eq_left hf]
    exact Nat.zero_le _
  · rw [ite_eq_right hf]
    have hsplit := hammingDist_eq_msg_add_red hC.1 (u i) (u j)
    have hd := hC.2 (u i) (u j) hf
    rw [hsplit] at hd
    refine max_le ?_ (Nat.zero_le _)
    omega

omit [Fintype F] in
/-- `(internal, §II — used by `#corollary 1#` and `#theorem 3#`)` — if two messages
carry different values of `f`, then so does some pair at Hamming distance exactly
one.  This is the paper's "if `|Im(f)| ≥ 2`, then there exist `u, v` with
`f(u) ≠ f(v)` and `d(u,v) = 1`" (stated there without proof): walk from `u` to `v`
changing one coordinate at a time (the `m`-th word of the walk agrees with `v` on
the first `m` coordinates), and note that `f` starts at `f(u)` and ends at `f(v)`,
so one step of the walk must change the value of `f`. -/
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

/-! ### §II results — the `(f,t)`-FCC bounds of [1]

Proved in phase 3.2 from the internal bricks above.  `N`'s index type is explicit
in each statement: the DRM is indexed by the messages (`Fin m`, or `Fin E` for a
representative family) and the FDM by the *image* of `f` (`Set.range f`, the
paper's `f₁, …, f_E`) — `ISSUES.md` §12 explains why the FDM must not be indexed
by the whole alphabet `α`. -/

/-- `#corollary 1#` (§II, quoted from [1, Cor. 1]) — "for any function
`f : F_q^k → Im(f)` and `{u₁, u₂, …, u_m} ⊆ F_q^k`:
`r_f(k,t) ≥ N(D_f(t, u₁, u₂, …, u_m))`". -/
theorem optimalRedundancy_ge_drm {k m : ℕ} (f : Word F k → α) (t : ℕ)
    (u : Fin m → Word F k) :
    N (F := F) (ι := Fin m) (drm f t u) ≤ optimalRedundancy f t := by
  classical
  obtain ⟨r, C, hC⟩ := exists_isFCC f t
  have hne : ∃ r' : ℕ, r' ∈ {r' : ℕ | ∃ C : Word F k → Word F (k + r'), IsFCC f C t} :=
    ⟨r, C, hC⟩
  rw [optimalRedundancy, dite_eq_left hne]
  have hspec := Nat.find_spec hne
  simp only [Set.mem_ofPred_eq] at hspec
  obtain ⟨C₀, hC₀⟩ := hspec
  exact N_le_of_isDCode (isDCode_drm_of_isFCC u hC₀)

/-- `#corollary 1#` (§II, quoted from [1, Cor. 1]) — "and for `|Im(f)| ≥ 2`,
`r_f(k,t) ≥ 2t`" (here `|Im(f)| ≥ 2` is stated as: two distinct values, each
attained). -/
theorem two_mul_le_optimalRedundancy {k : ℕ} (f : Word F k → α) (t : ℕ)
    (h : ∃ a b : α, a ≠ b ∧ (∃ u : Word F k, f u = a) ∧ ∃ v : Word F k, f v = b) :
    2 * t ≤ optimalRedundancy f t := by
  classical
  obtain ⟨a, b, hab, ⟨u, hu⟩, ⟨v, hv⟩⟩ := h
  have huv : f u ≠ f v := by rw [hu, hv]; exact hab
  obtain ⟨u', v', hd1, hfne⟩ := exists_hammingDist_one_ne f huv
  let w : Fin 2 → Word F k := fun i => if i = 0 then u' else v'
  have hw0 : w 0 = u' := by simp [w]
  have hw1 : w 1 = v' := by simp [w]
  have hentry : drm f t w 0 1 = 2 * t := by
    simp only [drm]
    rw [ite_eq_right (by rw [hw0, hw1]; exact hfne), hw0, hw1, hd1,
      show 2 * t + 1 - 1 = 2 * t from by omega, max_eq_left (Nat.zero_le _)]
  have hNentry : drm f t w 0 1 ≤ N (F := F) (ι := Fin 2) (drm f t w) := by
    obtain ⟨r, C, hC⟩ := exists_isFCC f t
    have hne : {r : ℕ | IsDCode (F := F) (drm f t w) r}.Nonempty :=
      ⟨r, isDCode_drm_of_isFCC w hC⟩
    obtain ⟨p, hp⟩ := Nat.sInf_mem hne
    calc drm f t w 0 1 ≤ hammingDist (p 0) (p 1) := hp 0 1 (by decide)
      _ ≤ N (F := F) (ι := Fin 2) (drm f t w) := by
        have hle := hammingDist_le_card_fintype (x := p 0) (y := p 1)
        rw [Fintype.card_fin] at hle
        exact hle
  calc 2 * t = drm f t w 0 1 := hentry.symm
    _ ≤ N (F := F) (ι := Fin 2) (drm f t w) := hNentry
    _ ≤ optimalRedundancy f t := optimalRedundancy_ge_drm f t w

/-- `#theorem 1#` (§II, quoted from [1, Thm. 2]) — "for any function
`f : F_q^k → Im(f) = {f₁, f₂, …, f_E}`, `r_f(k,t) ≤ N(D_f(t, f₁, f₂, …, f_E))`,
where `D_f(t, f₁, …, f_E)` is a FDM" (`#definition 5#`).

The FDM is indexed by the *image* of `f` — the paper's `f₁, …, f_E` — which in Lean
is `Set.range f`.  Indexing it by the whole alphabet `α` instead is **wrong**, and
not merely unproved: `fDist f a b = 0` for values outside `Im(f)`
(`#definition 4#`'s empty-preimage convention), so the `α`-indexed matrix demands
distance `2t+1` between *every* pair of values, which no finite code can meet when
`α` is infinite; `N` would then collapse to `0` (its `sInf ∅` convention) and the
inequality would be false.  See `ISSUES.md` §12.

Proof: a `D`-code `p` for the image-indexed FDM gives the FCC
`C u := (u, p_{f(u)})`: for `f(u) ≠ f(v)` the distance is
`d(u,v) + d(p_{f(u)}, p_{f(v)}) ≥ d(u,v) + max(2t+1 − d(f(u),f(v)), 0) ≥ 2t+1`,
the first inequality from the `D`-code and the last from
`d(f(u),f(v)) ≤ d(u,v)` (`fDist_le`). -/
theorem optimalRedundancy_le_fdm {k : ℕ} (f : Word F k → α) (t : ℕ) :
    optimalRedundancy f t ≤
      N (F := F) (ι := Set.range f) (fun a b => fdm f t a.1 b.1) := by
  classical
  have hbound : ∀ a b : Set.range f, fdm f t a.1 b.1 ≤ 2 * t + 1 := by
    intro a b
    rw [fdm]
    split_ifs with h
    · omega
    · exact max_le (by omega) (Nat.zero_le _)
  have hne : {r : ℕ |
      IsDCode (F := F) (fun a b : Set.range f => fdm f t a.1 b.1) r}.Nonempty := by
    refine ⟨k * (2 * t + 1),
      ⟨fun a => repWord (2 * t + 1) (Classical.choose a.2), ?_⟩⟩
    intro a b hab
    rw [hammingDist_repWord]
    have ha : f (Classical.choose a.2) = a.1 := Classical.choose_spec a.2
    have hb : f (Classical.choose b.2) = b.1 := Classical.choose_spec b.2
    have hfne : f (Classical.choose a.2) ≠ f (Classical.choose b.2) := by
      intro hh
      exact hab (Subtype.ext (by rw [← ha, hh, hb]))
    have hdne : Classical.choose a.2 ≠ Classical.choose b.2 := fun hh => hfne (by rw [hh])
    have hd1 : 0 < hammingDist (Classical.choose a.2) (Classical.choose b.2) :=
      hammingDist_pos.mpr hdne
    exact le_trans (hbound a b) (Nat.le_mul_of_pos_right _ hd1)
  obtain ⟨p, hp⟩ := Nat.sInf_mem hne
  refine optimalRedundancy_le_of
    (C := fun v => Fin.append v (p ⟨f v, ⟨v, rfl⟩⟩)) ⟨?_, ?_⟩
  · intro v i
    simp [Fin.append_left]
  · intro u v huv
    rw [hammingDist_append]
    have hidx : (⟨f u, ⟨u, rfl⟩⟩ : Set.range f) ≠ ⟨f v, ⟨v, rfl⟩⟩ := by
      intro hh
      exact huv (Subtype.ext_iff.mp hh)
    have hentry := hp _ _ hidx
    simp only [fdm] at hentry
    rw [ite_eq_right huv] at hentry
    have hple : 2 * t + 1 - fDist f (f u) (f v) ≤
        hammingDist (p ⟨f u, ⟨u, rfl⟩⟩) (p ⟨f v, ⟨v, rfl⟩⟩) :=
      le_trans (le_max_left _ _) hentry
    have hfle : fDist f (f u) (f v) ≤ hammingDist u v := fDist_le rfl rfl
    omega

/-- `#corollary 2#` (§II, quoted from [1, Cor. 2]) — "if there exists a set of
representative information vectors `u₁, u₂, …, u_E` with
`{f(u₁), …, f(u_E)} = Im(f)` and `D_f(t, u₁, …, u_E) = D_f(t, f₁, …, f_E)`, then
`r_f(k,t) = N(D_f(t, f₁, …, f_E))`".  The two hypotheses are stated as: the `u_i`
attain the pairwise minimum distances of `#definition 4#`, and they hit every
value of `f`.  `hattain` is what identifies the DRM of the representatives with
the image-indexed FDM of `#theorem 1#` entry by entry, so stating the bound over
the `Fin E`-indexed representatives (as here) is the paper's `D_f(t, f₁, …, f_E)`.

Proof: `≤` sends a `D`-code `p` of the representatives to
`C v := (v, p_{i(v)})`, where `i(v)` is a representative of the value `f(v)`
(from `hsurj`) — this is where `hattain` is used; `≥` restricts the optimal FCC to
the representatives (`isDCode_drm_of_isFCC`), which needs neither hypothesis. -/
theorem optimalRedundancy_eq_fdm {k E : ℕ} (f : Word F k → α) (t : ℕ)
    (u : Fin E → Word F k)
    (hattain : ∀ i j, f (u i) ≠ f (u j) →
      hammingDist (u i) (u j) = fDist f (f (u i)) (f (u j)))
    (hsurj : ∀ v : Word F k, ∃ i : Fin E, f (u i) = f v) :
    optimalRedundancy f t = N (F := F) (ι := Fin E) (drm f t u) := by
  classical
  refine le_antisymm ?_ ?_
  · obtain ⟨r, C, hC⟩ := exists_isFCC f t
    have hne : {r : ℕ | IsDCode (F := F) (drm f t u) r}.Nonempty :=
      ⟨r, isDCode_drm_of_isFCC u hC⟩
    obtain ⟨p, hp⟩ := Nat.sInf_mem hne
    refine optimalRedundancy_le_of
      (C := fun v => Fin.append v (p (Classical.choose (hsurj v)))) ⟨?_, ?_⟩
    · intro v i
      simp [Fin.append_left]
    · intro v w hvw
      have hv : f (u (Classical.choose (hsurj v))) = f v := Classical.choose_spec (hsurj v)
      have hw : f (u (Classical.choose (hsurj w))) = f w := Classical.choose_spec (hsurj w)
      have hidx : Classical.choose (hsurj v) ≠ Classical.choose (hsurj w) := by
        intro hh
        exact hvw (by rw [← hv, hh, hw])
      have hfe : f (u (Classical.choose (hsurj v))) ≠
          f (u (Classical.choose (hsurj w))) := by
        rw [hv, hw]
        exact hvw
      rw [hammingDist_append]
      have hentry := hp _ _ hidx
      simp only [drm] at hentry
      rw [ite_eq_right hfe] at hentry
      have hdist : hammingDist (u (Classical.choose (hsurj v)))
          (u (Classical.choose (hsurj w))) = fDist f (f v) (f w) := by
        rw [hattain _ _ hfe, hv, hw]
      rw [hdist] at hentry
      have hfle : fDist f (f v) (f w) ≤ hammingDist v w := fDist_le rfl rfl
      have hple := le_trans (le_max_left _ _) hentry
      omega
  · obtain ⟨r, C, hC⟩ := exists_isFCC f t
    have hne : ∃ r' : ℕ, r' ∈ {r' : ℕ | ∃ C : Word F k → Word F (k + r'), IsFCC f C t} :=
      ⟨r, C, hC⟩
    rw [optimalRedundancy, dite_eq_left hne]
    have hspec := Nat.find_spec hne
    simp only [Set.mem_ofPred_eq] at hspec
    obtain ⟨C₀, hC₀⟩ := hspec
    exact N_le_of_isDCode (isDCode_drm_of_isFCC u hC₀)

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
`0` on it, indexed here by the image values.  As with `#definition 5#`, it is
defined on all of `α` but meant to be read on `Set.range f` (the paper's
`f₁, …, f_E`), which is the index set `#theorem 7#` uses — see `ISSUES.md` §12. -/
noncomputable def cfdm {k ℓ : ℕ} (f : Word F k → α) (C : Word F k → Word F ℓ) (tf : ℕ) :
    α → α → ℕ :=
  fun a b => if a = b then 0 else max (2 * tf + 1 - codedFDist f C a b) 0

omit [Fintype F] [DecidableEq α] in
/-- `(internal, §III — used by `#lemma 8#` and `#theorem 7#`)` — the coded distance
is at most the distance of any *witness pair*: if `f(u) = a` and `f(v) = b` then
`d_C(a,b) ≤ d(C u, C v)`.  This is what makes a CFDM code usable as a second step
in §III-A: the codeword pair `(c_u,c_v)` is one of the pairs the minimum defining
`d_C(f(u),f(v))` ranges over. -/
theorem codedFDist_le {k ℓ : ℕ} (f : Word F k → α) (C : Word F k → Word F ℓ) {a b : α}
    {u v : Word F k} (hu : f u = a) (hv : f v = b) :
    codedFDist f C a b ≤ hammingDist (C u) (C v) :=
  Nat.sInf_le ⟨u, v, hu, hv, rfl⟩

/-! ## §III — A construction procedure for FCCs with data protection

Definitions 6–9 are above.  The construction method of §III-A itself carries no
number; it is modelled in §IV by `twoStepCode` (the encoder `C_f(u) = C'_f(c_u)`)
and `IsSecondStep` (the "Step 2" condition on the second block), and its two
guarantees are `#theorem 5#`/`#corollary 4#` (the CDRM bound) and `#theorem 7#`
(the two-sided bound on the scheme's total redundancy), together with the concrete
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
`2 ≤ |Im(f)| ≤ k` then `r_f(k,t_d,t_f) ≥ 2t_f + t_d`" — the binary strengthening of
`#theorem 3#`.

Proof (the paper's, pp. 4866–4867): take a message `u₁` with a neighbour
`u₂ = u₁ + e_j` at distance one and `f(u₂) ≠ f(u₁)` (`exists_hammingDist_one_ne`).
The `k` neighbours `u₁ + eᵢ` together with `f(u₁)` take at most `|Im f| ≤ k` values,
so either two neighbours share a value `≠ f(u₁)` (Case 1) or some neighbour has
`f(u₁ + eᵢ) = f(u₁)` (Case 2).  In both cases the three messages involved are at
pairwise distances `1, 1, 2`, so the corresponding redundancy blocks satisfy two
bounds of `2t_f` and one of `2t_d − 1` (from the FCC conditions
`d(Cu,Cv) ≥ 2t_f+1` resp. `2t_d+1` and the splitting identity).  Since three
*binary* words of length `r` have pairwise distances summing to at most `2r`
(`hammingDist_three_le_two_mul`), we get `4t_f + 2t_d − 1 ≤ 2r`, i.e.
`r ≥ 2t_f + t_d`.  The FCC attaining `r_f` exists by `exists_isFCCData`. -/
theorem binary_optimalRedundancyData_ge {k : ℕ} (f : Word (ZMod 2) k → α) (td tf : ℕ)
    (h2 : 2 ≤ (Finset.univ.image f).card) (hk : (Finset.univ.image f).card ≤ k) :
    2 * tf + td ≤ optimalRedundancyData f (2 * td + 1) (2 * tf + 1) := by
  classical
  obtain ⟨r, C, hC⟩ := exists_isFCCData f (2 * td + 1) (2 * tf + 1)
  have hne : ∃ r' : ℕ, r' ∈ {r' : ℕ | ∃ C : Word (ZMod 2) k → Word (ZMod 2) (k + r'),
      IsFCCData f C (2 * td + 1) (2 * tf + 1)} := ⟨r, C, hC⟩
  rw [optimalRedundancyData, dite_eq_left hne]
  have hspec := Nat.find_spec hne
  simp only [Set.mem_ofPred_eq] at hspec
  obtain ⟨C₀, hC₀⟩ := hspec
  have hsys : IsSystematic C₀ := hC₀.1
  have hex : ∃ u v : Word (ZMod 2) k, f u ≠ f v := by
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega :
      1 < (Finset.univ.image f).card)
    rw [Finset.mem_image] at ha hb
    obtain ⟨u, -, hu⟩ := ha
    obtain ⟨v, -, hv⟩ := hb
    exact ⟨u, v, by rw [hu, hv]; exact hab⟩
  obtain ⟨u, v, huv⟩ := hex
  obtain ⟨u₁, u₂, hd12, hf12⟩ := exists_hammingDist_one_ne f huv
  by_cases hcase : ∃ i : Fin k, f (flip u₁ i) = f u₁
  · -- Case 1 of the paper: a neighbour carries the value of `u₁`
    obtain ⟨i, hi⟩ := hcase
    obtain ⟨j, hj⟩ := eq_flip_of_hammingDist_eq_one hd12
    have hji : j ≠ i := by
      intro hji
      exact hf12 (by rw [hj, hji, hi])
    have e12 : 2 * tf ≤ hammingDist (redPart (C₀ u₁)) (redPart (C₀ u₂)) := by
      have h := hC₀.2.2 u₁ u₂ hf12
      rw [hammingDist_eq_msg_add_red hsys u₁ u₂, hd12] at h
      omega
    have e32 : 2 * tf - 1 ≤ hammingDist (redPart (C₀ u₂)) (redPart (C₀ (flip u₁ i))) := by
      have hfe : f u₂ ≠ f (flip u₁ i) := by rw [hi]; exact hf12.symm
      have h := hC₀.2.2 u₂ (flip u₁ i) hfe
      have hd : hammingDist u₂ (flip u₁ i) = 2 := by
        rw [hj]
        exact hammingDist_flip_flip u₁ hji
      rw [hammingDist_eq_msg_add_red hsys u₂ (flip u₁ i), hd] at h
      omega
    have e13 : 2 * td ≤ hammingDist (redPart (C₀ u₁)) (redPart (C₀ (flip u₁ i))) := by
      have hne' : u₁ ≠ flip u₁ i := fun hh => flip_ne_self u₁ i hh.symm
      have h := hC₀.2.1 u₁ (flip u₁ i) hne'
      have hd : hammingDist u₁ (flip u₁ i) = 1 := by
        rw [hammingDist_comm]
        exact hammingDist_flip_self u₁ i
      rw [hammingDist_eq_msg_add_red hsys u₁ (flip u₁ i), hd] at h
      omega
    have hsum := hammingDist_three_le_two_mul (redPart (C₀ u₁)) (redPart (C₀ u₂))
      (redPart (C₀ (flip u₁ i)))
    omega
  · -- Case 2 of the paper: no neighbour carries the value of `u₁`
    have hnot : ∀ i : Fin k, f (flip u₁ i) ≠ f u₁ := fun i hh => hcase ⟨i, hh⟩
    have hsub : ∀ i : Fin k,
        f (flip u₁ i) ∈ (Finset.univ.image f) \ {f u₁} := by
      intro i
      rw [Finset.mem_sdiff, Finset.mem_singleton]
      exact ⟨Finset.mem_image.mpr ⟨flip u₁ i, Finset.mem_univ _, rfl⟩, hnot i⟩
    have hlt : ((Finset.univ.image f) \ {f u₁}).card < k := by
      have hmem : f u₁ ∈ Finset.univ.image f :=
        Finset.mem_image.mpr ⟨u₁, Finset.mem_univ _, rfl⟩
      have hc : ((Finset.univ.image f) \ {f u₁}).card = (Finset.univ.image f).card - 1 := by
        rw [Finset.sdiff_singleton_eq_erase]
        exact Finset.card_erase_of_mem hmem
      omega
    obtain ⟨i, j, hij, hval⟩ :=
      exists_ne_eq_of_card_lt (g := fun i : Fin k => f (flip u₁ i)) hsub hlt
    have e1i : 2 * tf ≤ hammingDist (redPart (C₀ u₁)) (redPart (C₀ (flip u₁ i))) := by
      have h := hC₀.2.2 u₁ (flip u₁ i) (hnot i).symm
      have hd : hammingDist u₁ (flip u₁ i) = 1 := by
        rw [hammingDist_comm]
        exact hammingDist_flip_self u₁ i
      rw [hammingDist_eq_msg_add_red hsys u₁ (flip u₁ i), hd] at h
      omega
    have e1j : 2 * tf ≤ hammingDist (redPart (C₀ u₁)) (redPart (C₀ (flip u₁ j))) := by
      have h := hC₀.2.2 u₁ (flip u₁ j) (hnot j).symm
      have hd : hammingDist u₁ (flip u₁ j) = 1 := by
        rw [hammingDist_comm]
        exact hammingDist_flip_self u₁ j
      rw [hammingDist_eq_msg_add_red hsys u₁ (flip u₁ j), hd] at h
      omega
    have eij : 2 * td - 1 ≤
        hammingDist (redPart (C₀ (flip u₁ i))) (redPart (C₀ (flip u₁ j))) := by
      have hne' : flip u₁ i ≠ flip u₁ j := by
        intro hh
        have hd0 : hammingDist (flip u₁ i) (flip u₁ j) = 0 := by rw [hh, hammingDist_self]
        rw [hammingDist_flip_flip u₁ hij] at hd0
        exact two_ne_zero hd0
      have h := hC₀.2.1 (flip u₁ i) (flip u₁ j) hne'
      have hd : hammingDist (flip u₁ i) (flip u₁ j) = 2 := hammingDist_flip_flip u₁ hij
      rw [hammingDist_eq_msg_add_red hsys (flip u₁ i) (flip u₁ j), hd] at h
      omega
    have hsum := hammingDist_three_le_two_mul (redPart (C₀ u₁)) (redPart (C₀ (flip u₁ i)))
      (redPart (C₀ (flip u₁ j)))
    omega

omit [Fintype F] in
/-- `(internal, §IV — used by `#theorem 5#` and `#theorem 6#`)` — the CDRM entries
of an `[n, k, 2t_d+1]` code are at most `2(t_f − t_d)`: the entry is `0` when the two
function values agree, and otherwise `max(2t_f+1 − d(c_ui,c_uj), 0) ≤ 2(t_f − t_d)`
because `d(c_ui,c_uj) ≥ 2t_d + 1`.  This is the paper's one-line estimate in the
proof of `#theorem 6#`. -/
theorem cdrm_le {k r : ℕ} {ι : Type*} (f : Word F k → α) (td tf : ℕ)
    (C : Word F k → Word F (k + r)) (u : ι → Word F k)
    (hC : ∀ v w : Word F k, v ≠ w → 2 * td + 1 ≤ hammingDist (C v) (C w)) :
    ∀ i j : ι, cdrm f C tf u i j ≤ 2 * (tf - td) := by
  intro i j
  simp only [cdrm]
  split_ifs with hf
  · omega
  · refine max_le ?_ (Nat.zero_le _)
    have huv : u i ≠ u j := fun hh => hf (by rw [hh])
    have hd := hC (u i) (u j) huv
    have : 2 * (tf - td) = 2 * tf - 2 * td := by omega
    omega

/-- `(internal, §IV — used by `#theorem 6#`)` — a constant-distance matrix has a
`D`-code of some length as soon as the alphabet has two distinct letters: send
the `i`-th index to the word that is `y` at coordinate `i` and `x` elsewhere,
repeated `D₀ + 1` times, so that two different indices are at distance
`2(D₀ + 1) ≥ D₀`.  (If the alphabet is a single letter, no code satisfying a
positive entry exists at all — the degenerate case handled inside `#theorem 6#`.) -/
theorem exists_isDCode_const {m D₀ : ℕ} (h : ∃ x y : F, x ≠ y) :
    ∃ r : ℕ, IsDCode (F := F) (fun _ _ : Fin m => D₀) r := by
  classical
  obtain ⟨x, y, hxy⟩ := h
  refine ⟨m * (D₀ + 1), ⟨fun i => repWord (D₀ + 1) (fun t => if t = i then y else x), ?_⟩⟩
  intro i j hij
  rw [hammingDist_repWord]
  have hdiff : (fun t : Fin m => if t = i then y else x) ≠
      (fun t : Fin m => if t = j then y else x) := by
    intro hh
    have h1 := congrFun hh i
    simp [hij] at h1
    exact hxy h1.symm
  have hpos : 1 ≤ hammingDist (fun t : Fin m => if t = i then y else x)
      (fun t : Fin m => if t = j then y else x) :=
    Nat.one_le_iff_ne_zero.mpr (hammingDist_ne_zero.mpr hdiff)
  have hmul : D₀ + 1 ≤ (D₀ + 1) * hammingDist (fun t : Fin m => if t = i then y else x)
      (fun t : Fin m => if t = j then y else x) := by
    calc D₀ + 1 = (D₀ + 1) * 1 := (Nat.mul_one _).symm
      _ ≤ (D₀ + 1) * _ := Nat.mul_le_mul_left _ hpos
  change D₀ ≤ (D₀ + 1) * hammingDist (fun t : Fin m => if t = i then y else x)
      (fun t : Fin m => if t = j then y else x)
  omega

/-- `#theorem 5#` (§IV) — "let `C` be an `[n, k, 2t_d+1]` error-correcting code,
and let `c_u` denote the codeword that corresponds to the message vector
`u ∈ F_q^k`.  For any function `f`,
`N(D_f(t_d,t_f : u₁,…,u_{q^k})) ≤ N(D_{C,f}(t_f : u₁,…,u_{q^k})) + n − k`".

Two modelling notes (both in `ISSUES.md` §13):

* the family of messages is an arbitrary `u : ι → Word F k`; the paper's
  `u₁, …, u_{q^k}` is the instance `ι = Word F k`, `u = id`, and the definitions of
  `D_f`/`D_{C,f}` are family-based, so nothing is lost and `#corollary 4#` becomes
  immediate;
* the statement carries `IsSystematic C` explicitly.  The proof in the paper says
  "without loss of generality, consider a systematic form of `C`, i.e.
  `c_u = (u, w_u)`"; that step is justified for a *linear* code (permute the
  coordinates), but our `C` is an arbitrary labelling map, for which the
  systematic form is an extra hypothesis.  It is used exactly as in the paper:
  `d(w_u,w_v) = d(c_u,c_v) − d(u,v)`.

Proof (the paper's): take a `D₂`-code `p₁,…,p_m` of length `N(D₂)`, `D₂` being the
CDRM, and let `p̃ᵢ := (wᵢ, pᵢ)` where `wᵢ` is the redundancy part of `cᵢ`.  Then
`d(p̃ᵢ,p̃ⱼ) = d(wᵢ,wⱼ) + d(pᵢ,pⱼ)`; for `f(uᵢ) = f(uⱼ)` the first term alone is
`≥ 2t_d+1 − d(uᵢ,uⱼ)`, and for `f(uᵢ) ≠ f(uⱼ)` the CDRM condition supplies
`d(pᵢ,pⱼ) ≥ 2t_f+1 − d(cᵢ,cⱼ)`, which combines with `d(wᵢ,wⱼ)` to
`2t_f+1 − d(uᵢ,uⱼ)`.  Both are the corresponding entries of the DRM.  (The
`D₂`-code set is non-empty because the CDRM entries are at most `2(t_f−t_d)`:
repeat the messages.) -/
theorem N_drmData_le_N_cdrm_add {k r : ℕ} {ι : Type*} (f : Word F k → α) (td tf : ℕ)
    (C : Word F k → Word F (k + r)) (u : ι → Word F k)
    (hCsys : IsSystematic C)
    (hC : ∀ v w : Word F k, v ≠ w → 2 * td + 1 ≤ hammingDist (C v) (C w)) :
    N (F := F) (ι := ι) (drmData f td tf u) ≤
      N (F := F) (ι := ι) (cdrm f C tf u) + r := by
  classical
  have hentry := cdrm_le f td tf C u hC
  have hne2 : ∃ r₂ : ℕ, IsDCode (F := F) (cdrm f C tf u) r₂ := by
    refine ⟨k * (2 * (tf - td) + 1),
      ⟨fun i => repWord (2 * (tf - td) + 1) (u i), ?_⟩⟩
    intro i j hij
    by_cases huv : u i = u j
    · rw [show cdrm f C tf u i j = 0 from by
        simp only [cdrm]
        rw [ite_eq_left (by rw [huv])]]
      exact Nat.zero_le _
    · rw [hammingDist_repWord]
      have hd1 : 0 < hammingDist (u i) (u j) := hammingDist_pos.mpr huv
      have hmul : 2 * (tf - td) + 1 ≤ (2 * (tf - td) + 1) * hammingDist (u i) (u j) :=
        Nat.le_mul_of_pos_right _ hd1
      have := hentry i j
      omega
  have hgen : ∀ r₂ : ℕ, IsDCode (F := F) (cdrm f C tf u) r₂ →
      IsDCode (F := F) (drmData f td tf u) (r + r₂) := by
    intro r₂ hr₂
    obtain ⟨p, hp⟩ := hr₂
    refine ⟨fun i => Fin.append (redPart (C (u i))) (p i), ?_⟩
    intro i j hij
    have hsplit := hammingDist_eq_msg_add_red hCsys (u i) (u j)
    rw [hammingDist_append]
    simp only [drmData]
    by_cases huv : u i = u j
    · rw [ite_eq_left huv]
      exact Nat.zero_le _
    · rw [ite_eq_right huv]
      by_cases hf : f (u i) = f (u j)
      · rw [ite_eq_left hf]
        have hred : 2 * td + 1 - hammingDist (u i) (u j) ≤
            hammingDist (redPart (C (u i))) (redPart (C (u j))) := by
          have hd := hC (u i) (u j) huv
          rw [hsplit] at hd
          omega
        refine le_trans (max_le hred (Nat.zero_le _)) ?_
        omega
      · rw [ite_eq_right hf]
        have hpentry := hp i j hij
        simp only [cdrm] at hpentry
        rw [ite_eq_right hf] at hpentry
        have h1 : 2 * tf + 1 - hammingDist (C (u i)) (C (u j)) ≤
            hammingDist (p i) (p j) := le_trans (le_max_left _ _) hpentry
        have h2 : hammingDist (C (u i)) (C (u j)) - hammingDist (u i) (u j) ≤
            hammingDist (redPart (C (u i))) (redPart (C (u j))) := by
          rw [hsplit]
          omega
        have h3 : 2 * tf + 1 - hammingDist (u i) (u j) ≤
            hammingDist (redPart (C (u i))) (redPart (C (u j))) +
              hammingDist (p i) (p j) := by
          omega
        exact max_le h3 (Nat.zero_le _)
  have hmain := hgen (sInf {r₂ : ℕ | IsDCode (F := F) (cdrm f C tf u) r₂})
    (Nat.sInf_mem hne2)
  have hle := N_le_of_isDCode hmain
  rw [Nat.add_comm] at hle
  simpa only [N] using hle

/-- `#corollary 4#` (§IV) — "for any function `f : F_q^k → Im(f)`,
`r_f(k,t_d,t_f) ≤ N(D_{C,f}(t_f : u₁,…,u_{q^k})) + n − k`, where `C` is an
`[n, k, 2t_d+1]` error-correcting code".

The two hypotheses that the paper leaves to `#definition 6#` and its proof are
explicit here: `hdf` is the side condition `d_d ≤ d_f` (needed to invoke
`#theorem 2#`; `ISSUES.md` §11(a)) and `hCsys` is the systematic form of `C` used
by `#theorem 5#` (`ISSUES.md` §13).  The proof is one line: `#theorem 2#` turns
`r_f` into `N(D_f)` over the whole message space, and `#theorem 5#` bounds that by
the CDRM. -/
theorem optimalRedundancyData_le_N_cdrm_add {k r : ℕ} (f : Word F k → α) (td tf : ℕ)
    (C : Word F k → Word F (k + r))
    (hCsys : IsSystematic C)
    (hC : ∀ v w : Word F k, v ≠ w → 2 * td + 1 ≤ hammingDist (C v) (C w))
    (hdf : 2 * td + 1 ≤ 2 * tf + 1) :
    optimalRedundancyData f (2 * td + 1) (2 * tf + 1) ≤
      N (F := F) (ι := Word F k) (cdrm f C tf fun v => v) + r := by
  rw [optimalRedundancyData_eq_N_drmData f td tf hdf]
  exact N_drmData_le_N_cdrm_add f td tf C (fun v : Word F k => v) hCsys hC

/-- `#theorem 6#` (§IV) — "let `C` be an `[n, k, 2t_d+1]` code.  Then
`N(D_{C,f}(t_f : u₁, u₂, …, u_M)) ≤ N(M, 2(t_f − t_d))`".

Proof (the paper's): every entry of the CDRM is at most `2(t_f − t_d)`
(`cdrm_le`), so a code for the *constant* matrix `2(t_f−t_d)` is a `D`-code for the
CDRM, whence `N(D_{C,f}) ≤ N(M, 2(t_f−t_d))`.  Making that step in Lean needs the
optimum to be attained, so the proof splits on whether the constant matrix has a
code at all: if it has one, `Nat.sInf_mem` supplies it; if not, the alphabet is a
single letter (`exists_isDCode_const`), all messages coincide, the CDRM is `0` and
`N(D_{C,f}) = 0 ≤ N(M, 2(t_f−t_d))`. -/
theorem N_cdrm_le_Nconst {k r m : ℕ} (f : Word F k → α) (td tf : ℕ)
    (C : Word F k → Word F (k + r)) (u : Fin m → Word F k)
    (hC : ∀ v w : Word F k, v ≠ w → 2 * td + 1 ≤ hammingDist (C v) (C w)) :
  N (F := F) (ι := Fin m) (cdrm f C tf u) ≤ Nconst (F := F) m (2 * (tf - td)) := by
  classical
  have hentry := cdrm_le f td tf C u hC
  by_cases hne : ∃ r : ℕ, IsDCode (F := F) (fun _ _ : Fin m => 2 * (tf - td)) r
  · obtain ⟨p, hp⟩ := Nat.sInf_mem hne
    exact N_le_of_isDCode ⟨p, fun i j hij => le_trans (hentry i j) (hp i j hij)⟩
  · have hF : ∀ x y : F, x = y := by
      intro x y
      by_contra hxy
      exact hne (exists_isDCode_const ⟨x, y, hxy⟩)
    have huv : ∀ i j : Fin m, u i = u j := fun i j => funext fun t => hF _ _
    have hzero : IsDCode (F := F) (cdrm f C tf u) 0 := by
      refine ⟨fun _ => Fin.elim0, ?_⟩
      intro i j hij
      simp only [cdrm]
      rw [ite_eq_left (by rw [huv i j])]
      exact Nat.zero_le _
    have hle : N (F := F) (ι := Fin m) (cdrm f C tf u) ≤ 0 := N_le_of_isDCode hzero
    omega

/-- `(internal, §III-A — used by `#theorem 7#`)` — the total redundancy `r_s` of
the two-step construction: "the resulting mapping ... is an `(f : d_d, d_f)`-FCC
with total redundancy `r_s = n − k + r'`", i.e. the redundancy `r` of the first
code plus the length `r'` of the second (FCC) step. -/
def schemeRedundancy (r r' : ℕ) : ℕ := r + r'

/-- `(internal, §III-A)` — the encoder `C_f(u) = C'_f(c_u)` of the two-step
construction of §III-A: the codeword `c_u = C u` (length `k + r`, `r = n − k`)
followed by the second-step block `E u` (length `r'`).  The length of the result is
`(k + r) + r' = k + (r + r')`; the statement below uses the `k + (r + r')` shape so
that `schemeRedundancy r r'` is the total redundancy, and the distance lemmas undo
the reassociation with `hammingDist_comp_cast`. -/
def twoStepCode {k r r' : ℕ} (C : Word F k → Word F (k + r)) (E : Word F k → Word F r') :
    Word F k → Word F (k + (r + r')) :=
  fun u j => Fin.append (C u) (E u) (Fin.cast (Nat.add_assoc k r r').symm j)

/-- `(internal, §III-A — the "Step 2" condition of `#theorem 7#`)` — the second step
of the two-step construction: "construct an FCC based on the set `{c_u}` ... define a
systematic encoding `C'_f` such that for any `u₁, u₂` with `f(u₁) ≠ f(u₂)`,
`d(C'_f(c_{u₁}), C'_f(c_{u₂})) ≥ d_f`".  With `C'_f(c_u) = (c_u, E u)` this is
`d(C u₁, C u₂) + d(E u₁, E u₂) ≥ d_f = 2t_f+1`; note that the second step is *not*
required to separate the function values by itself (the codeword already helps),
which is exactly why the CDRM/CFDM bounds below are of the form they are. -/
def IsSecondStep {k r : ℕ} (f : Word F k → α) (C : Word F k → Word F (k + r)) (tf : ℕ)
    {r' : ℕ} (E : Word F k → Word F r') : Prop :=
  ∀ u v : Word F k, f u ≠ f v →
    2 * tf + 1 ≤ hammingDist (C u) (C v) + hammingDist (E u) (E v)

omit [Fintype F] [DecidableEq F] in
/-- `(internal, §III-A)` — the composite encoder is systematic: the first `k`
coordinates of `C_f(u)` are the message `u`, because the first step is. -/
theorem twoStepCode_systematic {k r r' : ℕ} {C : Word F k → Word F (k + r)}
    (hC : IsSystematic C) (E : Word F k → Word F r') : IsSystematic (twoStepCode C E) := by
  intro u i
  have hidx : Fin.cast (Nat.add_assoc k r r').symm (Fin.castAdd (r + r') i)
      = Fin.castAdd r' (Fin.castAdd r i) := Fin.ext (by simp)
  simp only [twoStepCode, hidx, Fin.append_left]
  exact hC u i

/-- `(internal, §III-A)` — the Hamming distance of two composite codewords is the
sum of the two steps' distances: `d(C_f(u), C_f(v)) = d(C u, C v) + d(E u, E v)`. -/
theorem hammingDist_twoStepCode {k r r' : ℕ} (C : Word F k → Word F (k + r))
    (E : Word F k → Word F r') (u v : Word F k) :
    hammingDist (twoStepCode C E u) (twoStepCode C E v) =
      hammingDist (C u) (C v) + hammingDist (E u) (E v) := by
  have hu : twoStepCode C E u = fun j => Fin.append (C u) (E u)
      (Fin.cast (Nat.add_assoc k r r').symm j) := rfl
  have hv : twoStepCode C E v = fun j => Fin.append (C v) (E v)
      (Fin.cast (Nat.add_assoc k r r').symm j) := rfl
  rw [hu, hv]
  rw [hammingDist_comp_cast (Nat.add_assoc k r r').symm, hammingDist_append]

omit [DecidableEq α] in
/-- `(internal, §III-A)` — the paper's "it is straightforward to verify that the
encoding `C_f` ... satisfies the properties of an `(f : d_d, d_f)`-FCC": if the first
step has minimum distance `2t_d+1` and the second step satisfies Step 2, then
`C_f = twoStepCode C E` is an `(f : 2t_d+1, 2t_f+1)`-FCC of redundancy `r + r'`.
For `u₁ ≠ u₂` the codeword part alone gives `≥ d(c_{u₁},c_{u₂}) ≥ 2t_d+1`, and for
`f(u₁) ≠ f(u₂)` Step 2 gives `2t_f+1` for the sum. -/
theorem twoStep_isFCCData {k r r' : ℕ} (f : Word F k → α) (td tf : ℕ)
    (C : Word F k → Word F (k + r)) (hCsys : IsSystematic C)
    (hC : ∀ v w : Word F k, v ≠ w → 2 * td + 1 ≤ hammingDist (C v) (C w))
    (E : Word F k → Word F r') (hE : IsSecondStep f C tf E) :
    IsFCCData f (twoStepCode C E) (2 * td + 1) (2 * tf + 1) := by
  refine ⟨twoStepCode_systematic hCsys E, ?_, ?_⟩
  · intro u v huv
    have h := hC u v huv
    rw [hammingDist_twoStepCode]
    omega
  · intro u v hf
    have h := hE u v hf
    rw [hammingDist_twoStepCode]
    exact h

/-- `#theorem 7#` (§IV, §III-A) — "let `C` be an `[n, k, 2t_d+1]` linear code, where
`n` denotes the minimum possible length of a linear code with dimension `k` and
minimum distance at least `2t_d + 1`.  Then, the redundancy `r_s` of the proposed
scheme is bounded as
`N(D_{C,f}(t_f : u₁,…,u_M)) + n − k ≤ r_s ≤ N(D_{C,f}(t_f : f₁,…,f_E)) + n − k`".

The scheme is modelled by its two steps (§III-A): the data-protection code `C`
(redundancy `r = n − k`) and the second step `E` (block length `r'`), so that
`r_s = schemeRedundancy r r' = r + r'` and the encoder is `twoStepCode C E`.  Both
inequalities are stated at the level the paper states them:

* **every** second step `E` (satisfying Step 2) produces an
  `(f : 2t_d+1, 2t_f+1)`-FCC (`twoStep_isFCCData`) whose redundancy is at least
  `N(D_{C,f}(t_f : u₁,…,u_M)) + n − k` — the lower bound, because the second step's
  block is a `D`-code for the CDRM by Step 2;
* taking the second step optimal for the CFDM attains `N(D_{C,f}(t_f : f₁,…,f_E))`
  — the upper bound: **any** CFDM `D`-code of length `L` (over the image values
  `Im f = {f₁,…,f_E}`, the paper's index set — see `ISSUES.md` §12) yields a second
  step of block length `L`, hence a scheme with `r_s = L + n − k`.  In the paper's
  finite setting the CFDM code set is non-empty, so `L := N(CFDM)` is available;
  stating it as "any CFDM code" keeps the Lean statement free of that side
  condition.

The printed clause "`n` denotes the minimum possible length ..." is a remark about
which first step the scheme *uses* (an optimal `[n,k,2t_d+1]` code); both bounds
hold for any `[n,k,2t_d+1]` code in systematic form, which is what the statement
assumes. -/
theorem two_step_redundancy_bounds {k r : ℕ} (f : Word F k → α) (td tf : ℕ)
    (C : Word F k → Word F (k + r)) (hCsys : IsSystematic C)
    (hC : ∀ v w : Word F k, v ≠ w → 2 * td + 1 ≤ hammingDist (C v) (C w)) :
    (∀ (r' : ℕ) (E : Word F k → Word F r'), IsSecondStep f C tf E →
        IsFCCData f (twoStepCode C E) (2 * td + 1) (2 * tf + 1) ∧
          N (F := F) (ι := Word F k) (cdrm f C tf fun v => v) + r ≤
            schemeRedundancy r r') ∧
      (∀ (L : ℕ) (q : Set.range f → Word F L),
        (∀ a b : Set.range f, a ≠ b →
          cfdm f C tf a.1 b.1 ≤ hammingDist (q a) (q b)) →
        ∃ E : Word F k → Word F L,
          IsSecondStep f C tf E ∧ schemeRedundancy r L = r + L) := by
  classical
  refine ⟨?_, ?_⟩
  · intro r' E hE
    refine ⟨twoStep_isFCCData f td tf C hCsys hC E hE, ?_⟩
    have hcode : IsDCode (F := F) (cdrm f C tf fun v => v) r' := by
      refine ⟨E, ?_⟩
      intro u v huv
      simp only [cdrm]
      by_cases hf : f u = f v
      · rw [ite_eq_left hf]
        exact Nat.zero_le _
      · rw [ite_eq_right hf]
        refine max_le ?_ (Nat.zero_le _)
        have := hE u v hf
        omega
    have hle := N_le_of_isDCode hcode
    simp only [schemeRedundancy]
    omega
  · intro L q hq
    refine ⟨fun u => q ⟨f u, ⟨u, rfl⟩⟩, ?_, rfl⟩
    intro u v hf
    show 2 * tf + 1 ≤ hammingDist (C u) (C v) +
      hammingDist (q ⟨f u, ⟨u, rfl⟩⟩) (q ⟨f v, ⟨v, rfl⟩⟩)
    have hidx : (⟨f u, ⟨u, rfl⟩⟩ : Set.range f) ≠ ⟨f v, ⟨v, rfl⟩⟩ :=
      fun hh => hf (Subtype.ext_iff.mp hh)
    have hq' := hq ⟨f u, ⟨u, rfl⟩⟩ ⟨f v, ⟨v, rfl⟩⟩ hidx
    simp only [cfdm] at hq'
    rw [ite_eq_right hf] at hq'
    have h1 : 2 * tf + 1 - codedFDist f C (f u) (f v) ≤
        hammingDist (q ⟨f u, ⟨u, rfl⟩⟩) (q ⟨f v, ⟨v, rfl⟩⟩) :=
      le_trans (le_max_left _ _) hq'
    have h2 : codedFDist f C (f u) (f v) ≤ hammingDist (C u) (C v) :=
      codedFDist_le f C rfl rfl
    omega

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
