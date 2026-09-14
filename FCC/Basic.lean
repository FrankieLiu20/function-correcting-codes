import FCC.Definitions

/-!
# Basic lemmas about words

Paper-independent facts about `hammingDist`, `wt` and Hamming balls, used by the
paper-specific arguments later (see `PLAN.md` §4, phases 2 and following).

Every lemma here is fully proved: this file, together with `FCC/Definitions.lean`,
is what `lake build` and `scripts/axioms_check.ps1` check from the start, so that
the toolchain is verified end to end before any paper statement is added.
-/

namespace FCC

section Weight

variable {F : Type*} [Zero F] [DecidableEq F] {n : ℕ}

/-- `(internal, §VI-C — used by `#lemma 6#`)` — the weight difference of two words is at most their Hamming
distance: `wt(u) ≤ wt(v) + d(u,v)`, i.e. `d(u,v) ≥ wt(u) − wt(v)`.

Used by `#lemma 6#` (§VI-C) in the case `|f(u) − f(v)| > 2t_f`, where the paper
writes "Since `d(u,v) ≥ wt(u) − wt(v)`, we have `d(u,v) ≥ 2t_f + 1`". -/
theorem wt_le_wt_add_hammingDist (u v : Word F n) :
    wt u ≤ wt v + hammingDist u v := by
  classical
  have hsub :
      (Finset.univ.filter fun i : Fin n => u i ≠ 0) ⊆
        (Finset.univ.filter fun i : Fin n => u i ≠ v i) ∪
          (Finset.univ.filter fun i : Fin n => v i ≠ 0) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases h : u i = v i
    · exact Or.inr (h ▸ hi)
    · exact Or.inl h
  have h :=
    calc (Finset.univ.filter fun i : Fin n => u i ≠ 0).card
        ≤ ((Finset.univ.filter fun i : Fin n => u i ≠ v i) ∪
            (Finset.univ.filter fun i : Fin n => v i ≠ 0)).card :=
          Finset.card_le_card hsub
      _ ≤ (Finset.univ.filter fun i : Fin n => u i ≠ v i).card +
            (Finset.univ.filter fun i : Fin n => v i ≠ 0).card :=
          Finset.card_union_le _ _
      _ = (Finset.univ.filter fun i : Fin n => v i ≠ 0).card +
            (Finset.univ.filter fun i : Fin n => u i ≠ v i).card :=
          Nat.add_comm _ _
  simpa only [wt, hammingNorm, hammingDist] using h

/-- `(internal, §I-E)` — the zero word has weight `0`. -/
@[simp]
theorem wt_zero : wt (0 : Word F n) = 0 := by
  simp [wt]

end Weight

section Ball

variable {F : Type*} [Fintype F] [DecidableEq F] {n : ℕ}

/-- `(internal, §I-E)` — every word lies in its own Hamming ball: `d(u,u) = 0 ≤ t`. -/
@[simp]
theorem mem_ball_self (u : Word F n) (t : ℕ) : u ∈ ball u t := by
  simp [ball]

end Ball

section Systematic

/-- `(internal, §II — the hypothesis of `#definition 1#`)` — a *systematic*
encoding: the first `k` coordinates of `C u` are the message `u` itself.  The
paper's Definition 1 calls its encoding systematic and every construction in the
paper is of this shape. -/
def IsSystematic {F : Type*} {k r : ℕ} (C : Word F k → Word F (k + r)) : Prop :=
  ∀ u i, C u (Fin.castAdd r i) = u i

/-- `(internal, §VII)` — the message part of a length-`k + r` word: its first `k`
coordinates.  Used to read off `u` from a codeword `(u,p)`. -/
def msgPart {F : Type*} {k r : ℕ} (c : Word F (k + r)) : Word F k :=
  fun i => c (Fin.castAdd r i)

end Systematic

section MinDist

/-- `(internal, §V — used by `#definition 12#`)` — the minimum distance `d_min(C)`
of a code: the smallest Hamming distance between two distinct codewords, and `0`
when `C` has fewer than two words. -/
noncomputable def minDist {F : Type*} [DecidableEq F] {n : ℕ} (C : Finset (Word F n)) : ℕ :=
  sInf {d : ℕ | ∃ x ∈ C, ∃ y ∈ C, x ≠ y ∧ hammingDist x y = d}

end MinDist

end FCC
