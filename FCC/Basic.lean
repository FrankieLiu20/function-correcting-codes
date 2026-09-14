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

/-- `(internal)` — the weight difference of two words is at most their Hamming
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

/-- `(internal)` — the zero word has weight `0`. -/
@[simp]
theorem wt_zero : wt (0 : Word F n) = 0 := by
  simp [wt]

end Weight

section Ball

variable {F : Type*} [Fintype F] [DecidableEq F] {n : ℕ}

/-- `(internal)` — every word lies in its own Hamming ball: `d(u,u) = 0 ≤ t`. -/
@[simp]
theorem mem_ball_self (u : Word F n) (t : ℕ) : u ∈ ball u t := by
  simp [ball]

end Ball

end FCC
