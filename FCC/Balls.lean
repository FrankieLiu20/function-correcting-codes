import FCC.Basic

/-!
# Counting words, spheres and balls

Paper: §I-E (the Hamming ball `B(u,t)`), §IV (the size `q^k` of the message
space) and §VIII + Appendix (the counts `Σ_{i≤t} C(n,i)(q-1)^i`).

Everything is stated for an arbitrary finite field `F`, so `Fintype.card F` plays
the role of the paper's `q`.  The main results are

* `card_word` — `|F_q^n| = q^n`, the size of the message space;
* `hammingDist_eq_card_diffSet` — `d(x,u)` is the number of *disagreeing*
  coordinates, the bridge between the metric and every counting argument;
* `ball_eq_biUnion_sphere` — a ball is the union of its spheres (and
  `disjoint_sphere`: different radii give disjoint spheres);
* `ball_eq_univ_of_le`, `card_ball_univ` — for `t ≥ n` the ball is everything.

The closed form `|B(u,t)| = Σ_{i≤t} C(n,i)(q-1)^i` is *not* here yet: it is the
next step of phase 1a (see `PLAN.md` §4 and `DEVLOG.md`, 2026-09-14).
-/

namespace FCC

/-- The set of coordinates on which two words disagree. -/
def diffSet {F : Type*} [DecidableEq F] {n : ℕ} (x u : Word F n) : Finset (Fin n) :=
  Finset.univ.filter fun j => x j ≠ u j

/-- The Hamming distance is the number of disagreeing coordinates. -/
theorem hammingDist_eq_card_diffSet {F : Type*} [DecidableEq F] {n : ℕ} (x u : Word F n) :
    hammingDist x u = (diffSet x u).card := rfl

/-- The message space has `q^n` elements (the paper's `q^k`). -/
theorem card_word {F : Type*} [Fintype F] (n : ℕ) :
    Fintype.card (Word F n) = Fintype.card F ^ n := by
  simp

/-- The sphere of radius `i` around `u`: the words at distance exactly `i`. -/
def sphere {F : Type*} [Fintype F] [DecidableEq F] {n : ℕ} (u : Word F n) (i : ℕ) :
    Finset (Word F n) :=
  Finset.univ.filter fun x => hammingDist x u = i

theorem mem_sphere {F : Type*} [Fintype F] [DecidableEq F] {n : ℕ} {u x : Word F n} {i : ℕ} :
    x ∈ sphere u i ↔ hammingDist x u = i := by
  simp [sphere]

/-- A ball is the union of the spheres of radius at most `t`. -/
theorem ball_eq_biUnion_sphere {F : Type*} [Fintype F] [DecidableEq F] {n : ℕ}
    (u : Word F n) (t : ℕ) :
    ball u t = (Finset.range (t + 1)).biUnion (sphere u) := by
  ext x
  simp only [ball, sphere, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
    Finset.mem_range]
  exact ⟨fun h => ⟨hammingDist x u, Nat.lt_succ_of_le h, rfl⟩,
    fun ⟨i, hi, hix⟩ => hix ▸ Nat.le_of_lt_succ hi⟩

/-- The spheres of different radii are disjoint. -/
theorem disjoint_sphere {F : Type*} [Fintype F] [DecidableEq F] {n : ℕ} {u : Word F n}
    {i j : ℕ} (h : i ≠ j) : Disjoint (sphere u i) (sphere u j) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  rw [mem_sphere] at hx hy
  exact h (hx.symm.trans hy)

/-- Balls are monotone in the radius. -/
theorem ball_mono {F : Type*} [Fintype F] [DecidableEq F] {n : ℕ} {u : Word F n} {t t' : ℕ}
    (h : t ≤ t') : ball u t ⊆ ball u t' := by
  intro x hx
  simp only [ball, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact le_trans hx h

/-- For `t ≥ n` the ball of radius `t` is the whole space. -/
theorem ball_eq_univ_of_le {F : Type*} [Fintype F] [DecidableEq F] {n : ℕ} {u : Word F n}
    {t : ℕ} (h : n ≤ t) : ball u t = Finset.univ := by
  refine Finset.eq_univ_of_forall fun x => ?_
  simp only [ball, Finset.mem_filter, Finset.mem_univ, true_and]
  exact le_trans hammingDist_le_card_fintype (by simpa using h)

/-- A ball of radius `t ≥ n` has `q^n` elements. -/
theorem card_ball_univ {F : Type*} [Fintype F] [DecidableEq F] {n : ℕ} {u : Word F n}
    {t : ℕ} (h : n ≤ t) : (ball u t).card = Fintype.card F ^ n := by
  rw [ball_eq_univ_of_le h, Finset.card_univ]
  exact card_word n

end FCC
