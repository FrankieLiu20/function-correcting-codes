import FCC.Basic
-- The binary results of §IV (`#theorem 4#`) are stated over `Word (ZMod 2) k`; this
-- module needs `ZMod` for the coordinate-flip lemmas at the end.
import Mathlib.Data.ZMod.Basic

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

/-- `(internal, §I-E)` — the set of coordinates on which two words disagree; `d(x,u)`
is by definition the size of this set (§I-E). -/
def diffSet {F : Type*} [DecidableEq F] {n : ℕ} (x u : Word F n) : Finset (Fin n) :=
  Finset.univ.filter fun j => x j ≠ u j

/-- `(internal, §I-E)` — the paper's `d(x,y)` made literal: the number of coordinates
in which `x` and `y` differ. -/
theorem hammingDist_eq_card_diffSet {F : Type*} [DecidableEq F] {n : ℕ} (x u : Word F n) :
    hammingDist x u = (diffSet x u).card := rfl

/-- `(internal, §IV)` — the message space `F_q^n` has `q^n` elements; the paper writes
`q^k` for it in, e.g., `#theorem 2#` and `#theorem 3#`. -/
theorem card_word {F : Type*} [Fintype F] (n : ℕ) :
    Fintype.card (Word F n) = Fintype.card F ^ n := by
  simp

/-- `(internal, §VIII + App. — used by `#theorem 17#`–`#theorem 19#`)` — the sphere of radius `i` around `u`: the words at distance
exactly `i` from `u`.  Its size `C(n,i)(q−1)^i` is what the appendix counts
(`#theorem 17#`–`#theorem 19#`). -/
def sphere {F : Type*} [Fintype F] [DecidableEq F] {n : ℕ} (u : Word F n) (i : ℕ) :
    Finset (Word F n) :=
  Finset.univ.filter fun x => hammingDist x u = i

/-- `(internal, §I-E)` — membership in a sphere, by definition of `sphere`. -/
theorem mem_sphere {F : Type*} [Fintype F] [DecidableEq F] {n : ℕ} {u x : Word F n} {i : ℕ} :
    x ∈ sphere u i ↔ hammingDist x u = i := by
  simp [sphere]

/-- `(internal, §VIII + App.)` — a ball is the union of its spheres; this is the decomposition
behind the counting arguments of §VIII and the appendix. -/
theorem ball_eq_biUnion_sphere {F : Type*} [Fintype F] [DecidableEq F] {n : ℕ}
    (u : Word F n) (t : ℕ) :
    ball u t = (Finset.range (t + 1)).biUnion (sphere u) := by
  ext x
  simp only [ball, sphere, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
    Finset.mem_range]
  exact ⟨fun h => ⟨hammingDist x u, Nat.lt_succ_of_le h, rfl⟩,
    fun ⟨i, hi, hix⟩ => hix ▸ Nat.le_of_lt_succ hi⟩

/-- `(internal, §VIII + App.)` — spheres of different radii are disjoint, so the union above
is a disjoint one. -/
theorem disjoint_sphere {F : Type*} [Fintype F] [DecidableEq F] {n : ℕ} {u : Word F n}
    {i j : ℕ} (h : i ≠ j) : Disjoint (sphere u i) (sphere u j) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  rw [mem_sphere] at hx hy
  exact h (hx.symm.trans hy)

/-- `(internal, §I-E)` — balls are monotone in the radius. -/
theorem ball_mono {F : Type*} [Fintype F] [DecidableEq F] {n : ℕ} {u : Word F n} {t t' : ℕ}
    (h : t ≤ t') : ball u t ⊆ ball u t' := by
  intro x hx
  simp only [ball, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact le_trans hx h

/-- `(internal, §I-E)` — for `t ≥ n` the ball of radius `t` is the whole space. -/
theorem ball_eq_univ_of_le {F : Type*} [Fintype F] [DecidableEq F] {n : ℕ} {u : Word F n}
    {t : ℕ} (h : n ≤ t) : ball u t = Finset.univ := by
  refine Finset.eq_univ_of_forall fun x => ?_
  simp only [ball, Finset.mem_filter, Finset.mem_univ, true_and]
  exact le_trans hammingDist_le_card_fintype (by simpa using h)

/-- `(internal, §I-E)` — a ball of radius `t ≥ n` has `q^n` elements. -/
theorem card_ball_univ {F : Type*} [Fintype F] [DecidableEq F] {n : ℕ} {u : Word F n}
    {t : ℕ} (h : n ≤ t) : (ball u t).card = Fintype.card F ^ n := by
  rw [ball_eq_univ_of_le h, Finset.card_univ]
  exact card_word n

/-! ## Concatenating coordinates adds the distances

The paper's two-step construction and §VII-B glue a message to a redundancy block,
i.e. concatenate words; this section records that the Hamming distance is additive
under that gluing.  It is stated outside any `[Field F]` section so that proofs
over an arbitrary alphabet (which is all `#theorem 2#` needs) can use it. -/

/-- `(internal, §VII — used by `#lemma 10#`, `#theorem 13#` and both halves of
`#theorem 2#`)` — concatenating coordinates adds the Hamming distances:
`d(Fin.append x₁ y₁, Fin.append x₂ y₂) = d(x₁,x₂) + d(y₁,y₂)`.  Field-free *and*
zero-free: the proof only ever counts *disagreeing* coordinates (`diffSet`), so
the lemma applies to an arbitrary alphabet, which is what `#theorem 2#` is stated
over (`α` need not be a field).

Proof: carve the two `diffSet`s at the `Fin.castAdd`/`Fin.natAdd` boundary
(`Fin.addCases` with `Fin.append_left`/`Fin.append_right`), show the two segments
disjoint by comparing `Fin.val` (there is no ready-made `Fin.castAdd_ne_natAdd`,
so `omega` closes `a.val < m ≤ m + b.val`), and add the cardinalities with
`Finset.card_union_of_disjoint` and the two injectivity lemmas. -/
theorem hammingDist_append {F : Type*} [Fintype F] [DecidableEq F] {m n : ℕ}
    (x₁ x₂ : Word F m) (y₁ y₂ : Word F n) :
    hammingDist (Fin.append x₁ y₁) (Fin.append x₂ y₂) = hammingDist x₁ x₂ + hammingDist y₁ y₂ := by
  classical
  have hne : ∀ (a : Fin m) (b : Fin n), Fin.castAdd n a ≠ Fin.natAdd m b := by
    intro a b h
    have hval : (Fin.castAdd n a).val = (Fin.natAdd m b).val := congrArg Fin.val h
    simp [Fin.castAdd, Fin.natAdd] at hval
    omega
  have hne' : ∀ (a : Fin m) (b : Fin n), Fin.natAdd m b ≠ Fin.castAdd n a :=
    fun a b => (hne a b).symm
  have hsplit : diffSet (Fin.append x₁ y₁) (Fin.append x₂ y₂) =
      (diffSet x₁ x₂).image (Fin.castAdd n) ∪ (diffSet y₁ y₂).image (Fin.natAdd m) := by
    ext i
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i <;>
      simp [diffSet, Fin.append_left, Fin.append_right, hne, hne']
  have hdisj : Disjoint ((diffSet x₁ x₂).image (Fin.castAdd n))
      ((diffSet y₁ y₂).image (Fin.natAdd m)) := by
    rw [Finset.disjoint_left]
    intro i hi hj
    obtain ⟨a, -, ha⟩ := Finset.mem_image.mp hi
    obtain ⟨b, -, hb⟩ := Finset.mem_image.mp hj
    exact hne a b (ha.trans hb.symm)
  rw [hammingDist_eq_card_diffSet, hammingDist_eq_card_diffSet, hammingDist_eq_card_diffSet, hsplit,
    Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ (Fin.castAdd_injective m n),
    Finset.card_image_of_injective _ (Fin.natAdd_injective n m)]

/-! ## Repeating a word

`repWord t u` writes the word `u` down `t` times, in the shape `Word F (k * t)`.
Its use is the non-vacuity lemma `exists_isFCCData` of `FCC/Paper.lean`: writing a
message down `m` times puts any two distinct messages at distance at least `m`, so
an `(f : d_d, d_f)`-FCC of *some* redundancy always exists (take `m = max d_d d_f`).
That is what lets the `sInf`-based `optimalRedundancyData` be assumed attained. -/

/-- `(internal, §II — used by the non-vacuity brick of §III)` — `t` copies of the
word `u`, concatenated, in the shape `Word F (k * t)`. -/
def repWord {F : Type*} {k : ℕ} : (t : ℕ) → Word F k → Word F (k * t)
  | 0, _ => Fin.elim0
  | t + 1, u =>
    fun j => Fin.append u (repWord t u) (Fin.cast (by rw [Nat.mul_succ, Nat.add_comm]) j)

/-- `(internal, §I-E)` — re-indexing a word along a cardinality equality does not
change Hamming distances.  (The recurrence defining `repWord` shifts the shape by
`Fin.cast`, and this is the lemma that makes that shift invisible to distances.) -/
theorem hammingDist_comp_cast {F : Type*} [DecidableEq F] {m n : ℕ} (h : m = n)
    (x y : Word F n) :
    hammingDist (fun i => x (Fin.cast h i)) (fun i => y (Fin.cast h i)) = hammingDist x y := by
  subst h
  simp

/-- `(internal, §II)` — `t` copies of a word are at `t` times the distance:
`d(u…u, v…v) = t · d(u,v)`. -/
theorem hammingDist_repWord {F : Type*} [Fintype F] [DecidableEq F] {k : ℕ} (t : ℕ)
    (u v : Word F k) :
    hammingDist (repWord t u) (repWord t v) = t * hammingDist u v := by
  induction t with
  | zero => simp [repWord]
  | succ t ih =>
    rw [show repWord (t + 1) u = fun j => Fin.append u (repWord t u)
          (Fin.cast (by rw [Nat.mul_succ, Nat.add_comm]) j) from rfl,
      show repWord (t + 1) v = fun j => Fin.append v (repWord t v)
          (Fin.cast (by rw [Nat.mul_succ, Nat.add_comm]) j) from rfl]
    rw [hammingDist_comp_cast (by rw [Nat.mul_succ, Nat.add_comm])
      (Fin.append u (repWord t u)) (Fin.append v (repWord t v))]
    rw [hammingDist_append, ih, Nat.succ_mul, Nat.add_comm]

/-! ## Binary words: flipping coordinates

`#theorem 4#` is the only binary-specific result of §IV: its proof moves around one
message and its `k` neighbours `u + eᵢ`.  This section supplies the vocabulary it
needs — `flip` (the neighbour `u + eᵢ`), the distance facts
`d(u, u+eᵢ) = 1` and `d(u+eᵢ, u+eⱼ) = 2` for `i ≠ j`, the converse statement that a
word at distance one from `u` *is* a flip of `u`, the fact that three binary words
have pairwise distances summing to at most `2r` (each coordinate contributes to at
most two of the three pairs), and the pigeonhole used on the `k` neighbours. -/

/-- `(internal, §IV — used by `#theorem 4#`)` — `a + 1 ≠ a` in `ZMod 2`. -/
theorem zmod_two_add_one_ne_self (a : ZMod 2) : a + 1 ≠ a := fun h =>
  one_ne_zero (add_left_cancel (show a + 1 = a + 0 by rw [add_zero]; exact h))

/-- `(internal, §IV — used by `#theorem 4#`)` — in `ZMod 2`, two different elements
differ by one. -/
theorem zmod_two_eq_add_one_of_ne {a b : ZMod 2} (h : a ≠ b) : a = b + 1 := by
  revert h
  revert a b
  decide

/-- `(internal, §IV — used by `#theorem 4#`)` — toggle the `i`-th coordinate, i.e.
the neighbour `u + eᵢ` of the standard basis vector `eᵢ`. -/
def flip {k : ℕ} (w : Word (ZMod 2) k) (i : Fin k) : Word (ZMod 2) k :=
  fun t => if t = i then w t + 1 else w t

/-- `(internal, §IV — used by `#theorem 4#`)` — flipping the same coordinate twice
returns the word. -/
theorem flip_flip {k : ℕ} (w : Word (ZMod 2) k) (i : Fin k) : flip (flip w i) i = w := by
  funext t
  by_cases ht : t = i
  · rw [ht]
    simp only [flip, ite_true]
    rw [add_assoc, show (1 : ZMod 2) + 1 = 0 from by decide, add_zero]
  · simp only [flip, ite_eq_right ht]

/-- `(internal, §IV — used by `#theorem 4#`)` — a neighbour is a different word. -/
theorem flip_ne_self {k : ℕ} (w : Word (ZMod 2) k) (i : Fin k) : flip w i ≠ w := by
  intro h
  have h1 := congrFun h i
  simp only [flip, ite_true] at h1
  exact zmod_two_add_one_ne_self (w i) h1

/-- `(internal, §IV — used by `#theorem 4#`)` — `d(u, u+eᵢ) = 1`. -/
theorem hammingDist_flip_self {k : ℕ} (w : Word (ZMod 2) k) (i : Fin k) :
    hammingDist (flip w i) w = 1 := by
  rw [hammingDist_eq_card_diffSet]
  have hset : diffSet (flip w i) w = {i} := by
    ext t
    simp only [diffSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro ht
      by_contra hti
      exact ht (by simp only [flip, ite_eq_right hti])
    · intro hti
      rw [hti]
      simp only [flip, ite_true]
      exact zmod_two_add_one_ne_self (w i)
  rw [hset, Finset.card_singleton]

/-- `(internal, §IV — used by `#theorem 4#`)` — `d(u+eᵢ, u+eⱼ) = 2` for `i ≠ j`. -/
theorem hammingDist_flip_flip {k : ℕ} (w : Word (ZMod 2) k) {i j : Fin k} (hij : i ≠ j) :
    hammingDist (flip w i) (flip w j) = 2 := by
  rw [hammingDist_eq_card_diffSet]
  have hi : i ∈ diffSet (flip w i) (flip w j) := by
    rw [diffSet, Finset.mem_filter]
    refine ⟨Finset.mem_univ i, ?_⟩
    simp only [flip, ite_true, ite_eq_right hij]
    exact zmod_two_add_one_ne_self (w i)
  have hj : j ∈ diffSet (flip w i) (flip w j) := by
    rw [diffSet, Finset.mem_filter]
    refine ⟨Finset.mem_univ j, ?_⟩
    simp only [flip, ite_eq_right hij.symm, ite_true]
    exact (zmod_two_add_one_ne_self (w j)).symm
  have hsub : diffSet (flip w i) (flip w j) ⊆ {i, j} := by
    intro t ht
    rw [diffSet, Finset.mem_filter] at ht
    rw [Finset.mem_insert, Finset.mem_singleton]
    by_contra hcon
    push Not at hcon
    exact ht.2 (by simp only [flip, ite_eq_right hcon.1, ite_eq_right hcon.2])
  have hcard2 : ({i, j} : Finset (Fin k)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using hij), Finset.card_singleton]
  have hge : 2 ≤ (diffSet (flip w i) (flip w j)).card := by
    have h2' : ({i, j} : Finset (Fin k)).card ≤ (diffSet (flip w i) (flip w j)).card :=
      Finset.card_le_card (by
        intro t ht
        rw [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl
        exacts [hi, hj])
    rwa [hcard2] at h2'
  have hle : (diffSet (flip w i) (flip w j)).card ≤ 2 := by
    have h1' : (diffSet (flip w i) (flip w j)).card ≤ ({i, j} : Finset (Fin k)).card :=
      Finset.card_le_card hsub
    rwa [hcard2] at h1'
  omega

/-- `(internal, §IV — used by `#theorem 4#`)` — in `ZMod 2` a word at distance one
from `w` is a flip of `w` (the converse of `hammingDist_flip_self`). -/
theorem eq_flip_of_hammingDist_eq_one {k : ℕ} {w v : Word (ZMod 2) k}
    (h : hammingDist w v = 1) : ∃ i, v = flip w i := by
  obtain ⟨i, hi⟩ : ∃ i, diffSet w v = {i} := by
    have hc : (diffSet w v).card = 1 := by rw [← hammingDist_eq_card_diffSet]; exact h
    exact Finset.card_eq_one.mp hc
  refine ⟨i, ?_⟩
  funext t
  by_cases ht : t = i
  · rw [ht]
    have hmem : i ∈ diffSet w v := by rw [hi]; exact Finset.mem_singleton_self i
    rw [diffSet, Finset.mem_filter] at hmem
    have hswap : v i = w i + 1 := zmod_two_eq_add_one_of_ne hmem.2.symm
    simp only [flip, ite_true]
    exact hswap
  · have hnot : t ∉ diffSet w v := by
      rw [hi]
      simpa [Finset.mem_singleton] using ht
    rw [diffSet, Finset.mem_filter] at hnot
    have heq : w t = v t := by
      by_contra hne
      exact hnot ⟨Finset.mem_univ t, hne⟩
    simp only [flip, ite_eq_right ht]
    exact heq.symm

/-- `(internal, §IV — used by `#theorem 4#`)` — any three binary words of length `r`
have pairwise distances summing to at most `2r`: a coordinate contributes to at
most two of the three pairs, since three pairwise different values cannot fit into
`ZMod 2`. -/
theorem hammingDist_three_le_two_mul {r : ℕ} (x y z : Word (ZMod 2) r) :
    hammingDist x y + hammingDist x z + hammingDist y z ≤ 2 * r := by
  have h1 : (diffSet x y).card = ∑ t : Fin r, (if x t ≠ y t then 1 else 0) := by
    rw [diffSet, Finset.card_filter]
  have h2 : (diffSet x z).card = ∑ t : Fin r, (if x t ≠ z t then 1 else 0) := by
    rw [diffSet, Finset.card_filter]
  have h3 : (diffSet y z).card = ∑ t : Fin r, (if y t ≠ z t then 1 else 0) := by
    rw [diffSet, Finset.card_filter]
  rw [hammingDist_eq_card_diffSet, hammingDist_eq_card_diffSet, hammingDist_eq_card_diffSet,
    h1, h2, h3, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  calc (∑ t : Fin r, ((if x t ≠ y t then 1 else 0) + (if x t ≠ z t then 1 else 0) +
        (if y t ≠ z t then 1 else 0)))
      ≤ ∑ _t : Fin r, 2 := by
        refine Finset.sum_le_sum fun t _ => ?_
        have hpt : ∀ a b c : ZMod 2,
            ((if a ≠ b then (1 : ℕ) else 0) + (if a ≠ c then 1 else 0) +
              (if b ≠ c then 1 else 0)) ≤ 2 := by decide
        exact hpt (x t) (y t) (z t)
    _ = 2 * r := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_comm]

/-- `(internal, §IV — used by `#theorem 4#`)` — pigeonhole: `k` values that all lie
in a set of size `< k` are not pairwise different. -/
theorem exists_ne_eq_of_card_lt {k : ℕ} {γ : Type*} [DecidableEq γ] {g : Fin k → γ}
    {S : Finset γ} (hsub : ∀ i, g i ∈ S) (hcard : S.card < k) :
    ∃ i j, i ≠ j ∧ g i = g j := by
  by_contra hcon
  push Not at hcon
  have hinj : Function.Injective g := fun i j hij => by
    by_contra hne
    exact hcon i j hne hij
  have hc : (Finset.univ.image g).card = k := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hle : (Finset.univ.image g).card ≤ S.card := by
    refine Finset.card_le_card ?_
    intro a ha
    rw [Finset.mem_image] at ha
    obtain ⟨i, -, rfl⟩ := ha
    exact hsub i
  omega

end FCC
