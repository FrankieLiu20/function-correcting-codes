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

/-! ## The Singleton bound

The paper quotes the Singleton bound from [17] (`M ≤ q^{n−d+1}`) and uses it in §V-B;
it is proved here from scratch, because the only ingredient is the projection
argument: two codewords that agree on `n − d_min + 1` coordinates are at distance at
most `d_min − 1`, hence equal. -/

/-- `(internal, §V-B — used by `#corollary 8#`)` — the Singleton bound: a code of
length `n` over a non-empty alphabet (`1 ≤ q`) has at most `q^{n − d_min(C) + 1}`
words.  (`1 ≤ q` is needed: for the empty alphabet and `n = 0` the bound fails.) -/
theorem card_le_pow_minDist {F : Type*} [Fintype F] [DecidableEq F] {n : ℕ}
    {C : Finset (Word F n)} (hq : 1 ≤ Fintype.card F) :
    C.card ≤ Fintype.card F ^ (n - minDist C + 1) := by
  classical
  by_cases hsmall : C.card ≤ 1
  · -- at most one codeword: no pair of distinct codewords, so `d_min = 0`
    have hempty : ¬∃ d' : ℕ,
        d' ∈ {d' : ℕ | ∃ x ∈ C, ∃ y ∈ C, x ≠ y ∧ hammingDist x y = d'} := by
      rintro ⟨d', x, hx, y, hy, hxy, -⟩
      have h2 : 2 ≤ C.card := by
        have hsub : ({x, y} : Finset (Word F n)) ⊆ C := by
          intro z hz
          rw [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          exacts [hx, hy]
        have := Finset.card_le_card hsub
        rwa [Finset.card_insert_of_notMem (by simpa using hxy), Finset.card_singleton] at this
      omega
    have hmin0 : minDist C = 0 := by rw [minDist, dite_eq_right hempty]
    rw [hmin0]
    calc C.card ≤ Fintype.card (Word F n) := Finset.card_le_univ C
      _ = Fintype.card F ^ n := card_word n
      _ ≤ Fintype.card F ^ (n - 0 + 1) := by
          exact Nat.pow_le_pow_right hq (by omega)
  · -- at least two codewords: project onto `n - d_min + 1` coordinates
    obtain ⟨u, hu, v, hv, huv⟩ : ∃ u ∈ C, ∃ v ∈ C, u ≠ v := by
      obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < C.card)
      exact ⟨x, hx, y, hy, hxy⟩
    have hdn : minDist C ≤ n := by
      refine le_trans (minDist_le hu hv huv) ?_
      have := hammingDist_le_card_fintype (x := u) (y := v)
      rwa [Fintype.card_fin] at this
    have hd1 : 1 ≤ minDist C := by
      have hne : ∃ d' : ℕ,
          d' ∈ {d' : ℕ | ∃ x ∈ C, ∃ y ∈ C, x ≠ y ∧ hammingDist x y = d'} :=
        ⟨hammingDist u v, ⟨u, hu, v, hv, huv, rfl⟩⟩
      rw [minDist, dite_eq_left hne]
      obtain ⟨x, hx, y, hy, hxy, hval⟩ := Nat.find_spec hne
      have := hammingDist_pos.mpr hxy
      omega
    obtain ⟨J, -, hJcard⟩ :=
      Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin n)))
        (n := n - minDist C + 1)
        (by rw [Finset.card_univ, Fintype.card_fin]; omega)
    have hinj : ∀ x ∈ C, ∀ y ∈ C, (∀ i : {i // i ∈ J}, x i.1 = y i.1) → x = y := by
      intro x hx y hy hagree
      by_contra hxy
      have h1 : minDist C ≤ hammingDist x y := minDist_le hx hy hxy
      have hsub : diffSet x y ⊆ Jᶜ := by
        intro i hi
        rw [diffSet, Finset.mem_filter] at hi
        rw [Finset.mem_compl]
        intro hiJ
        exact hi.2 (hagree ⟨i, hiJ⟩)
      have h2' : (diffSet x y).card ≤ Jᶜ.card := Finset.card_le_card hsub
      rw [hammingDist_eq_card_diffSet] at h1
      rw [Finset.card_compl, Fintype.card_fin, hJcard] at h2'
      omega
    have hcard_le : C.card ≤ Fintype.card F ^ J.card := by
      have := Fintype.card_le_of_injective
        (fun x : ↥C => fun i : {i // i ∈ J} => (x : Word F n) i.1)
        (by
          intro x y hxy
          refine Subtype.ext (hinj x.val x.2 y.val y.2 ?_)
          intro i
          exact congrFun hxy i)
      rwa [Fintype.card_coe, Fintype.card_fun, Fintype.card_coe] at this
    rwa [hJcard] at hcard_le

/-! ## §V-B — the counting behind the perfect-code argument

`#theorem 10#` ("the minimum-distance graph of a perfect `t`-error correcting code
is connected") rests on the closed forms of §VIII + App. for the sphere and the
ball,

`|S(u,i)| = C(n,i)(q−1)^i`   and   `|B(u,t)| = Σ_{i ≤ t} C(n,i)(q−1)^i`,

on the packing bound behind the Hamming bound quoted in §V-B (disjoint balls
around a code with pairwise distances `≥ 2t+1` fit in the space), and on three
consequences: every word is within `t` of a codeword of a perfect code, a perfect
code has minimum distance exactly `2t+1`, and the paper's step 5 of the proof of
`#theorem 10#` (moving to a codeword at distance `≤ t` from the intermediate
vector `x` strictly decreases the distance to `v`). -/

/-- `(internal, §VIII + App.)` — the number of words whose set of disagreements with
`u` is a prescribed `S`: `(q−1)^{|S|}` (on each coordinate of `S` pick one of the
`q−1` letters different from `u`, and copy `u` outside `S`). -/
theorem card_sphere_fiber {F : Type*} [Fintype F] [DecidableEq F] {n : ℕ}
    (u : Word F n) (S : Finset (Fin n)) :
    (Finset.univ.filter fun x : Word F n => diffSet x u = S).card
      = (Fintype.card F - 1) ^ S.card := by
  classical
  rw [← Fintype.card_subtype (fun x : Word F n => diffSet x u = S)]
  have hcard : ∀ j : Fin n, Fintype.card {c : F // c ≠ u j} = Fintype.card F - 1 := by
    intro j
    rw [Fintype.card_subtype]
    have h : (Finset.univ.filter fun c : F => c ≠ u j) = Finset.univ.erase (u j) := by
      ext c
      simp [Finset.mem_erase]
    rw [h, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  have heq : {x : Word F n // diffSet x u = S} ≃ ((j : ↥S) → {c : F // c ≠ u ↑j}) :=
    { toFun := fun x => fun j => ⟨x.1 ↑j, by
        have hj : (↑j : Fin n) ∈ diffSet x.1 u := by rw [x.2]; exact j.2
        simpa [diffSet] using hj⟩
      invFun := fun g => ⟨fun j => if h : j ∈ S then (g ⟨j, h⟩ : F) else u j, by
        ext j
        by_cases h : j ∈ S
        · simp [diffSet, h, (g ⟨j, h⟩).2]
        · simp [diffSet, h]⟩
      left_inv := fun x => by
        refine Subtype.ext (funext fun j => ?_)
        by_cases h : j ∈ S
        · simp [h]
        · have hxj : x.1 j = u j := by
            by_contra hne
            have hmem : j ∈ diffSet x.1 u := by simp [diffSet, hne]
            rw [x.2] at hmem
            exact h hmem
          simp [h, hxj]
      right_inv := fun g => by
        refine funext fun j => Subtype.ext ?_
        simp [j.2] }
  calc Fintype.card {x : Word F n // diffSet x u = S}
      = Fintype.card ((j : ↥S) → {c : F // c ≠ u ↑j}) := Fintype.card_congr heq
    _ = ∏ j : ↥S, Fintype.card {c : F // c ≠ u ↑j} := Fintype.card_pi
    _ = ∏ _j : ↥S, (Fintype.card F - 1) :=
        Finset.prod_congr rfl fun j _ => hcard j
    _ = (Fintype.card F - 1) ^ S.card := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe]

/-- `(internal, §VIII + App. — used by `#theorem 15#`–`#theorem 19#` and §V-B)` —
the sphere count: `|{x | d(x,u) = i}| = C(n,i)(q−1)^i`.  A word at distance exactly
`i` from `u` is determined by the set `S` of `i` disagreeing coordinates (`C(n,i)`
choices) together with a value `≠ u j` on each of them (`(q−1)^i` choices, the
`i`-fold product of the `q−1` alternatives). -/
theorem card_sphere {F : Type*} [Fintype F] [DecidableEq F] {n : ℕ} (u : Word F n) (i : ℕ) :
    (sphere u i).card = n.choose i * (Fintype.card F - 1) ^ i := by
  classical
  have hdisj : Set.PairwiseDisjoint (fun S : Finset (Fin n) => S ∈ Finset.univ.powersetCard i)
      (fun S => Finset.univ.filter fun x : Word F n => diffSet x u = S) := by
    intro S _ T _ hne
    exact Finset.disjoint_left.mpr fun x hx hy => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
      exact hne (hx.symm.trans hy)
  have hunion : sphere u i = (Finset.univ.powersetCard i).biUnion
      (fun S => Finset.univ.filter fun x : Word F n => diffSet x u = S) := by
    ext x
    constructor
    · intro hx
      rw [mem_sphere] at hx
      refine Finset.mem_biUnion.mpr ⟨diffSet x u, ?_, ?_⟩
      · rw [Finset.mem_powersetCard]
        exact ⟨Finset.subset_univ _, hx⟩
      · simp
    · intro hx
      obtain ⟨S, hS, hxS⟩ := Finset.mem_biUnion.mp hx
      rw [Finset.mem_powersetCard] at hS
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hxS
      simp [mem_sphere, hammingDist_eq_card_diffSet, hxS, hS.2]
  rw [hunion, Finset.card_biUnion hdisj]
  calc ∑ S ∈ Finset.univ.powersetCard i,
        (Finset.univ.filter fun x : Word F n => diffSet x u = S).card
      = ∑ _S ∈ Finset.univ.powersetCard i, (Fintype.card F - 1) ^ i := by
        refine Finset.sum_congr rfl fun S hS => ?_
        rw [card_sphere_fiber u S, (Finset.mem_powersetCard.mp hS).2]
    _ = (n.choose i) * (Fintype.card F - 1) ^ i := by
        rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, smul_eq_mul]
        simp

/-- `(internal, §VIII + App. — used by §V-B and `#theorem 15#`–`#theorem 19#`)` —
the ball count: `|B(u,t)| = Σ_{i ≤ t} C(n,i)(q−1)^i`, the sum of the sphere counts
(`ball_eq_biUnion_sphere` and `disjoint_sphere` make the union disjoint). -/
theorem card_ball {F : Type*} [Fintype F] [DecidableEq F] {n : ℕ} (u : Word F n) (t : ℕ) :
    (ball u t).card = ∑ i ∈ Finset.range (t + 1), n.choose i * (Fintype.card F - 1) ^ i := by
  classical
  rw [ball_eq_biUnion_sphere, Finset.card_biUnion]
  · exact Finset.sum_congr rfl fun i _ => card_sphere u i
  · intro i _ j _ hij
    exact disjoint_sphere hij

/-- `(internal, §VIII + App.)` — the ball count, one radius at a time:
`|B(u,t+1)| = |B(u,t)| + C(n,t+1)(q−1)^{t+1}`.  In particular `|B(u,t)|` grows
with `t` as long as `t + 1 ≤ n` and `q ≥ 2` (`card_ball_lt_succ`). -/
theorem card_ball_succ {F : Type*} [Fintype F] [DecidableEq F] {n : ℕ} (u : Word F n) (t : ℕ) :
    (ball u (t + 1)).card
      = (ball u t).card + n.choose (t + 1) * (Fintype.card F - 1) ^ (t + 1) := by
  rw [card_ball, card_ball, Finset.sum_range_succ]

/-- `(internal, §I-E)` — a ball strictly grows with its radius while there is room
for a sphere at the new radius and the alphabet has at least two letters. -/
theorem card_ball_lt_succ {F : Type*} [Fintype F] [DecidableEq F] {n : ℕ} (u : Word F n)
    {t : ℕ} (ht : t + 1 ≤ n) (hq : 1 < Fintype.card F) :
    (ball u t).card < (ball u (t + 1)).card := by
  rw [card_ball_succ]
  have h1 : 0 < n.choose (t + 1) := Nat.choose_pos ht
  have h2 : 0 < (Fintype.card F - 1) ^ (t + 1) :=
    pow_pos (Nat.sub_pos_of_lt hq) _
  have h3 : 0 < n.choose (t + 1) * (Fintype.card F - 1) ^ (t + 1) := Nat.mul_pos h1 h2
  omega

/-- `(internal, §V-B — used by `#theorem 10#`)` — for `k ≤ n` and an alphabet with
at least two letters there is a word at distance exactly `k` from any prescribed
word: change `k` coordinates to a different letter. -/
theorem exists_hammingDist_eq {F : Type*} [Fintype F] [DecidableEq F] {n : ℕ} (x : Word F n)
    {k : ℕ} (hk : k ≤ n) (hq : 2 ≤ Fintype.card F) :
    ∃ z : Word F n, hammingDist z x = k := by
  classical
  obtain ⟨a, b, hab⟩ := Fintype.one_lt_card_iff.mp (by omega : 1 < Fintype.card F)
  obtain ⟨T, -, hT⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin n)))
    (n := k) (by
      rw [Finset.card_univ, Fintype.card_fin]
      exact hk)
  refine ⟨fun i => if i ∈ T then (if x i = a then b else a) else x i, ?_⟩
  rw [hammingDist_eq_card_diffSet]
  have hset : diffSet (fun i => if i ∈ T then (if x i = a then b else a) else x i) x = T := by
    ext i
    by_cases h : i ∈ T
    · have hne : (if x i = a then b else a) ≠ x i := by
        split_ifs with hx
        · exact fun hh => hab (hh.trans hx).symm
        · exact fun hh => hx hh.symm
      simp [diffSet, h, hne]
    · simp [diffSet, h]
  rw [hset, hT]

/-- `(internal, §V-B — used by `#theorem 10#`)` — the balls of radius `r` around
the words of a code with pairwise distances `≥ 2r+1` are pairwise disjoint (two of
them meeting at `z` would give `2r+1 ≤ d(x,y) ≤ d(x,z) + d(z,y) ≤ 2r` by the
triangle inequality). -/
theorem pairwiseDisjoint_ball {F : Type*} [Fintype F] [DecidableEq F] {n : ℕ}
    {C : Finset (Word F n)} {r : ℕ}
    (h : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → 2 * r + 1 ≤ hammingDist x y) :
    Set.PairwiseDisjoint (fun c : Word F n => c ∈ C) (fun c => ball c r) := by
  intro x hx y hy hxy
  refine Finset.disjoint_left.mpr fun z hzx hzy => ?_
  simp only [ball, Finset.mem_filter, Finset.mem_univ, true_and] at hzx hzy
  have h1 : 2 * r + 1 ≤ hammingDist x y := h x hx y hy hxy
  have h2 : hammingDist x y ≤ hammingDist x z + hammingDist z y := hammingDist_triangle x z y
  rw [hammingDist_comm z x] at hzx
  rw [hammingDist_comm z y] at h2 hzy
  omega

/-- `(internal, §V-B — used by `#theorem 10#`)` — the packing bound behind the
Hamming bound quoted in §V-B: the balls of radius `r` around the words of a code
whose pairwise distances are `≥ 2r + 1` are disjoint (`pairwiseDisjoint_ball`), so
`|C| · |B(0,r)| ≤ q^n`. -/
theorem card_mul_card_ball_le {F : Type*} [Zero F] [Fintype F] [DecidableEq F] {n : ℕ}
    (C : Finset (Word F n)) (r : ℕ)
    (h : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → 2 * r + 1 ≤ hammingDist x y) :
    C.card * (ball (0 : Word F n) r).card ≤ Fintype.card F ^ n := by
  classical
  have hcard : (C.biUnion fun c => ball c r).card = ∑ c ∈ C, (ball c r).card :=
    Finset.card_biUnion (pairwiseDisjoint_ball h)
  have hball : ∀ c : Word F n, (ball c r).card = (ball (0 : Word F n) r).card := by
    intro c
    rw [card_ball, card_ball]
  have hsum : ∑ c ∈ C, (ball c r).card = C.card * (ball (0 : Word F n) r).card := by
    rw [Finset.sum_congr rfl fun c _ => hball c, Finset.sum_const, smul_eq_mul]
  calc C.card * (ball (0 : Word F n) r).card
      = ∑ c ∈ C, (ball c r).card := hsum.symm
    _ = (C.biUnion fun c => ball c r).card := hcard.symm
    _ ≤ Fintype.card (Word F n) := Finset.card_le_univ _
    _ = Fintype.card F ^ n := card_word n

/-- `(internal, §V-B — used by `#theorem 10#` and `#corollary 7#`)` — the covering
half of "a perfect code achieves the Hamming bound with equality": in a perfect
`t`-error correcting code the balls of radius `t` around the codewords partition
the space, so every word is within distance `t` of a (unique) codeword. -/
theorem exists_mem_ball_of_isPerfect {F : Type*} [Zero F] [Fintype F] [DecidableEq F]
    {n t : ℕ} {C : Finset (Word F n)} (h : IsPerfect C t) (x : Word F n) :
    ∃ c ∈ C, hammingDist x c ≤ t := by
  classical
  have hball : ∀ c : Word F n, (ball c t).card = (ball (0 : Word F n) t).card := by
    intro c
    rw [card_ball, card_ball]
  have hcard : (C.biUnion fun c => ball c t).card
      = C.card * (ball (0 : Word F n) t).card := by
    rw [Finset.card_biUnion (pairwiseDisjoint_ball h.1),
      Finset.sum_congr rfl fun c _ => hball c, Finset.sum_const, smul_eq_mul]
  have huniv : (C.biUnion fun c => ball c t) = Finset.univ := by
    refine Finset.eq_univ_of_card _ ?_
    rw [hcard, ← h.2, card_word]
  have hx : x ∈ C.biUnion fun c => ball c t := by rw [huniv]; exact Finset.mem_univ x
  obtain ⟨c, hc, hxc⟩ := Finset.mem_biUnion.mp hx
  exact ⟨c, hc, by simpa [ball] using hxc⟩

/-- `(internal, §V-B — used by `#theorem 10#` and `#corollary 7#`)` — a perfect
`t`-error correcting code with at least two words has minimum distance *exactly*
`2t+1` (so it can be used with `#theorem 8#`, whose hypothesis is `d_min(C) = d`).

`≥ 2t+1` is the definition of perfectness.  For `≤`: if `d_min ≥ 2t+2` then a word
`z` at distance `t+1` from a codeword `x` (which exists because `2t+2 ≤ d_min ≤ n`
and `q ≥ 2`) is at distance `> t` from `x`, so the codeword `c` covering `z` is
different from `x` yet `d(x,c) ≤ (t+1) + t = 2t+1 < d_min` — contradiction. -/
theorem minDist_eq_of_isPerfect {F : Type*} [Zero F] [Fintype F] [DecidableEq F] {n t : ℕ}
    {C : Finset (Word F n)} (h : IsPerfect C t) (hcard : 2 ≤ C.card) :
    minDist C = 2 * t + 1 := by
  classical
  have hq : 2 ≤ Fintype.card F := by
    by_contra hcon
    have hle1 : Fintype.card F ≤ 1 := by omega
    have hone : Fintype.card (Word F n) ≤ 1 := by
      rw [card_word]
      calc Fintype.card F ^ n ≤ 1 ^ n := Nat.pow_le_pow_left hle1 n
        _ = 1 := one_pow n
    have h2 : C.card ≤ Fintype.card (Word F n) := Finset.card_le_univ C
    omega
  have hge : 2 * t + 1 ≤ minDist C := by
    obtain ⟨x, hx, y, hy, hxy, hd⟩ := exists_hammingDist_eq_minDist hcard
    rw [← hd]
    exact h.1 x hx y hy hxy
  refine le_antisymm ?_ hge
  by_contra hlt
  have hm2 : 2 * t + 2 ≤ minDist C := by omega
  have hmn : minDist C ≤ n := by
    obtain ⟨x, hx, y, hy, hxy, hd⟩ := exists_hammingDist_eq_minDist hcard
    rw [← hd]
    have := hammingDist_le_card_fintype (x := x) (y := y)
    rwa [Fintype.card_fin] at this
  obtain ⟨x, hx, -, -, -, -⟩ := exists_hammingDist_eq_minDist hcard
  obtain ⟨z, hz⟩ := exists_hammingDist_eq x (by omega : t + 1 ≤ n) hq
  obtain ⟨c, hc, hcz⟩ := exists_mem_ball_of_isPerfect h z
  have hcx : c ≠ x := by
    intro hceq
    rw [hceq, hz] at hcz
    omega
  have h1 : minDist C ≤ hammingDist x c := minDist_le hx hc hcx.symm
  have h2 : hammingDist x c ≤ hammingDist x z + hammingDist z c := hammingDist_triangle x z c
  have h3 : hammingDist z c = hammingDist c z := hammingDist_comm z c
  have h4 : hammingDist x z = t + 1 := hammingDist_comm x z ▸ hz
  omega

/-- `(internal, §V-B — used by `#theorem 10#`)` — step 5 of the proof of
`#theorem 10#`: if `T` is a set of `t+1` coordinates on which `u` and `v` differ,
`x` is the word that follows `v` on `T` and `u` outside it, and `u'` is a codeword
at distance `≤ t` from `x`, then `d(u',v) < d(u,v)`.

The paper counts coordinates: writing `m_in` and `m_out` for the disagreements of
`u'` with `x` inside and outside `T` (`m_in + m_out = d(x,u') ≤ t`),
`d(u',v) ≤ d(u,v) − |T| + m_in + m_out ≤ d(u,v) − 1`; the Lean proof turns this
into the set inclusion `D(u',v) ⊆ (D(u',x) ∩ T) ∪ (D(u,v) \ T) ∪ (D(u',x) \ T)`
and adds cardinalities. -/
theorem hammingDist_lt_of_close {F : Type*} [Fintype F] [DecidableEq F] {n t : ℕ}
    {u v u' : Word F n} {T : Finset (Fin n)} (hT : T ⊆ diffSet u v)
    (hcardT : T.card = t + 1)
    (hclose : hammingDist (fun i => if i ∈ T then v i else u i) u' ≤ t) :
    hammingDist u' v < hammingDist u v := by
  classical
  set x : Word F n := fun i => if i ∈ T then v i else u i with hx
  have hxT : ∀ i ∈ T, x i = v i := fun i hi => by rw [hx]; exact ite_eq_left hi
  have hxnT : ∀ i, i ∉ T → x i = u i := fun i hi => by rw [hx]; exact ite_eq_right hi
  have hsub : diffSet u' v ⊆ (diffSet u' x ∩ T) ∪ (diffSet u v \ T) ∪ (diffSet u' x \ T) := by
    intro i hi
    have huv : u' i ≠ v i := by simpa [diffSet] using hi
    by_cases hiD : i ∈ diffSet u v
    · by_cases hiT : i ∈ T
      · refine Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl
          (Finset.mem_inter.mpr ⟨?_, hiT⟩))))
        simp only [diffSet, Finset.mem_filter, Finset.mem_univ, true_and]
        rwa [hxT i hiT]
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr
          (Finset.mem_sdiff.mpr ⟨hiD, hiT⟩))))
    · refine Finset.mem_union.mpr (Or.inr ?_)
      have hiT : i ∉ T := fun h => hiD (hT h)
      refine Finset.mem_sdiff.mpr ⟨?_, hiT⟩
      simp only [diffSet, Finset.mem_filter, Finset.mem_univ, true_and]
      have hui : u i = v i := by
        by_contra hne
        exact hiD (by simp [diffSet, hne])
      rw [hxnT i hiT, hui]
      exact huv
  have hmain : (diffSet u' v).card ≤ (diffSet u v).card - 1 := by
    have h1 : (diffSet u' v).card
        ≤ (diffSet u' x ∩ T).card + (diffSet u v \ T).card + (diffSet u' x \ T).card := by
      refine le_trans (Finset.card_le_card hsub) ?_
      have h2 := Finset.card_union_le ((diffSet u' x ∩ T) ∪ (diffSet u v \ T))
        (diffSet u' x \ T)
      have h3 := Finset.card_union_le (diffSet u' x ∩ T) (diffSet u v \ T)
      omega
    have h4 : (diffSet u' x ∩ T).card + (diffSet u' x \ T).card = (diffSet u' x).card :=
      Finset.card_inter_add_card_sdiff _ _
    have h5 : (diffSet u v \ T).card = (diffSet u v).card - T.card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hT]
    have h6 : (diffSet u' x).card ≤ t := by
      have h1 := hammingDist_eq_card_diffSet u' x
      have h2 : hammingDist u' x = hammingDist x u' := hammingDist_comm u' x
      omega
    have h7 : T.card ≤ (diffSet u v).card := Finset.card_le_card hT
    omega
  rw [hammingDist_eq_card_diffSet u' v, hammingDist_eq_card_diffSet u v]
  have hpos : 0 < (diffSet u v).card := by
    have := Finset.card_le_card hT
    omega
  omega

end FCC
