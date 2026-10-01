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

/-! ### §V-B — the truncated binomial sums of `#corollary 7#`

`#corollary 7#` compares the Hamming-bound denominator `A_t(m) = Σ_{i≤t} C(m,i)(q−1)^i`
at two lengths `m < n`: the sequence `A_t(m)/q^m` is strictly decreasing in `m`
(the probability that a binomial variable is `≤ t`), which is what rules out a code
shorter than the perfect one.  The proofs below use the Pascal recurrence
`A_t(m+1) = A_t(m) + (q−1)·A_{t−1}(m)` (`Nat.choose_succ_succ`, shifting the index
of the sum with `Finset.sum_range_succ'`) and hence `A_t(m+1) < q·A_t(m)` whenever
`t ≤ m` and `q ≥ 2` (the extra term `C(m,t)(q−1)^t` is positive). -/

/-- `(internal, §V-B — used by `#corollary 7#`)` — `q * b = (q−1) * b + b` for
`q ≥ 1`, the arithmetic behind the truncated binomial sums. -/
theorem mul_eq_pred_mul_add {a b : ℕ} (ha : 1 ≤ a) : a * b = (a - 1) * b + b := by
  conv_lhs => rw [show a = (a - 1) + 1 from (Nat.sub_add_cancel ha).symm]
  rw [add_mul, one_mul]

/-- `(internal, §V-B — used by `#corollary 7#`)` — the Pascal recurrence for the
truncated sums: `A_t(m+1) = A_t(m) + (q−1)·A_{t−1}(m)`, i.e. all binomial
coefficients of one row are rebuilt from the previous row. -/
theorem sum_range_choose_mul_pow_succ {q m t : ℕ} :
    (∑ i ∈ Finset.range (t + 1), (m + 1).choose i * (q - 1) ^ i)
      = (∑ i ∈ Finset.range (t + 1), m.choose i * (q - 1) ^ i)
        + (q - 1) * (∑ i ∈ Finset.range t, m.choose i * (q - 1) ^ i) := by
  have h1 : (∑ i ∈ Finset.range (t + 1), (m + 1).choose i * (q - 1) ^ i)
      = (∑ i ∈ Finset.range t, (m + 1).choose (i + 1) * (q - 1) ^ (i + 1)) + 1 := by
    rw [Finset.sum_range_succ']
    simp
  have h2 : (∑ i ∈ Finset.range (t + 1), m.choose i * (q - 1) ^ i)
      = (∑ i ∈ Finset.range t, m.choose (i + 1) * (q - 1) ^ (i + 1)) + 1 := by
    rw [Finset.sum_range_succ']
    simp
  have h3 : (∑ i ∈ Finset.range t, (m + 1).choose (i + 1) * (q - 1) ^ (i + 1))
      = (∑ i ∈ Finset.range t, m.choose i * (q - 1) ^ (i + 1))
        + (∑ i ∈ Finset.range t, m.choose (i + 1) * (q - 1) ^ (i + 1)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Nat.choose_succ_succ]
    ring
  have h4 : (∑ i ∈ Finset.range t, m.choose i * (q - 1) ^ (i + 1))
      = (q - 1) * (∑ i ∈ Finset.range t, m.choose i * (q - 1) ^ i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pow_succ]
    ring
  rw [h1, h2, h3, h4]
  ring

/-- `(internal, §V-B — used by `#corollary 7#`)` — `A_t(m+1) ≤ q·A_t(m)`: the
Hamming-ball density does not increase when the length grows by one. -/
theorem sum_range_choose_mul_pow_le_succ {q m t : ℕ} (hq : 1 ≤ q) :
    (∑ i ∈ Finset.range (t + 1), (m + 1).choose i * (q - 1) ^ i)
      ≤ q * (∑ i ∈ Finset.range (t + 1), m.choose i * (q - 1) ^ i) := by
  rw [sum_range_choose_mul_pow_succ]
  have hsub : (∑ i ∈ Finset.range t, m.choose i * (q - 1) ^ i)
      ≤ ∑ i ∈ Finset.range (t + 1), m.choose i * (q - 1) ^ i := by
    rw [Finset.sum_range_succ]
    exact Nat.le_add_right _ _
  have h1 := Nat.mul_le_mul_left (q - 1) hsub
  rw [mul_eq_pred_mul_add hq]
  omega

/-- `(internal, §V-B — used by `#corollary 7#`)` — the strict form of the previous
lemma, valid as soon as the radius fits (`t ≤ m`) and the alphabet has at least two
letters: the `t`-th binomial term `C(m,t)(q−1)^t` is then a positive gap. -/
theorem sum_range_choose_mul_pow_lt_succ {q m t : ℕ} (htm : t ≤ m) (hq : 1 < q) :
    (∑ i ∈ Finset.range (t + 1), (m + 1).choose i * (q - 1) ^ i)
      < q * (∑ i ∈ Finset.range (t + 1), m.choose i * (q - 1) ^ i) := by
  rw [sum_range_choose_mul_pow_succ]
  have hsplit : (∑ i ∈ Finset.range (t + 1), m.choose i * (q - 1) ^ i)
      = (∑ i ∈ Finset.range t, m.choose i * (q - 1) ^ i) + m.choose t * (q - 1) ^ t :=
    Finset.sum_range_succ _ _
  have hT : 0 < m.choose t * (q - 1) ^ t :=
    Nat.mul_pos (Nat.choose_pos htm) (pow_pos (by omega) t)
  have hlt : m.choose t * (q - 1) ^ t < q * (m.choose t * (q - 1) ^ t) := by
    calc m.choose t * (q - 1) ^ t = 1 * (m.choose t * (q - 1) ^ t) := (one_mul _).symm
      _ < q * (m.choose t * (q - 1) ^ t) := Nat.mul_lt_mul_of_pos_right hq hT
  rw [hsplit]
  have h2 : q * ((∑ i ∈ Finset.range t, m.choose i * (q - 1) ^ i)
      + m.choose t * (q - 1) ^ t)
      = q * (∑ i ∈ Finset.range t, m.choose i * (q - 1) ^ i)
        + q * (m.choose t * (q - 1) ^ t) := by
    rw [Nat.mul_add]
  rw [h2]
  rw [mul_eq_pred_mul_add (by omega : 1 ≤ q)]
  omega

/-- `(internal, §V-B — used by `#corollary 7#`)` — iterating the strict step:
`A_t(m+d) < A_t(m)·q^d` for `d ≥ 1`, `t ≤ m` and `q ≥ 2`. -/
theorem sum_range_choose_mul_pow_lt_add {q m d t : ℕ} (hd : 1 ≤ d) (htm : t ≤ m)
    (hq : 1 < q) :
    (∑ i ∈ Finset.range (t + 1), (m + d).choose i * (q - 1) ^ i)
      < (∑ i ∈ Finset.range (t + 1), m.choose i * (q - 1) ^ i) * q ^ d := by
  induction d with
  | zero => omega
  | succ d ih =>
    by_cases hd0 : d = 0
    · subst hd0
      simpa [mul_comm] using sum_range_choose_mul_pow_lt_succ htm hq
    · have hd1 : 1 ≤ d := by omega
      have hle := sum_range_choose_mul_pow_le_succ (q := q) (m := m + d) (t := t) (by omega)
      have := ih hd1
      calc (∑ i ∈ Finset.range (t + 1), (m + (d + 1)).choose i * (q - 1) ^ i)
          = (∑ i ∈ Finset.range (t + 1), ((m + d) + 1).choose i * (q - 1) ^ i) := by
            rw [show m + (d + 1) = (m + d) + 1 by omega]
        _ ≤ q * (∑ i ∈ Finset.range (t + 1), (m + d).choose i * (q - 1) ^ i) := hle
        _ < q * ((∑ i ∈ Finset.range (t + 1), m.choose i * (q - 1) ^ i) * q ^ d) :=
            Nat.mul_lt_mul_of_pos_left this (by omega)
        _ = (∑ i ∈ Finset.range (t + 1), m.choose i * (q - 1) ^ i) * q ^ (d + 1) := by
            rw [pow_succ]
            ring

/-! ## Appendix — the ball-union counts

The appendix computes the size of a union (or intersection) of two or three Hamming
balls; everything rests on carving the coordinates at which the centres differ.
The first two ingredients are here: the unique differing coordinate of two words at
distance one, and the characterisation of `B(u,t) ∩ B(v,t)` for such a pair (see
the `#theorem 17#` entry of `PLAN.md` for the resulting count). -/

/-- `(internal, Appendix — first step of `#theorem 17#`)` — two words at Hamming
distance one differ in exactly one coordinate. -/
theorem exists_diffSet_eq_singleton {F : Type*} [Fintype F] [DecidableEq F] {n : ℕ}
    {u v : Word F n} (h : hammingDist u v = 1) : ∃ c : Fin n, diffSet u v = {c} := by
  have hcard : (diffSet u v).card = 1 := by
    rw [← hammingDist_eq_card_diffSet]
    exact h
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hcard
  exact ⟨c, hc⟩

/-- `(internal, Appendix — the characterisation behind `#theorem 17#`)` — if `u` and
`v` differ only in the coordinate `c`, then `x` lies in both balls `B(u,t)` and
`B(v,t)` **iff** it disagrees with `u` in at most `t−1` of the *other* coordinates.

Writing `a` for that number of disagreements: outside `c` the two centres agree, so
`x` agrees with both or with neither and these coordinates contribute `a` to each
distance; at `c` the two centres differ, so exactly one or both of the distances
picks up one more — never none.  Hence the two distances are `a+1, a` or `a+1, a+1`,
and "both `≤ t`" is equivalent to `a + 1 ≤ t` in either case.  (The `+ 1 ≤ t` form
also covers `t = 0`, where `a ≤ t − 1` would be wrong; this matches the printed
empty sum in `#theorem 17#`.) -/
theorem mem_ball_inter_iff_of_dist_one {F : Type*} [Fintype F] [DecidableEq F] {n t : ℕ}
    {u v x : Word F n} {c : Fin n} (hc : diffSet u v = {c}) :
    x ∈ ball u t ∩ ball v t ↔ ((diffSet x u).erase c).card + 1 ≤ t := by
  classical
  have hucv : u c ≠ v c := by
    have : c ∈ diffSet u v := by rw [hc]; simp
    simpa [diffSet] using this
  have hout : ∀ j, j ≠ c → u j = v j := by
    intro j hj
    by_contra hne
    have : j ∈ diffSet u v := by simp [diffSet, hne]
    rw [hc] at this
    simp only [Finset.mem_singleton] at this
    exact hj this
  have herase : (diffSet x v).erase c = (diffSet x u).erase c := by
    ext j
    by_cases hj : j = c
    · subst hj; simp
    · have h1 : u j = v j := hout j hj
      simp only [Finset.mem_erase, ne_eq, hj, not_false_eq_true, true_and]
      simp only [diffSet, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [h1]
  have keyu : ∀ hmem : c ∈ diffSet x u,
      hammingDist x u = ((diffSet x u).erase c).card + 1 := by
    intro hmem
    rw [hammingDist_eq_card_diffSet]
    exact (Finset.card_erase_add_one hmem).symm
  have keyu' : c ∉ diffSet x u →
      hammingDist x u = ((diffSet x u).erase c).card := by
    intro hmem
    rw [hammingDist_eq_card_diffSet, Finset.erase_eq_of_notMem hmem]
  have keyv : ∀ hmem : c ∈ diffSet x v,
      hammingDist x v = ((diffSet x u).erase c).card + 1 := by
    intro hmem
    rw [hammingDist_eq_card_diffSet, ← herase]
    exact (Finset.card_erase_add_one hmem).symm
  have keyv' : c ∉ diffSet x v →
      hammingDist x v = ((diffSet x u).erase c).card := by
    intro hmem
    rw [hammingDist_eq_card_diffSet, ← herase, Finset.erase_eq_of_notMem hmem]
  have hnotboth : ¬ (c ∉ diffSet x u ∧ c ∉ diffSet x v) := by
    rintro ⟨h1, h2⟩
    have hx1 : x c = u c := by
      by_contra hne
      exact h1 (by simp [diffSet, hne])
    have hx2 : x c = v c := by
      by_contra hne
      exact h2 (by simp [diffSet, hne])
    exact hucv (by rw [← hx1, hx2])
  simp only [Finset.mem_inter, ball, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩
    by_cases hu : c ∈ diffSet x u
    · rw [keyu hu] at h1
      omega
    · have hv : c ∈ diffSet x v := by
        by_contra hv
        exact hnotboth ⟨hu, hv⟩
      rw [keyv hv] at h2
      omega
  · intro hle
    constructor
    · by_cases hu : c ∈ diffSet x u
      · rw [keyu hu]; omega
      · rw [keyu' hu]; omega
    · by_cases hv : c ∈ diffSet x v
      · rw [keyv hv]; omega
      · rw [keyv' hv]; omega

/-- `(internal, Appendix — the counting step of `#theorem 17#`)` — the number of
words whose disagreements with `u`, *apart from the coordinate `c`*, form a
prescribed set `S ∌ c`:

`|{x | D(x,u) \ {c} = S}| = q · (q−1)^{|S|}`.

Such an `x` either disagrees with `u` exactly on `S` (`(q−1)^{|S|}` words, by
`card_sphere_fiber`) or exactly on `S ∪ {c}` (`(q−1)^{|S|+1}` words); the two cases
are disjoint, and `(q−1)^{|S|} + (q−1)^{|S|+1} = q(q−1)^{|S|}`.  Summing over the
`i`-subsets of `{c}ᶜ` (there are `C(n−1,i)` of them) gives the appendix's
`q·Σ_{i≤t−1}C(n−1,i)(q−1)^i`. -/
theorem card_fiber_erase {F : Type*} [Zero F] [Fintype F] [DecidableEq F] {n : ℕ}
    (u : Word F n) {c : Fin n} {S : Finset (Fin n)} (hS : c ∉ S) :
    (Finset.univ.filter (fun x : Word F n => (diffSet x u).erase c = S)).card
      = Fintype.card F * (Fintype.card F - 1) ^ S.card := by
  classical
  have hsplit : (Finset.univ.filter (fun x : Word F n => (diffSet x u).erase c = S))
      = (Finset.univ.filter (fun x : Word F n => diffSet x u = S))
        ∪ (Finset.univ.filter (fun x : Word F n => diffSet x u = insert c S)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro hx
      by_cases hmem : c ∈ diffSet x u
      · right
        rw [← Finset.insert_erase hmem, hx]
      · left
        rwa [Finset.erase_eq_of_notMem hmem] at hx
    · rintro (h | h)
      · rw [h, Finset.erase_eq_of_notMem hS]
      · rw [h, Finset.erase_insert hS]
  have hdisj : Disjoint (Finset.univ.filter (fun x : Word F n => diffSet x u = S))
      (Finset.univ.filter (fun x : Word F n => diffSet x u = insert c S)) := by
    rw [Finset.disjoint_left]
    intro x h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    have hne : insert c S ≠ S := fun hh => hS (Finset.insert_eq_self.mp hh)
    refine hne ?_
    calc insert c S = diffSet x u := h2.symm
      _ = S := h1
  have hq1 : 1 ≤ Fintype.card F := Fintype.card_pos_iff.mpr ⟨(0 : F)⟩
  have hgoal : (Fintype.card F - 1) ^ S.card
        + (Fintype.card F - 1) ^ S.card * (Fintype.card F - 1)
      = Fintype.card F * (Fintype.card F - 1) ^ S.card := by
    calc (Fintype.card F - 1) ^ S.card
          + (Fintype.card F - 1) ^ S.card * (Fintype.card F - 1)
        = (Fintype.card F - 1) ^ S.card * 1
          + (Fintype.card F - 1) ^ S.card * (Fintype.card F - 1) := by rw [mul_one]
      _ = (Fintype.card F - 1) ^ S.card * (1 + (Fintype.card F - 1)) := by rw [← mul_add]
      _ = (Fintype.card F - 1) ^ S.card * Fintype.card F := by
            rw [Nat.add_comm, Nat.sub_add_cancel hq1]
      _ = Fintype.card F * (Fintype.card F - 1) ^ S.card := by rw [mul_comm]
  rw [hsplit, Finset.card_union_of_disjoint hdisj, card_sphere_fiber, card_sphere_fiber,
    Finset.card_insert_of_notMem hS, pow_succ]
  exact hgoal

/-- `(internal, Appendix — the invariant count behind `#theorem 17#`)` — the number
of words that disagree with `u` in at most `s` coordinates *other than* `c`:

`|{x | |D(x,u) \ {c}| ≤ s}| = q · Σ_{i≤s} C(n−1,i)(q−1)^i`.

Split by the value `i` of the invariant `|D(x,u) \ {c}|` (`Finset.range (s+1)`) and,
inside, by the disagreement set `S = D(x,u) \ {c}`, which ranges over the `i`-subsets
of `{c}ᶜ`: each contributes `card_fiber_erase`, i.e. `q·(q−1)^i`, and there are
`C(n−1,i)` of them (`Finset.card_powersetCard`, with `({c}ᶜ).card = n−1`). -/
theorem card_filter_erase_le {F : Type*} [Zero F] [Fintype F] [DecidableEq F] {n : ℕ}
    (u : Word F n) (c : Fin n) (s : ℕ) :
    (Finset.univ.filter (fun x : Word F n => ((diffSet x u).erase c).card ≤ s)).card
      = Fintype.card F *
        (∑ i ∈ Finset.range (s + 1), (n - 1).choose i * (Fintype.card F - 1) ^ i) := by
  classical
  have hpartition : (Finset.univ.filter (fun x : Word F n => ((diffSet x u).erase c).card ≤ s))
      = (Finset.range (s + 1)).biUnion
          (fun i => Finset.univ.filter fun x : Word F n => ((diffSet x u).erase c).card = i) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Finset.mem_range]
    constructor
    · intro hx
      exact ⟨_, Nat.lt_succ_of_le hx, rfl⟩
    · rintro ⟨i, hi, hix⟩
      rw [hix]
      exact Nat.le_of_lt_succ hi
  have hdisj1 : Set.PairwiseDisjoint (fun i => i ∈ Finset.range (s + 1))
      (fun i => Finset.univ.filter fun x : Word F n => ((diffSet x u).erase c).card = i) := by
    intro i _ j _ hij
    change Disjoint (Finset.univ.filter fun x : Word F n => ((diffSet x u).erase c).card = i)
      (Finset.univ.filter fun x : Word F n => ((diffSet x u).erase c).card = j)
    rw [Finset.disjoint_left]
    intro x hx hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    exact hij (hx.symm.trans hy)
  have hstep : ∀ i, (Finset.univ.filter
        (fun x : Word F n => ((diffSet x u).erase c).card = i)).card
      = (n - 1).choose i * (Fintype.card F * (Fintype.card F - 1) ^ i) := by
    intro i
    have hsplit : (Finset.univ.filter (fun x : Word F n => ((diffSet x u).erase c).card = i))
        = (({c}ᶜ : Finset (Fin n)).powersetCard i).biUnion
            (fun S => Finset.univ.filter fun x : Word F n => (diffSet x u).erase c = S) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
        Finset.mem_powersetCard]
      constructor
      · intro hx
        refine ⟨(diffSet x u).erase c, ⟨?_, hx⟩, rfl⟩
        intro j hj
        rw [Finset.mem_compl]
        intro hjc
        rw [Finset.mem_erase] at hj
        exact hj.1 (Finset.mem_singleton.mp hjc)
      · rintro ⟨S, ⟨-, hcard⟩, hxS⟩
        rw [hxS]
        exact hcard
    have hdisj2 : Set.PairwiseDisjoint (fun S => S ∈ ({c}ᶜ : Finset (Fin n)).powersetCard i)
        (fun S => Finset.univ.filter fun x : Word F n => (diffSet x u).erase c = S) := by
      intro S _ T _ hne
      change Disjoint (Finset.univ.filter fun x : Word F n => (diffSet x u).erase c = S)
        (Finset.univ.filter fun x : Word F n => (diffSet x u).erase c = T)
      rw [Finset.disjoint_left]
      intro x hx hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
      exact hne (hx.symm.trans hy)
    have hcard2 : (Finset.univ.filter (fun x : Word F n => ((diffSet x u).erase c).card = i)).card
        = ∑ S ∈ ({c}ᶜ : Finset (Fin n)).powersetCard i,
            (Finset.univ.filter fun x : Word F n => (diffSet x u).erase c = S).card := by
      rw [hsplit]
      exact Finset.card_biUnion (s := ({c}ᶜ : Finset (Fin n)).powersetCard i)
        (t := fun S => Finset.univ.filter fun x : Word F n => (diffSet x u).erase c = S)
        hdisj2
    rw [hcard2]
    have hterm : ∀ S ∈ ({c}ᶜ : Finset (Fin n)).powersetCard i,
        (Finset.univ.filter fun x : Word F n => (diffSet x u).erase c = S).card
          = Fintype.card F * (Fintype.card F - 1) ^ i := by
      intro S hS
      rw [card_fiber_erase u (by
        intro hc
        have h1 := (Finset.mem_powersetCard.mp hS).1 hc
        rw [Finset.mem_compl] at h1
        exact h1 (Finset.mem_singleton_self c)), (Finset.mem_powersetCard.mp hS).2]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_powersetCard,
      Finset.card_compl, Fintype.card_fin, Finset.card_singleton, smul_eq_mul]
  calc (Finset.univ.filter (fun x : Word F n => ((diffSet x u).erase c).card ≤ s)).card
      = ((Finset.range (s + 1)).biUnion
          (fun i => Finset.univ.filter fun x : Word F n => ((diffSet x u).erase c).card = i)).card := by
        rw [hpartition]
    _ = ∑ i ∈ Finset.range (s + 1),
          (Finset.univ.filter fun x : Word F n => ((diffSet x u).erase c).card = i).card :=
        Finset.card_biUnion (s := Finset.range (s + 1))
          (t := fun i => Finset.univ.filter fun x : Word F n => ((diffSet x u).erase c).card = i)
          hdisj1
    _ = Fintype.card F *
          (∑ i ∈ Finset.range (s + 1), (n - 1).choose i * (Fintype.card F - 1) ^ i) := by
        rw [Finset.sum_congr rfl fun i _ => hstep i]
        have hfactor : ∀ i ∈ Finset.range (s + 1),
            (n - 1).choose i * (Fintype.card F * (Fintype.card F - 1) ^ i)
              = Fintype.card F * ((n - 1).choose i * (Fintype.card F - 1) ^ i) :=
          fun i _ => by ring
        rw [Finset.sum_congr rfl hfactor, ← Finset.mul_sum]

/-- `(internal, Appendix — the intersection step of `#theorem 17#`)` — for two words
at Hamming distance one, the two radius-`t` balls meet in exactly
`q · Σ_{i≤t−1} C(n−1,i)(q−1)^i` words.

`mem_ball_inter_iff_of_dist_one` turns membership in the intersection into
`|D(x,u) \ {c}| + 1 ≤ t`, which is exactly what `card_filter_erase_le` counts
(`t ≥ 1`; for `t = 0` the filter is empty and the empty sum is `0`). -/
theorem card_ball_inter_dist_one {F : Type*} [Zero F] [Fintype F] [DecidableEq F] {n : ℕ}
    (u v : Word F n) (t : ℕ) (h : hammingDist u v = 1) :
    (ball u t ∩ ball v t).card =
      Fintype.card F *
        (∑ i ∈ Finset.range t, (n - 1).choose i * (Fintype.card F - 1) ^ i) := by
  classical
  obtain ⟨c, hc⟩ := exists_diffSet_eq_singleton h
  have hset : ball u t ∩ ball v t
      = Finset.univ.filter (fun x : Word F n => ((diffSet x u).erase c).card + 1 ≤ t) := by
    ext x
    rw [mem_ball_inter_iff_of_dist_one hc]
    simp
  rw [hset]
  rcases Nat.eq_zero_or_pos t with ht0 | htpos
  · subst ht0
    have hemp : (Finset.univ.filter fun x : Word F n =>
        ((diffSet x u).erase c).card + 1 ≤ 0) = ∅ := by
      refine Finset.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      omega
    rw [hemp, Finset.card_empty]
    simp
  · have hfil : (Finset.univ.filter fun x : Word F n =>
        ((diffSet x u).erase c).card + 1 ≤ t)
        = Finset.univ.filter fun x : Word F n => ((diffSet x u).erase c).card ≤ t - 1 := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    rw [hfil, card_filter_erase_le u c (t - 1), Nat.sub_add_cancel htpos]

/-! ### Appendix — two balls at distance two (`#lemma 14#`)

The paper proves `#lemma 14#` by normalising to `u₁ = 0`, `u₂ = (1,1,0,…,0)` and
splitting on the first two coordinates of `x`.  Writing `c₁, c₂` for the two
coordinates in which `u` and `v` differ and `a = |D(x,u) \ {c₁,c₂}|`:

* outside `{c₁,c₂}` the two centres agree, so each disagreement costs `1` in both
  distances;
* at `c₁` and at `c₂` the centres differ, so each of those coordinates costs `1` in
  exactly one of the two distances.

Hence, in the four cases (agreement of `x` with `u` at `c₁` and at `c₂`), the pairs
`(d(x,u), d(x,v))` are `(a, a+2)`, `(a+1, a+1)`, `(a+1, a+1)`, `(a+2, a)`, so `x`
lies in both balls iff `a + 1 ≤ t` (the two inner cases) or `a + 2 ≤ t` (the two
outer ones).  Counting the `C(n−2,i)` points with `a = i` (each of weight
`(q−1)^i = 1` over `F₂`) gives the paper's
`2 Σ_{i≤t−1} C(n−2,i) + 2 Σ_{i≤t−2} C(n−2,i)`, and Pascal's rule simplifies this to
`2 Σ_{i≤t−1} C(n−1,i)`. -/

/-- `(internal, Appendix — cardinal bookkeeping for `#lemma 14#`)` — erasing two
*distinct* coordinates from a finset removes each of them at most once: the size of
the doubly erased set plus the two membership indicators is the original size. -/
theorem card_erase_erase_add {α : Type*} [DecidableEq α] {s : Finset α} {c₁ c₂ : α}
    (hne : c₁ ≠ c₂) :
    ((s.erase c₁).erase c₂).card + (if c₁ ∈ s then 1 else 0) + (if c₂ ∈ s then 1 else 0)
      = s.card := by
  classical
  by_cases h1 : c₁ ∈ s <;> by_cases h2 : c₂ ∈ s
  · have h21 : c₂ ∈ s.erase c₁ := Finset.mem_erase.mpr ⟨hne.symm, h2⟩
    have e1 : ((s.erase c₁).erase c₂).card + 1 = (s.erase c₁).card :=
      Finset.card_erase_add_one h21
    have e2 : (s.erase c₁).card + 1 = s.card := Finset.card_erase_add_one h1
    simp only [h1, h2, ↓reduceIte]
    omega
  · have h21 : c₂ ∉ s.erase c₁ := fun hh => h2 (Finset.mem_of_mem_erase hh)
    rw [Finset.erase_eq_of_notMem h21]
    have e2 : (s.erase c₁).card + 1 = s.card := Finset.card_erase_add_one h1
    simp only [h1, h2, ↓reduceIte]
    omega
  · rw [Finset.erase_eq_of_notMem h1]
    have e2 : (s.erase c₂).card + 1 = s.card := Finset.card_erase_add_one h2
    simp only [h1, h2, ↓reduceIte]
    omega
  · have he : ((s.erase c₁).erase c₂) = s := by
      rw [Finset.erase_eq_of_notMem h1, Finset.erase_eq_of_notMem h2]
    rw [he]
    simp only [h1, h2, ↓reduceIte]
    omega

/-- `(internal, Appendix — over `F₂`, for `#lemma 14#`)` — in `F₂` there is only one
point other than `a`, so `x ≠ a ↔ x = b` whenever `a ≠ b`.  This is what turns "`x`
agrees with `u` at `c₁`" into "`x` disagrees with `v` at `c₁`". -/
theorem zmod2_ne_iff_eq (a b x : ZMod 2) (h : a ≠ b) : (x ≠ a ↔ x = b) := by
  revert a b x
  decide

/-- `(internal, Appendix — the two special coordinates of `#lemma 14#`)` — over
`F₂`, two words at Hamming distance two differ in exactly two coordinates
`c₁ ≠ c₂`. -/
theorem exists_diffSet_eq_pair {n : ℕ} {u v : Word (ZMod 2) n} (h : hammingDist u v = 2) :
    ∃ c₁ c₂ : Fin n, c₁ ≠ c₂ ∧ diffSet u v = {c₁, c₂} := by
  have hcard : (diffSet u v).card = 2 := by
    rw [← hammingDist_eq_card_diffSet]
    exact h
  obtain ⟨c₁, c₂, hne, hpair⟩ := Finset.card_eq_two.mp hcard
  exact ⟨c₁, c₂, hne, hpair⟩

/-- `(internal, Appendix — the characterisation behind `#lemma 14#`)` — if `u` and
`v` differ exactly in `c₁` and `c₂`, then `x` lies in both balls `B(u,t)`, `B(v,t)`
iff `|D(x,u) \ {c₁,c₂}| + 1 ≤ t` when exactly one of `c₁`, `c₂` is a disagreement of
`x` with `u`, and iff `|D(x,u) \ {c₁,c₂}| + 2 ≤ t` when both or neither is — that is
the dichotomy encoded by the `if … then 2 else 1` below. -/
theorem mem_ball_inter_iff_dist_two {n t : ℕ} {u v x : Word (ZMod 2) n} {c₁ c₂ : Fin n}
    (hne : c₁ ≠ c₂) (hc : diffSet u v = {c₁, c₂}) :
    x ∈ ball u t ∩ ball v t ↔
      ((diffSet x u).erase c₁ |>.erase c₂).card +
        (if c₁ ∈ diffSet x u ↔ c₂ ∈ diffSet x u then 2 else 1) ≤ t := by
  classical
  have huv₁ : u c₁ ≠ v c₁ := by
    have : c₁ ∈ diffSet u v := by rw [hc]; simp
    simpa [diffSet] using this
  have huv₂ : u c₂ ≠ v c₂ := by
    have : c₂ ∈ diffSet u v := by rw [hc]; simp
    simpa [diffSet] using this
  have hout : ∀ j : Fin n, j ≠ c₁ → j ≠ c₂ → u j = v j := by
    intro j hj1 hj2
    by_contra hne'
    have hmem : j ∈ diffSet u v := by simp [diffSet, hne']
    rw [hc] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h
    · exact hj1 h
    · exact hj2 h
  have hswap₁ : c₁ ∈ diffSet x v ↔ c₁ ∉ diffSet x u := by
    simp only [diffSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [zmod2_ne_iff_eq (v c₁) (u c₁) (x c₁) huv₁.symm]
    exact (not_not (a := x c₁ = u c₁)).symm
  have hswap₂ : c₂ ∈ diffSet x v ↔ c₂ ∉ diffSet x u := by
    simp only [diffSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [zmod2_ne_iff_eq (v c₂) (u c₂) (x c₂) huv₂.symm]
    exact (not_not (a := x c₂ = u c₂)).symm
  have herase : ((diffSet x v).erase c₁).erase c₂ = ((diffSet x u).erase c₁).erase c₂ := by
    ext j
    simp only [Finset.mem_erase, diffSet, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hj2, hj1, hjv⟩
      exact ⟨hj2, hj1, fun hju => hjv (hju.trans (hout j hj1 hj2))⟩
    · rintro ⟨hj2, hj1, hju⟩
      exact ⟨hj2, hj1, fun hjv => hju (hjv.trans (hout j hj1 hj2).symm)⟩
  have hdu : hammingDist x u
      = ((diffSet x u).erase c₁ |>.erase c₂).card
        + (if c₁ ∈ diffSet x u then 1 else 0) + (if c₂ ∈ diffSet x u then 1 else 0) := by
    rw [hammingDist_eq_card_diffSet]
    exact (card_erase_erase_add hne).symm
  have hb₁ : (if c₁ ∈ diffSet x v then (1:ℕ) else 0)
      = 1 - (if c₁ ∈ diffSet x u then 1 else 0) := by
    by_cases h : c₁ ∈ diffSet x u
    · have h' : c₁ ∉ diffSet x v := fun hh => (hswap₁.mp hh) h
      simp [h, h']
    · have h' : c₁ ∈ diffSet x v := hswap₁.mpr h
      simp [h, h']
  have hb₂ : (if c₂ ∈ diffSet x v then (1:ℕ) else 0)
      = 1 - (if c₂ ∈ diffSet x u then 1 else 0) := by
    by_cases h : c₂ ∈ diffSet x u
    · have h' : c₂ ∉ diffSet x v := fun hh => (hswap₂.mp hh) h
      simp [h, h']
    · have h' : c₂ ∈ diffSet x v := hswap₂.mpr h
      simp [h, h']
  have hdv : hammingDist x v
      = ((diffSet x u).erase c₁ |>.erase c₂).card
        + (1 - (if c₁ ∈ diffSet x u then 1 else 0))
        + (1 - (if c₂ ∈ diffSet x u then 1 else 0)) := by
    rw [hammingDist_eq_card_diffSet, (card_erase_erase_add (s := diffSet x v) hne).symm,
      herase, hb₁, hb₂]
  simp only [Finset.mem_inter, ball, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hdu, hdv]
  by_cases p : c₁ ∈ diffSet x u <;> by_cases q : c₂ ∈ diffSet x u <;> simp [p, q] <;> omega

/-- `(internal, Appendix — counting step of `#lemma 14#`)` — the number of subsets
`S ⊆ s` with `|S| + k ≤ t` is the truncated binomial sum `Σ_{i ≤ t−k} C(|s|,i)`;
the cases `k = 1` and `k = 2` used below are the paper's `Σ_{i≤t−1}` and
`Σ_{i≤t−2}`. -/
theorem card_powerset_filter_add_le {α : Type*} [DecidableEq α] (s : Finset α) (k t : ℕ) :
    (s.powerset.filter (fun S => S.card + k ≤ t)).card
      = ∑ i ∈ Finset.range (t + 1 - k), s.card.choose i := by
  classical
  have hset : s.powerset.filter (fun S => S.card + k ≤ t)
      = (Finset.range (t + 1 - k)).biUnion (fun i => s.powersetCard i) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_biUnion, Finset.mem_range,
      Finset.mem_powersetCard]
    constructor
    · rintro ⟨hsub, hcard⟩
      refine ⟨S.card, ?_, hsub, rfl⟩
      rw [Nat.lt_sub_iff_add_lt]
      omega
    · rintro ⟨i, hi, hsub, hcard⟩
      refine ⟨hsub, ?_⟩
      rw [← hcard, Nat.lt_sub_iff_add_lt] at hi
      omega
  have hdisj : Set.PairwiseDisjoint (fun i => i ∈ Finset.range (t + 1 - k))
      (fun i => s.powersetCard i) := by
    intro i _ j _ hij
    change Disjoint (s.powersetCard i) (s.powersetCard j)
    rw [Finset.disjoint_left]
    intro S hi hj
    rw [Finset.mem_powersetCard] at hi hj
    exact hij (hi.2.symm.trans hj.2)
  rw [hset, Finset.card_biUnion hdisj]
  exact Finset.sum_congr rfl (fun i _ => Finset.card_powersetCard i s)

/-- `(internal, Appendix — Pascal's rule, summed)`` — `Σ_{i≤t} C(n,i) =
Σ_{i≤t} C(n−1,i) + Σ_{i≤t−1} C(n−1,i)`: summing Pascal's rule
`C(n,i) = C(n−1,i−1) + C(n−1,i)` along the top index. -/
theorem sum_range_choose_succ (n t : ℕ) (hn : 1 ≤ n) :
    (∑ i ∈ Finset.range (t + 1), n.choose i)
      = (∑ i ∈ Finset.range (t + 1), (n - 1).choose i)
        + (∑ i ∈ Finset.range t, (n - 1).choose i) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hpascal : n.choose (t + 1) = (n - 1).choose t + (n - 1).choose (t + 1) := by
      have h := Nat.choose_succ_succ (n - 1) t
      have hsucc : (n - 1).succ = n := by omega
      rwa [hsucc] at h
    rw [Finset.sum_range_succ (fun i => n.choose i) (t + 1), ih, hpascal]
    rw [Finset.sum_range_succ (fun i => (n - 1).choose i) (t + 1),
      Finset.sum_range_succ (fun i => (n - 1).choose i) t]
    ring

/-- `(internal, Appendix — the final simplification of `#lemma 14#`)` — the form of
summed Pascal's rule used at the end of the paper's proof:
`Σ_{i≤t−1} C(n−1,i) = Σ_{i≤t−1} C(n−2,i) + Σ_{i≤t−2} C(n−2,i)`. -/
theorem sum_range_choose_pred {n t : ℕ} (hn : 2 ≤ n) :
    (∑ i ∈ Finset.range t, (n - 1).choose i)
      = (∑ i ∈ Finset.range t, (n - 2).choose i)
        + (∑ i ∈ Finset.range (t - 1), (n - 2).choose i) := by
  rcases Nat.eq_zero_or_pos t with ht | ht
  · subst ht
    simp
  · obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp ht)
    subst hs
    have hsub : (n - 1) - 1 = n - 2 := by omega
    have h := sum_range_choose_succ (n - 1) s (by omega)
    rw [hsub] at h
    simpa using h

/-- `(internal, Appendix — counting step of `#lemma 14#`)` — the number of
*disagreement sets* `D ⊆ Fin n` that are compatible with membership of the
corresponding word in both balls: with `a = |D \ {c₁,c₂}|` the extra cost is `1` when
exactly one of `c₁`, `c₂` lies in `D` and `2` when both or neither do, so
`D` is admissible iff `a + (if c₁ ∈ D ↔ c₂ ∈ D then 2 else 1) ≤ t`.

Splitting by the four possibilities for `c₁, c₂ ∈ D` counts two copies of
`|S| + 1 ≤ t` and two copies of `|S| + 2 ≤ t` as `S` runs over the `i`-subsets of
`{c₁,c₂}ᶜ` (there are `C(n−2,i)` of each), giving the paper's
`2 Σ_{i≤t−1} C(n−2,i) + 2 Σ_{i≤t−2} C(n−2,i)`. -/
theorem card_allowed_dist_two {n t : ℕ} {c₁ c₂ : Fin n} (hne : c₁ ≠ c₂) :
    (Finset.univ.filter (fun D : Finset (Fin n) =>
        ((D.erase c₁).erase c₂).card + (if c₁ ∈ D ↔ c₂ ∈ D then 2 else 1) ≤ t)).card
      = 2 * (∑ i ∈ Finset.range t, (n - 2).choose i)
        + 2 * (∑ i ∈ Finset.range (t - 1), (n - 2).choose i) := by
  classical
  set TC : Finset (Fin n) := ({c₁, c₂} : Finset (Fin n))ᶜ with hTC
  have hc₁TC : c₁ ∉ TC := by rw [hTC]; simp
  have hc₂TC : c₂ ∉ TC := by rw [hTC]; simp
  have hsubTC : ∀ D : Finset (Fin n), c₁ ∉ D → c₂ ∉ D → D ⊆ TC := by
    intro D h1 h2 x hx
    rw [hTC, Finset.mem_compl]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun hh => h1 (hh ▸ hx), fun hh => h2 (hh ▸ hx)⟩
  set F1 : Finset (Finset (Fin n)) := TC.powerset.filter (fun S => S.card + 1 ≤ t) with hF1
  set F2 : Finset (Finset (Fin n)) := TC.powerset.filter (fun S => S.card + 2 ≤ t) with hF2
  have hmemF1 : ∀ S, S ∈ F1 ↔ S ⊆ TC ∧ S.card + 1 ≤ t := by
    intro S; rw [hF1, Finset.mem_filter, Finset.mem_powerset]
  have hmemF2 : ∀ S, S ∈ F2 ↔ S ⊆ TC ∧ S.card + 2 ≤ t := by
    intro S; rw [hF2, Finset.mem_filter, Finset.mem_powerset]
  have hc1 : ∀ S, S ⊆ TC → c₁ ∉ S := fun S hS h => hc₁TC (hS h)
  have hc2 : ∀ S, S ⊆ TC → c₂ ∉ S := fun S hS h => hc₂TC (hS h)
  set X1 : Finset (Finset (Fin n)) := F1.image (fun S => insert c₁ S) with hX1
  set X2 : Finset (Finset (Fin n)) := F1.image (fun S => insert c₂ S) with hX2
  set X3 : Finset (Finset (Fin n)) := F2.image (fun S => S) with hX3
  set X4 : Finset (Finset (Fin n)) := F2.image (fun S => insert c₁ (insert c₂ S)) with hX4
  have hX1mem : ∀ D : Finset (Fin n), D ∈ X1 ↔ c₁ ∈ D ∧ c₂ ∉ D ∧
      (((D.erase c₁).erase c₂).card + (if c₁ ∈ D ↔ c₂ ∈ D then 2 else 1) ≤ t) := by
    intro D
    rw [hX1, Finset.mem_image]
    constructor
    · rintro ⟨S, hS, rfl⟩
      rw [hmemF1] at hS
      obtain ⟨hSTC, hScard⟩ := hS
      have hS1 := hc1 S hSTC
      have hS2 := hc2 S hSTC
      have hins : ((insert c₁ S).erase c₁).erase c₂ = S := by
        rw [Finset.erase_insert hS1, Finset.erase_eq_of_notMem hS2]
      have hnotin : c₂ ∉ insert c₁ S := by
        simp only [Finset.mem_insert, not_or]
        exact ⟨hne.symm, hS2⟩
      refine ⟨Finset.mem_insert_self _ _, hnotin, ?_⟩
      have hiff : ¬ (c₁ ∈ insert c₁ S ↔ c₂ ∈ insert c₁ S) := by simp [hnotin]
      rw [hins, ite_eq_right hiff]
      exact hScard
    · rintro ⟨h1, h2, hcond⟩
      have hiff : ¬ (c₁ ∈ D ↔ c₂ ∈ D) := by simp [h1, h2]
      have hcond' : ((D.erase c₁).erase c₂).card + 1 ≤ t := by
        have := hcond
        rwa [ite_eq_right hiff] at this
      have herase : (D.erase c₁).erase c₂ = D.erase c₁ :=
        Finset.erase_eq_of_notMem (fun h => h2 (Finset.mem_of_mem_erase h))
      refine ⟨D.erase c₁, ?_, ?_⟩
      · rw [hmemF1]
        exact ⟨hsubTC _ (Finset.notMem_erase _ _)
          (fun h => h2 (Finset.mem_of_mem_erase h)), by rw [← herase]; exact hcond'⟩
      · exact Finset.insert_erase h1
  have hX2mem : ∀ D : Finset (Fin n), D ∈ X2 ↔ c₂ ∈ D ∧ c₁ ∉ D ∧
      (((D.erase c₁).erase c₂).card + (if c₁ ∈ D ↔ c₂ ∈ D then 2 else 1) ≤ t) := by
    intro D
    rw [hX2, Finset.mem_image]
    constructor
    · rintro ⟨S, hS, rfl⟩
      rw [hmemF1] at hS
      obtain ⟨hSTC, hScard⟩ := hS
      have hS1 := hc1 S hSTC
      have hS2 := hc2 S hSTC
      have hc1ins : c₁ ∉ insert c₂ S := by
        simp only [Finset.mem_insert, not_or]
        exact ⟨hne, hS1⟩
      have hins : ((insert c₂ S).erase c₁).erase c₂ = S := by
        rw [Finset.erase_eq_of_notMem hc1ins, Finset.erase_insert hS2]
      refine ⟨Finset.mem_insert_self _ _, hc1ins, ?_⟩
      have hiff : ¬ (c₁ ∈ insert c₂ S ↔ c₂ ∈ insert c₂ S) := by simp [hc1ins]
      rw [hins, ite_eq_right hiff]
      exact hScard
    · rintro ⟨h1, h2, hcond⟩
      have hiff : ¬ (c₁ ∈ D ↔ c₂ ∈ D) := by simp [h1, h2]
      have hcond' : ((D.erase c₁).erase c₂).card + 1 ≤ t := by
        have := hcond
        rwa [ite_eq_right hiff] at this
      have herase : (D.erase c₁).erase c₂ = D.erase c₂ := by
        rw [Finset.erase_eq_of_notMem h2]
      refine ⟨D.erase c₂, ?_, ?_⟩
      · rw [hmemF1]
        exact ⟨hsubTC _ (fun h => h2 (Finset.mem_of_mem_erase h))
          (Finset.notMem_erase _ _), by rw [← herase]; exact hcond'⟩
      · exact Finset.insert_erase h1
  have hX3mem : ∀ D : Finset (Fin n), D ∈ X3 ↔ c₁ ∉ D ∧ c₂ ∉ D ∧
      (((D.erase c₁).erase c₂).card + (if c₁ ∈ D ↔ c₂ ∈ D then 2 else 1) ≤ t) := by
    intro D
    rw [hX3, Finset.mem_image]
    constructor
    · rintro ⟨S, hS, rfl⟩
      rw [hmemF2] at hS
      obtain ⟨hSTC, hScard⟩ := hS
      have hS1 := hc1 S hSTC
      have hS2 := hc2 S hSTC
      have hins : (S.erase c₁).erase c₂ = S := by
        rw [Finset.erase_eq_of_notMem hS1, Finset.erase_eq_of_notMem hS2]
      have hiff : (c₁ ∈ S ↔ c₂ ∈ S) := by simp [hS1, hS2]
      refine ⟨hS1, hS2, ?_⟩
      rw [hins, ite_eq_left hiff]
      exact hScard
    · rintro ⟨h1, h2, hcond⟩
      have hiff : (c₁ ∈ D ↔ c₂ ∈ D) := by simp [h1, h2]
      have hcond' : ((D.erase c₁).erase c₂).card + 2 ≤ t := by
        have := hcond
        rwa [ite_eq_left hiff] at this
      have herase : (D.erase c₁).erase c₂ = D := by
        rw [Finset.erase_eq_of_notMem h1, Finset.erase_eq_of_notMem h2]
      refine ⟨D, ?_, rfl⟩
      rw [hmemF2]
      exact ⟨hsubTC D h1 h2, by rw [← herase]; exact hcond'⟩
  have hX4mem : ∀ D : Finset (Fin n), D ∈ X4 ↔ c₁ ∈ D ∧ c₂ ∈ D ∧
      (((D.erase c₁).erase c₂).card + (if c₁ ∈ D ↔ c₂ ∈ D then 2 else 1) ≤ t) := by
    intro D
    rw [hX4, Finset.mem_image]
    constructor
    · rintro ⟨S, hS, rfl⟩
      rw [hmemF2] at hS
      obtain ⟨hSTC, hScard⟩ := hS
      have hS1 := hc1 S hSTC
      have hS2 := hc2 S hSTC
      have hc1ins : c₁ ∉ insert c₂ S := by
        simp only [Finset.mem_insert, not_or]
        exact ⟨hne, hS1⟩
      have hins : ((insert c₁ (insert c₂ S)).erase c₁).erase c₂ = S := by
        rw [Finset.erase_insert hc1ins, Finset.erase_insert hS2]
      have hiff : (c₁ ∈ insert c₁ (insert c₂ S) ↔ c₂ ∈ insert c₁ (insert c₂ S)) := by simp
      refine ⟨Finset.mem_insert_self _ _,
        Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), ?_⟩
      rw [hins, ite_eq_left hiff]
      exact hScard
    · rintro ⟨h1, h2, hcond⟩
      have hiff : (c₁ ∈ D ↔ c₂ ∈ D) := by simp [h1, h2]
      have hcond' : ((D.erase c₁).erase c₂).card + 2 ≤ t := by
        have := hcond
        rwa [ite_eq_left hiff] at this
      have hrec : insert c₁ (insert c₂ ((D.erase c₁).erase c₂)) = D := by
        ext x
        simp only [Finset.mem_insert, Finset.mem_erase]
        constructor
        · rintro (rfl | rfl | ⟨hne2, hne1, hx⟩)
          · exact h1
          · exact h2
          · exact hx
        · intro hx
          rcases eq_or_ne x c₁ with hh | hh
          · exact Or.inl hh
          · rcases eq_or_ne x c₂ with hh' | hh'
            · exact Or.inr (Or.inl hh')
            · exact Or.inr (Or.inr ⟨hh', hh, hx⟩)
      refine ⟨(D.erase c₁).erase c₂, ?_, hrec⟩
      rw [hmemF2]
      refine ⟨hsubTC _ (fun h => (Finset.mem_erase.mp (Finset.mem_erase.mp h).2).1 rfl)
        (fun h => (Finset.mem_erase.mp h).1 rfl), hcond'⟩
  have hAeq : (Finset.univ.filter (fun D : Finset (Fin n) =>
        ((D.erase c₁).erase c₂).card + (if c₁ ∈ D ↔ c₂ ∈ D then 2 else 1) ≤ t))
      = (X1 ∪ X2) ∪ (X3 ∪ X4) := by
    ext D
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      hX1mem D, hX2mem D, hX3mem D, hX4mem D]
    by_cases h1 : c₁ ∈ D <;> by_cases h2 : c₂ ∈ D <;> simp [h1, h2]
  have hcard1 : X1.card = F1.card := by
    rw [hX1]
    refine Finset.card_image_of_injOn ?_
    intro S hS S' hS' heq
    have hS1 := (hmemF1 S).mp (by rw [Finset.mem_coe] at hS; exact hS)
    have hS1' := (hmemF1 S').mp (by rw [Finset.mem_coe] at hS'; exact hS')
    have heq' : insert c₁ S = insert c₁ S' := heq
    have h := congrArg (fun T => T.erase c₁) heq'
    rwa [Finset.erase_insert (hc1 S hS1.1), Finset.erase_insert (hc1 S' hS1'.1)] at h
  have hcard2 : X2.card = F1.card := by
    rw [hX2]
    refine Finset.card_image_of_injOn ?_
    intro S hS S' hS' heq
    have hS1 := (hmemF1 S).mp (by rw [Finset.mem_coe] at hS; exact hS)
    have hS1' := (hmemF1 S').mp (by rw [Finset.mem_coe] at hS'; exact hS')
    have heq' : insert c₂ S = insert c₂ S' := heq
    have h := congrArg (fun T => T.erase c₂) heq'
    rwa [Finset.erase_insert (hc2 S hS1.1), Finset.erase_insert (hc2 S' hS1'.1)] at h
  have hcard3 : X3.card = F2.card := by
    rw [hX3]
    simp
  have hcard4 : X4.card = F2.card := by
    rw [hX4]
    refine Finset.card_image_of_injOn ?_
    intro S hS S' hS' heq
    have hS2 := (hmemF2 S).mp (by rw [Finset.mem_coe] at hS; exact hS)
    have hS2' := (hmemF2 S').mp (by rw [Finset.mem_coe] at hS'; exact hS')
    have hc1S := hc1 S hS2.1
    have hc2S := hc2 S hS2.1
    have hc1S' := hc1 S' hS2'.1
    have hc2S' := hc2 S' hS2'.1
    have heq' : insert c₁ (insert c₂ S) = insert c₁ (insert c₂ S') := heq
    have e1 : insert c₂ S = insert c₂ S' := by
      have h := congrArg (fun T => T.erase c₁) heq'
      have hc1ins : c₁ ∉ insert c₂ S := by
        simp only [Finset.mem_insert, not_or]
        exact ⟨hne, hc1S⟩
      have hc1ins' : c₁ ∉ insert c₂ S' := by
        simp only [Finset.mem_insert, not_or]
        exact ⟨hne, hc1S'⟩
      rwa [Finset.erase_insert hc1ins, Finset.erase_insert hc1ins'] at h
    have h := congrArg (fun T => T.erase c₂) e1
    rwa [Finset.erase_insert hc2S, Finset.erase_insert hc2S'] at h
  have hdisj12 : Disjoint X1 X2 := by
    rw [Finset.disjoint_left]
    intro D h1 h2
    rw [hX1mem D] at h1
    rw [hX2mem D] at h2
    exact h1.2.1 h2.1
  have hdisj34 : Disjoint X3 X4 := by
    rw [Finset.disjoint_left]
    intro D h3 h4
    rw [hX3mem D] at h3
    rw [hX4mem D] at h4
    exact h3.1 h4.1
  have hdisj : Disjoint (X1 ∪ X2) (X3 ∪ X4) := by
    rw [Finset.disjoint_left]
    intro D hD hD'
    rw [Finset.mem_union] at hD hD'
    rcases hD with h1 | h2 <;> rcases hD' with h3 | h4
    · rw [hX1mem D] at h1; rw [hX3mem D] at h3; exact h3.1 h1.1
    · rw [hX1mem D] at h1; rw [hX4mem D] at h4; exact h1.2.1 h4.2.1
    · rw [hX2mem D] at h2; rw [hX3mem D] at h3; exact h3.2.1 h2.1
    · rw [hX2mem D] at h2; rw [hX4mem D] at h4; exact h2.2.1 h4.1
  have hF1card : F1.card = ∑ i ∈ Finset.range t, (n - 2).choose i := by
    rw [hF1, card_powerset_filter_add_le TC 1 t, Nat.add_sub_cancel]
    have hTCcard : TC.card = n - 2 := by
      rw [hTC, Finset.card_compl, Fintype.card_fin, Finset.card_pair hne]
    rw [hTCcard]
  have hF2card : F2.card = ∑ i ∈ Finset.range (t - 1), (n - 2).choose i := by
    rw [hF2, card_powerset_filter_add_le TC 2 t]
    have hsub : t + 1 - 2 = t - 1 := by omega
    have hTCcard : TC.card = n - 2 := by
      rw [hTC, Finset.card_compl, Fintype.card_fin, Finset.card_pair hne]
    rw [hsub, hTCcard]
  rw [hAeq, Finset.card_union_of_disjoint hdisj, Finset.card_union_of_disjoint hdisj12,
    Finset.card_union_of_disjoint hdisj34, hcard1, hcard2, hcard3, hcard4, hF1card, hF2card]
  ring

/-! ### Appendix — three balls at pairwise distances `1, 1, 2` (`#theorem 18#`)

The paper proves `#theorem 18#` in two steps:

1. the **triple** intersection of the three balls: writing `w` for the number of
   disagreements of `x` with `u₁` outside the two special coordinates, the paper's
   four cases give `|B(u₁,t) ∩ B(u₂,t) ∩ B(u₃,t)| = #₁ + 3#₂`, where
   `#₁ = Σ_{i≤t−1}C(n−2,i)` (both special coordinates agree) and
   `#₂ = Σ_{i≤t−2}C(n−2,i)` (the other three patterns), i.e.
   `C(n−2,t−1) + 4Σ_{i≤t−2}C(n−2,i)`;
2. **inclusion–exclusion** over the three balls, in which each *pairwise*
   intersection is `2Σ_{i≤t−1}C(n−1,i)` — `#theorem 17#`'s intersection for the two
   pairs at distance one and `#lemma 14#` for the pair at distance two.

Over `F₂` a word and its disagreement set with `u₁` determine each other, so both
steps are counting problems for *sets* `D ⊆ Fin n`, and the counting lemmas below
are shared with `#theorem 19#`. -/

/-- `(internal, Appendix — 3-set inclusion–exclusion in additive form, for
`#theorem 18#`)` — `|A ∪ B ∪ C| + |A∩B| + |A∩C| + |B∩C| = |A| + |B| + |C| +
|A∩B∩C|`.  This is the subtraction-free form of the paper's inclusion–exclusion,
so no `ℕ`-truncation can arise. -/
theorem card_union_three_add {α : Type*} [DecidableEq α] (A B C : Finset α) :
    (A ∪ B ∪ C).card + (A ∩ B).card + (A ∩ C).card + (B ∩ C).card
      = A.card + B.card + C.card + (A ∩ B ∩ C).card := by
  classical
  have e1 : (A ∪ B).card + (A ∩ B).card = A.card + B.card :=
    Finset.card_union_add_card_inter A B
  have e2 : ((A ∪ B) ∪ C).card + ((A ∪ B) ∩ C).card = (A ∪ B).card + C.card :=
    Finset.card_union_add_card_inter (A ∪ B) C
  have hUC : (A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C) := by
    ext x; simp only [Finset.mem_inter, Finset.mem_union]; tauto
  have e3 : ((A ∩ C) ∪ (B ∩ C)).card + ((A ∩ C) ∩ (B ∩ C)).card
      = (A ∩ C).card + (B ∩ C).card :=
    Finset.card_union_add_card_inter (A ∩ C) (B ∩ C)
  have hT : (A ∩ C) ∩ (B ∩ C) = A ∩ B ∩ C := by
    ext x; simp only [Finset.mem_inter]; tauto
  rw [hUC] at e2
  rw [hT] at e3
  omega

/-- `(internal, Appendix — over `F₂`)` — the element of `F₂` other than `x` is
`x + 1`. -/
theorem zmod2_eq_add_one_of_ne {x y : ZMod 2} (h : y ≠ x) : y = x + 1 := by
  revert x y
  decide

/-- `(internal, Appendix — over `F₂`)` — `x + 1 ≠ x`. -/
theorem zmod2_add_one_ne (x : ZMod 2) : x + 1 ≠ x := by
  revert x
  decide

/-- `(internal, Appendix — over `F₂`, for `#theorem 18#` and `#theorem 19#`)` —
every prescribed disagreement set is realised by a word (`x j = u j + 1` exactly on
`D`): over `F₂` the map `x ↦ D(x,u)` is onto. -/
theorem diffSet_surjective {n : ℕ} (u : Word (ZMod 2) n) :
    Function.Surjective fun x : Word (ZMod 2) n => diffSet x u := by
  intro D
  refine ⟨fun j => if j ∈ D then u j + 1 else u j, ?_⟩
  ext j
  simp only [diffSet, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases h : j ∈ D
  · rw [ite_eq_left h]; exact iff_of_true (zmod2_add_one_ne (u j)) h
  · rw [ite_eq_right h]; exact iff_of_false (fun hh => hh rfl) h

/-- `(internal, Appendix — over `F₂`, for `#theorem 18#` and `#theorem 19#`)` — over
`F₂` the disagreement set with `u` determines the word: `x ↦ D(x,u)` is injective. -/
theorem diffSet_injective {n : ℕ} (u : Word (ZMod 2) n) :
    Function.Injective fun x : Word (ZMod 2) n => diffSet x u := by
  intro x y hxy
  have hxy' : diffSet x u = diffSet y u := hxy
  funext j
  by_cases hj : j ∈ diffSet x u
  · have hx : x j ≠ u j := by simpa [diffSet] using hj
    have hy : y j ≠ u j := by
      have : j ∈ diffSet y u := by rw [← hxy']; exact hj
      simpa [diffSet] using this
    rw [zmod2_eq_add_one_of_ne hx, zmod2_eq_add_one_of_ne hy]
  · have hx : x j = u j := by
      by_contra hne
      exact hj (by simp [diffSet, hne])
    have hy : y j = u j := by
      have hnj : j ∉ diffSet y u := by rw [← hxy']; exact hj
      by_contra hne
      exact hnj (by simp [diffSet, hne])
    rw [hx, hy]

/-- `(internal, Appendix — over `F₂`, for `#theorem 18#` and `#theorem 19#`)` —
counting words by a property of their disagreement set with `u` is the same as
counting the disagreement sets themselves (the previous two lemmas). -/
theorem card_filter_diffSet {n : ℕ} (u : Word (ZMod 2) n) (p : Finset (Fin n) → Prop)
    [DecidablePred p] :
    (Finset.univ.filter fun x : Word (ZMod 2) n => p (diffSet x u)).card
      = (Finset.univ.filter p).card := by
  classical
  refine Finset.card_bij (fun x _ => diffSet x u) ?_ ?_ ?_
  · intro x hx; simpa using hx
  · intro x₁ _ x₂ _ h; exact diffSet_injective u h
  · intro D hD
    obtain ⟨x, rfl⟩ := diffSet_surjective u D
    exact ⟨x, by simpa using hD, rfl⟩

/-- `(internal, Appendix — for `#theorem 18#`)` — erasing two coordinates is
removing them: `(D.erase c₁).erase c₂ = D \ {c₁, c₂}`. -/
theorem erase_erase_eq_sdiff_pair {α : Type*} [DecidableEq α] (D : Finset α) (a b : α) :
    (D.erase a).erase b = D \ {a, b} := by
  ext x
  simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
  tauto

/-- `(internal, Appendix — the fibre split used by `#theorem 18#`)` — the subsets
`D` whose intersection with `T` is a fixed `P ⊆ T`.  They are in bijection with the
subsets `S ⊆ Tᶜ` (`S ↦ S ∪ P`, inverse `D ↦ D \ T`), the bijection preserving
`|D \ T|`; hence the two families below have the same cardinality. -/
theorem card_filter_inter_eq_card {α : Type*} [Fintype α] [DecidableEq α]
    (T P : Finset α) (hP : P ⊆ T) (s t : ℕ) :
    (Finset.univ.filter (fun D : Finset α => D ∩ T = P ∧ (D \ T).card + s ≤ t)).card
      = ((Tᶜ).powerset.filter (fun S => S.card + s ≤ t)).card := by
  classical
  have hST : ∀ S ⊆ Tᶜ, S ∩ T = ∅ := by
    intro S hS
    ext x
    simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
    intro hx hxT
    exact (Finset.mem_compl.mp (hS hx)) hxT
  have hdisjST : ∀ S ⊆ Tᶜ, Disjoint S T := fun S hS =>
    Finset.disjoint_left.mpr fun x hx hxT => (Finset.mem_compl.mp (hS hx)) hxT
  have hSP : ∀ S ⊆ Tᶜ, (S ∪ P) ∩ T = P := by
    intro S hS
    rw [Finset.union_inter_distrib_right, hST S hS, Finset.inter_eq_left.mpr hP,
      Finset.empty_union]
  have hdiff : ∀ S ⊆ Tᶜ, (S ∪ P) \ T = S := by
    intro S hS
    rw [Finset.union_sdiff_distrib, Finset.sdiff_eq_self_iff_disjoint.mpr (hdisjST S hS),
      Finset.sdiff_eq_empty_iff_subset.mpr hP, Finset.union_empty]
  refine Finset.card_bij' (fun D _ => D \ T) (fun S _ => S ∪ P) ?_ ?_ ?_ ?_
  · intro D hD
    have hD' : D ∩ T = P ∧ (D \ T).card + s ≤ t := by simpa using hD
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨fun x hx => by rw [Finset.mem_compl]; exact (Finset.mem_sdiff.mp hx).2, hD'.2⟩
  · intro S hS
    have hS' : S ⊆ Tᶜ ∧ S.card + s ≤ t := by simpa using hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hSP S hS'.1, by rw [hdiff S hS'.1]; exact hS'.2⟩
  · intro D hD
    have hD' : D ∩ T = P ∧ (D \ T).card + s ≤ t := by simpa using hD
    rw [← hD'.1, Finset.sdiff_union_inter]
  · intro S hS
    have hS' : S ⊆ Tᶜ ∧ S.card + s ≤ t := by simpa using hS
    exact hdiff S hS'.1

/-! ### Appendix — the triple intersection of `#theorem 18#`

For the paper's Theorem 18 the three centres are `u`, `v = u + e₁` and `w = u + e₂`
(they differ from `u` in the single coordinates `c₁`, `c₂`), so for a word `x`,
with `a = |D(x,u) \ {c₁,c₂}|` and `bᵢ = [cᵢ ∈ D(x,u)] ∈ {0,1}`:

* `d(x,u) = a + b₁ + b₂`,
* `d(x,v) = a + (1−b₁) + b₂` (at `c₁` exactly one of the two distances picks up `1`),
* `d(x,w) = a + b₁ + (1−b₂)`.

Hence `x` lies in all three balls iff `a + (if b₁ ∨ b₂ then 2 else 1) ≤ t`: the
paper's four cases, with the "agrees at both special coordinates" pattern costing
`1` and the other three patterns costing `2`.  Over `F₂` the disagreement set
determines the word, so the count is the number of admissible sets
`D ⊆ Fin n`. -/

/-- `(internal, Appendix — the characterisation behind `#theorem 18#`)` — if `u`, `v`
differ only in `c₁` and `u`, `w` differ only in `c₂` (with `c₁ ≠ c₂`), then `x` is in
all three balls iff `|D(x,u) \ {c₁,c₂}| + 2 ≤ t` when `x` disagrees with `u` in at
least one of `c₁`, `c₂`, and `+ 1 ≤ t` when it agrees with `u` in both. -/
theorem mem_ball_inter_three_iff {n t : ℕ} {u v w x : Word (ZMod 2) n} {c₁ c₂ : Fin n}
    (hne : c₁ ≠ c₂) (h1 : diffSet u v = {c₁}) (h2 : diffSet u w = {c₂}) :
    x ∈ ball u t ∩ ball v t ∩ ball w t ↔
      ((diffSet x u).erase c₁ |>.erase c₂).card +
        (if c₁ ∈ diffSet x u ∨ c₂ ∈ diffSet x u then 2 else 1) ≤ t := by
  classical
  have huv : u c₁ ≠ v c₁ := by
    have : c₁ ∈ diffSet u v := by rw [h1]; simp
    simpa [diffSet] using this
  have huw : u c₂ ≠ w c₂ := by
    have : c₂ ∈ diffSet u w := by rw [h2]; simp
    simpa [diffSet] using this
  have houtv : ∀ j : Fin n, j ≠ c₁ → u j = v j := by
    intro j hj
    by_contra hne'
    have hmem : j ∈ diffSet u v := by simp [diffSet, hne']
    rw [h1] at hmem
    exact hj (Finset.mem_singleton.mp hmem)
  have houtw : ∀ j : Fin n, j ≠ c₂ → u j = w j := by
    intro j hj
    by_contra hne'
    have hmem : j ∈ diffSet u w := by simp [diffSet, hne']
    rw [h2] at hmem
    exact hj (Finset.mem_singleton.mp hmem)
  have hswapv : c₁ ∈ diffSet x v ↔ c₁ ∉ diffSet x u := by
    simp only [diffSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [zmod2_ne_iff_eq (v c₁) (u c₁) (x c₁) huv.symm]
    exact (not_not (a := x c₁ = u c₁)).symm
  have hswapw : c₂ ∈ diffSet x w ↔ c₂ ∉ diffSet x u := by
    simp only [diffSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [zmod2_ne_iff_eq (w c₂) (u c₂) (x c₂) huw.symm]
    exact (not_not (a := x c₂ = u c₂)).symm
  have hsame₂v : c₂ ∈ diffSet x v ↔ c₂ ∈ diffSet x u := by
    have hvc : v c₂ = u c₂ := (houtv c₂ hne.symm).symm
    simp only [diffSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hvc]
  have hsame₁w : c₁ ∈ diffSet x w ↔ c₁ ∈ diffSet x u := by
    have hwc : w c₁ = u c₁ := (houtw c₁ hne).symm
    simp only [diffSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hwc]
  have herasev : ((diffSet x v).erase c₁).erase c₂ = ((diffSet x u).erase c₁).erase c₂ := by
    ext j
    simp only [Finset.mem_erase, diffSet, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hj2, hj1, hjv⟩
      exact ⟨hj2, hj1, fun hju => hjv (hju.trans (houtv j hj1))⟩
    · rintro ⟨hj2, hj1, hju⟩
      exact ⟨hj2, hj1, fun hjv => hju (hjv.trans (houtv j hj1).symm)⟩
  have herasew : ((diffSet x w).erase c₁).erase c₂ = ((diffSet x u).erase c₁).erase c₂ := by
    ext j
    simp only [Finset.mem_erase, diffSet, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hj2, hj1, hjw⟩
      exact ⟨hj2, hj1, fun hju => hjw (hju.trans (houtw j hj2))⟩
    · rintro ⟨hj2, hj1, hju⟩
      exact ⟨hj2, hj1, fun hjw => hju (hjw.trans (houtw j hj2).symm)⟩
  have hdu : hammingDist x u = ((diffSet x u).erase c₁ |>.erase c₂).card
      + (if c₁ ∈ diffSet x u then 1 else 0) + (if c₂ ∈ diffSet x u then 1 else 0) := by
    rw [hammingDist_eq_card_diffSet]
    exact (card_erase_erase_add hne).symm
  have hv1 : (if c₁ ∈ diffSet x v then (1:ℕ) else 0)
      = 1 - (if c₁ ∈ diffSet x u then 1 else 0) := by
    by_cases h : c₁ ∈ diffSet x u
    · have h' : c₁ ∉ diffSet x v := fun hh => (hswapv.mp hh) h
      simp [h, h']
    · have h' : c₁ ∈ diffSet x v := hswapv.mpr h
      simp [h, h']
  have hv2 : (if c₂ ∈ diffSet x v then (1:ℕ) else 0)
      = (if c₂ ∈ diffSet x u then 1 else 0) := by
    by_cases h : c₂ ∈ diffSet x u
    · have h' : c₂ ∈ diffSet x v := hsame₂v.mpr h
      simp [h, h']
    · have h' : c₂ ∉ diffSet x v := fun hh => h (hsame₂v.mp hh)
      simp [h, h']
  have hw1 : (if c₁ ∈ diffSet x w then (1:ℕ) else 0)
      = (if c₁ ∈ diffSet x u then 1 else 0) := by
    by_cases h : c₁ ∈ diffSet x u
    · have h' : c₁ ∈ diffSet x w := hsame₁w.mpr h
      simp [h, h']
    · have h' : c₁ ∉ diffSet x w := fun hh => h (hsame₁w.mp hh)
      simp [h, h']
  have hw2 : (if c₂ ∈ diffSet x w then (1:ℕ) else 0)
      = 1 - (if c₂ ∈ diffSet x u then 1 else 0) := by
    by_cases h : c₂ ∈ diffSet x u
    · have h' : c₂ ∉ diffSet x w := fun hh => (hswapw.mp hh) h
      simp [h, h']
    · have h' : c₂ ∈ diffSet x w := hswapw.mpr h
      simp [h, h']
  have hdv : hammingDist x v = ((diffSet x u).erase c₁ |>.erase c₂).card
      + (1 - (if c₁ ∈ diffSet x u then 1 else 0)) + (if c₂ ∈ diffSet x u then 1 else 0) := by
    rw [hammingDist_eq_card_diffSet, (card_erase_erase_add (s := diffSet x v) hne).symm,
      herasev, hv1, hv2]
  have hdw : hammingDist x w = ((diffSet x u).erase c₁ |>.erase c₂).card
      + (if c₁ ∈ diffSet x u then 1 else 0) + (1 - (if c₂ ∈ diffSet x u then 1 else 0)) := by
    rw [hammingDist_eq_card_diffSet, (card_erase_erase_add (s := diffSet x w) hne).symm,
      herasew, hw1, hw2]
  simp only [Finset.mem_inter, ball, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hdu, hdv, hdw]
  by_cases p : c₁ ∈ diffSet x u <;> by_cases q : c₂ ∈ diffSet x u <;> simp [p, q] <;> omega

/-- `(internal, Appendix — counting step of `#theorem 18#`)` — the number of
disagreement sets admissible for the triple intersection: pattern "`c₁, c₂` both
outside `D`" costs `1`, the other three patterns cost `2`, so the count is
`#{S ⊆ {c₁,c₂}ᶜ : |S| + 1 ≤ t} + 3 · #{S ⊆ {c₁,c₂}ᶜ : |S| + 2 ≤ t}`. -/
theorem card_allowed_pair_three {n t : ℕ} {c₁ c₂ : Fin n} (hne : c₁ ≠ c₂) :
    (Finset.univ.filter (fun D : Finset (Fin n) =>
        ((D.erase c₁).erase c₂).card + (if c₁ ∈ D ∨ c₂ ∈ D then 2 else 1) ≤ t)).card
      = ((({c₁, c₂} : Finset (Fin n))ᶜ).powerset.filter (fun S => S.card + 1 ≤ t)).card
        + 3 * ((({c₁, c₂} : Finset (Fin n))ᶜ).powerset.filter (fun S => S.card + 2 ≤ t)).card := by
  classical
  set T : Finset (Fin n) := {c₁, c₂} with hT
  have hc₁T : c₁ ∈ T := by rw [hT]; simp
  have hc₂T : c₂ ∈ T := by rw [hT]; simp
  have hempty : ∀ D : Finset (Fin n), D ∩ T = ∅ ↔ c₁ ∉ D ∧ c₂ ∉ D := by
    intro D
    constructor
    · intro h
      refine ⟨fun hc => ?_, fun hc => ?_⟩
      · have hm : c₁ ∈ D ∩ T := Finset.mem_inter.mpr ⟨hc, hc₁T⟩
        rw [h] at hm
        exact Finset.notMem_empty c₁ hm
      · have hm : c₂ ∈ D ∩ T := Finset.mem_inter.mpr ⟨hc, hc₂T⟩
        rw [h] at hm
        exact Finset.notMem_empty c₂ hm
    · rintro ⟨h1, h2⟩
      rw [Finset.eq_empty_iff_forall_notMem]
      intro x hx
      rw [Finset.mem_inter] at hx
      rcases (by simpa [hT] using hx.2 : x = c₁ ∨ x = c₂) with rfl | rfl
      · exact h1 hx.1
      · exact h2 hx.1
  have hnonempty : ∀ D : Finset (Fin n), D ∩ T ≠ ∅ ↔ c₁ ∈ D ∨ c₂ ∈ D := by
    intro D
    constructor
    · intro h
      by_contra hc
      exact h ((hempty D).mpr (not_or.mp hc))
    · intro h hcon
      exact not_or.mpr ((hempty D).mp hcon) h
  have hDT : ∀ D : Finset (Fin n), D ∩ T = ∅ → (D.erase c₁).erase c₂ = D := by
    intro D h
    rw [erase_erase_eq_sdiff_pair]
    exact Finset.sdiff_eq_self_iff_disjoint.mpr (Finset.disjoint_iff_inter_eq_empty.mpr h)
  have hsubTC : ∀ D : Finset (Fin n), D ∩ T = ∅ → D ⊆ Tᶜ := by
    intro D h x hx
    rw [Finset.mem_compl]
    intro hxT
    have hm : x ∈ D ∩ T := Finset.mem_inter.mpr ⟨hx, hxT⟩
    rw [h] at hm
    exact Finset.notMem_empty x hm
  have hsplit : (Finset.univ.filter (fun D : Finset (Fin n) =>
        ((D.erase c₁).erase c₂).card + (if c₁ ∈ D ∨ c₂ ∈ D then 2 else 1) ≤ t))
      = (Finset.univ.filter (fun D : Finset (Fin n) => D ∩ T = ∅ ∧
            ((D.erase c₁).erase c₂).card + (if c₁ ∈ D ∨ c₂ ∈ D then 2 else 1) ≤ t))
        ∪ (Finset.univ.filter (fun D : Finset (Fin n) => D ∩ T ≠ ∅ ∧
            ((D.erase c₁).erase c₂).card + (if c₁ ∈ D ∨ c₂ ∈ D then 2 else 1) ≤ t)) := by
    ext D
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    tauto
  have hdisj : Disjoint (Finset.univ.filter (fun D : Finset (Fin n) => D ∩ T = ∅ ∧
        ((D.erase c₁).erase c₂).card + (if c₁ ∈ D ∨ c₂ ∈ D then 2 else 1) ≤ t))
      (Finset.univ.filter (fun D : Finset (Fin n) => D ∩ T ≠ ∅ ∧
        ((D.erase c₁).erase c₂).card + (if c₁ ∈ D ∨ c₂ ∈ D then 2 else 1) ≤ t)) := by
    rw [Finset.disjoint_left]
    intro D h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    exact h2.1 h1.1
  have hgroup1 : (Finset.univ.filter (fun D : Finset (Fin n) => D ∩ T = ∅ ∧
        ((D.erase c₁).erase c₂).card + (if c₁ ∈ D ∨ c₂ ∈ D then 2 else 1) ≤ t)).card
      = (Tᶜ.powerset.filter (fun S => S.card + 1 ≤ t)).card := by
    have hfilter : (Finset.univ.filter (fun D : Finset (Fin n) => D ∩ T = ∅ ∧
          ((D.erase c₁).erase c₂).card + (if c₁ ∈ D ∨ c₂ ∈ D then 2 else 1) ≤ t))
        = (Tᶜ.powerset.filter (fun S => S.card + 1 ≤ t)) := by
      ext D
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powerset]
      constructor
      · rintro ⟨hemp, hcond⟩
        refine ⟨hsubTC D hemp, ?_⟩
        have hif : ¬ (c₁ ∈ D ∨ c₂ ∈ D) := not_or.mpr ((hempty D).mp hemp)
        rw [hDT D hemp, ite_eq_right hif] at hcond
        exact hcond
      · rintro ⟨hsub, hcard⟩
        have hemp : D ∩ T = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro x hx
          rw [Finset.mem_inter] at hx
          exact (Finset.mem_compl.mp (hsub hx.1)) hx.2
        refine ⟨hemp, ?_⟩
        have hif : ¬ (c₁ ∈ D ∨ c₂ ∈ D) := not_or.mpr ((hempty D).mp hemp)
        rw [hDT D hemp, ite_eq_right hif]
        exact hcard
    rw [hfilter]
  have hgroup2 : (Finset.univ.filter (fun D : Finset (Fin n) => D ∩ T ≠ ∅ ∧
        ((D.erase c₁).erase c₂).card + (if c₁ ∈ D ∨ c₂ ∈ D then 2 else 1) ≤ t)).card
      = 3 * (Tᶜ.powerset.filter (fun S => S.card + 2 ≤ t)).card := by
    have hpart : (Finset.univ.filter (fun D : Finset (Fin n) => D ∩ T ≠ ∅ ∧
          ((D.erase c₁).erase c₂).card + (if c₁ ∈ D ∨ c₂ ∈ D then 2 else 1) ≤ t))
        = (T.powerset.filter (fun P => P ≠ ∅)).biUnion (fun P =>
            Finset.univ.filter (fun D : Finset (Fin n) => D ∩ T = P ∧
              ((D.erase c₁).erase c₂).card + (if c₁ ∈ D ∨ c₂ ∈ D then 2 else 1) ≤ t)) := by
      ext D
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
      constructor
      · rintro ⟨hne0, hcond⟩
        exact ⟨D ∩ T, ⟨Finset.mem_powerset.mpr Finset.inter_subset_right, hne0⟩, rfl, hcond⟩
      · rintro ⟨P, ⟨hPT, hPne⟩, hDP, hcond⟩
        exact ⟨by rw [hDP]; exact hPne, hcond⟩
    have hdisj2 : Set.PairwiseDisjoint (fun P => P ∈ T.powerset.filter (fun P => P ≠ ∅))
        (fun P => Finset.univ.filter (fun D : Finset (Fin n) => D ∩ T = P ∧
          ((D.erase c₁).erase c₂).card + (if c₁ ∈ D ∨ c₂ ∈ D then 2 else 1) ≤ t)) := by
      intro P _ P' _ hne'
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro D h1 h2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      exact hne' (h1.1.symm.trans h2.1)
    rw [hpart, Finset.card_biUnion hdisj2]
    have hfiber : ∀ P ∈ T.powerset.filter (fun P => P ≠ ∅),
        (Finset.univ.filter (fun D : Finset (Fin n) => D ∩ T = P ∧
          ((D.erase c₁).erase c₂).card + (if c₁ ∈ D ∨ c₂ ∈ D then 2 else 1) ≤ t)).card
          = (Tᶜ.powerset.filter (fun S => S.card + 2 ≤ t)).card := by
      intro P hP
      have hPT : P ⊆ T := Finset.mem_powerset.mp (Finset.mem_filter.mp hP).1
      have hPne : P ≠ ∅ := (Finset.mem_filter.mp hP).2
      have hcongr : (Finset.univ.filter (fun D : Finset (Fin n) => D ∩ T = P ∧
            ((D.erase c₁).erase c₂).card + (if c₁ ∈ D ∨ c₂ ∈ D then 2 else 1) ≤ t))
          = (Finset.univ.filter (fun D : Finset (Fin n) => D ∩ T = P ∧
            (D \ T).card + 2 ≤ t)) := by
        ext D
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨hDP, hcond⟩
          have hif : c₁ ∈ D ∨ c₂ ∈ D := (hnonempty D).mp (by rw [hDP]; exact hPne)
          rw [ite_eq_left hif, erase_erase_eq_sdiff_pair, ← hT] at hcond
          exact ⟨hDP, hcond⟩
        · rintro ⟨hDP, hcard⟩
          have hif : c₁ ∈ D ∨ c₂ ∈ D := (hnonempty D).mp (by rw [hDP]; exact hPne)
          rw [ite_eq_left hif, erase_erase_eq_sdiff_pair, ← hT]
          exact ⟨hDP, hcard⟩
      rw [hcongr]
      exact card_filter_inter_eq_card T P hPT 2 t
    rw [Finset.sum_congr rfl hfiber, Finset.sum_const, smul_eq_mul]
    have hcard : (T.powerset.filter (fun P => P ≠ ∅)).card = 3 := by
      have h₁ : T.powerset.filter (fun P => P ≠ ∅) = T.powerset.erase ∅ := by
        ext P
        simp only [Finset.mem_filter, Finset.mem_erase]
        tauto
      rw [h₁, Finset.card_erase_of_mem (Finset.mem_powerset.mpr (Finset.empty_subset T))]
      have hT2 : T.card = 2 := by rw [hT]; exact Finset.card_pair hne
      rw [Finset.card_powerset, hT2]
      norm_num
    rw [hcard]
  rw [hsplit, Finset.card_union_of_disjoint hdisj, hgroup1, hgroup2]

/-- `(internal, Appendix — the triple-intersection step of `#theorem 18#`)` — for
three binary words `u`, `v`, `w` with `d(u,v) = d(u,w) = 1` in distinct coordinates
and `d(v,w) = 2`,
`|B(u,t) ∩ B(v,t) ∩ B(w,t)| = Σ_{i<t}C(n−2,i) + 3Σ_{i<t−1}C(n−2,i)`, the paper's
`#₁ + 3#₂` (equal to `C(n−2,t−1) + 4Σ_{i<t−2}C(n−2,i)` for `t ≥ 1`). -/
theorem card_ball_inter_three {n t : ℕ} {u v w : Word (ZMod 2) n} {c₁ c₂ : Fin n}
    (hne : c₁ ≠ c₂) (h1 : diffSet u v = {c₁}) (h2 : diffSet u w = {c₂}) :
    (ball u t ∩ ball v t ∩ ball w t).card
      = (∑ i ∈ Finset.range t, (n - 2).choose i)
        + 3 * (∑ i ∈ Finset.range (t - 1), (n - 2).choose i) := by
  classical
  set TC : Finset (Fin n) := ({c₁, c₂} : Finset (Fin n))ᶜ with hTC
  have hTCcard : TC.card = n - 2 := by
    rw [hTC, Finset.card_compl, Fintype.card_fin, Finset.card_pair hne]
  have hset : ball u t ∩ ball v t ∩ ball w t
      = Finset.univ.filter (fun x : Word (ZMod 2) n =>
          ((diffSet x u).erase c₁ |>.erase c₂).card +
            (if c₁ ∈ diffSet x u ∨ c₂ ∈ diffSet x u then 2 else 1) ≤ t) := by
    ext x
    rw [mem_ball_inter_three_iff hne h1 h2]
    simp
  have hkey := card_filter_diffSet u (fun D : Finset (Fin n) =>
      ((D.erase c₁).erase c₂).card + (if c₁ ∈ D ∨ c₂ ∈ D then 2 else 1) ≤ t)
  rw [hset, hkey, card_allowed_pair_three hne]
  rw [← hTC]
  rw [card_powerset_filter_add_le TC 1 t, Nat.add_sub_cancel,
    card_powerset_filter_add_le TC 2 t]
  have hsub : t + 1 - 2 = t - 1 := by omega
  rw [hsub, hTCcard]

/-! ### Appendix — two balls at distance three (`#theorem 19#`)

The paper's Theorem 19 normalises to `u₁ = 0`, `u₂ = (1,1,1,0,…,0)` and splits on
`x₁, x₂, x₃`.  With `T = {c₁,c₂,c₃}` the three differing coordinates, a word `x` is
described by `S = D(x,u) \ T` and the pattern `P = D(x,u) ∩ T`; then
`d(x,u) = |S| + |P|` and `d(x,v) = |S| + (3 − |P|)`, so `x` lies in both balls iff
`|S| + max(|P|, 3 − |P|) ≤ t` — the paper's table (`|P| = 0` and `|P| = 3` cost
`3`, the other six patterns cost `2`).  Over `F₂` the disagreement set determines
the word, so the count is a count of admissible sets. -/

/-- `(internal, Appendix — the three special coordinates of `#theorem 19#`)` — over
`F₂`, two words at Hamming distance three differ in exactly three coordinates
`c₁, c₂, c₃`. -/
theorem exists_diffSet_eq_triple {n : ℕ} {u v : Word (ZMod 2) n} (h : hammingDist u v = 3) :
    ∃ c₁ c₂ c₃ : Fin n, c₁ ≠ c₂ ∧ c₁ ≠ c₃ ∧ c₂ ≠ c₃ ∧ diffSet u v = {c₁, c₂, c₃} := by
  have hcard : (diffSet u v).card = 3 := by
    rw [← hammingDist_eq_card_diffSet]
    exact h
  obtain ⟨c₁, c₂, c₃, h12, h13, h23, hset⟩ := Finset.card_eq_three.mp hcard
  exact ⟨c₁, c₂, c₃, h12, h13, h23, hset⟩

/-- `(internal, Appendix — the characterisation behind `#theorem 19#`)` — if `u` and
`v` differ exactly in `c₁, c₂, c₃`, then `x` lies in both balls iff
`|D(x,u) \ {c₁,c₂,c₃}| + max |D(x,u) ∩ {c₁,c₂,c₃}| (3 − |D(x,u) ∩ {c₁,c₂,c₃}|) ≤ t`
(agreement in `k` of the three coordinates costs `max k (3−k)`, the paper's table). -/
theorem mem_ball_inter_iff_dist_three {n t : ℕ} {u v x : Word (ZMod 2) n} {c₁ c₂ c₃ : Fin n}
    (h : hammingDist u v = 3) (hc : diffSet u v = {c₁, c₂, c₃}) :
    x ∈ ball u t ∩ ball v t ↔
      (diffSet x u \ {c₁, c₂, c₃}).card +
        max ((diffSet x u ∩ {c₁, c₂, c₃}).card) (3 - (diffSet x u ∩ {c₁, c₂, c₃}).card) ≤ t := by
  classical
  set T : Finset (Fin n) := {c₁, c₂, c₃} with hT
  have hcardT : T.card = 3 := by
    rw [← hc, ← hammingDist_eq_card_diffSet, h]
  have hout : ∀ j : Fin n, j ∉ T → u j = v j := by
    intro j hj
    by_contra hne'
    have hmem : j ∈ diffSet u v := by simp [diffSet, hne']
    rw [hc] at hmem
    exact hj hmem
  have hswap : ∀ j ∈ T, (j ∈ diffSet x v ↔ j ∉ diffSet x u) := by
    intro j hj
    have huv : u j ≠ v j := by
      have hmem : j ∈ diffSet u v := by rw [hc]; exact hj
      simpa [diffSet] using hmem
    simp only [diffSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [zmod2_ne_iff_eq (v j) (u j) (x j) huv.symm]
    exact (not_not (a := x j = u j)).symm
  have herase : diffSet x v \ T = diffSet x u \ T := by
    ext j
    rw [Finset.mem_sdiff, Finset.mem_sdiff]
    constructor
    · rintro ⟨hjv, hjT⟩
      refine ⟨?_, hjT⟩
      have hv : x j ≠ v j := by simpa [diffSet] using hjv
      rw [← hout j hjT] at hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hv⟩
    · rintro ⟨hju, hjT⟩
      refine ⟨?_, hjT⟩
      have hu : x j ≠ u j := by simpa [diffSet] using hju
      rw [hout j hjT] at hu
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hu⟩
  have hinter : diffSet x v ∩ T = T \ (diffSet x u ∩ T) := by
    ext j
    simp only [Finset.mem_inter, Finset.mem_sdiff]
    constructor
    · rintro ⟨hjv, hjT⟩
      exact ⟨hjT, fun h => ((hswap j hjT).mp hjv) h.1⟩
    · rintro ⟨hjT, hjnot⟩
      exact ⟨(hswap j hjT).mpr (fun hju => hjnot ⟨hju, hjT⟩), hjT⟩
  have hdu : hammingDist x u = (diffSet x u ∩ T).card + (diffSet x u \ T).card := by
    rw [hammingDist_eq_card_diffSet]
    exact (Finset.card_inter_add_card_sdiff (diffSet x u) T).symm
  have hdv : hammingDist x v = (3 - (diffSet x u ∩ T).card) + (diffSet x u \ T).card := by
    rw [hammingDist_eq_card_diffSet,
      (Finset.card_inter_add_card_sdiff (diffSet x v) T).symm, hinter,
      Finset.card_sdiff, Finset.inter_eq_left.mpr Finset.inter_subset_right, hcardT, herase]
  simp only [Finset.mem_inter, ball, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hdu, hdv]
  omega

/-- `(internal, Appendix — counting step of `#theorem 19#`)` — the admissible
disagreement sets of the distance-three intersection: with `T = {c₁,c₂,c₃}`, the
patterns `D ∩ T = ∅` and `D ∩ T = T` cost `3` while the other six patterns cost `2`,
so the count is `2 · #{S ⊆ Tᶜ : |S| + 3 ≤ t} + 6 · #{S ⊆ Tᶜ : |S| + 2 ≤ t}` (the
index `T.powerset.filter (· ≠ ∅ ∧ · ≠ T)` has six elements). -/
theorem card_allowed_triple {n t : ℕ} {c₁ c₂ c₃ : Fin n}
    (hcard3 : ({c₁, c₂, c₃} : Finset (Fin n)).card = 3) :
    (Finset.univ.filter (fun D : Finset (Fin n) =>
        (D \ ({c₁, c₂, c₃} : Finset (Fin n))).card +
          max ((D ∩ ({c₁, c₂, c₃} : Finset (Fin n))).card)
              (3 - (D ∩ ({c₁, c₂, c₃} : Finset (Fin n))).card) ≤ t)).card
      = 2 * ((({c₁, c₂, c₃} : Finset (Fin n))ᶜ).powerset.filter (fun S => S.card + 3 ≤ t)).card
        + 6 * ((({c₁, c₂, c₃} : Finset (Fin n))ᶜ).powerset.filter (fun S => S.card + 2 ≤ t)).card := by
  classical
  set T : Finset (Fin n) := {c₁, c₂, c₃} with hT
  set TC : Finset (Fin n) := Tᶜ with hTC
  have hcardT : T.card = 3 := hcard3
  have hTne : T ≠ ∅ := by
    intro h
    have := hcardT
    rw [h] at this
    exact absurd this (by norm_num)
  have hpart : (Finset.univ.filter (fun D : Finset (Fin n) =>
        (D \ T).card + max ((D ∩ T).card) (3 - (D ∩ T).card) ≤ t))
      = (Finset.univ.filter (fun D : Finset (Fin n) => D ∩ T = ∅ ∧
            (D \ T).card + max ((D ∩ T).card) (3 - (D ∩ T).card) ≤ t))
        ∪ ((Finset.univ.filter (fun D : Finset (Fin n) => D ∩ T = T ∧
              (D \ T).card + max ((D ∩ T).card) (3 - (D ∩ T).card) ≤ t))
            ∪ (T.powerset.filter (fun P => P ≠ ∅ ∧ P ≠ T)).biUnion (fun P =>
                Finset.univ.filter (fun D : Finset (Fin n) => D ∩ T = P ∧
                  (D \ T).card + max ((D ∩ T).card) (3 - (D ∩ T).card) ≤ t))) := by
    ext D
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_biUnion, Finset.mem_powerset]
    constructor
    · intro hc
      by_cases hemp : D ∩ T = ∅
      · exact Or.inl ⟨hemp, hc⟩
      · by_cases hfull : D ∩ T = T
        · exact Or.inr (Or.inl ⟨hfull, hc⟩)
        · exact Or.inr (Or.inr ⟨D ∩ T, ⟨Finset.inter_subset_right, hemp, hfull⟩, rfl, hc⟩)
    · rintro (⟨hemp, hc⟩ | ⟨hfull, hc⟩ | ⟨P, ⟨hPT, hPne, hPneT⟩, hDP, hc⟩)
      · exact hc
      · exact hc
      · exact hc
  have hdisj1 : Disjoint (Finset.univ.filter (fun D : Finset (Fin n) => D ∩ T = ∅ ∧
        (D \ T).card + max ((D ∩ T).card) (3 - (D ∩ T).card) ≤ t))
      ((Finset.univ.filter (fun D : Finset (Fin n) => D ∩ T = T ∧
            (D \ T).card + max ((D ∩ T).card) (3 - (D ∩ T).card) ≤ t))
        ∪ (T.powerset.filter (fun P => P ≠ ∅ ∧ P ≠ T)).biUnion (fun P =>
              Finset.univ.filter (fun D : Finset (Fin n) => D ∩ T = P ∧
                (D \ T).card + max ((D ∩ T).card) (3 - (D ∩ T).card) ≤ t))) := by
    rw [Finset.disjoint_left]
    intro D h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_biUnion, Finset.mem_powerset] at h1 h2
    rcases h2 with h2 | ⟨P, ⟨hPT, hPne, hPneT⟩, hDP, hc⟩
    · rw [h1.1] at h2
      exact hTne h2.1.symm
    · rw [← hDP, h1.1] at hPne
      exact hPne rfl
  have hdisj2 : Disjoint (Finset.univ.filter (fun D : Finset (Fin n) => D ∩ T = T ∧
        (D \ T).card + max ((D ∩ T).card) (3 - (D ∩ T).card) ≤ t))
      ((T.powerset.filter (fun P => P ≠ ∅ ∧ P ≠ T)).biUnion (fun P =>
              Finset.univ.filter (fun D : Finset (Fin n) => D ∩ T = P ∧
                (D \ T).card + max ((D ∩ T).card) (3 - (D ∩ T).card) ≤ t))) := by
    rw [Finset.disjoint_left]
    intro D h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Finset.mem_powerset] at h1 h2
    obtain ⟨P, ⟨hPT, hPne, hPneT⟩, hDP, hc⟩ := h2
    rw [← hDP, h1.1] at hPneT
    exact hPneT rfl
  have hG0 : (Finset.univ.filter (fun D : Finset (Fin n) => D ∩ T = ∅ ∧
        (D \ T).card + max ((D ∩ T).card) (3 - (D ∩ T).card) ≤ t)).card
      = (TC.powerset.filter (fun S => S.card + 3 ≤ t)).card := by
    have hfilter : (Finset.univ.filter (fun D : Finset (Fin n) => D ∩ T = ∅ ∧
          (D \ T).card + max ((D ∩ T).card) (3 - (D ∩ T).card) ≤ t))
        = (Finset.univ.filter (fun D : Finset (Fin n) => D ∩ T = ∅ ∧ (D \ T).card + 3 ≤ t)) := by
      ext D
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hemp, hcond⟩
        refine ⟨hemp, ?_⟩
        rw [hemp, Finset.card_empty] at hcond
        simpa using hcond
      · rintro ⟨hemp, hcond⟩
        refine ⟨hemp, ?_⟩
        rw [hemp, Finset.card_empty]
        simpa using hcond
    rw [hfilter, card_filter_inter_eq_card T ∅ (Finset.empty_subset T) 3 t]
  have hGT : (Finset.univ.filter (fun D : Finset (Fin n) => D ∩ T = T ∧
        (D \ T).card + max ((D ∩ T).card) (3 - (D ∩ T).card) ≤ t)).card
      = (TC.powerset.filter (fun S => S.card + 3 ≤ t)).card := by
    have hfilter : (Finset.univ.filter (fun D : Finset (Fin n) => D ∩ T = T ∧
          (D \ T).card + max ((D ∩ T).card) (3 - (D ∩ T).card) ≤ t))
        = (Finset.univ.filter (fun D : Finset (Fin n) => D ∩ T = T ∧ (D \ T).card + 3 ≤ t)) := by
      ext D
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hfull, hcond⟩
        refine ⟨hfull, ?_⟩
        rw [hfull, hcardT] at hcond
        simpa using hcond
      · rintro ⟨hfull, hcond⟩
        refine ⟨hfull, ?_⟩
        rw [hfull, hcardT]
        simpa using hcond
    rw [hfilter, card_filter_inter_eq_card T T (Finset.Subset.refl T) 3 t]
  have hGmid : ((T.powerset.filter (fun P => P ≠ ∅ ∧ P ≠ T)).biUnion (fun P =>
          Finset.univ.filter (fun D : Finset (Fin n) => D ∩ T = P ∧
            (D \ T).card + max ((D ∩ T).card) (3 - (D ∩ T).card) ≤ t))).card
      = 6 * (TC.powerset.filter (fun S => S.card + 2 ≤ t)).card := by
    have hdisj3 : Set.PairwiseDisjoint (fun P => P ∈ T.powerset.filter (fun P => P ≠ ∅ ∧ P ≠ T))
        (fun P => Finset.univ.filter (fun D : Finset (Fin n) => D ∩ T = P ∧
          (D \ T).card + max ((D ∩ T).card) (3 - (D ∩ T).card) ≤ t)) := by
      intro P _ P' _ hne'
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro D h1 h2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      exact hne' (h1.1.symm.trans h2.1)
    rw [Finset.card_biUnion hdisj3]
    have hfiber : ∀ P ∈ T.powerset.filter (fun P => P ≠ ∅ ∧ P ≠ T),
        (Finset.univ.filter (fun D : Finset (Fin n) => D ∩ T = P ∧
          (D \ T).card + max ((D ∩ T).card) (3 - (D ∩ T).card) ≤ t)).card
          = (TC.powerset.filter (fun S => S.card + 2 ≤ t)).card := by
      intro P hP
      have hPT : P ⊆ T := Finset.mem_powerset.mp (Finset.mem_filter.mp hP).1
      have hPne : P ≠ ∅ := (Finset.mem_filter.mp hP).2.1
      have hPneT : P ≠ T := (Finset.mem_filter.mp hP).2.2
      have hcost : max P.card (3 - P.card) = 2 := by
        have hle : P.card ≤ 3 := by
          have h := Finset.card_le_card hPT
          rwa [hcardT] at h
        have hpos : 1 ≤ P.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hPne)
        have hne3 : P.card ≠ 3 := by
          intro h3
          exact hPneT (Finset.eq_of_subset_of_card_le hPT (by rw [hcardT]; omega))
        have hk : P.card = 1 ∨ P.card = 2 := by omega
        rcases hk with h | h <;> rw [h] <;> norm_num
      have hcongr : (Finset.univ.filter (fun D : Finset (Fin n) => D ∩ T = P ∧
            (D \ T).card + max ((D ∩ T).card) (3 - (D ∩ T).card) ≤ t))
          = (Finset.univ.filter (fun D : Finset (Fin n) => D ∩ T = P ∧ (D \ T).card + 2 ≤ t)) := by
        ext D
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨hDP, hcond⟩
          refine ⟨hDP, ?_⟩
          rw [hDP, hcost] at hcond
          exact hcond
        · rintro ⟨hDP, hcond⟩
          refine ⟨hDP, ?_⟩
          rw [hDP, hcost]
          exact hcond
      rw [hcongr]
      exact card_filter_inter_eq_card T P hPT 2 t
    rw [Finset.sum_congr rfl hfiber, Finset.sum_const, smul_eq_mul]
    have hidx : (T.powerset.filter (fun P => P ≠ ∅ ∧ P ≠ T)).card = 6 := by
      have hset : T.powerset.filter (fun P => P ≠ ∅ ∧ P ≠ T) = (T.powerset.erase ∅).erase T := by
        ext P
        simp only [Finset.mem_filter, Finset.mem_erase]
        constructor
        · rintro ⟨hP, hne0, hneT⟩
          exact ⟨hneT, hne0, hP⟩
        · rintro ⟨hneT, hne0, hP⟩
          exact ⟨hP, hne0, hneT⟩
      rw [hset,
        Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hTne, Finset.mem_powerset.mpr
          (Finset.Subset.refl T)⟩),
        Finset.card_erase_of_mem (Finset.mem_powerset.mpr (Finset.empty_subset T)),
        Finset.card_powerset, hcardT]
      norm_num
    rw [hidx]
  rw [hpart, Finset.card_union_of_disjoint hdisj1, Finset.card_union_of_disjoint hdisj2,
    hG0, hGT, hGmid]
  ring

/-- `(internal, Appendix — the intersection step of `#theorem 19#`)` — for two binary
words at distance three,
`|B(u,t) ∩ B(v,t)| = 2Σ_{i<t−2}C(n−3,i) + 6Σ_{i<t−1}C(n−3,i)`, the paper's
`2#₂ + 6#₁` (equal to `8Σ_{i<t−3}C(n−3,i) + 6C(n−3,t−2)` for `t ≥ 2`). -/
theorem card_ball_inter_dist_three {n t : ℕ} {u v : Word (ZMod 2) n} {c₁ c₂ c₃ : Fin n}
    (h : hammingDist u v = 3) (hc : diffSet u v = {c₁, c₂, c₃}) :
    (ball u t ∩ ball v t).card
      = 2 * (∑ i ∈ Finset.range (t - 2), (n - 3).choose i)
        + 6 * (∑ i ∈ Finset.range (t - 1), (n - 3).choose i) := by
  classical
  set T : Finset (Fin n) := {c₁, c₂, c₃} with hT
  set TC : Finset (Fin n) := Tᶜ with hTC
  have hcard3 : T.card = 3 := by
    rw [← hc, ← hammingDist_eq_card_diffSet, h]
  have hTCcard : TC.card = n - 3 := by
    rw [hTC, Finset.card_compl, Fintype.card_fin, hcard3]
  have hset : ball u t ∩ ball v t = Finset.univ.filter (fun x : Word (ZMod 2) n =>
      (diffSet x u \ T).card + max ((diffSet x u ∩ T).card) (3 - (diffSet x u ∩ T).card) ≤ t) := by
    ext x
    rw [mem_ball_inter_iff_dist_three h (by rw [← hT]; exact hc)]
    simp [hT]
  have hkey := card_filter_diffSet u (fun D : Finset (Fin n) =>
      (D \ T).card + max ((D ∩ T).card) (3 - (D ∩ T).card) ≤ t)
  rw [hset, hkey, card_allowed_triple hcard3,
    card_powerset_filter_add_le TC 3 t, card_powerset_filter_add_le TC 2 t]
  have h3 : t + 1 - 3 = t - 2 := by omega
  have h2 : t + 1 - 2 = t - 1 := by omega
  rw [h3, h2, hTCcard]

/-! ### §VIII-A — the per-coordinate estimate of the Plotkin bounds (`#lemma 13#`,
`#theorem 14#`)

Both Plotkin bounds rest on one counting fact: for `M` words over a `q`-ary alphabet,
the number of pairs of positions carrying *different* symbols is maximised when the
symbols are as evenly distributed as possible.  The weak form needed by
`#theorem 14#` is `Σ_ε n_ε(M − n_ε) ≤ M²(q−1)/q`, i.e. `q·Σ_ε n_ε² ≥ M²` — the
Cauchy–Schwarz inequality, obtained from the doubled sum-of-squares identity
`Σ_{ε,δ}(n_ε − n_δ)² = 2q·Σ n_ε² − 2(Σ n_ε)² ≥ 0`. -/

/-- `(internal, §VIII-A — the Cauchy–Schwarz step of `#theorem 14#`)` — for a
`q`-ary alphabet, `(Σ_ε n_ε)² ≤ q · Σ_ε n_ε²`. -/
theorem sum_sq_le_card_mul_sum_sq {F : Type*} [Fintype F] (n : F → ℕ) :
    (∑ ε, n ε) ^ 2 ≤ Fintype.card F * ∑ ε, n ε ^ 2 := by
  have hA : (∑ ε, n ε) * (∑ ε, n ε) = ∑ ε, ∑ δ, n ε * n δ := by
    rw [Finset.sum_mul_sum]
  have hB : ∑ ε, ∑ δ, (2 * (n ε * n δ)) ≤ ∑ ε, ∑ δ, (n ε ^ 2 + n δ ^ 2) := by
    refine Finset.sum_le_sum fun ε _ => Finset.sum_le_sum fun δ _ => ?_
    nlinarith [sq_nonneg ((n ε : ℤ) - n δ)]
  have hC : ∑ ε, ∑ δ, (2 * (n ε * n δ)) = 2 * ∑ ε, ∑ δ, n ε * n δ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ε _ => ?_
    rw [Finset.mul_sum]
  have hD : ∑ ε, ∑ δ, (n ε ^ 2 + n δ ^ 2)
      = 2 * (Fintype.card F * ∑ ε, n ε ^ 2) := by
    have h1 : ∑ ε, ∑ _δ : F, n ε ^ 2 = Fintype.card F * ∑ ε, n ε ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ε _ => ?_
      rw [Finset.sum_const, smul_eq_mul, Finset.card_univ]
    have h2 : ∑ _ε : F, ∑ δ, n δ ^ 2 = Fintype.card F * ∑ δ, n δ ^ 2 := by
      rw [Finset.sum_const, smul_eq_mul, Finset.card_univ]
    simp only [Finset.sum_add_distrib]
    rw [h1, h2]
    ring
  have key : 2 * ((∑ ε, n ε) * (∑ ε, n ε)) ≤ 2 * (Fintype.card F * ∑ ε, n ε ^ 2) := by
    calc 2 * ((∑ ε, n ε) * (∑ ε, n ε))
        = ∑ ε, ∑ δ, (2 * (n ε * n δ)) := by rw [hA, hC]
      _ ≤ ∑ ε, ∑ δ, (n ε ^ 2 + n δ ^ 2) := hB
      _ = 2 * (Fintype.card F * ∑ ε, n ε ^ 2) := hD
  exact Nat.le_of_mul_le_mul_left (by simpa [pow_two] using key) (by norm_num : 0 < 2)

/-- `(internal, §VIII-A — the per-coordinate estimate of `#theorem 14#`)` — among `M`
positions carrying symbols of a `q`-ary alphabet, the number of ordered pairs of
positions with *different* symbols is at most `M²(q−1)/q`.  With `n_ε` the number of
positions carrying `ε`, the count is `M² − Σ_ε n_ε²` (the equal pairs form the
disjoint union of the squares of the fibres) and `q·Σ_ε n_ε² ≥ M²`
(`sum_sq_le_card_mul_sum_sq`).

The index type is an arbitrary finite type (the codewords of `#theorem 14#` are
indexed by the *messages* `Word F k`, not by `Fin M`); `M = Fintype.card ι`. -/
theorem card_ne_pairs_mul_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : Type*} [Fintype F] [DecidableEq F] (x : ι → F) :
    Fintype.card F * ((Finset.univ : Finset (ι × ι)).filter
        (fun p => x p.1 ≠ x p.2)).card ≤ (Fintype.card ι) ^ 2 * (Fintype.card F - 1) := by
  classical
  set n : F → ℕ := fun ε => (Finset.univ.filter (fun i : ι => x i = ε)).card with hn
  have hset : (Finset.univ.filter (fun p : ι × ι => x p.1 = x p.2))
      = Finset.univ.biUnion (fun ε : F =>
          (Finset.univ.filter (fun i : ι => x i = ε)) ×ˢ
            (Finset.univ.filter (fun j : ι => x j = ε))) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Finset.mem_product]
    constructor
    · intro h
      exact ⟨x p.1, rfl, h.symm⟩
    · rintro ⟨ε, h1, h2⟩
      rw [h1, h2]
  have hdisj : Set.PairwiseDisjoint (fun ε => ε ∈ (Finset.univ : Finset F))
      (fun ε => (Finset.univ.filter (fun i : ι => x i = ε)) ×ˢ
        (Finset.univ.filter (fun j : ι => x j = ε))) := by
    intro ε _ δ _ hne
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro p hp hq
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    exact hne (hp.1.symm.trans hq.1)
  have hcardEq : (Finset.univ.filter (fun p : ι × ι => x p.1 = x p.2)).card
      = ∑ ε, n ε ^ 2 := by
    rw [hset, Finset.card_biUnion hdisj]
    refine Finset.sum_congr rfl fun ε _ => ?_
    rw [Finset.card_product, hn, pow_two]
  have hpart : (Finset.univ.filter (fun p : ι × ι => x p.1 ≠ x p.2)).card
      + (Finset.univ.filter (fun p : ι × ι => x p.1 = x p.2)).card
      = (Fintype.card ι) ^ 2 := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (ι × ι)))
      (p := fun p => x p.1 = x p.2)
    simpa [Finset.card_univ, Fintype.card_prod, pow_two, mul_comm, add_comm] using h
  have hM : Fintype.card ι = ∑ ε, n ε := by
    have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset ι))
      (t := (Finset.univ : Finset F)) (f := x) (fun i _ => Finset.mem_univ _)
    simpa [Finset.card_univ, hn] using h
  have hCS : (Fintype.card ι) ^ 2 ≤ Fintype.card F * ∑ ε, n ε ^ 2 := by
    rw [hM]
    exact sum_sq_le_card_mul_sum_sq n
  rcases Nat.eq_zero_or_pos (Fintype.card F) with hq0 | hqpos
  · rw [hq0]; simp
  · set T := (Fintype.card ι) ^ 2 with hT
    have h1 : T ≤ Fintype.card F * ∑ ε, n ε ^ 2 := hCS
    have h2 : (Finset.univ.filter (fun p : ι × ι => x p.1 ≠ x p.2)).card
        + ∑ ε, n ε ^ 2 = T := by rw [← hcardEq, hpart]
    have h3 : T * (Fintype.card F - 1) = Fintype.card F * T - T := by
      rw [Nat.mul_sub_left_distrib, mul_one, mul_comm T (Fintype.card F)]
    rw [h3]
    have hne_eq : (Finset.univ.filter (fun p : ι × ι => x p.1 ≠ x p.2)).card
        = T - ∑ ε, n ε ^ 2 := by omega
    rw [hne_eq, Nat.mul_sub_left_distrib]
    exact Nat.sub_le_sub_left h1 (Fintype.card F * T)


/-- `(internal, §VIII-A — the *sharp* balanced-distribution estimate of `#lemma 13#`)` —
for `M` positions carrying symbols of a `q`-ary alphabet (`M` = the sum of the
symbol counts `n_ε`), the sum of squares of the counts is minimal when the symbols
are as evenly distributed as possible: with `a = M % q`,
`q · Σ_ε n_ε² ≥ M² + a(q−a)`  (equality for `a` symbols `⌈M/q⌉` times and the
remaining `q−a` symbols `⌊M/q⌋` times).

Proof: with `t = M / q` the pointwise inequality `(n−t)(n−t−1) ≥ 0` (integrality!)
says `n(2t+1) ≤ n² + t(t+1)`; summing over `ε` and using `M = qt + a` gives
`(2t+1)M − q·t(t+1) ≤ Σ n_ε²`, and multiplying by `q` turns the left side into
`M² + a(q−a)`.  This is the sharpening of `sum_sq_le_card_mul_sum_sq` (which is
the `a = 0` case up to the correction term) that `#lemma 13#` needs. -/
theorem card_mul_sum_sq_ge {ι : Type*} [Fintype ι] (n : ι → ℕ) :
    Fintype.card ι * (∑ ε, n ε ^ 2) ≥
      (∑ ε, n ε) ^ 2 + (∑ ε, n ε) % Fintype.card ι *
        (Fintype.card ι - (∑ ε, n ε) % Fintype.card ι) := by
  classical
  set M := ∑ ε, n ε with hM
  set q := Fintype.card ι with hq
  set t := M / q with ht
  have hMta : q * t + M % q = M := by
    rw [ht, hq]
    exact Nat.div_add_mod M (Fintype.card ι)
  -- the pointwise inequality `(n − t)(n − t − 1) ≥ 0` over `ℤ`
  have hkey : ∀ m : ℤ, 0 ≤ m * (m - 1) := by
    intro m
    by_cases h : m ≤ 0
    · exact mul_nonneg_of_nonpos_of_nonpos h (by linarith)
    · have h1 : 1 ≤ m := by omega
      exact mul_nonneg (by linarith) (by linarith)
  have hpoint : ∀ ε, (n ε : ℤ) * (2 * (t : ℤ) + 1) ≤
      (n ε : ℤ) ^ 2 + (t : ℤ) * ((t : ℤ) + 1) := by
    intro ε
    have h := hkey ((n ε : ℤ) - (t : ℤ))
    nlinarith [h]
  -- sum it over `ε`
  have hsum : (2 * (t : ℤ) + 1) * (M : ℤ) - (q : ℤ) * ((t : ℤ) * ((t : ℤ) + 1))
      ≤ ∑ ε, (n ε : ℤ) ^ 2 := by
    have h1 : (∑ ε, (n ε : ℤ) * (2 * (t : ℤ) + 1))
        ≤ ∑ ε, ((n ε : ℤ) ^ 2 + (t : ℤ) * ((t : ℤ) + 1)) :=
      Finset.sum_le_sum fun ε _ => hpoint ε
    have h2 : (∑ ε, (n ε : ℤ) * (2 * (t : ℤ) + 1)) = (M : ℤ) * (2 * (t : ℤ) + 1) := by
      rw [hM]
      push_cast
      rw [Finset.sum_mul]
    have h3 : (∑ ε, ((n ε : ℤ) ^ 2 + (t : ℤ) * ((t : ℤ) + 1)))
        = (∑ ε, (n ε : ℤ) ^ 2) + (q : ℤ) * ((t : ℤ) * ((t : ℤ) + 1)) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ← hq, nsmul_eq_mul]
    rw [h2, h3] at h1
    linarith
  -- multiply by `q` and evaluate at `M = q·t + a`
  have hMcast : (M : ℤ) = (q : ℤ) * (t : ℤ) + ((M % q : ℕ) : ℤ) := by
    conv_lhs => rw [← hMta]
    simp only [Nat.cast_add, Nat.cast_mul]
  have hident : (q : ℤ) * ((2 * (t : ℤ) + 1) * (M : ℤ) -
        (q : ℤ) * ((t : ℤ) * ((t : ℤ) + 1)))
      = (M : ℤ) ^ 2 + (((M % q) * (q - M % q) : ℕ) : ℤ) := by
    have h1 : (((M % q) * (q - M % q) : ℕ) : ℤ)
        = ((M % q : ℕ) : ℤ) * ((q : ℤ) - ((M % q : ℕ) : ℤ)) := by
      have hle : M % q ≤ q := by
        rcases Nat.eq_zero_or_pos q with h0 | h0
        · have hempty : IsEmpty ι := Fintype.card_eq_zero_iff.mp (by rw [← hq]; exact h0)
          have hM0 : M = 0 := by
            rw [hM]
            exact Finset.sum_eq_zero fun ε _ => (hempty.false ε).elim
          omega
        · exact le_of_lt (Nat.mod_lt M h0)
      rw [Nat.cast_mul, Nat.cast_sub hle]
    rw [h1, hMcast]
    ring
  have hmul := mul_le_mul_of_nonneg_left hsum (Int.natCast_nonneg q)
  have hmain : (M : ℤ) ^ 2 + (((M % q) * (q - M % q) : ℕ) : ℤ)
      ≤ (q : ℤ) * (∑ ε, (n ε : ℤ) ^ 2) := by
    linarith [hmul, hident]
  have hgoal : ((M ^ 2 + M % q * (q - M % q) : ℕ) : ℤ)
      ≤ ((q * ∑ ε, n ε ^ 2 : ℕ) : ℤ) := by
    have hcast : ((M ^ 2 + M % q * (q - M % q) : ℕ) : ℤ)
        = (M : ℤ) ^ 2 + (((M % q) * (q - M % q) : ℕ) : ℤ) := by
      rw [Nat.cast_add, Nat.cast_pow]
    rw [hcast]
    push_cast
    exact hmain
  exact_mod_cast hgoal

/-- `(internal, §VIII-A — the *sharp* per-coordinate estimate of `#lemma 13#`)` — the
sharpening of `card_ne_pairs_mul_le` by the correction term `a(q−a)`: among `M`
positions carrying symbols of a `q`-ary alphabet, the number of ordered pairs of
positions with *different* symbols is at most `(M²(q−1) − a(q−a))/q`, i.e.
`q · #{(i,j) : symbols differ} ≤ M²(q−1) − a(q−a)` with `a = M mod q`.  With
`n_ε` the number of positions carrying `ε`, the count is `M² − Σ_ε n_ε²` (the
supporting count of `card_ne_pairs_mul_le`) and the sharp inequality
`q·Σ_ε n_ε² ≥ M² + a(q−a)` is `card_mul_sum_sq_ge`; the two together give
`q·#(differences) = qM² − q·Σ_ε n_ε² ≤ qM² − M² − a(q−a) = M²(q−1) − a(q−a)`.

The preamble is the one of `card_ne_pairs_mul_le` (unchanged); only the final
arithmetic uses the sharp `card_mul_sum_sq_ge` in place of Cauchy–Schwarz. -/
theorem card_ne_pairs_mul_le_sharp {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : Type*} [Fintype F] [DecidableEq F] (x : ι → F) :
    Fintype.card F * ((Finset.univ : Finset (ι × ι)).filter
        (fun p => x p.1 ≠ x p.2)).card ≤
      (Fintype.card ι) ^ 2 * (Fintype.card F - 1) -
        ((Fintype.card ι) % Fintype.card F) *
          (Fintype.card F - (Fintype.card ι) % Fintype.card F) := by
  classical
  set n : F → ℕ := fun ε => (Finset.univ.filter (fun i : ι => x i = ε)).card with hn
  have hcardEq : (Finset.univ.filter (fun p : ι × ι => x p.1 = x p.2)).card
      = ∑ ε, n ε ^ 2 := by
    have hset : (Finset.univ.filter (fun p : ι × ι => x p.1 = x p.2))
        = Finset.univ.biUnion (fun ε : F =>
            (Finset.univ.filter (fun i : ι => x i = ε)) ×ˢ
              (Finset.univ.filter (fun j : ι => x j = ε))) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
        Finset.mem_product]
      constructor
      · intro h
        exact ⟨x p.1, rfl, h.symm⟩
      · rintro ⟨ε, h1, h2⟩
        rw [h1, h2]
    have hdisj : Set.PairwiseDisjoint (fun ε => ε ∈ (Finset.univ : Finset F))
        (fun ε => (Finset.univ.filter (fun i : ι => x i = ε)) ×ˢ
          (Finset.univ.filter (fun j : ι => x j = ε))) := by
      intro ε _ δ _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro p hp hq
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
      exact hne (hp.1.symm.trans hq.1)
    rw [hset, Finset.card_biUnion hdisj]
    refine Finset.sum_congr rfl fun ε _ => ?_
    rw [Finset.card_product, hn, pow_two]
  have hpart : (Finset.univ.filter (fun p : ι × ι => x p.1 ≠ x p.2)).card
      + (Finset.univ.filter (fun p : ι × ι => x p.1 = x p.2)).card
      = (Fintype.card ι) ^ 2 := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (ι × ι)))
      (p := fun p => x p.1 = x p.2)
    simpa [Finset.card_univ, Fintype.card_prod, pow_two, mul_comm, add_comm] using h
  have hM : Fintype.card ι = ∑ ε, n ε := by
    have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset ι))
      (t := (Finset.univ : Finset F)) (f := x) (fun i _ => Finset.mem_univ _)
    simpa [Finset.card_univ, hn] using h
  rcases Nat.eq_zero_or_pos (Fintype.card F) with hq0 | hqpos
  · rw [hq0]
    simp
  · set T := (Fintype.card ι) ^ 2 with hT
    have h2 : (Finset.univ.filter (fun p : ι × ι => x p.1 ≠ x p.2)).card
        + ∑ ε, n ε ^ 2 = T := by rw [← hcardEq, hpart]
    have hne_eq : (Finset.univ.filter (fun p : ι × ι => x p.1 ≠ x p.2)).card
        = T - ∑ ε, n ε ^ 2 := by omega
    have hsharp : T + (Fintype.card ι) % Fintype.card F *
        (Fintype.card F - (Fintype.card ι) % Fintype.card F)
        ≤ Fintype.card F * ∑ ε, n ε ^ 2 := by
      have h := card_mul_sum_sq_ge (n := n)
      rw [← hM, ← hT] at h
      exact h
    have h3 : T * (Fintype.card F - 1) = Fintype.card F * T - T := by
      rw [Nat.mul_sub_left_distrib, mul_one, mul_comm T (Fintype.card F)]
    rw [hne_eq, Nat.mul_sub_left_distrib, h3, Nat.sub_sub]
    exact Nat.sub_le_sub_left hsharp (Fintype.card F * T)

end FCC

