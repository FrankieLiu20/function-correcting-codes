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

end FCC
