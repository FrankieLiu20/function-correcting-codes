import FCC.Balls

/-!
# §VIII-A — the generalized Plotkin bound (`#lemma 13#`, `#theorem 14#`)

Paper: §VIII-A.  The paper's Theorem 14 bounds the optimal redundancy
`r_f(k : d_d, d_f)` of an `(f : d_d, d_f)`-FCC from below by

`((L−1)d_d + (q^k−L)d_f)/(q^{k−1}(q−1)) − k`,  `L = max_{α ∈ Im f} |f⁻¹(α)|`,

and its Lemma 13 is the same Plotkin argument for irregular distance codes over
`F_q`.  Both rest on one counting fact, already proved in `FCC/Balls.lean`:

* `sum_sq_le_card_mul_sum_sq` — `(Σ_ε n_ε)² ≤ q·Σ_ε n_ε²` (Cauchy–Schwarz);
* `card_ne_pairs_mul_le` — among `M` words over a `q`-ary alphabet at most
  `M²(q−1)/q` *ordered pairs* differ in a fixed coordinate.

This module assembles them into the paper's two inequalities for the total
pairwise distance `Σ_{x≠y} d(x,y)` of a code `C : Word F k → Word F (k+r)`:

* **lower bound** (`plotkin_total_ge`) — the codewords of `C` are indexed by the
  `q^k` messages; those sharing the function value of `x` are at distance at
  least `d_d` from `x` (and there are `|f⁻¹(f x)| − 1` of them), the others at
  distance at least `d_f`, so summing over `x` gives `q^k((L−1)d_d+(q^k−L)d_f)`;
* **upper bound** (`plotkin_total_le`) — summing over the `n = k+r` coordinates
  and using the per-coordinate estimate `q·#{pairs differing in a coordinate}
  ≤ q^{2k}(q−1)` gives `q·Σ_{x≠y} d(x,y) ≤ (k+r)·q^{2k}(q−1)`.

Comparing the two and cancelling the positive factor `q^k` is the arithmetic
content of `#theorem 14#`; `plotkin_bound_fcc_aux` does that comparison and
`FCC/Paper.lean` instantiates it at the attained value of `optimalRedundancyData`.
-/

namespace FCC

section Plotkin

variable {F : Type*} [Fintype F] [DecidableEq F] {α : Type*} [DecidableEq α]

/-! ### Preimage sizes -/

omit [DecidableEq F] in
/-- `(internal, §VIII-A — used by `#theorem 14#`)` — the set of preimage sizes
`{|f⁻¹(α)| : α}` of a function on `Word F k` is bounded above by the number of
messages `q^k` (every preimage is a subset of the message space).  Needed because
`sSup` on `ℕ` is the *conditionally* complete lattice supremum. -/
theorem bddAbove_preimageCard {k : ℕ} (f : Word F k → α) :
    BddAbove {c : ℕ | ∃ a : α, (Finset.univ.filter fun u : Word F k => f u = a).card = c} :=
  ⟨Fintype.card F ^ k, fun c ⟨a, hc⟩ => by
    rw [← hc]
    exact (Finset.card_filter_le _ _).trans_eq (card_word k)⟩

/-- `(internal, §VIII-A — used by `#theorem 14#`)` — `L = max_{α∈Im(f)} |f⁻¹(α)|`
dominates every preimage size: each `|f⁻¹(a)|` is one of the numbers `L` is the
maximum of. -/
theorem card_filter_le_maxPreimageCard {k : ℕ} (f : Word F k → α) (a : α) :
    (Finset.univ.filter fun u : Word F k => f u = a).card ≤ maxPreimageCard f := by
  rw [maxPreimageCard]
  exact le_csSup (bddAbove_preimageCard f) ⟨a, rfl⟩

/-- `(internal, §VIII-A — used by `#theorem 14#`)` — `L ≤ q^k`. -/
theorem maxPreimageCard_le_card {k : ℕ} (f : Word F k → α) :
    maxPreimageCard f ≤ Fintype.card F ^ k := by
  rw [maxPreimageCard]
  rcases Set.eq_empty_or_nonempty
      {c : ℕ | ∃ a : α, (Finset.univ.filter fun u : Word F k => f u = a).card = c} with h | h
  · rw [h, csSup_empty]
    exact Nat.zero_le _
  · exact csSup_le h fun c ⟨a, hc⟩ => by
      rw [← hc]
      exact (Finset.card_filter_le _ _).trans_eq (card_word k)

end Plotkin

/-! ### Arithmetic of one row of the Plotkin sum -/

/-- `(internal, §VIII-A — used by `#theorem 14#`)` — one row of the Plotkin sum is
decreasing in the preimage size: for `1 ≤ n ≤ L ≤ M` and `d_d < d_f`,
`(L−1)d_d + (M−L)d_f ≤ (n−1)d_d + (M−n)d_f`.  The two sides differ by
`(L−n)(d_f−d_d)`, so each of the three hypotheses is needed. -/
theorem plotkin_row_le {n L M dd df : ℕ} (hn : 1 ≤ n) (hnL : n ≤ L) (hLM : L ≤ M)
    (hlt : dd < df) :
    (L - 1) * dd + (M - L) * df ≤ (n - 1) * dd + (M - n) * df := by
  have hn1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
  have hL1 : ((L - 1 : ℕ) : ℤ) = (L : ℤ) - 1 := by omega
  have hML : ((M - L : ℕ) : ℤ) = (M : ℤ) - L := by omega
  have hMn : ((M - n : ℕ) : ℤ) = (M : ℤ) - n := by omega
  have hle : (((L - 1) * dd + (M - L) * df : ℕ) : ℤ)
      ≤ (((n - 1) * dd + (M - n) * df : ℕ) : ℤ) := by
    push_cast
    rw [hL1, hML, hn1, hMn]
    nlinarith [hnL, hLM, hlt]
  exact_mod_cast hle

section LowerBound

variable {F : Type*} [Fintype F] [DecidableEq F] {α : Type*} [DecidableEq α]
variable {k r : ℕ}

/-- `(internal, §VIII-A — first step of the lower bound of `#theorem 14#`)` — the
contribution of the codeword `C u` to the total pairwise distance: the messages `v`
with `f v = f u` are at distance at least `d_d` from `C u`, and there are
`|f⁻¹(f u)| − 1` of them (all but `u` itself), while each of the remaining
`q^k − |f⁻¹(f u)|` messages is at distance at least `d_f`. -/
theorem sum_erase_hammingDist_ge (f : Word F k → α) (C : Word F k → Word F (k + r))
    (dd df : ℕ) (hdd : ∀ u v : Word F k, u ≠ v → dd ≤ hammingDist (C u) (C v))
    (hdf : ∀ u v : Word F k, f u ≠ f v → df ≤ hammingDist (C u) (C v))
    (u : Word F k) :
    ((Finset.univ.filter fun v : Word F k => f v = f u).card - 1) * dd +
        (Fintype.card F ^ k -
          (Finset.univ.filter fun v : Word F k => f v = f u).card) * df ≤
      ∑ v ∈ (Finset.univ.erase u), hammingDist (C u) (C v) := by
  classical
  set A : Finset (Word F k) := Finset.univ.filter (fun v => f v = f u) with hA
  set B' : Finset (Word F k) := (Finset.univ.erase u).filter (fun v => f v = f u) with hB'
  set D' : Finset (Word F k) := (Finset.univ.erase u).filter (fun v => ¬ f v = f u) with hD'
  have huA : u ∈ A := by simp [hA]
  have hB'eq : B' = A.erase u := by rw [hB', hA, Finset.filter_erase]
  have hB'card : B'.card = A.card - 1 := by rw [hB'eq, Finset.card_erase_of_mem huA]
  have hD'eq : D' = Finset.univ.filter (fun v : Word F k => ¬ f v = f u) := by
    rw [hD', Finset.filter_erase]
    exact Finset.erase_eq_self.mpr (by simp)
  have hD'card : D'.card = Fintype.card F ^ k - A.card := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Word F k)))
      (p := fun v => f v = f u)
    rw [← hA, Finset.card_univ, card_word k] at h
    rw [← hD'eq] at h
    omega
  have hsplit : (∑ v ∈ (Finset.univ : Finset (Word F k)).erase u, hammingDist (C u) (C v))
      = (∑ v ∈ B', hammingDist (C u) (C v)) +
        (∑ v ∈ D', hammingDist (C u) (C v)) := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ.erase u) (fun v => f v = f u)]
  have h1 : B'.card * dd ≤ ∑ v ∈ B', hammingDist (C u) (C v) := by
    calc B'.card * dd = ∑ _v ∈ B', dd := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ v ∈ B', hammingDist (C u) (C v) := by
        refine Finset.sum_le_sum fun v hv => ?_
        have hv' : v ∈ (Finset.univ : Finset (Word F k)).erase u := (Finset.mem_filter.mp hv).1
        exact hdd u v (Finset.mem_erase.mp hv').1.symm
  have h2 : D'.card * df ≤ ∑ v ∈ D', hammingDist (C u) (C v) := by
    calc D'.card * df = ∑ _v ∈ D', df := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ v ∈ D', hammingDist (C u) (C v) := by
        refine Finset.sum_le_sum fun v hv => ?_
        exact hdf u v (fun h => (Finset.mem_filter.mp hv).2 h.symm)
  calc (A.card - 1) * dd + (Fintype.card F ^ k - A.card) * df
      = B'.card * dd + D'.card * df := by rw [hB'card, hD'card]
    _ ≤ (∑ v ∈ B', hammingDist (C u) (C v)) +
          (∑ v ∈ D', hammingDist (C u) (C v)) := add_le_add h1 h2
    _ = ∑ v ∈ (Finset.univ : Finset (Word F k)).erase u, hammingDist (C u) (C v) :=
        hsplit.symm

end LowerBound

section UpperBound

variable {F : Type*} [Fintype F] [DecidableEq F] {α : Type*} [DecidableEq α]
variable {k r : ℕ}

/-- `(internal, §VIII-A — first step of the upper bound of `#theorem 14#`)` — for a
fixed coordinate `j`, summing "the two codewords differ in coordinate `j`" over the
pairs of *distinct messages* is the number of *all* ordered pairs of messages whose
codewords differ there: `(C u) j ≠ (C v) j` forces `u ≠ v`, so dropping the
condition costs nothing, and the diagonal contributes `0`. -/
theorem sum_erase_ite_eq_card_filter (C : Word F k → Word F (k + r)) (j : Fin (k + r)) :
    (∑ u : Word F k, ∑ v ∈ (Finset.univ : Finset (Word F k)).erase u,
        (if (C u) j ≠ (C v) j then 1 else 0))
      = ((Finset.univ : Finset (Word F k × Word F k)).filter
          (fun p => (C p.1) j ≠ (C p.2) j)).card := by
  classical
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, ← Finset.univ_product_univ,
    Finset.sum_product]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← Finset.sum_erase_add (Finset.univ : Finset (Word F k))
    (fun v => if (C u) j ≠ (C v) j then 1 else 0) (Finset.mem_univ u)]
  simp

/-- `(internal, §VIII-A — the double count of the upper bound of `#theorem 14#`)` —
the total pairwise distance of a code is the sum over the coordinates of the number
of ordered pairs of messages whose codewords differ in that coordinate. -/
theorem plotkin_total_eq_sum_card_filter (C : Word F k → Word F (k + r)) :
    (∑ u : Word F k, ∑ v ∈ (Finset.univ : Finset (Word F k)).erase u,
        hammingDist (C u) (C v))
      = ∑ j : Fin (k + r), ((Finset.univ : Finset (Word F k × Word F k)).filter
          (fun p => (C p.1) j ≠ (C p.2) j)).card := by
  classical
  have hdist : ∀ u v : Word F k, hammingDist (C u) (C v)
      = ∑ j : Fin (k + r), (if (C u) j ≠ (C v) j then 1 else 0) := by
    intro u v
    rw [hammingDist, Finset.card_eq_sum_ones, Finset.sum_filter]
  calc (∑ u : Word F k, ∑ v ∈ (Finset.univ : Finset (Word F k)).erase u,
          hammingDist (C u) (C v))
      = ∑ u : Word F k, ∑ j : Fin (k + r), ∑ v ∈ (Finset.univ : Finset (Word F k)).erase u,
          (if (C u) j ≠ (C v) j then 1 else 0) := by
        refine Finset.sum_congr rfl fun u _ => ?_
        simp only [hdist u]
        exact Finset.sum_comm
    _ = ∑ j : Fin (k + r), ∑ u : Word F k,
          ∑ v ∈ (Finset.univ : Finset (Word F k)).erase u,
          (if (C u) j ≠ (C v) j then 1 else 0) := Finset.sum_comm
    _ = ∑ j : Fin (k + r), ((Finset.univ : Finset (Word F k × Word F k)).filter
          (fun p => (C p.1) j ≠ (C p.2) j)).card :=
        Finset.sum_congr rfl fun j _ => sum_erase_ite_eq_card_filter C j

/-- `(internal, §VIII-A — second step of the upper bound of `#theorem 14#`)` — the
per-coordinate estimate `card_ne_pairs_mul_le`, multiplied by `q` and summed over
the `k+r` coordinates: `q·Σ_{x≠y} d(x,y) ≤ (k+r)·q^{2k}(q−1)`. -/
theorem plotkin_total_le (C : Word F k → Word F (k + r)) :
    Fintype.card F * (∑ u : Word F k, ∑ v ∈ (Finset.univ : Finset (Word F k)).erase u,
        hammingDist (C u) (C v))
      ≤ (k + r) * (Fintype.card F ^ k) ^ 2 * (Fintype.card F - 1) := by
  classical
  rw [plotkin_total_eq_sum_card_filter, Finset.mul_sum]
  calc ∑ j : Fin (k + r), Fintype.card F *
        ((Finset.univ : Finset (Word F k × Word F k)).filter
          (fun p => (C p.1) j ≠ (C p.2) j)).card
      ≤ ∑ _j : Fin (k + r), (Fintype.card F ^ k) ^ 2 * (Fintype.card F - 1) :=
        Finset.sum_le_sum fun j _ => by
          simpa [Finset.card_univ, card_word k] using
            (card_ne_pairs_mul_le (F := F) (fun u : Word F k => (C u) j))
    _ = (k + r) * (Fintype.card F ^ k) ^ 2 * (Fintype.card F - 1) := by
        rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fin]
        ring

end UpperBound

section Main

variable {F : Type*} [Zero F] [Fintype F] [DecidableEq F] {α : Type*} [DecidableEq α]

/-- `(internal, §VIII-A — used by `#theorem 14#`)` — the maximum preimage size is at
least `1`: `f` is defined on the non-empty message space (`0` provides an element of
`F`, and `u ↦ 0` is a message of every length), and its preimage is non-empty. -/
theorem one_le_maxPreimageCard {k : ℕ} (f : Word F k → α) : 1 ≤ maxPreimageCard f := by
  refine le_trans ?_ (card_filter_le_maxPreimageCard f (f (0 : Word F k)))
  exact Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨0, by simp⟩)

omit [Zero F] in
/-- `(internal, §VIII-A — second step of the lower bound of `#theorem 14#`)` —
replacing `|f⁻¹(f u)|` by the maximum `L = maxPreimageCard f` can only lower the row
(`plotkin_row_le`), which is the step that produces the paper's `L`. -/
theorem sum_erase_hammingDist_ge_max {k r : ℕ} (f : Word F k → α)
    (C : Word F k → Word F (k + r)) (dd df : ℕ)
    (hdd : ∀ u v : Word F k, u ≠ v → dd ≤ hammingDist (C u) (C v))
    (hdf : ∀ u v : Word F k, f u ≠ f v → df ≤ hammingDist (C u) (C v))
    (hlt : dd < df) (u : Word F k) :
    (maxPreimageCard f - 1) * dd + (Fintype.card F ^ k - maxPreimageCard f) * df ≤
      ∑ v ∈ (Finset.univ.erase u), hammingDist (C u) (C v) := by
  have hn : 1 ≤ (Finset.univ.filter fun v : Word F k => f v = f u).card :=
    Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨u, by simp⟩)
  exact (plotkin_row_le hn (card_filter_le_maxPreimageCard f (f u))
    (maxPreimageCard_le_card f) hlt).trans
    (sum_erase_hammingDist_ge f C dd df hdd hdf u)

omit [Zero F] in
/-- `(internal, §VIII-A — the lower bound of `#theorem 14#`)` — summing the
per-codeword bound over the `q^k` messages:
`q^k((L−1)d_d + (q^k−L)d_f) ≤ Σ_{x≠y} d(x,y)`. -/
theorem plotkin_total_ge {k r : ℕ} (f : Word F k → α) (C : Word F k → Word F (k + r))
    (dd df : ℕ) (hdd : ∀ u v : Word F k, u ≠ v → dd ≤ hammingDist (C u) (C v))
    (hdf : ∀ u v : Word F k, f u ≠ f v → df ≤ hammingDist (C u) (C v))
    (hlt : dd < df) :
    Fintype.card F ^ k * ((maxPreimageCard f - 1) * dd +
        (Fintype.card F ^ k - maxPreimageCard f) * df) ≤
      ∑ u : Word F k, ∑ v ∈ (Finset.univ.erase u), hammingDist (C u) (C v) := by
  calc Fintype.card F ^ k * ((maxPreimageCard f - 1) * dd +
        (Fintype.card F ^ k - maxPreimageCard f) * df)
      = ∑ _u : Word F k, ((maxPreimageCard f - 1) * dd +
          (Fintype.card F ^ k - maxPreimageCard f) * df) := by
        rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, card_word k]
    _ ≤ ∑ u : Word F k, ∑ v ∈ (Finset.univ.erase u), hammingDist (C u) (C v) :=
        Finset.sum_le_sum fun u _ => sum_erase_hammingDist_ge_max f C dd df hdd hdf hlt u

/-- `(internal, §VIII-A — the degenerate half of `#theorem 14#`)` — when `q^k = 1`
(i.e. `k = 0`, or `q = 1`) the paper's numerator is `≤ 0`: it is
`(L−1)(d_d−d_f)` with `L ≥ 1` and `d_d < d_f`. -/
theorem plotkin_num_nonpos {k : ℕ} (f : Word F k → α) (dd df : ℕ) (hlt : dd < df)
    (hpow : (Fintype.card F : ℚ) ^ k = 1) :
    ((maxPreimageCard f - 1 : ℕ) : ℚ) * dd +
        ((Fintype.card F : ℚ) ^ k - maxPreimageCard f) * df ≤ 0 := by
  have hL1 : 1 ≤ maxPreimageCard f := one_le_maxPreimageCard f
  have hLq : (1 : ℚ) ≤ (maxPreimageCard f : ℚ) := by exact_mod_cast hL1
  have hcast : ((maxPreimageCard f - 1 : ℕ) : ℚ) = (maxPreimageCard f : ℚ) - 1 := by
    rw [Nat.cast_sub hL1]
    norm_num
  rw [hcast, hpow]
  have hkey : ((maxPreimageCard f : ℚ) - 1) * (dd : ℚ) + (1 - (maxPreimageCard f : ℚ)) * (df : ℚ)
      = ((maxPreimageCard f : ℚ) - 1) * ((dd : ℚ) - (df : ℚ)) := by ring
  rw [hkey]
  refine mul_nonpos_of_nonneg_of_nonpos (by linarith) ?_
  have hdf' : (dd : ℚ) ≤ (df : ℚ) := by exact_mod_cast Nat.le_of_lt hlt
  linarith

omit [Zero F] in
/-- `(internal, §VIII-A — the degenerate half of `#theorem 14#`)` — with a
non-negative denominator, a numerator `≤ 0` gives the paper's inequality. -/
theorem plotkin_bound_of_num_nonpos {k r : ℕ} (f : Word F k → α) (dd df : ℕ)
    (hden : 0 ≤ (Fintype.card F : ℚ) ^ (k - 1) * ((Fintype.card F : ℚ) - 1))
    (hnonpos : ((maxPreimageCard f - 1 : ℕ) : ℚ) * dd +
        ((Fintype.card F : ℚ) ^ k - maxPreimageCard f) * df ≤ 0) :
    (((maxPreimageCard f - 1 : ℕ) : ℚ) * dd +
        ((Fintype.card F : ℚ) ^ k - maxPreimageCard f) * df) /
        ((Fintype.card F : ℚ) ^ (k - 1) * ((Fintype.card F : ℚ) - 1)) - k ≤ (r : ℚ) := by
  have h1 : (((maxPreimageCard f - 1 : ℕ) : ℚ) * dd +
        ((Fintype.card F : ℚ) ^ k - maxPreimageCard f) * df) /
        ((Fintype.card F : ℚ) ^ (k - 1) * ((Fintype.card F : ℚ) - 1)) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hnonpos hden
  have hk : (0 : ℚ) ≤ (k : ℚ) := Nat.cast_nonneg k
  have hr : (0 : ℚ) ≤ (r : ℚ) := Nat.cast_nonneg r
  linarith

/-- `(internal, §VIII-A — the arithmetic of `#theorem 14#`)` — the paper's bound for
the redundancy of a *given* `(f : d_d, d_f)`-FCC of length `k + r`.  Comparing
`plotkin_total_ge` and `plotkin_total_le` and cancelling the positive factor `q^k`
leaves `((L−1)d_d + (q^k−L)d_f)/(q^{k−1}(q−1)) − k ≤ r`. -/
theorem plotkin_bound_fcc_aux {k r : ℕ} (f : Word F k → α)
    (C : Word F k → Word F (k + r)) (dd df : ℕ)
    (hdd : ∀ u v : Word F k, u ≠ v → dd ≤ hammingDist (C u) (C v))
    (hdf : ∀ u v : Word F k, f u ≠ f v → df ≤ hammingDist (C u) (C v))
    (hlt : dd < df) :
    (((maxPreimageCard f - 1 : ℕ) : ℚ) * dd +
        ((Fintype.card F : ℚ) ^ k - maxPreimageCard f) * df) /
        ((Fintype.card F : ℚ) ^ (k - 1) * ((Fintype.card F : ℚ) - 1)) - k ≤ (r : ℚ) := by
  classical
  have hq1 : 1 ≤ Fintype.card F := by
    have h := Fintype.card_pos_iff.mpr ⟨(0 : F)⟩
    omega
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    have hq : (1 : ℚ) ≤ (Fintype.card F : ℚ) := by exact_mod_cast hq1
    refine plotkin_bound_of_num_nonpos f dd df ?_ (plotkin_num_nonpos f dd df hlt (by simp))
    have : (Fintype.card F : ℚ) ^ (0 - 1) = 1 := by simp
    rw [this]
    linarith
  · rcases eq_or_lt_of_le hq1 with hqeq | hqlt
    · have hq : (Fintype.card F : ℚ) = 1 := by exact_mod_cast hqeq.symm
      refine plotkin_bound_of_num_nonpos f dd df ?_ (plotkin_num_nonpos f dd df hlt ?_)
      · rw [hq]; simp
      · rw [hq]; simp
    · set den : ℚ := (Fintype.card F : ℚ) ^ (k - 1) * ((Fintype.card F : ℚ) - 1) with hdendef
      set B : ℕ := (maxPreimageCard f - 1) * dd + (Fintype.card F ^ k - maxPreimageCard f) * df
        with hBdef
      have hqpos : 0 < Fintype.card F := lt_of_lt_of_le (by norm_num) hqlt
      have hMpos : 0 < Fintype.card F ^ k := pow_pos hqpos k
      have hdenpos : 0 < den := by
        have h1 : (0 : ℚ) < (Fintype.card F : ℚ) ^ (k - 1) :=
          pow_pos (by exact_mod_cast hqpos : (0 : ℚ) < (Fintype.card F : ℚ)) _
        have h2 : (0 : ℚ) < (Fintype.card F : ℚ) - 1 := by
          have : (2 : ℚ) ≤ (Fintype.card F : ℚ) := by exact_mod_cast hqlt
          linarith
        exact mul_pos h1 h2
      have hlow : Fintype.card F ^ k * B ≤
          ∑ u : Word F k, ∑ v ∈ (Finset.univ.erase u), hammingDist (C u) (C v) :=
        plotkin_total_ge f C dd df hdd hdf hlt
      have hup : Fintype.card F * (∑ u : Word F k, ∑ v ∈ (Finset.univ.erase u),
            hammingDist (C u) (C v))
          ≤ (k + r) * (Fintype.card F ^ k) ^ 2 * (Fintype.card F - 1) :=
        plotkin_total_le C
      -- cancel `q^k`
      have hstep1 : Fintype.card F ^ k * (Fintype.card F * B)
          ≤ Fintype.card F ^ k * ((k + r) * Fintype.card F ^ k * (Fintype.card F - 1)) := by
        calc Fintype.card F ^ k * (Fintype.card F * B)
            = Fintype.card F * (Fintype.card F ^ k * B) := by ring
          _ ≤ Fintype.card F * (∑ u : Word F k, ∑ v ∈ (Finset.univ.erase u),
                hammingDist (C u) (C v)) := Nat.mul_le_mul_left _ hlow
          _ ≤ (k + r) * (Fintype.card F ^ k) ^ 2 * (Fintype.card F - 1) := hup
          _ = Fintype.card F ^ k *
                ((k + r) * Fintype.card F ^ k * (Fintype.card F - 1)) := by ring
      have hstep2 : Fintype.card F * B
          ≤ (k + r) * Fintype.card F ^ k * (Fintype.card F - 1) :=
        Nat.le_of_mul_le_mul_left hstep1 hMpos
      -- cancel `q` (using `q^k = q^{k-1}·q`, i.e. `k ≥ 1`)
      have hstep3 : Fintype.card F * B
          ≤ Fintype.card F * ((k + r) * Fintype.card F ^ (k - 1) * (Fintype.card F - 1)) := by
        calc Fintype.card F * B
            ≤ (k + r) * Fintype.card F ^ k * (Fintype.card F - 1) := hstep2
          _ = Fintype.card F *
                ((k + r) * Fintype.card F ^ (k - 1) * (Fintype.card F - 1)) := by
              have hpow : Fintype.card F ^ k = Fintype.card F ^ (k - 1) * Fintype.card F := by
                rw [← Nat.sub_add_cancel hkpos, pow_add]
                simp
              rw [hpow]
              ring
      have hB : B ≤ (k + r) * Fintype.card F ^ (k - 1) * (Fintype.card F - 1) :=
        Nat.le_of_mul_le_mul_left hstep3 hqpos
      -- back to `ℚ`
      have hqcast : ((Fintype.card F - 1 : ℕ) : ℚ) = (Fintype.card F : ℚ) - 1 := by
        rw [Nat.cast_sub hq1]
        norm_num
      have hBq : ((B : ℕ) : ℚ) ≤ (k + r : ℚ) * den := by
        calc ((B : ℕ) : ℚ)
            ≤ (((k + r) * Fintype.card F ^ (k - 1) * (Fintype.card F - 1) : ℕ) : ℚ) :=
              by exact_mod_cast hB
          _ = (k + r : ℚ) * den := by
              rw [hdendef]
              push_cast
              rw [hqcast]
              ring
      have hnum : ((B : ℕ) : ℚ) = ((maxPreimageCard f - 1 : ℕ) : ℚ) * dd +
          ((Fintype.card F : ℚ) ^ k - maxPreimageCard f) * df := by
        rw [hBdef]
        push_cast
        rw [Nat.cast_sub (maxPreimageCard_le_card f), Nat.cast_pow]
      rw [← hnum]
      have hle : ((B : ℕ) : ℚ) / den ≤ (k + r : ℚ) := by
        have hneq : den ≠ 0 := ne_of_gt hdenpos
        have h := div_nonpos_of_nonpos_of_nonneg
          (show ((B : ℕ) : ℚ) - (k + r : ℚ) * den ≤ 0 by linarith [hBq]) (le_of_lt hdenpos)
        rw [sub_div, mul_div_cancel_right₀ _ hneq] at h
        linarith
      have hkr : (k + r : ℚ) - k = (r : ℚ) := by ring
      linarith

end Main

section GeneralPairCount

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Fintype F] [DecidableEq F] {n : ℕ}

omit [Fintype F] in
/-- `(internal, §VIII-A — the general form of `sum_erase_ite_eq_card_filter`, needed
by `#lemma 13#`)` — for a fixed coordinate, the indicator sum over the pairs of
distinct indices is the number of *all* pairs of indices whose words differ there.
The only difference from the version used for `#theorem 14#` is the index type: a
`D`-code is indexed by `Fin M`, not by the messages `Word F k`. -/
theorem sum_erase_ite_eq_card_filter_gen (p : ι → Word F n) (c : Fin n) :
    (∑ i : ι, ∑ j ∈ (Finset.univ : Finset ι).erase i,
        (if (p i) c ≠ (p j) c then 1 else 0))
      = ((Finset.univ : Finset (ι × ι)).filter (fun q => (p q.1) c ≠ (p q.2) c)).card := by
  classical
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, ← Finset.univ_product_univ,
    Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_erase_add (Finset.univ : Finset ι)
    (fun j => if (p i) c ≠ (p j) c then 1 else 0) (Finset.mem_univ i)]
  simp

omit [Fintype F] in
/-- `(internal, §VIII-A — the general double count of `#lemma 13#`)` — the total
pairwise distance of a code is the sum over the coordinates of the number of pairs
of codewords differing in that coordinate (over an arbitrary index type). -/
theorem total_pair_eq_sum_coord (p : ι → Word F n) :
    (∑ i : ι, ∑ j ∈ (Finset.univ : Finset ι).erase i, hammingDist (p i) (p j))
      = ∑ c : Fin n, ((Finset.univ : Finset (ι × ι)).filter
          (fun q => (p q.1) c ≠ (p q.2) c)).card := by
  classical
  have hdist : ∀ i j : ι, hammingDist (p i) (p j)
      = ∑ c : Fin n, (if (p i) c ≠ (p j) c then 1 else 0) := by
    intro i j
    rw [hammingDist, Finset.card_eq_sum_ones, Finset.sum_filter]
  calc (∑ i : ι, ∑ j ∈ (Finset.univ : Finset ι).erase i, hammingDist (p i) (p j))
      = ∑ i : ι, ∑ c : Fin n, ∑ j ∈ (Finset.univ : Finset ι).erase i,
          (if (p i) c ≠ (p j) c then 1 else 0) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [hdist i]
        exact Finset.sum_comm
    _ = ∑ c : Fin n, ∑ i : ι, ∑ j ∈ (Finset.univ : Finset ι).erase i,
          (if (p i) c ≠ (p j) c then 1 else 0) := Finset.sum_comm
    _ = ∑ c : Fin n, ((Finset.univ : Finset (ι × ι)).filter
          (fun q => (p q.1) c ≠ (p q.2) c)).card :=
        Finset.sum_congr rfl fun c _ => sum_erase_ite_eq_card_filter_gen p c

end GeneralPairCount

end FCC
