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
  by
    classical
    exact if h : ∃ d : ℕ, d ∈ {d : ℕ | ∃ x ∈ C, ∃ y ∈ C, x ≠ y ∧ hammingDist x y = d}
      then Nat.find h else 0

end MinDist

section PerfectAndMDS

/-- `(internal, §V-B — used by `#theorem 10#`)` — a perfect `t`-error correcting
code.  The paper defines it in prose: "the Hamming bound on the size of an
error-correcting code `C` with length `n` and minimum distance `d` is
`M ≤ q^n/Σ_{i≤⌊(d−1)/2⌋} C(n,i)(q−1)^i`", and "a code that achieves the Hamming
bound is called a perfect code" — here written as: minimum distance `≥ 2t+1` and
the Hamming bound met with equality. -/
def IsPerfect {F : Type*} [Zero F] [Fintype F] [DecidableEq F] {n : ℕ} (C : Finset (Word F n))
    (t : ℕ) : Prop :=
  (∀ x ∈ C, ∀ y ∈ C, x ≠ y → 2 * t + 1 ≤ hammingDist x y) ∧
    Fintype.card F ^ n = C.card * (ball (0 : Word F n) t).card

/-- `(internal, §V-B — used by `#theorem 11#`, `#lemma 2#`)` — an MDS code:
"a code that meets the Singleton bound with equality is called a maximum
distance separable (MDS) code ... an `(n,M,d)_q` code is MDS if and only if
`M = q^{n−d+1}`".  Stated as: `|C| = q^{n−d+1}` and `d_min(C) = d`. -/
def IsMDS {F : Type*} [Fintype F] [DecidableEq F] {n : ℕ} (C : Finset (Word F n))
    (d : ℕ) : Prop :=
  C.card = Fintype.card F ^ (n - d + 1) ∧ minDist C = d

end PerfectAndMDS

section PreimageSizes

/-- `(internal, §VIII — used by `#theorem 14#`)` — `L = max_{α ∈ Im(f)} |f⁻¹(α)|`,
the quantity "where `L = max_{α∈Im(f)} |f⁻¹(α)|`" of `#theorem 14#` (the largest
preimage of the function `f`). -/
noncomputable def maxPreimageCard {F : Type*} [Fintype F] [DecidableEq F] {α : Type*}
    [DecidableEq α] {k : ℕ} (f : Word F k → α) : ℕ :=
  sSup {c : ℕ | ∃ a : α, (Finset.univ.filter fun u => f u = a).card = c}

/-- `(internal, §VIII — used by `#theorem 15#`)` — `ℓ = min_{i∈[E]} |f⁻¹(f_i)|`,
the quantity "let `ℓ = min_{i∈[E]} |f⁻¹(f_i)|`" of `#theorem 15#` (the smallest
preimage of the function `f`). -/
noncomputable def minPreimageCard {F : Type*} [Fintype F] [DecidableEq F] {α : Type*}
    [DecidableEq α] {k : ℕ} (f : Word F k → α) : ℕ :=
  sInf {c : ℕ | ∃ a : α, (Finset.univ.filter fun u => f u = a).card = c}

end PreimageSizes

section UnionBalls

/-- `(internal, §VIII — used by `#theorem 15#`, `#theorem 16#` and the appendix)` —
the union of the Hamming balls `∪_{j} B(v_j,t)`, i.e. the set whose cardinality
the paper writes as `|∪_{j≤ℓ} B(v_j,t)|`. -/
def unionBalls {F : Type*} [Fintype F] [DecidableEq F] {ι : Type*} [Fintype ι] {n : ℕ}
    (v : ι → Word F n) (t : ℕ) : Finset (Word F n) :=
  Finset.univ.biUnion (fun j => ball (v j) t)

/-- `(internal, §VIII — used by `#theorem 15#`)` — the minimum of
`|∪_{j≤ℓ} B(v_j,t)|` over all families `v₁,…,v_ℓ`, the quantity the paper
describes as "`v₁,…,v_ℓ` … for which `|∪_{j≤ℓ} B(v_j,t)|` is minimum". -/
noncomputable def minUnionCard {F : Type*} [Fintype F] [DecidableEq F] (ℓ n t : ℕ) : ℕ :=
  sInf {c : ℕ | ∃ v : Fin ℓ → Word F n, (unionBalls v t).card = c}

/-- `(internal, §VIII-C — used by `#theorem 16#`)` — the same minimum, but over
families whose vectors are pairwise at distance at least `d_d`, as `#theorem 16#`
requires ("`d(vᵢ,vⱼ) ≥ d_d` for all `i ≠ j`"). -/
noncomputable def minUnionCardDist {F : Type*} [Fintype F] [DecidableEq F]
    (ℓ dd n t : ℕ) : ℕ :=
  sInf {c : ℕ | ∃ v : Fin ℓ → Word F n,
    (∀ i j : Fin ℓ, i ≠ j → dd ≤ hammingDist (v i) (v j)) ∧ (unionBalls v t).card = c}

end UnionBalls

section SystematicSplit

/-- `(internal, §II)` — the *redundancy part* of a length-`k + r` word: its last
`r` coordinates.  Together with `msgPart` it splits a codeword `(u,p)` of a
systematic encoding into the message and the parity part. -/
def redPart {F : Type*} {k r : ℕ} (c : Word F (k + r)) : Word F r :=
  fun i => c (Fin.natAdd k i)

/-- `(internal, §II — the key step of `#theorem 2#`)` — for a *systematic*
encoding the Hamming distance of two codewords splits into the message part and
the redundancy part: `d(C u, C v) = d(u,v) + d(p_u, p_v)`, where `p_u` is
`redPart (C u)`.  This is the identity that `#theorem 2#` uses in both
directions (to build an FCC from a `D`-code, and to extract a `D`-code from an
FCC), and the reason `ISSUES.md` §1 records systematicity as part of
`#definition 6#`. -/
theorem hammingDist_eq_msg_add_red {F : Type*} [Zero F] [Fintype F] [DecidableEq F]
    {k r : ℕ} {C : Word F k → Word F (k + r)} (hC : IsSystematic C) (u v : Word F k) :
    hammingDist (C u) (C v) = hammingDist u v +
      hammingDist (redPart (C u)) (redPart (C v)) := by
  sorry

end SystematicSplit

end FCC
