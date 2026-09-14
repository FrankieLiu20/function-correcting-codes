# Notation: paper ↔ Lean dictionary

Paper: C. Rajput, B. S. Rajan, R. Freij-Hollanti, C. Hollanti,
"Function-Correcting Codes With Data Protection", IEEE Trans. Inform. Theory
**72**(7), pp. 4860–4880, July 2026, DOI 10.1109/TIT.2026.3692458.

This file is the contract between the PDF and the Lean code.  It must be updated
**in the same commit** as any definition it describes.  Anything a reader needs
to re-derive a Lean statement by hand belongs here.

Section numbers are the paper's; never cite tex line numbers.

---

## 1. Labels: which paper item does a declaration formalize?

The paper has no LaTeX labels, only numbers, so the labels are ours.  A label is
written **at the very start of the docstring** of the declaration that owns the
statement, in the paper's own words, for example

```lean
/-- `#definition 5#` (§II, function distance matrix): the `E × E` matrix with …
/-- `#theorem 2#` (§IV): `r_f(k, t_d, t_f) = N(D_f(t_d, t_f : u₁, …, u_{q^k}))`.
```

| Paper item | Label (write this in the docstring and in `PLAN.md`) |
| --- | --- |
| Definition 5 | `#definition 5#` |
| Theorem 2 | `#theorem 2#` |
| Lemma 3 | `#lemma 3#` |
| Corollary 9 | `#corollary 9#` |
| Example 6 | `#example 6#` |
| Remark 1 | `#remark 1#` |

Definitions, theorems, lemmas, corollaries, examples and remarks share the
paper's single counter, so `#theorem 10#` is Theorem 10 and `#lemma 10#` is
Lemma 10.  The identical string appears in the inventory table of `PLAN.md`
(§1.1 for the numbered results, §1.2 for the examples), and
`scripts/consistency_check.ps1` checks both directions: every marker used in
`FCC/*.lean` must be an inventory row, and every inventory row must be *stated*
— by the declaration named in that row's "Lean name" column, whose docstring
opens with the marker.  A marker buried in the middle of a docstring does not
count as a stated result.

Declarations that are **not** a numbered item of the paper — helpers,
restatements of mathlib lemmas, notation — open their docstring with
`(internal)` or `(paper notation, §I-E)` instead, and name the paper item that
consumes them (e.g. "used by `#lemma 6#`").  The text after the marker stays
close to the paper's wording, so that a reader can compare docstring and PDF
without translating.

---

## 2. Dictionary

### 2.1 Ambient objects

| Paper | Meaning | Lean | Notes |
| --- | --- | --- | --- |
| `F_q` | finite field of size `q` | a type `F` with `[Field F] [Fintype F] [DecidableEq F]`; `q = Fintype.card F` | the field is *always* a parameter, never `ZMod q` (see §3.1) |
| `F_q^k`, `F_q^n` | words of length `k` / `n` | `Word F k` = `Fin k → F` | 0-based `Fin`, the paper is 1-based (§3.2) |
| `u`, `c`, `e`, `x`, `y` | words | `u c e x y : Word F n` | |
| `u_i` (subscript) | `i`-th coordinate | `u i` with `i : Fin n` | paper `u_1` ↔ Lean `u 0` |
| `wt(u)` | number of non-zero entries | `wt u`, an abbreviation for mathlib's `hammingNorm u` | §I-E |
| `d(x,y)` | Hamming distance | mathlib's `hammingDist x y` | `Mathlib.InformationTheory.Hamming`; already `#{i | x i ≠ y i}`, with `hammingDist_self`, `hammingDist_comm`, `hammingDist_triangle`, … |
| `B(u,t)` | Hamming ball of radius `t` | `ball u t : Finset (Word F n)` | `def`; membership is decidable |
| `[n]` | `{1,…,n}` | `Fin n` | |
| `ℕ` | natural numbers | `ℕ` | |
| `ℕ^{m×m}` | integer matrices | `Fin m → Fin m → ℕ` | distance matrices are *functions of two indices*, not `Matrix` |
| `|S|` | cardinality | `Finset.card` / `Fintype.card` | |
| `Im(f)` | image of `f` | `Finset.univ.image f`; `imageCard f` for its size | |
| `f⁻¹(α)` | preimage | `{u | f u = α}` | |
| `A \ B` | set difference | `A \ B` | |
| `q^k` | size of the message space | `Fintype.card (Word F k)` | |

### 2.2 Codes and parameters

| Paper | Meaning | Lean | Notes |
| --- | --- | --- | --- |
| `(f,t)`-FCC, `C` | systematic `C : F_q^k → F_q^{k+r}`, `d(C(u₁),C(u₂)) ≥ 2t+1` when `f(u₁) ≠ f(u₂)` | `IsFCC f C t` (`#definition 1#`) | systematicity is a field of the predicate |
| `r_f(k,t)` | optimal redundancy | `optimalRedundancy f t` (`#definition 1#`) | `ℕ`-valued, defined by minimality |
| `(f : d_d, d_f)`-FCC | both conditions at once | `IsFCCData f C d_d d_f` (`#definition 6#`) | `#definition 1#` is the case `d_d = 0`, `d_f = 2t+1` |
| `(f, t_d, t_f)`-FCC | the same with `d_d = 2t_d+1`, `d_f = 2t_f+1` | `IsFCCData f C (2*t_d+1) (2*t_f+1)` | the paper switches notations silently (§2.3) |
| `r_f(k : d_d, d_f)` = `r_f(k,t_d,t_f)` | optimal redundancy with data protection | `optimalRedundancyData f d_d d_f` (`#definition 10#`) | |
| `D ∈ ℕ^{M×M}` | distance requirement matrix | `D : Fin M → Fin M → ℕ` | diagonal is `0` |
| `D_f(t, u₁,…,u_M)` | DRM | `drm f t` on the index family `u : Fin M → Word F k` (`#definition 2#`) | |
| `D_f(t_d,t_f : u₁,…,u_M)` | DRM with data protection | `drmData f t_d t_f u` (`#definition 11#`) | |
| `D_{C,f}(t_f : u₁,…,u_M)` | coded DRM | `cdrm f C t_f u` (`#definition 7#`) | |
| `D_f(t, f₁,…,f_E)` | FDM | `fdm f t` (`#definition 5#`) | indexed by the image, not the messages |
| `D_{C,f}(t_f : f₁,…,f_E)` | coded FDM | `cfdm f C t_f` (`#definition 9#`) | |
| `d(fᵢ,fⱼ)` | distance between function values | `fDist f i j` (`#definition 4#`) | |
| `d_C(fᵢ,fⱼ)` | coded distance between function values | `codedFDist f C i j` (`#definition 8#`) | |
| `D`-code | `P = {p₁,…,p_M}`, `d(pᵢ,pⱼ) ≥ [D]ᵢⱼ` | `IsDCode D r` (a family `Fin M → Word F r`) (`#definition 3#`) | the paper's "ordering of `P`" is the indexing of the family (§3.4) |
| `N(D)` | minimal length of a `D`-code | `N D` (`#definition 3#`) | `sInf` of the lengths that admit a `D`-code |
| `N(M,D)` | minimal length of a code with `M` words, distance `≥ D` | `Nconst M D` (`#definition 3#`) | `= N` of the constant matrix |
| `d_min(C)` | minimum distance of a code | `minDist C` | `0` for `|C| ≤ 1`; `#definition 12#` uses it for the graph |
| `G(C)` | minimum-distance graph | `minDistGraph C` (`#definition 12#`) | `SimpleGraph (Word F n)` |
| `B_f(u,ρ)` | function ball | `functionBall f u ρ` (`#definition 13#`) | a `Finset` of image values |
| `ρ`-locally binary | `|B_f(u,ρ)| ≤ 2` | `IsLocallyBinary f ρ` (`#definition 14#`) | |
| `(ρ,λ)`-bounded | `|B_f(u,ρ)| ≤ λ` | `IsLocallyBounded f ρ λ` (`#definition 15#`) | |
| `Col_f` | the colouring of `#lemma 4#` | a hypothesis `col : Word F k → Fin λ` of `#theorem 12#` | `#lemma 4#` is external (§6) |
| `C/D`, `d(C/D)` | coset code and its minimum distance | `CosetCode C D`, `cosetCodeMinDist C D` (`#definition 17#`) | |
| `D_f` (linear case) | `{(u,p) ∈ C | u ∈ ker f}` | `kernelSubcode f C` (`#lemma 7#`) | not to be confused with the DRM `D_f` of §II! |
| `C_cat` | concatenated code of `#lemma 10#`/`#theorem 13#` | `image_linear_concat` | |
| `L` (`#theorem 14#`) | `max_α |f⁻¹(α)|` | `maxPreimageCard f` | |
| `ℓ` (`#theorem 15#`) | `min_α |f⁻¹(α)|` | `minPreimageCard f` | |

### 2.3 Conventions that are easy to get wrong

1. **`D_f` is overloaded.**  In §II and §IV `D_f` is a distance requirement
   matrix; in §VII it is the *subcode* `{(u,p) ∈ C | u ∈ ker f}`.  Lean names
   distinguish them (`drm`/`drmData`/`cdrm` vs `kernelSubcode`).
2. **Two parameter pairs.**  The paper states §II/§III results with `t`, §IV–§VIII
   with `(d_d, d_f)`, and translates by `d_d = 2t_d+1`, `d_f = 2t_f+1`.  Lean
   states the `(d_d,d_f)` version as primary (the paper's own view — see the
   paragraph after `#definition 6#`) and derives the `t`-version.
3. **`d_d ≤ d_f` vs `d_d < d_f`.**  `#definition 6#` says `d_d ≤ d_f` ("two non-negative
   integers"); `#definition 16#` says `0 ≠ d_d < d_f`.  The strict case is called *strict*
   in §V.  Each result carries the paper's own hypothesis, and the difference is
   recorded here instead of being silently unified.
4. **Diagonal of a DRM.**  Always `0`; the Lean side therefore quantifies over
   `i ≠ j` in `IsDCode`, and the paper's "for all `i,j`" is recovered because
   `d(pᵢ,pᵢ) = 0 ≥ 0`.
5. **Which distance goes where in `#definition 11#`.**  Equal function value ⇒ the
   `2t_d+1` row; different function value ⇒ the `2t_f+1` row.  Sanity check with
   `#example 7#`, whose matrix is reproduced in `PLAN.md` §1.2 as a test case.
6. **`N(q^k, 2t_d+1) − k`** in `#theorem 3#` is truncated subtraction in `ℕ`; the
   statement is only interesting when the first term exceeds `k`.
7. **Bit order.**  Nothing in the paper depends on a bit order and neither do we:
   `Word F n = Fin n → F` with no endianness convention.  A `decide` test that
   *does* depend on an explicit enumeration of words (e.g. `#example 6#`) must state the
   enumeration in a comment.

---

## 3. Design decisions for the Lean model

### 3.1 The alphabet is a parameter (`F`, not `ZMod q`)

The paper works over `F_q` throughout (with `q = 2` in §IV and §VI-B/C).  We
formalize `Word F n` for an arbitrary `[Field F] [Fintype F] [DecidableEq F]`,
so `#theorem 4#` (binary) is a specialisation and no statement is silently weakened.
`ZMod 2` is a `Field`, so the binary rows instantiate.

*Alternative considered:* formalize over `Bool` / `ZMod 2` first and generalise
later.  Rejected: the paper's bounds carry `q` in their constants
(`q^{k-1}(q-1)`, `2q/(M²(q−1)−a(q−a))`), so re-deriving them later costs more
than parameterising now.

### 3.2 Words are `Fin n → F`

`Word F n` is `Fin n → F`, the paper's `F_q^n`.  Consequences: mathlib's
`Fintype (Word F n)` gives `q^n` words; `Finset.univ` enumerates the space for
`decide` tests; a coordinate index is `i : Fin n` and the paper's `u_1` is `u 0`.

### 3.3 `hammingDist` comes from mathlib

`Mathlib.InformationTheory.Hamming` already provides `hammingDist`,
`hammingNorm`, the `Hamming` metric space and their lemmas
(`hammingDist_self`, `hammingDist_comm`, `hammingDist_triangle`,
`hammingDist_eq_hammingNorm`, `hammingDist_le_card_fintype`, …).  We import that
single module and do not re-derive coding theory.  `wt` abbreviates
`hammingNorm`.

### 3.4 `IsDCode` is a family, and `N` is a `sInf`

The paper's `D`-code is a *set* `P = {p₁,…,p_M}` together with "an ordering of
`P`"; Lean takes the ordered family `p : Fin M → Word F r` directly.  `N D` is
`sInf {r | IsDCode D r}`, the paper's "smallest integer `r` such that there
exists a `D`-code of length `r`".  An existence lemma (large `r` suffices:
concatenate one block per pair) shows the set is nonempty, which is what makes
`N` behave (attained, monotone).  This is `#remark 1#`'s "reduction to `N(D)`" made
literal.

### 3.5 Systematic encodings

`#definition 1#`/`#definition 6#` say *systematic* encoding.  In Lean, `IsSystematic C` records
`∀ u i, C u (Fin.castAdd r i) = u i`, i.e. the first `k` coordinates of `C u`
are `u`.  This hypothesis is what makes `d(C u, C v) = d(u,v) + d(p_u,p_v)` exact
(`#theorem 2#`, `#theorem 5#`); that identity is where a faithfulness error would be easiest
to hide, so the hypothesis is explicit in every statement that uses it.

### 3.6 Codes are `Finset`s of words, not matrices

Minimum distance, `G(C)`, coset codes and so on are stated for
`C : Finset (Word F n)` (or a `SimpleGraph` on words), so §V needs no matrix
machinery.  The generator matrix `G` and the standard form `[I_k | P]` appear
only where the paper actually uses them (§VII, via `LinearMap`/`Matrix`).

### 3.7 The *tests* use `Bool` as `F₂`, the library does not

The paper's examples are formalized as `decide` tests (`FCC/Examples.lean`), and
`decide` needs an alphabet whose `DecidableEq` the kernel can reduce.  `ZMod 2`
fails on that (the tactic gets stuck on `ZMod.decidableEq`), while `Bool` is
exactly `F₂` in mathlib's sense — `Mathlib.Algebra.Ring.BooleanRing` gives
`false = 0`, `true = 1`, `+` = xor — and reduces.  So the *tests* use `Bool`
(and `Fin 3` for the `q = 3` ball size), while every *statement of the paper*
stays over a general `[Field F]`, with `F = ZMod 2` available for the binary
corollaries of §IV.  This distinction is only about how a proof is discharged,
not about what is being claimed.

---

## 4. Open questions (to confirm before Phase 1 is frozen)

1. **Tiering.**  Is §V + §VI (perfect/MDS graphs, locally bounded, Hamming
   weight) in scope for this project, or is the deliverable §III–IV (the
   framework and the redundancy bounds) plus `#theorem 13#`?  The inventory in
   `PLAN.md` §1.1 covers everything; the phase table in §4 lets us stop after any
   milestone.
2. **`external` handling.**  Confirm the policy: results quoted from [1], [10],
   [14] are *never* `axiom`s; they appear as explicit hypotheses of the
   statements that need them (§6).  This keeps `axioms_check.ps1` honest, at the
   price of a few conditional statements (`#corollary 5#`, `#corollary 6#`).
3. **`N(M,D)` vs `N(D)`.**  Keep both, with `Nconst M D` defined as `N` of the
   constant matrix (definitional equality, proved as a lemma).
4. **Examples as tests.**  Confirm that §1.2's `decide` regression tests are
   wanted (they cost a session but pin the conventions).

---

## 5. Suspected paper issues (to check against the PDF when we reach them)

Recorded now so that they are not silently "fixed" later.  Each is resolved when
its phase is done, in `DEVLOG.md`.

1. **Direction of `#theorem 15#`/`#theorem 16#`.**  Both are printed as "*there exists* an
   `(f,t)`-FCC with length `n` **if** `E ≤ q^n/|∪_j B(v_j,t)|`", but the proofs
   establish the converse (an existing FCC forces that inequality), and both are
   then used in the converse direction, exactly like the classical Hamming
   bound: `#example 16#` concludes `n ≥ 9` ("the optimal length is 10"), `#example 17#`
   concludes "any `(f:3,5)`-FCC must have length `n ≥ 9`", and `#corollary 13#` says the
   bound "turns into the Hamming bound" for a bijection — where the Hamming
   bound is an upper bound on `E`.  We therefore expect to state them as "*if an
   FCC of length `n` exists then …*" and to flag the printed wording.
2. **Constants of `#lemma 1#`.**  `N(M,D) ≤ 2(D−2)/(1−2/q)·ln(D)/D` for `D ≥ 10`,
   `M ≤ D²`: the PDF's typesetting is ambiguous about the factors (`2D−2` vs
   `2(D−2)`, and whether `ln(D)/D` multiplies the whole right-hand side).  Check
   against [10, Lemma 2] before use; the row is `external` either way.
3. **`#definition 11#`'s missing `max(·,0)`.**  The printed case distinction shows
   `max(⋯,0)` only in its first line, while `#definition 7#` and the `#example 7#` matrix show
   `max` in every off-diagonal entry.  We use `max(⋯,0)` everywhere (the only
   version consistent with `#example 7#`).
   *Resolved 2026-09-14:* the `#example 7#` test also settles the diagonal — the
   printed matrix has zeros there, so the definition definitely carries the
   third case "`0` if `u_i = u_j`"; an earlier transcription of ours that
   omitted it failed the test.  See `DEVLOG.md`, phase 1a.
4. **`#theorem 4#`'s "similar proof" for Case 2.**  The paper states Case 2's matrix
   `D_f(t_d,t_f : u₂,u₁,u₃)` and says "a similar proof will follow"; the
   displayed matrix differs from Case 1's in two entries.  Both cases must give
   `r ≥ (4t_f+2t_d−1)/2`; verify when formalizing (a genuine gap would show up
   here).
5. **`#theorem 10#`'s covering argument.**  The proof needs the balls of a perfect
   code to *cover* `F_q^n` and be *disjoint*; the paper gets this from
   Hamming-bound equality plus `d = 2t+1`.  The Lean statement will make both
   facts explicit fields of "perfect" rather than re-deriving them.
6. **`#lemma 6#`, Case 2.**  "Since `d(u,v) ≥ wt(u) − wt(v)`, we have
   `d(u,v) ≥ 2t_f+1`, and `d(C_f(u),C_f(v)) = d(c_u,c_v)+d(p_u,p_v) ≥ 2t_f+1`"
   glides over the step `d(c_u,c_v) ≥ d(u,v)`, which needs `C` to be
   *systematic*.  Our proof makes that hypothesis explicit.

---

## 6. External results (used as hypotheses, never as `axiom`s)

| Label | Source | Used by |
| --- | --- | --- |
| `#lemma 1#` | [10, Lemma 2] | `#corollary 6#` |
| `#corollary 3#` | [1, Corollary 3] | `#example 8#` and discussion only (no theorem depends on it) |
| `#lemma 4#` | [14] | `#theorem 12#` (as the colouring hypothesis) |
| `#lemma 12#` | [1] (Gilbert–Varshamov type) | optional; §VIII upper bounds |
| — | [1, Appendix]: a binary code of length `n`, distance `2t+1` and redundancy `≤ t·log k + t(1 − (t/k)log e)` exists | `#corollary 5#` (carried as an explicit hypothesis).  The result is external; `#corollary 5#` itself is a formalizable statement. |

---

## 7. Review log

| Date | Step | What was checked against the PDF |
| --- | --- | --- |
| 2026-09-14 | Phase 0 | dictionary §2 built from §I-E, §II, §III, §IV, §VI, §VII, §VIII and the appendix; the `#example 6#` and `#example 7#` matrices recomputed entry by entry against the paper (they agree, and `#example 7#`'s DRM is reproduced in `PLAN.md` §1.2 as a test case); the suspected issues of §5 recorded. |
