# Statement-fidelity log

Every place where the Lean statement is **not** a literal transcription of the
paper, with the reason and the direction of the difference (a *stronger*
statement, i.e. fewer hypotheses, or a *weaker* one).  Transient problems —
things that are merely not written yet and will be written in the next session —
are not recorded here; they are `TODO`s in `FCC/Paper.lean`.

Each entry: where it is, what the paper says, what we do, why.

## 1. Definition 6 carries systematicity (stronger)

`#definition 6#` prints only the two distance conditions, but every encoding in
§III-A is systematic and `#theorem 2#`'s proof needs it (to split `d(Cu,Cv)` into
the message part and the redundancy part).  Our `IsFCCData` therefore includes
`IsSystematic`, exactly as `#definition 1#` does.  *If we ever want the literal
§III-vs-§II distinction, split off an `IsSystematicFCCData` and restate.*

## 2. §VI uses the codes only through their minimum distance (stronger)

`#lemma 3#`, `#corollary 9#`–`#corollary 12#`, `#theorem 12#` and `#lemma 6#`
assume a "systematic `[n,k,d_d]` linear code".  Our statements assume only
`2t_d+1 ≤ d(Cv,Cw)` for `v ≠ w` (and `n = k + r`).  Fewer hypotheses = a
*stronger* statement; nothing about the paper's conclusion is lost.

## 3. External results enter as hypotheses, never as `axiom`s

`#lemma 1#` ([10]), `#lemma 4#` ([14]), `#lemma 12#` ([1]) and the [1, Appendix]
bound behind `#corollary 5#` are **not** formalized.  Where a result is needed it
appears as an explicit hypothesis: `#theorem 12#` takes the colouring of
`#lemma 4#` as `hcol`, and `#corollary 5#`/`#corollary 6#` are therefore still
`todo` — they would be statements *about an unproved external bound*.

## 4. Perfect and MDS codes: prose in the paper, `(internal)` here

§V-B introduces both classes in prose ("a code that achieves the Hamming bound
is called a perfect code"; "an `(n,M,d)_q` code is MDS if and only if
`M = q^{n−d+1}`"), with no numbered definition.  Per the convention of
`Notation.md` §1 they are `(internal, §V-B)` declarations in `FCC/Basic.lean`:
`IsPerfect` = minimum distance `≥ 2t+1` **and** the Hamming bound met with
equality; `IsMDS` = `|C| = q^{n−d+1}` **and** `d_min(C) = d`.  The paper's
perfect-code discussion also uses "the balls of radius `t` cover the space,
without overlap", which our `IsPerfect` does **not** spell out — `#theorem 10#`
will have to derive it from the Hamming equality.

## 5. "Connected graph" is `SimpleGraph.Preconnected`

The paper's connectedness of `G(C)` is `G.Preconnected` in mathlib
(`∀ u v, G.Reachable u v`).  mathlib's `Connected` is a strictly stronger
notion (it also asks the vertex set to be non-empty), so we use `Preconnected`
and never the stronger one in the statements of §V.

## 6. `N`, `r_f`, `d_min`, `d(fᵢ,fⱼ)` are minima (`sInf`) — the "attained" API is phase 3.0

The paper defines all four as minima.  In Lean they are `sInf`s over `ℕ`, which
are not computable, so until phase 3.0 supplies "there is a code attaining it"
lemmas:

* the examples' `N(D) = k` and `d_min = k` claims are checked as the decidable
  pair "a witness exists" + "nothing smaller exists";
* the FDM checks of `#example 3#` and of `#example 5#` cannot be `decide`d at all
  (a `sInf` does not reduce) — they wait for the API or for a computable
  restatement of the minimum over preimages.

## 7. `d(C/D)` is defined through Lemma 8's equivalent form

`#definition 17#` defines the coset distance as a double minimum over cosets.
We define `cosetDist D z` as `min_{d ∈ D} wt(z + d)` — the form `#lemma 8#`
proves equal to the double minimum — and `CosetCode` as the *set of cosets*
(`Set (Set C)`) instead of the quotient `C ⧸ D`.  `#lemma 8#` therefore becomes
the bridge between the printed definition and ours, not a mere remark.

## 8. Not stated, and why (not merely "not yet")

* `#theorem 7#` speaks about the redundancy `r_s` of the two-step *scheme* —
  a construction-level quantity that §III-A introduces but neither §I–§II nor
  our phase 1 defines.  Stating it faithfully needs `r_s` as a definition first.
* `#theorem 9#` counts the connected components `Q` of `G(C)`; mathlib has
  `ConnectedComponent` but the paper's "cannot be an `(f : d, d_f)`-FCC for any
  `f` with `|Im(f)| ≥ Q + 1`" needs `Q` as a number, i.e. a component-count
  helper that phase 1 did not define.
* `#corollary 3#` is quoted from [1] and used only in the paper's discussion.
* `#remark 1#` is a design remark; it has no Lean declaration by convention
  (`PLAN.md` §1.1 marks it `recorded here only`).

## 9. Examples that depend on later results

`#example 11#` quotes `N(2⁸,3) = 12` from [1]; `#example 15#`, `#example 16#`
and `#example 17#` illustrate the §VIII bounds (Plotkin/Hamming) and their
conclusions ("`n ≥ 9`") are exactly those bounds.  They are completed together
with `#theorem 14#`–`#theorem 16#`.

## 10. Suspicious print in the paper (see `Notation.md` §5 for the details)

`#theorem 15#`/`#theorem 16#` are printed as existence statements while their
proofs and all their uses run the other way; `#lemma 1#`'s constants are
ambiguous in the PDF; `#definition 11#`'s printed case split omits `max(·,0)` in
two branches; `#theorem 4#`'s "similar proof" needs checking.  Each is resolved
when its phase is done, and the resolution is recorded in `DEVLOG.md`.

## 11. `#theorem 2#` carries one side condition that the paper leaves implicit

`#theorem 2#` is the first paper result proved in this development (phase 3.2).
Two things the paper leaves implicit showed up while proving it; one became a
hypothesis of the statement and the other was *proved* as an internal lemma
(phase 3.14), so the final statement carries only `d_d ≤ d_f`.  Neither is a
`sorry`-style gap, and neither weakens the content of the identity.

**(a) `d_d ≤ d_f`.**  `#definition 6#` states `d_d ≤ d_f` as part of the
definition, and the paper's `r_f(k : d_d, d_f)` is only ever used under it, so
making it a hypothesis is faithful.  It is *used* by the proof, though — it is
not decoration: `IsFCCData` demands the data-protection distance `d_d` of
**every** pair `u ≠ v` (the paper's literal wording: "for any `u₁, u₂` with
`u₁ ≠ u₂`, `d(C_f(u₁), C_f(u₂)) ≥ d_d`"), while the DRM `D_f` only records the
`2t_d+1` slack on the pairs with `f(u₁) = f(u₂)`; for a pair with
`f(u₁) ≠ f(u₂)` the DRM supplies `2t_f+1 − d`, so `2t_d + 1 ≤ 2t_f + 1` is what
closes the `≤` half.  Without it the identity is **false**: a DRM code of length
`r` can exist while the systematic code built from it fails data protection.
Hence `hdf : 2 * t_d + 1 ≤ 2 * t_f + 1` in `optimalRedundancyData_eq_N_drmData`
and in the internal `optimalRedundancyData_le_of_isDCode`.

**(b) Non-vacuity of the FCC set — *proved*, not assumed.**  `optimalRedundancyData`
and `N` are `sInf`s with the convention `sInf ∅ = 0` (issue §6).  If no
`(f : 2t_d+1, 2t_f+1)`-FCC existed at all, the left-hand side of `#theorem 2#`
would be the vacuous `0` while `N(D_f) > 0` in general, and the identity would
fail for a reason that has nothing to do with the paper.  In the first version of
the proof this entered as an explicit hypothesis `hex`.  It is now a theorem:

`exists_isFCCData : ∃ r, ∃ C : Word F k → Word F (k + r), IsFCCData f C d_d d_f`

for **arbitrary** `f`, `d_d`, `d_f` — write the message down `m = max d_d d_f`
times (`C u = (u, u, …, u)`, `m` copies of `u` in the redundancy block); then
`d(C u, C v) = d(u,v) + m·d(u,v) ≥ m ≥ d_d, d_f` for `u ≠ v`, and `C` is
systematic by construction (`repWord`, `hammingDist_repWord` in `FCC/Balls.lean`).
This removes `hex` from `#theorem 2#` and is what makes every lower bound of §IV
(`#theorem 2#`, `#theorem 3#`) go through: the optima are attained, so
`Nat.sInf_mem` and `Nat.find_spec` can be used.

Only (a) remains as a hypothesis, and only of `#theorem 2#` and of the internal
`optimalRedundancyData_le_of_isDCode`; no other row of the catalogue is affected.

## 12. `#theorem 1#` and `#theorem 7#`: the FDM/CFDM must be indexed by `Im(f)`

**Found while preparing the §II proofs (2026-09-20), fixed 2026-09-22.**  The
paper's matrices `D_f(t, f₁, …, f_E)` and `D_{C,f}(t_f, f₁, …, f_E)` are indexed
by the *image* of `f` (`E = |Im(f)|`, the finitely many function values).  Two of
our transcriptions instead handed `N` the matrix indexed by the ambient alphabet
`α`, which in our signatures is an arbitrary type — `optimalRedundancy_le_fdm`
(`#theorem 1#`, via `fdm`) and the upper-bound half of `two_step_redundancy_bounds`
(`#theorem 7#`, via `cfdm`).  As stated they are **false for infinite `α`**:

* `fDist f a b = 0` (resp. `codedFDist f C a b = 0`) when a preimage is empty —
  the blanket conventions of `#definition 4#`/`#definition 8#` (issue §8) — so
  for `a, b ∉ Im(f)` the matrix demands distance `2t+1` between *distinct values*;
* an infinite index set cannot be placed in the finite space `Word F r`, so the
  code set is empty and `N = 0` by the `sInf ∅ = 0` convention (issue §6), while
  the left-hand side can be positive;
* concrete counterexample: `F = ZMod 2`, `k = 1`, `α = ℕ`, `f` the two-valued map
  on the one-bit messages, `t = 1`: `r_f = 2` (two messages at distance `≥ 3`
  need length `≥ 3 = k + r`), while the `α`-indexed right-hand side is
  `N (fdm f 1) = 0`.

**Fix (applied).**  Both statements now index the matrix by the image,
`ι := Set.range f` (`{a : α // ∃ u, f u = a}`), with the matrix
`fun a b => fdm f t a.1 b.1` (resp. `cfdm f C tf a.1 b.1`) — the paper's
`f₁, …, f_E` literally.  The definitions `#definition 5#`/`#definition 9#` stay
total functions on `α` (so that they need no subtype plumbing), and their
docstrings now say that they are meant to be read on `Im(f)`, and why the
whole-`α` index set is not merely unproved but wrong.

**Not affected: `#corollary 1#` and `#corollary 2#`.**  Their right-hand sides are
DRMs indexed by *messages* (`Fin m`, `Fin E`) — exactly what the paper does — so
their statements were faithful as printed.  With the corrected `#theorem 1#` they
are now proved too (the code set for the image-indexed FDM is nonempty: take a
representative of each value and repeat it `2t+1` times, which is the same
`repWord` device as in issue §11(b)).
