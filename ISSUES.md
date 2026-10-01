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

## 13. `#theorem 5#`/`#corollary 4#` use the systematic form of `C`; `#theorem 7#` is still a proxy

**(a) Systematicity of `C` (`#theorem 5#`, `#corollary 4#`).**  The proof of
`#theorem 5#` in the paper begins "Without loss of generality, consider a
systematic form of `C`, i.e. `c_u = (u, w_u)`".  That step is legitimate for a
*linear* code (permute coordinates to reach standard form), but our
`C : Word F k → Word F (k+r)` is an arbitrary labelling map, for which the
systematic form is an extra hypothesis.  It is now explicit
(`hCsys : IsSystematic C`) in both `#theorem 5#` and `#corollary 4#`.  Exactly
where it is used: turning `d(c_u,c_v) ≥ 2t_d+1` into
`d(w_u,w_v) = d(c_u,c_v) − d(u,v) ≥ 2t_d+1 − d(u,v)` — the paper's identity (1).

**(b) The message family is arbitrary.**  `#theorem 5#` is stated for an arbitrary
`u : ι → Word F k`; the paper's `u₁, …, u_{q^k}` is the instance
`ι = Word F k`, `u = id`.  `D_f`/`D_{C,f}` are family-indexed (`#definition 11#`,
`#definition 7#`) and the paper itself uses subsets in `#theorem 3#`, so this is a
harmless generalization — and it is what makes `#corollary 4#` a one-liner.

**(c) `#corollary 4#` also carries `hdf`.**  It combines `#theorem 2#` with
`#theorem 5#`, so it inherits the standing `d_d ≤ d_f` of §IV (issue §11(a)).

**(d) `#theorem 7#` — reworked so that it says what the paper says (2026-09-22).**
The paper bounds the redundancy `r_s` of the two-step *scheme* from both sides,
`N(D_{C,f}(t_f : u₁,…,u_M)) + n − k ≤ r_s ≤ N(D_{C,f}(t_f : f₁,…,f_E)) + n − k`,
with `r_s = (n−k) + r'` and `r'` the second-step block.  The first transcription
asserted instead (i) the definitional unfolding of `schemeRedundancy` — a
tautology standing in for the lower bound — and (ii) a comparison of two `N`'s,
neither of which is the paper's statement.  It now reads:

* the scheme is modelled by `twoStepCode C E` (the encoder `C_f(u) = C'_f(c_u)`
  of §III-A: the codeword `C u` followed by the second block `E u`) and by
  `IsSecondStep f C tf E`, which is the paper's Step 2 condition
  `d(C'_f(c_u), C'_f(c_v)) ≥ d_f` for `f(u) ≠ f(v)`, i.e.
  `d(C u,C v) + d(E u,E v) ≥ 2t_f+1`;
* **lower bound**: every second step produces an `(f : 2t_d+1, 2t_f+1)`-FCC
  (`twoStep_isFCCData`, the paper's "straightforward verification") whose total
  redundancy `r_s = r + r'` is at least `N(D_{C,f}(u₁,…,u_M)) + n − k`: by Step 2
  the block `E` is a `D`-code for the CDRM;
* **upper bound**: any CFDM `D`-code of length `L` over the image values — the
  index set of `#theorem 1#`, `ISSUES.md` §12 — gives a second step of block
  length `L`, hence a scheme with `r_s = L + n − k`; taking `L := N(CFDM)` (which
  exists in the paper's finite setting) is the printed upper bound.

One further modelling note: the second step is a *block assignment*
`E : Word F k → Word F r'` on the messages rather than a function on the codeword
set `Im(C)`.  Since `C` has minimum distance `2t_d+1 ≥ 1` it is injective, so the
two are the same data, and the message-indexed form avoids introducing a partial
function `f ∘ C⁻¹` on the image.  The paper's clause "`n` denotes the minimum
possible length of a linear code ..." is a remark about which first step the
scheme *uses*; both bounds hold for any systematic `[n,k,2t_d+1]` code, which is
what the Lean statement assumes.

## 14. `#theorem 8#`/`#theorem 9#`: the codeword set must be the *range* of the encoding

**Found while checking §V against the PDF (2026-09-22); fixed and proved.**  In §V
the paper works with a `(n, q^k, d)` code `C`: it has exactly `q^k` codewords, one
per message ("let `c_u` denote the codeword that corresponds to the message vector
`u ∈ F_q^k`"), so the encoding is a *bijection* onto `C`.  The first transcription
weakened this to "all codewords lie in `C`" (`∀ u, enc u ∈ C`), and that makes both
statements **false**:

* counterexample: `k = 1`, `r = 2` (so `n = 3`), `F = F₂`, `C = {000, 001, 100}`,
  `d = d_min(C) = 1` — the only pairs at distance one are `000–001` and `000–100`,
  so `G(C)` is a `V`, hence connected — with `f` the two-valued function on `F₂¹`
  (`|Im f| = 2`) and `d_f = 2 > d`.  The encoding `enc 0 = 001`, `enc 1 = 100` is
  systematic, its codewords lie in `C`, and the only pair with different values is
  at distance `3 ≥ 2 = d_f`, so it *is* an `(f : 1, 2)`-FCC whose codewords all lie
  in `C` — although `G(C)` is connected.  (What the paper's setting excludes:
  `|C| = 3 ≠ 2 = q^k`.)
* the corrected statements require the range to be exactly `C`,
  `Set.range enc = ↑C`, i.e. every codeword of `C` is used by the encoding.  That is
  the paper's `(n, q^k, d)` code together with its labelling.

With the correction both theorems are provable, and the proof shows where the
hypothesis is used: function values are *locally constant* on `C` (two codewords at
the minimum distance `d < d_f` cannot be images of messages with different values),
so the set of values carried by a codeword is the same on every connected component
— and that set is a subsingleton (one codeword cannot serve two values either,
since `d_f ≤ d(x,x) = 0`).  Hence different function values force different
components; `#theorem 8#` is the case `|Im f| ≥ 2` with `G(C)` connected, and
`#theorem 9#` is the counting version with `Q` components and `|Im f| ≥ Q + 1`.

## 15. §V-B: the Hamming-radius sum in `#corollary 7#`, and the hypotheses of `#corollary 8#`

**Found while checking §V-B against the PDF (2026-09-29); both statements corrected.**

**(a) `#corollary 7#`: the sum runs to `⌊(d_d−1)/2⌋`, not to `d_d/2`.**  The printed
condition is `q^{n−k} = Σ_{i≤⌊(d_d−1)/2⌋} C(n,i)(q−1)^i`, i.e. the ball radius
`(d_d−1)/2` (the number of errors a code of minimum distance `d_d` corrects).  The
first transcription wrote `Finset.range (dd / 2 + 1)`, i.e. `i ≤ d_d/2`, which adds
one spurious term when `d_d` is even (`d_d = 4`: `⌊3/2⌋ = 1` versus `4/2 = 2`).  That
made the hypothesis strictly stronger than the paper's.  Fixed to
`Finset.range ((dd - 1) / 2 + 1)`.

**(b) `#corollary 8#`: the hypothesis is the *existence* of an MDS code, and
`|Im(f)| ≥ 2` is needed.**  The paper writes "Assume there exists an MDS `(n, q^k, d)_q`
code, i.e. `n = k + d − 1`".  The first transcription kept only the parameter
relation `n = k + d − 1` and dropped `|Im(f)| ≥ 2`; as stated the corollary is
**false**:

* with a *constant* `f` (`|Im f| = 1`) the function-correcting condition is vacuous,
  so an `(f : d, d_f)`-FCC only needs data protection at distance `d`.  Concretely
  `F = F₂`, `k = 1`, `d = 2`, `n = k + d − 1 = 2`: the encoding `u ↦ (u,u)` is
  systematic with `d(C0,C1) = 2 = d`, so a scheme of redundancy `1 < 2 = d` exists
  and `d ≤ r_f` fails;
* and the parameter relation alone does not give a code to apply `#theorem 8#`/`#theorem 11#`
  to — for some triples with `n = k + d − 1` no MDS code exists at all (e.g. `q = 2`,
  `n = 4`, `d = 3`: the Hamming bound forbids `M = 4`).

The statement now takes `hmds : ∃ C : Finset (Word F n), IsMDS C d ∧ C.card = q^k`
(the paper's "there exists an MDS code", which by `IsMDS` forces `n = k + d − 1`) and
`h2 : |Im f| ≥ 2` (as in `#theorem 8#`).

## 16. `minDistGraph` has the ambient word space as its vertex type

**Found while proving `#lemma 2#`/`#theorem 11#` (2026-09-29); the connectivity
statements were corrected.**  The paper's `G(C)` has vertex set `C` ("the graph
whose vertex set is `C`"), whereas our `minDistGraph C : SimpleGraph (Word F n)`
uses the ambient space as the vertex type and folds `x, y ∈ C` into the adjacency
relation.  The two graphs have the same paths *between codewords* — a walk starting
at a codeword runs through codewords only, because every edge joins two of them —
but the connectivity *predicate* differs: `(minDistGraph C).Preconnected` also
demands that words outside `C` be reachable, and those are isolated, so it is false
for every proper code.  Hence:

* "`G(C)` is connected" is stated as *codeword reachability*,
  `∀ u ∈ C, ∀ v ∈ C, (minDistGraph C).Reachable u v`, in `#theorem 8#`/`#theorem 9#`
  (hypothesis) and `#theorem 10#`/`#theorem 11#` (conclusion).  This is exactly
  "the graph on vertex set `C` is connected", so nothing is weakened;
* `componentCount` (internal, used by `#theorem 9#`) now counts the components of
  the paper's graph, i.e. the components of `minDistGraph C` that meet `C`:
  `Nat.card ↥(Set.range fun x : ↥C => (minDistGraph C).connectedComponentMk x)`.
  The previous version counted *all* components of the ambient graph, which
  included one isolated component per word outside `C`; that made `#theorem 9#`'s
  hypothesis `componentCount = Q` strictly stronger than the paper's (its `Q` was
  `q^n − |C|` too large).

## 17. `#corollary 7#` needs `|Im f| ≥ 2` (its statement is false for `k = 0`)

**Found while preparing phase 3.7 (2026-09-30); the proof is the next step.**  The
paper states: "Let `f : F_q^k → Im(f)` be a function.  Then for an
`(f : d_d, d_f)`-FCC with `d_f > d_d` we have `r_f(k : d_d, d_f) ≥ n−k+1`, where
`n` satisfies `q^{n−k} = Σ_{i≤⌊(d_d−1)/2⌋} C(n,i)(q−1)^i`", and derives it "from
`#theorem 8#` and `#theorem 10#`" — but `#theorem 8#` needs `|Im f| ≥ 2`, and
without that hypothesis the claim is false:

* take `k = 0` (so `F_q^0` has a single message and `|Im f| = 1`).  Then `r_f = 0`
  (the empty encoding protects the only message vacuously), while `#corollary 7#`
  would claim `n − 0 + 1 ≥ 2`, i.e. `r_f ≥ 2`.  Concretely `q = 2`, `d_d = 3`,
  `d_f = 4`: `n = 1` satisfies `2^{1−0} = 2 = Σ_{i≤1} C(1,i)1^i`, and the claim
  `2 ≤ r_f(0 : 3, 4) = 0` is false;
* more generally the case `d_d = 2s+1`, `d_f = 2s+2` needs `|Im f| ≥ 2` for the
  proof of `#corollary 7#` to close: the `m = n` case of the argument is exactly
  "the code is perfect, hence `G(C)` is connected by `#theorem 10#`, hence no
  `(f : d_d, d_f)`-FCC for `|Im f| ≥ 2` by `#theorem 8#`" — for a *constant* `f`
  that step is unavailable (and `#theorem 8#` itself, hence the paper's derivation,
  already excludes it).

The statement will therefore take `h2 : |Im f| ≥ 2` (the same hypothesis as
`#theorem 8#` and, after §15(b), `#corollary 8#`), exactly as the printed proof
does.  (`|Im f| ≥ 2` also gives `q ≥ 2` and `k ≥ 1`, which the argument needs.)

Proving the corollary found two further hypotheses that the printed one-liner
("where `n` is the integer satisfying `q^{n−k} = Σ_{i≤⌊(d_d−1)/2⌋}…`") does not
supply; both hold in the paper's picture, where `n` is the length of a perfect code
with `q^k` codewords:

* `hdd : 1 ≤ d_d`.  For `d_d = 0` the transcription is **false**: take `q = 2`,
  `k = 1`, `d_f = 1`, `f = id` (so `|Im f| = 2` and `d_f > d_d`).  The printed
  equation reads `2^{n−1} = Σ_{i≤0} C(n,i) = 1`, i.e. `n = k = 1`, so the corollary
  would claim `r_f ≥ n − k + 1 = 1`; but the systematic encoding `u ↦ u` of
  redundancy `0` satisfies every clause of `#definition 6#` for `(f : 0, 1)` (data
  protection at distance `0` is vacuous, and `f u ≠ f v` forces `u ≠ v`, so
  `d = 1 ≥ d_f`), hence `r_f = 0`;
* `hkn : k ≤ n`.  The printed equation *does* have solutions with `k > n`: with
  `t = 0` (i.e. `d_d ≤ 1`) the sum is `1` for every `n`, so any `n < k` satisfies
  it; the claim then reduces to `1 ≤ r_f`, which needs a separate argument (that no
  systematic encoding of redundancy `0` can be function-correcting) that is not part
  of the paper's derivation.  Since the paper's `n` comes from a perfect code of
  length `n` holding `M = q^k` codewords, `q^k ≤ q^n` and `k ≤ n` there.

The proof itself (`perfect_optimalRedundancyData_ge`) is the paper's: the packing
bound on the optimum gives `A_t(k+r) ≤ q^r`; `k + r = n` makes the code perfect
(then `#theorem 10#` + `#theorem 8#`), `k + r < n` contradicts the strict
monotonicity `A_t(n) < A_t(k+r)·q^{n−k−r}`, and `t > k + r` forces `k = 0`.

## 18. §VI-A: the construction of `#lemma 3#` needs *systematicity* and an order on the values

**Found while proving `#lemma 3#` (2026-09-30); the first two are applied, the third is
recorded for the corollaries.**  Three things the printed statement leaves implicit:

* **`C` is used as a *systematic* encoding.**  The printed hypothesis is "a systematic
  `[n,k,d_d]` linear error-correcting code `C`", but the transcription in
  `FCC/Paper.lean` had kept only its minimum distance.  The construction needs more:
  Case 1 of the proof (`d(u,v) ≥ d_f`) concludes `d(c_u,c_v) ≥ d_f` *from
  systematicity* — for a systematic code the message coordinates alone force
  `d(c_u,c_v) ≥ d(u,v)` (`hammingDist_eq_msg_add_red`) — which a minimum-distance
  hypothesis does not give.  The statement now carries `hCsys : IsSystematic C`,
  i.e. the paper's own word;
* **the two parity blocks need `q ≥ 2`.**  The construction writes `1…1` or `0…0`
  in `d_f − d_d` fresh coordinates; the paper's alphabet is the field `F_q`, so
  `q ≥ 2` is automatic there, while our statements are over an arbitrary finite
  alphabet.  `#lemma 3#` therefore assumes `[Nontrivial F]` (⟺ `1 < q`);
* **the paper's `max B_f(u,d_f−1)` needs a total order on the value set**, which it
  inherits from `Im(f) ⊆ ℕ` in [1].  Our value type `α` is arbitrary, so the
  marking is defined through a *fixed global choice function of the set*
  (`pickElem`), which is what the proof actually uses: for `d(u,v) ≤ d_f−1` with
  `f(u) ≠ f(v)` the two function balls are *equal* two-element sets (both contain
  `f u`, `f v` and have at most two elements), hence get the same marked value, so
  exactly one of `f(u)`, `f(v)` is marked (`ballMark_ne`).  Nothing is weakened: no
  order is needed for the argument.

The same review found that `#corollary 9#`–`#corollary 12#` have a related problem:
their hypothesis is a perfect *linear* code (resp. an MDS code), and the proof needs
its **systematic form** — a linear-[n,k]-code has one (the paper invokes it in §VII:
"any linear code is equivalent to a linear code with a generator matrix in standard
form"), but this repository has no linear-code theory yet (definitions 16–18 and
`#lemma 7#`–`#lemma 10#` are phases 3.10, still `sorry`).  Until then those
corollaries will carry the systematic encoder explicitly, with the perfect/MDS code
kept as the hypothesis that supplies it (`ISSUES.md` §18, continued in the next
session).

**Resolution (2026-09-30, same day).**  `#corollary 9#`–`#corollary 12#` are now
stated with a single bundled hypothesis

```text
hcode : ∃ (C : Finset (Word F (k + r))) (E : Word F k → Word F (k + r)),
  IsPerfect C t ∧ C.card = q^k ∧ IsSystematic E ∧ Set.range E = ↑C ∧
  ∀ v w, v ≠ w → d_d ≤ d(E v, E w)          (and, for the MDS pair, IsMDS C d_d
                                              and d_d = r + 1 in place of IsPerfect)
```

i.e. the paper's perfect/MDS code *together with* its systematic form; the
proofs only use `E` (via `#lemma 3#`), exactly as the paper does.  When §VII's
linear-code theory lands, the second and third components become derivable from
the first and the bundle can be simplified.  The optimality corollaries
(`#corollary 10#`, `#corollary 12#`) additionally carry `|Im f| ≥ 2` (their lower
half is `#corollary 7#`/`#corollary 8#`, `ISSUES.md` §17) and `#corollary 10#`
carries `1 ≤ d_d` for the same reason.  The `Finset`-valued statements need a
larger elaboration budget (`set_option maxHeartbeats 1000000` around the four
declarations).

The same review confirmed that `IsPerfect C t` — minimum distance `≥ 2t+1` plus
`q^n = |C| · |B(0,t)|` — is enough for everything `#theorem 10#` uses: it implies
the balls of radius `t` around the codewords tile the space (`card_ball`,
`pairwiseDisjoint_ball`) and that the minimum distance is *exactly* `2t+1`
(`minDist_eq_of_isPerfect`, needed for the adjacency `d(u,u') = 2t+1`, which the
paper reads off `d_min(C) = 2t+1`).

## 19. `#lemma 5#` is a *binary* statement (`N(4,2t) = 3t`)

**Found while proving `#lemma 5#` (2026-09-30).**  The paper writes: "let
`N(λ, 2t)` be the minimum length of a **binary** error-correcting code with `λ`
codewords and minimum distance `2t`.  Then `N(4, 2t) = 3t`", and quotes it from
[14].  The transcription had stated it over an arbitrary alphabet `F`
(`Nconst (F := F) 4 (2 * t) = 3 * t`), which is **false** as soon as `q ≥ 4`: for
`t = 1`, `q = 4` the four words `(x, −x)` (`x ∈ F₄`) of length `2` are pairwise at
distance `2`, so `N(4, 2) ≤ 2 < 3 = 3t`.

The statement is therefore specialised to `F₂` — `Nconst (F := F₂) 4 (2 * t) = 3 * t`
— and *proved* here instead of quoted ([14, Lemma 5]): the four odd words of `F₂³`
(`000, 011, 101, 110`, internal `base4`) are pairwise at distance `≥ 2`, and
repeating them `t` times (`repWord`) gives the upper bound; the lower bound is the
Plotkin double counting `three_binary_le` — three binary words at pairwise distance
`≥ 2t` have length `≥ 3t`, since at each coordinate three binary letters disagree in
`a(3−a) ≤ 2` of the three pairs, so the three distances sum to at most `2n` while
they sum to at least `3 · 2t`.

## 20. `#theorem 12#` needs systematicity, `t_d ≤ t_f` and `q ≥ 2`

**Found while proving `#theorem 12#` (2026-09-30).**  The printed statement is
"for any `(2t_f, λ)`-bounded function `f` satisfying the contiguous block condition
given in Lemma 4, and a systematic `[n,k,2t_d+1]` linear error-correcting code `C`,
`r_f(k,t_d,t_f) ≤ n − k + N(λ, 2(t_f − t_d))`".  The proof (the two-step
construction of §III-A with second step `p_u := c'_{Col_f(u)}`) needs three things
the transcription had left implicit:

* **systematicity** of `C` — Case 1 (`d(u,v) ≥ 2t_f+1`) concludes
  `d(C u, C v) ≥ d(u,v)` from it (`hammingDist_eq_msg_add_red`), exactly as in
  `#lemma 3#`; the statement now carries `hCsys : IsSystematic C`;
* **`t_d ≤ t_f`** — the arithmetic `(2t_d+1) + 2(t_f−t_d) = 2t_f+1` of Case 2 needs
  it; it is the standing `d_d ≤ d_f` of `#definition 6#` (`htd`);
* **`q ≥ 2`** — the second step uses a code of length *exactly*
  `N(λ, 2(t_f−t_d))`, obtained from the attainment of `N`, which needs two distinct
  letters (`exists_isDCode_const`, whence `[Nontrivial F]`; in the paper's field
  this is automatic).

The boundedness hypothesis `IsLocallyBounded f (2*t_f) lam` is retained for
fidelity but not used in the proof: boundedness plus the contiguous block condition
is what the *external* `#lemma 4#` turns into the colouring hypothesis `hcol`
(hence the name `_hf`).  The paper's "particularly, for `q = 2` and `λ = 4`"
(`r_f ≤ n − k + 3(t_f−t_d)`) is this bound combined with `#lemma 5#`.

## 21. `#lemma 6#`: two bounds, and the same implicit hypotheses as `#theorem 12#`

**Statement fixed and both bounds proved 2026-09-30.**  The paper's Lemma 6 gives
**two** bounds for the Hamming weight function `f(u) = wt(u)` and a systematic
`[n,k,2t_d+1]` code `C`:

```text
r_f ≤ n − k + N(2t_f+1, 2(t_f − t_d)),   or
r_f ≤ N(q^k, 2t_d+1) + N(2t_f+1, 2(t_f − t_d)) − k,
```

while the transcription had only the first, and had dropped the word *systematic*.
Both are now stated (`hammingWeight_redundancy_le`, `hammingWeight_redundancy_le_optimal`),
with the same three explicit hypotheses as `#theorem 12#` (§20): `IsSystematic C`
(the case `|f(u) − f(v)| > 2t_f` needs `d(u,v) ≤ d(C u, C v)`), `t_d ≤ t_f` (the
standing `d_d ≤ d_f`), and `[Nontrivial F]` (`q ≥ 2`, for the attainment of `N`).
The second bound replaces the given code by an *optimal* `q^k`-word code of
minimum distance `2t_d+1`; as in §18, that code has to come with its systematic
form, so its proof will bundle it (the statement above is the paper's shape).

The proof is the paper's: the second step is `p_u := c'_{f(u) mod (2t_f+1)}` (an
optimal `2t_f+1`-word code `c'` of minimum distance `2(t_f−t_d)`, obtained from the
attainment of `N`), and for `f(u) ≠ f(v)` either the residues differ — then the two
second blocks are at distance `≥ 2(t_f−t_d)` and the total is `≥ 2t_f+1` — or they
agree, in which case the weights differ by at least the modulus `2t_f+1` (the
internal residue lemma `mod_ne_of_sub_lt`, from `Nat.ModEq.dvd'`), so
`d(u,v) ≥ wt(u) − wt(v) ≥ 2t_f+1` (`wt_le_wt_add_hammingDist`) and systematicity
folds the first step in.  The second bound is the first one applied to a systematic
encoder of the optimal length `N(q^k, 2t_d+1)` (bundled in `hcode`, as in §18).

## 22. `#theorem 18#`: the binomial `C(n−2,t−1)` needs `t ≥ 1` in Lean

**Found and fixed 2026-10-01, before proving the theorem.**  The printed formula

```text
|B(u₁,t) ∪ B(u₂,t) ∪ B(u₃,t)| = 3 Σ_{i≤t} C(n,i) − 6 Σ_{i≤t−1} C(n−1,i)
                                  + C(n−2,t−1) + 4 Σ_{i≤t−2} C(n−2,i)
```

is stated for all `t ≥ 0` in the paper, where `C(n−2,t−1)` with `t = 0` means
`C(n−2,−1) = 0` (and the formula then reads `3 = 3`, the union of three distinct
singleton balls).  In `ℕ`, however, `t - 1` truncates to `0`, so the same expression
reads `C(n−2,0) = 1`.  At `n = 2`, `t = 0`, for the three distinct vectors
`u₁ = 00`, `u₂ = 10`, `u₃ = 01`:

* the left side is `|{u₁} ∪ {u₂} ∪ {u₃}| = 3`;
* the right side is `3·C(2,0) − 6·0 + C(0, 0−1) + 4·0 = 3 + C(0,0) = 4`.

So the transcription as printed is *false* at `t = 0`.  The statement now carries
the hypothesis `1 ≤ t` (`card_ball_union_three` in `FCC/Paper.lean`), which makes
every `t - 1`, `t - 2` exact and leaves the formula verbatim; this is the same
convention the paper prints explicitly for the twin result `#theorem 19#`
(`t ≥ 2` there).  The identity is provable for all `t ≥ 1` — the paper's proof
(four cases for the triple intersection, then inclusion–exclusion) is unaffected.

## 23. `#theorem 16#`/`#corollary 14#`: the ball radius must be tied to the distance

**Found and fixed 2026-10-01, before proving them.**  An `(f : d_d, d_f)`-FCC has
*two* error-correction radii `t_d ≤ t_f`, and the paper fixes `d_d = 2t_d + 1`,
`d_f = 2t_f + 1` (`Notation.md` §5).  The transcriptions of `#theorem 16#` and
`#corollary 14#` had left the ball radius (`t_f`, respectively `t_d`) as a free
parameter with no link to the distances, which makes both statements false:

counterexample: `F = Bool`, `k = 1`, `r = 0` (so `n = 1` and `q^n = 2`),
`f = C = id` (the identity is systematic and preserves distances) and
`d_d = d_f = 1`.  Then `E = 2`, `ℓ = 1`, and with `t_d = 1` the ball `B(0,1)` is
the whole space, so `#corollary 14#` would read `2 · 1 · 2 = 4 ≤ 2` — false.

The fix restores the paper's convention as explicit hypotheses: `#theorem 16#`
carries `2t_f + 1 ≤ d_f`, and `#corollary 14#` carries `2t_d + 1 ≤ d_d` and
`2t_d + 1 ≤ d_f` (the second is automatic in the paper, where `t_d ≤ t_f` forces
`d_f = 2t_f + 1 ≥ 2t_d + 1`).  With them the statements are exactly the paper's,
and the proofs are the usual ball-packing argument (`#theorem 15#`'s proof, with the
same-value balls also disjoint).

## 24. `#corollary 5#`: the code must be systematic, and `t_d ≤ t_f`

**Found and fixed 2026-10-01**, while proving the two "own step" corollaries of §IV.

`binary_optimalRedundancyData_le` (`#corollary 5#`'s step: turn a `[n,k,2t_d+1]`
code into an upper bound for `r_f`) was stated with only the distance hypothesis on
the code (`2t_d+1 ≤ d(C v, C w)` for `v ≠ w`).  Its proof, however, uses the
systematic form of `C`, exactly as `#theorem 5#` does (`ISSUES.md` §13(a)): the
two-step construction writes the answer as `(u, p_u)` and needs `C u` to start with
the message `u` to identify messages with the message part of their codewords.  The
paper's standing assumption `t_d ≤ t_f` is also used (the CDRM entries are compared
with `2(t_f − t_d)`).  The statement now carries `IsSystematic C` and `td ≤ tf`.

The companion `N_cdrm_le_bounded` (`#corollary 6#`'s step) needed no change: it is
the transitivity of the already-proved `#theorem 6#` (`N_cdrm_le_Nconst`) with the
external numerical bound supplied as `hbound`.

## 25. `#lemma 8#`: the printed hypothesis `v_i ≠ v_j` is not needed

**Found 2026-10-01**, while proving `#lemma 8#`.  The paper states the coset
distance identity for `v_i, v_j ∈ C` with `v_i ≠ v_j`; the identity holds for
*all* `x, y ∈ C` (it is a statement about the sets `x + D` and `y + D`, not about
their being distinct), and the Lean statement `cosetDist_eq` therefore omits the
hypothesis.  At `x = y` both sides are `0`: the left-hand minimum is witnessed by
`c₁ = c₂ = x`, and the right-hand one by `d = 0 ∈ D`.  This is a deliberate,
harmless weakening of the *hypothesis* (the catalogue row `PLAN.md` §1.1 was
written that way in phase 2), not a change of the identity itself; nothing in the
development uses the `v_i ≠ v_j` case, so no counterexample-style correction is
involved.  Recorded here because the project transcribes the paper's hypotheses
literally wherever they are needed.

## 26. `#lemma 7#`: the dimension statement is false without "standard form"

**Found and fixed 2026-10-01**, while proving `#lemma 7#`.  As transcribed in
phase 2, `kernelSubcode_finrank` carried **no** hypotheses at all:
`finrank F D_f = finrank F (ker f)` for every subspace `C ≤ F_q^{k+r}` and every
linear `f : F_q^k → F_q^r`.  That is false: take `F = F₂`, `k = r = 1` and
`C = span{(0,1)} ⊂ F₂²`.  The message part `c ↦ c 0` is identically `0` on `C`,
so `D_f = {c ∈ C | msgPart c ∈ ker f} = C` has dimension `1`, while with
`f = id` the kernel is `{0}` of dimension `0`.

The paper's hypothesis "`C` … in standard form" is exactly what rules this out:
a linear code in standard form has generator matrix `[I_k | P]`, i.e. *every*
message `u ∈ F_q^k` occurs as the message part of a codeword.  The statement now
carries the paper's hypotheses — `hC : IsLinearFCC f C dd df` (which includes
`dim C = k`) and `hstd : ∀ u : Word F k, ∃ c ∈ C, msgPart c = u` — and the proof
is rank–nullity: `msgPart` is onto by `hstd`, and `dim C = k = dim F_q^k` makes
it injective, so `C ≃ₗ F_q^k`; pulling `ker f` back along that equivalence is
dimension-preserving (`Submodule.map_comap_eq_self`, `LinearEquiv.finrank_map_eq`).
