# Verification status

What has been checked, by which command, and with which trusted base.  This file
is updated at every phase boundary and is the release record (`PLAN.md` §6,
milestone M5).

## Trusted base

* **Lean** `leanprover/lean4:v4.34.0-rc2` (`lean-toolchain`), **mathlib** at the
  revision pinned in `lake-manifest.json` (`70f3f134…`, the revision mathlib's
  prebuilt cache is available for).
* Axioms allowed in headline results: `propext`, `Quot.sound`,
  `Classical.choice`.  `scripts/axioms_check.ps1` fails on anything else,
  including `sorryAx` and the `native_decide` trust axioms.
* `decide`/`native_decide` are used only on small, concrete instances (the
  paper's examples) and never in a headline result.

## Reproduce

```bash
lake exe cache get      # once: restore prebuilt mathlib oleans
lake build              # kernel check of every module
```

```powershell
powershell -ExecutionPolicy Bypass -File scripts\consistency_check.ps1
powershell -ExecutionPolicy Bypass -File scripts\axioms_check.ps1
```

CI runs exactly these commands on every push (`.github/workflows/ci.yml`).

## Phase 0 — infrastructure and base layer (2026-09-14)

Verified:

| Check | Result |
| --- | --- |
| `lake build` | green |
| `scripts/consistency_check.ps1` | green (no paper labels referenced yet) |
| `scripts/axioms_check.ps1` | green — `wt_zero`, `wt_le_wt_add_hammingDist`, `mem_ball_self` depend only on the allowed axioms |
| GitHub Actions | green (see the badge in `README.md`) |

Formalized in phase 0: `Word F n`, `wt`, `ball` (`FCC/Definitions.lean`);
`wt_zero`, `wt_le_wt_add_hammingDist`, `mem_ball_self` (`FCC/Basic.lean`).
No statement of the paper is formalized yet.

## Phase 1a (part 1) — counting API and paper-example tests (2026-09-14)

Verified:

| Check | Result |
| --- | --- |
| `lake build` | green (1487 jobs) |
| `scripts/consistency_check.ps1` | green (no paper label referenced; 62 catalogue rows still to be stated in phase 2) |
| `scripts/axioms_check.ps1` | green — 13 audited results, only `propext`, `Classical.choice`, `Quot.sound` |
| `sorry` in the library | 0 |
| regression tests (`FCC/Examples.lean`) | green — the paper's Examples 6, 7 and 10 reproduce exactly, including `N(D) = 3` for Example 6 |

Formalized: `card_word`, `hammingDist_eq_card_diffSet`, `sphere`,
`ball_eq_biUnion_sphere`, `disjoint_sphere`, `ball_mono`,
`ball_eq_univ_of_le`, `card_ball_univ` (`FCC/Balls.lean`).

`FCC/Examples.lean` from that step was split in the next commit: the example
checks now live in `FCC/Paper.lean` (the main file, in paper order) and the
scaffolding they need in `FCC/Internal.lean`.

Not yet formalized in this step: the closed form
`|B(u,t)| = Σ_{i≤t} C(n,i)(q-1)^i`.  The `decide` tests check its first values
(`F₂³`: 4, 7, 8; `F₃²`: 5) but not the general identity — see `TODO.md`.

## Phase 1 (definitions) — Definitions 1–18 (2026-09-14)

Verified:

| Check | Result |
| --- | --- |
| `lake build` | green (1799 jobs) |
| `scripts/consistency_check.ps1` | green — the 18 definition rows of `PLAN.md` §1.1 are `stated`; 43 rows (theorems, lemmas, corollaries, the remaining examples) still pending |
| `scripts/axioms_check.ps1` | green — 13 audited results, only `propext`, `Classical.choice`, `Quot.sound` |
| docstring convention | green — every docstring opens with a paper marker or an `(internal, …)` tag |
| `sorry` in the library | 0 |

Formalized in `FCC/Paper.lean`, in the paper's order: `IsFCC`/`optimalRedundancy`
(`#definition 1#`), `drm` (`#definition 2#`), `IsDCode`/`N`/`Nconst`
(`#definition 3#`), `fDist` (`#definition 4#`), `fdm` (`#definition 5#`),
`IsFCCData` (`#definition 6#`), `cdrm` (`#definition 7#`), `codedFDist`
(`#definition 8#`), `cfdm` (`#definition 9#`), `optimalRedundancyData`
(`#definition 10#`), `drmData` (`#definition 11#`), `minDistGraph`
(`#definition 12#`), `functionBall` (`#definition 13#`), `IsLocallyBinary`
(`#definition 14#`), `IsLocallyBounded` (`#definition 15#`), `IsLinearFCC`
(`#definition 16#`), `CosetCode`/`cosetDist`/`cosetCodeMinDist`
(`#definition 17#`), `kernelSubcode`/`IsLinearFCCKernel` (`#definition 18#`).
Helpers they need: `IsSystematic`, `msgPart`, `minDist` (`FCC/Basic.lean`),
`msgPartLinear` (`FCC/Paper.lean`, §VII).

The three example checks of phase 1a now call the real `cdrm`/`drmData`; the
temporary transcriptions were deleted and `FCC/Internal.lean` holds only the
test alphabet `F₂`.

(The examples were formalized afterwards — see the section below.)

## Phase 1b (examples) — 12 of the paper's 17 examples (2026-09-14)

Formalized as `decide` checks in `FCC/Paper.lean`: `#example 1#`, `2`, `4`, `5`
(DRM, `D`-code and the length-9 code), `6`, `7`, `8`, `9`, `10`, `12`, `13`,
`14`.  Build, consistency check (72 markers, all inventory rows; docstring
convention green) and the axiom audit are green; CI green in 2m14s.

Not formalized, with the reason recorded in `PLAN.md` §1.2: `#example 3#` and
the FDM part of `#example 5#` (the minimum over preimages is `sInf`-based until
phase 3.0), `#example 5#`'s `N(D) = 6` (Plotkin, phase 3.11), and
`#example 11#`, `#example 15#`, `#example 16#`, `#example 17#` (§VIII bounds or
a value quoted from [1]).

## Phase 3.2–3.3 — the §II bounds and the §IV lower bounds proved (2026-09-20/22)

Verified:

| Check | Result |
| --- | --- |
| `lake build` | green (1818 jobs), warning-free apart from the `sorry` stubs |
| `scripts/consistency_check.ps1 -Strict` | green — 78 paper markers, all inventory rows, 73 rows stated, docstring convention, no orphan modules |
| `scripts/axioms_check.ps1` | green — 45 audited results; every one of them depends only on `propext`, `Classical.choice`, `Quot.sound` |
| `sorry` in the library | 17 (was 49: thirty-one paper statements discharged, plus the two internal halves of `#theorem 2#`) |
| GitHub Actions | green on the push that carries this section |

Proved:

* §II (the `(f,t)`-FCC bounds quoted from [1]): `#corollary 1#` in both parts
  (`optimalRedundancy_ge_drm`, `two_mul_le_optimalRedundancy`), `#theorem 1#`
  (`optimalRedundancy_le_fdm`) and `#corollary 2#` (`optimalRedundancy_eq_fdm`);
* §IV (the two-step construction of §III-A): `#theorem 5#`
  (`N_drmData_le_N_cdrm_add`), `#corollary 4#`
  (`optimalRedundancyData_le_N_cdrm_add`) and `#theorem 6#`
  (`N_cdrm_le_Nconst`);
* §IV: `#theorem 7#` (`two_step_redundancy_bounds`), reworked to the paper's
  two-sided bound on the scheme redundancy `r_s` (the scheme is modelled by
  `twoStepCode`/`IsSecondStep`, and `twoStep_isFCCData` is the paper's
  "straightforward verification") — `ISSUES.md` §13(d);
* §IV: `#theorem 4#` (`binary_optimalRedundancyData_ge`), the binary strengthening
  `r_f ≥ 2t_f + t_d`, with the binary bricks in `FCC/Balls.lean`;
* §V-A: `#theorem 8#` and `#theorem 9#` (`not_isFCCData_of_connected`,
  `not_isFCCData_of_components`), both with the corrected range condition
  (`ISSUES.md` §14), via `connectedComponentMk_ne_of_isFCCData`;
* §V-B (MDS part): `#lemma 2#` (`exists_mds_neighbor`) and `#theorem 11#`
  (`isConnected_minDistGraph_of_mds`), with connectivity stated as codeword
  reachability and `componentCount` counting the components that meet `C`
  (`ISSUES.md` §16);
* the **Singleton bound** `card_le_pow_minDist` (`|C| ≤ q^{n − d_min + 1}`), which
  the paper quotes from [17] and which is proved here from the projection argument
  (`FCC/Balls.lean`); it is one of the two ingredients of `#corollary 8#`;
* §V-B (MDS optimality): `#corollary 8#` (`mds_optimalRedundancyData_ge`) — if an
  MDS `(n, q^k, d)` code exists and `|Im f| ≥ 2`, then `d ≤ r_f(k : d, d_f)` for
  `d < d_f`.  A hypothetical optimum with redundancy `r < d` has an injective
  encoding, so its codeword set `C'` has `q^k` words and `d_min(C') ≥ d`; for
  `r = d − 1` Singleton forces `C'` to be MDS and `#theorem 11#`/`#theorem 8#`
  rule it out, while for `r ≤ d − 2` the Singleton bound and `q ≥ 2` do;
* §V-B (perfect codes): `#theorem 10#` (`isConnected_minDistGraph_of_perfect`) —
  `G(C)` is connected for every perfect `t`-error-correcting code.  The counting
  behind it is now proved rather than quoted: the closed forms
  `card_sphere`/`card_ball` (`|S(u,i)| = C(n,i)(q−1)^i`, phase 1a part 3), the
  Hamming-bound packing inequality `card_mul_card_ball_le`/`pairwiseDisjoint_ball`,
  and three §V-B consequences — `exists_mem_ball_of_isPerfect` (the balls of
  radius `t` tile the space, so every word is within `t` of a codeword),
  `minDist_eq_of_isPerfect` (a perfect code has `d_min = 2t+1`, which is what makes
  the paper's `d(u,u') = 2t+1` step legal) and `hammingDist_lt_of_close` (the
  paper's step 5 counting); `exists_hammingDist_eq` (Balls) and
  `exists_hammingDist_eq_minDist` (Basic) supply the intermediate words;
* §V-B (optimality of perfect codes): `#corollary 7#`
  (`perfect_optimalRedundancyData_ge`) — if `q^{n−k} = Σ_{i≤t}C(n,i)(q−1)^i` with
  `t = ⌊(d_d−1)/2⌋`, `|Im f| ≥ 2`, `1 ≤ d_d` and `k ≤ n`, then
  `r_f(k : d_d, d_f) ≥ n−k+1` for `d_f > d_d`.  The packing bound on an optimal FCC
  gives `A_t(k+r) ≤ q^r`; length exactly `n` makes the code perfect (so
  `#theorem 10#` + `#theorem 8#` apply) while a shorter code contradicts the strict
  monotonicity `A_t(n) < A_t(k+r)·q^{n−k−r}` of the truncated binomial sums
  (`sum_range_choose_mul_pow_lt_add`, built from the Pascal recurrence
  `sum_range_choose_mul_pow_succ`); the remaining case `t > k+r` forces `k = 0`.
* §VI-A (locally binary functions): `#lemma 3#` (`locallyBinary_redundancy_le`) —
  for a `(d_f−1)`-locally binary `f` and a systematic code `C` of redundancy `r`
  and minimum distance `d_d`, the two-step construction (the codeword `C u`
  followed by `1…1` or `0…0` according to whether `f(u)` is the marked value of its
  function ball) is an `(f : d_d, d_f)`-FCC of redundancy `r + (d_f − d_d)`.  The
  marking is order-free (`ballMark`/`pickElem`, `ISSUES.md` §18), and the paper's
  Case 1 uses the systematicity `d(u,v) ≤ d(C u, C v)`.
* §VI-A (corollaries): `#corollary 9#`–`#corollary 12#` — the upper bounds at a
  perfect (resp. MDS) first-step code and the matching optimality statements for
  `d_f = d_d + 1`.  Their hypotheses bundle the paper's perfect/MDS code with its
  systematic form (`ISSUES.md` §18); the upper halves are `#lemma 3#`, the lower
  halves are `#corollary 7#`/`#corollary 8#`.
* §VI-B (binary bound): `#lemma 5#` (`Nconst_four_two`) — `N(4,2t) = 3t` for
  *binary* codes (the general-alphabet transcription was false, `ISSUES.md` §19).
  Upper bound: the four odd words of `F₂³` repeated `t` times (`base4`,
  `hammingDist_repWord`); lower bound: the Plotkin double counting
  `three_binary_le` (three binary words at pairwise distance `≥ 2t` need length
  `≥ 3t`).
* §VI-B (locally bounded functions): `#theorem 12#`
  (`locallyBounded_redundancy_le`) — with the `#lemma 4#` colouring `hcol`, a
  systematic first-step code of minimum distance `2t_d+1` and `t_d ≤ t_f`, the
  two-step construction with `p_u := c'_{Col_f(u)}` (a code of length
  `N(λ, 2(t_f−t_d))`, from the attainment of `N`) gives
  `r_f ≤ r + N(λ, 2(t_f−t_d))`.  The three hypotheses the printed statement left
  implicit (systematicity, `t_d ≤ t_f`, `q ≥ 2`) are `ISSUES.md` §20.
* §VI-C (Hamming weight): `#lemma 6#` in both of the paper's bounds —
  `hammingWeight_redundancy_le` (`r_f ≤ r + N(2t_f+1, 2(t_f−t_d))`, second step
  `p_u := c'_{f(u) mod (2t_f+1)}` with `c'` of length exactly
  `N(2t_f+1, 2(t_f−t_d))` from the attainment of `N`, the residue lemma
  `mod_ne_of_sub_lt`, and `wt_le_wt_add_hammingDist`) and
  `hammingWeight_redundancy_le_optimal`
  (`r_f ≤ (N(q^k, 2t_d+1) − k) + N(2t_f+1, 2(t_f−t_d))`, the first bound applied
  to the bundled systematic encoder of the optimal length; `ISSUES.md` §21).
* §VIII-B (Hamming bound): `#corollary 13#` (`hamming_bound_fcc_sphere`) — an
  `(f,t)`-FCC forces `\|Im f\| · \|B(0,t)\| ≤ q^n`.  Pick one message per attained
  value (`Classical.choose` on the preimages); their codewords are pairwise at
  distance `≥ 2t+1` by `IsFCC`, so the ball-packing inequality
  `card_mul_card_ball_le` applies.
* `optimalRedundancyData_eq_N_drmData` — the paper's central identity
  `r_f(k,t_d,t_f) = N(D_f(t_d,t_f : u₁, …, u_{q^k}))` — with the internal bricks
  `hammingDist_eq_msg_add_red`, `isDCode_drmData_of_isFCCData`,
  `N_drmData_le_of_isFCCData`, `optimalRedundancyData_le_of_isDCode`;
* `#theorem 3#` in all three parts: `optimalRedundancyData_ge_N_subset`,
  `two_mul_le_optimalRedundancyData`, `optimalRedundancyData_ge_Nconst_sub`;
* the non-vacuity bricks `exists_isFCCData` (§III, phase 3.14) and `exists_isFCC`
  (§II), on which every lower bound rests: an `(f, d_d, d_f)`-FCC always exists
  (`C u = (u, u, …, u)`).

Statement-level caveat for this result: the paper's implicit `d_d ≤ d_f` is an
explicit hypothesis of `#theorem 2#` (it is used by the proof, and without it the
identity is false); see `ISSUES.md` §11 and `Notation.md` §3.5.  The existence of
an FCC, which the `sInf`-based `r_f` needs, is no longer a hypothesis: it is
proved (`exists_isFCCData`).  `#theorem 3#` needs no extra hypothesis at all.

Two statements had to be **corrected**, not merely proved: `#theorem 1#` and the
upper-bound half of `#theorem 7#` indexed their FDM/CFDM by the whole alphabet
`α`, which is false for infinite `α`; both now index by `Im(f)` (`Set.range f`),
the paper's `f₁, …, f_E` — see `ISSUES.md` §12 for the counterexample and the
reasoning.  `#corollary 1#`/`#corollary 2#` were re-checked and are faithful as
printed (their DRMs are indexed by messages).

Two further statement deviations were found while comparing §IV with the paper
and are recorded in `ISSUES.md` §13: `#theorem 5#`/`#corollary 4#` now carry the
*systematic form* of `C` that the paper's proof assumes (`hCsys`; the WLOG is
justified for linear codes, not for our arbitrary labelling map), and
`#theorem 7#` was a proxy for the paper's two-sided bound on the scheme
redundancy `r_s` and has since been reworked and proved (`ISSUES.md` §13(d)).

## Phase 3.13 — the appendix ball-union counts (2026-10-01)

All four appendix counts are proved: `#theorem 17#` (`card_ball_union_dist_one`),
`#lemma 14#` (`card_ball_inter_dist_two`), `#theorem 18#`
(`card_ball_union_three`) and `#theorem 19#` (`card_ball_union_dist_three`).

Verified:

| Check | Result |
| --- | --- |
| `lake build` | green (1818 jobs; 16 `sorry` warnings, all in phases 3.11–3.13) |
| `scripts/consistency_check.ps1 -Strict` | green (78 paper markers, all inventory rows; 73 rows stated; 14 `sorry`) |
| `scripts/axioms_check.ps1` | green — 48 audited results, only `propext`, `Classical.choice`, `Quot.sound` |

`#lemma 14#` is the paper's Appendix Lemma 14: over `F₂`, for `d(u₁,u₂) = 2`,
`|B(u₁,t) ∩ B(u₂,t)| = 2Σ_{i≤t−1}C(n−1,i)`.  Statement re-read against the PDF
verbatim (no deviation, no new `ISSUES.md` entry).  The paper normalises to
`u₁ = 0`, `u₂ = (1,1,0,…,0)`; the formalisation instead extracts the two differing
coordinates from `diffSet u v` (`exists_diffSet_eq_pair`), which avoids any
relabelling of coordinates.

Method: `mem_ball_inter_iff_dist_two` shows `x` is in both balls iff
`|D(x,u) \ {c₁,c₂}| + (if `x` agrees with `u` at `c₁` and `c₂` alike then 2 else 1)
≤ t`; over `F₂` every disagreement set is realised by exactly one word, so the
count reduces to the number of admissible sets `D ⊆ Fin n`
(`card_allowed_dist_two`), which is `2Σ_{i<t}C(n−2,i) + 2Σ_{i<t−1}C(n−2,i)`, and
summed Pascal (`sum_range_choose_pred`) gives the printed
`2Σ_{i<t}C(n−1,i)`.  The counting layer (`card_powerset_filter_add_le`,
`sum_range_choose_succ/pred`) is generic and will be reused by
`#theorem 18#`/`#theorem 19#`.

**Statement fix, same day.**  `#theorem 18#` as printed is *false* at `t = 0` in
Lean's `ℕ`: the term `C(n−2,t−1)` truncates to `C(n−2,0) = 1`, while the paper's
convention reads `C(n−2,−1) = 0` (and the identity there is the trivial `3 = 3`).
Concretely, for `n = 2` and the centres `00, 10, 01` the left side is `3` and the
printed right side evaluates to `4`.  The statement now carries `1 ≤ t`
(`card_ball_union_three`), the convention the paper itself prints for the twin
result `#theorem 19#` (`t ≥ 2`); the counterexample and the reasoning are
`ISSUES.md` §22.  The shared machinery needed by both appendix results is now in
`FCC/Balls.lean` and audited: `card_union_three_add` (subtraction-free 3-set
inclusion–exclusion), `diffSet_surjective`/`diffSet_injective` +
`card_filter_diffSet` (over `F₂` a word and its disagreement set determine each
other), `zmod2_eq_add_one_of_ne`, `zmod2_add_one_ne`,
`erase_erase_eq_sdiff_pair`, and `card_filter_inter_eq_card`.  Proving
`#theorem 18#` (and then `#theorem 19#`) from this machinery is the next step.

`#theorem 18#` itself then took the paper's two steps; it is now proved.

* **Triple intersection** (`card_ball_inter_three`, in the same file as
  `#theorem 18#`): `|B(u₁,t) ∩ B(u₂,t) ∩ B(u₃,t)| = #₁ + 3#₂` with
  `#₁ = Σ_{i<t−1}C(n−2,i)` and `#₂ = Σ_{i<t−2}C(n−2,i)` (the paper's four cases).
  The characterisation `mem_ball_inter_three_iff` is the two-coordinate model with
  `c₁ ∈ D ↔ c₂ ∈ D` replaced by `c₁ ∈ D ∨ c₂ ∈ D`, and the count
  (`card_allowed_pair_three`) splits the admissible sets `D` by `D ∩ {c₁,c₂} = ∅`
  (the filter *is* a powerset filter, card `Σ_{i<t}C(n−2,i)`) versus the three
  non-empty patterns (fibres with card `Σ_{i<t−1}C(n−2,i)`, `card_filter_inter_eq_card`,
  the index set `T.powerset.filter (· ≠ ∅)` having card `3`).
* **Inclusion–exclusion**: `card_union_three_add` with `card_ball` (each ball
  `Σ_{i<t+1}C(n,i)` over `F₂`), the two distance-one intersections and the
  distance-two one (each `2Σ_{i<t}C(n−1,i)`), and then `omega` on the additive
  identities `Σ_{i≤t}C(n,i) = Σ_{i≤t}C(n−1,i) + Σ_{i≤t−1}C(n−1,i)`
  (`sum_range_choose_succ`), `C(n−1,t) = C(n−2,t−1) + C(n−2,t)`
  (`Nat.choose_succ_succ`) and `Σ_{i<t}C(n−2,i) = Σ_{i<t−1}C(n−2,i) + C(n−2,t−1)`.
* `c₁ ≠ c₂` is derived from `d(u₂,u₃) = 2`: over `F₂` two words that differ from
  `u₁` in the *same* single coordinate coincide.

`#theorem 19#` (two balls at distance three, `t ≥ 2` — the paper's own threshold, so
no `t − 2` truncation can arise) is proved the same way, with three special
coordinates:

* **intersection** (`card_ball_inter_dist_three`): `2Σ_{i<t−2}C(n−3,i) +
  6Σ_{i<t−1}C(n−3,i)`, the paper's `2#₂ + 6#₁`.  The characterisation
  `mem_ball_inter_iff_dist_three` gives `d(x,u) = |S| + k` and
  `d(x,v) = |S| + (3−k)`, where `k = |D(x,u) ∩ T|`, so membership in both balls is
  `|S| + max k (3−k) ≤ t`; `card_allowed_triple` counts the admissible sets by
  splitting `D ∩ T` into `∅`, `T` (cost `3`) and the six other patterns (cost `2`),
  each half being `card_filter_inter_eq_card` fibres with the index cardinalities
  `1`, `6` and `1` (the middle one via `T.powerset.filter (· ≠ ∅ ∧ · ≠ T)` having
  `8 − 2` elements).
* **union**: `Finset.card_union_add_card_inter` with `card_ball` on both balls and
  `Σ_{i<t−1}C(n−3,i) = Σ_{i<t−2}C(n−3,i) + C(n−3,t−2)` to recover the printed
  `−8Σ − 6C`.

With `#theorem 18#` this means the whole appendix (and hence the §VIII bounds
`#theorem 15#`/`#theorem 16#`/`#corollary 14#`) is now unblocked: the appendix
counting layer is complete.

## Not formalized (and why)

Nothing yet; this section is filled in as results are classified.

Planned to appear here: the paper's numbered **examples**
(`PLAN.md` §1.2 — they are illustrations, not theorems; some are used as
`decide` regression tests) and the **external** rows of `PLAN.md` §1.1
(`#lemma 1#`, `#lemma 4#`, `#lemma 12#`, `#corollary 3#`, `#corollary 5#`), which are quoted from other
papers and will be used as explicit hypotheses rather than assumed as axioms.

## Statement-level caveats

`#theorem 2#` is stated with one side condition that the paper assumes rather
than prints — `d_d ≤ d_f` (from `#definition 6#`, and used by the proof) — see
`ISSUES.md` §11(a).  The other implicit ingredient, the existence of an
`(f : d_d, d_f)`-FCC, is proved rather than assumed (`exists_isFCCData`,
`ISSUES.md` §11(b)), so `#theorem 2#` and `#theorem 3#` carry no existence
hypotheses.

`Notation.md` §5 lists the places where the paper's printed statement
needs care (the direction of `#theorem 15#`/`#theorem 16#`, the constants of `#lemma 1#`, the
missing `max(·,0)` in `#definition 11#`, the "similar proof" of `#theorem 4#` Case 2, the
covering argument of `#theorem 10#`, and the systematicity step in `#lemma 6#`); each entry
stays there until the corresponding phase resolves it, and the resolution is
recorded in `DEVLOG.md`.
