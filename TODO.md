# TODO

Near-term, in the order the project works through `PLAN.md` §4.  Tick items off
in the same commit that does the work.

## Phase 0 — done

- [x] Create the repository, the toolchain pin and the CI workflow.
- [x] Base layer: `Word`, `wt`, `ball` + `wt_le_wt_add_hammingDist`, `wt_zero`,
      `mem_ball_self` (builds; axiom audit green).
- [x] `PLAN.md` §1.1: the full inventory of the paper's 45 numbered results.
- [x] `Notation.md`: the paper ↔ Lean dictionary and the design decisions.

## Phase 1 — model the paper (one commit per sub-step)

- [x] 1a (part 1). `card_word`, `diffSet`/`hammingDist_eq_card_diffSet`,
      `sphere`, `ball_eq_biUnion_sphere`, `disjoint_sphere`, `ball_mono`,
      `ball_eq_univ_of_le`, `card_ball_univ`.
- [x] 1a (part 2). `decide` regression tests (`FCC/Examples.lean`): the paper's
      Examples 6, 7 and 10 — the CDRM and DRM transcriptions, `N(D) = 3` for
      Example 6, the `[6,3,3]` and `[7,4,3]` minimum distances — plus ball sizes.
- [ ] 1a (part 3). The closed form `|B(u,t)| = Σ_{i≤t} C(n,i)(q-1)^i`
      (`card_sphere`, `ball_card`); the proof goes through the equivalence
      "word at distance `i` from `u` ↔ (set of `i` changed coordinates, values
      on it)".  Needed by `#theorem 15#`–`#theorem 19#` and `#corollary 13#`/`#corollary 14#`.
- [x] 1b. `IsSystematic`, `minDist`; Definition 1 (`IsFCC`,
      `optimalRedundancy`) and Definition 6 (`IsFCCData`).
      Every paper item written from here on goes into `FCC/Paper.lean`, in paper
      order (see `PLAN.md` §2 and `AGENTS.md` rule 2a); helpers stay in the
      `(internal, …)` modules.
- [x] 1c. `drm` (`#definition 2#`), `drmData` (`#definition 11#`), `fDist`/`fdm`
      (`#definition 4#`, `#definition 5#`), `IsDCode`/`N`/`Nconst`
      (`#definition 3#`).  (The `N` API — existence, attainment, monotonicity —
      is phase 3.0.)
- [x] 1d. `cdrm` (`#definition 7#`), `codedFDist` (`#definition 8#`), `cfdm`
      (`#definition 9#`).
- [x] 1e. `minDistGraph` (`#definition 12#`), `functionBall` (`#definition 13#`),
      `IsLocallyBinary` (`#definition 14#`), `IsLocallyBounded` (`#definition 15#`).
- [x] 1f. `IsLinearFCC` (`#definition 16#`), `CosetCode`/`cosetDist`/
      `cosetCodeMinDist` (`#definition 17#`), `kernelSubcode`/`IsLinearFCCKernel`
      (`#definition 18#`).

## Phase 1b — the paper's examples

- [ ] Examples 1, 2, 3, 4, 5 (the `F₂²`/`F₂³` worked examples of §II–§IV): the
      DRM, the FDM, the quoted `D`-codes and the printed matrices, as `decide`
      checks in `FCC/Paper.lean`.  (An `N(D) = k` claim needs the phase-3.0
      `N`-API; until then it is checked as the decidable pair "a `D`-code of
      length `k` exists / none of length `k−1` exists".)
- [ ] Examples 8, 9 (a `D`-code for the 8×8 DRM; the 4-cycle minimum-distance
      graph of `{0000,0011,1100,1111}`).
- [ ] Examples 12, 13, 14 (§VII: the non-linear `f`, the `(f:2,3)`-FCC, the
      `[10,3,4]` construction).
- [ ] Examples 11, 15, 16, 17 — these need the §VIII bounds (`#theorem 14#`–
      `#theorem 16#`) or a value quoted from [1]; do them together with those.

## Phase 2 — statement catalogue

- [x] Every non-`external` row of `PLAN.md` §1.1 as a `sorry`-stubbed statement
      with its paper label in the docstring (73 rows; the four `external` rows
      stay without a declaration and enter as hypotheses, `#remark 1#` has no
      declaration).
- [x] Flip `scripts/consistency_check.ps1 -Strict` on in CI (milestone M2).

## Phase 3 — proofs (`PLAN.md` §4)

- [x] 3.0. The `sInf` API: `N_le_of_isDCode`, `minDist_le`, `fDist_le`,
      `optimalRedundancy_le_of`, `optimalRedundancyData_le_of` and the five
      `…_eq_of` minimality lemmas.
- [x] 3.1/3.2. `#theorem 2#` — the central identity `r_f = N(D_f(t_d,t_f:u₁,…,u_{q^k}))`:
      `hammingDist_eq_msg_add_red`, `isDCode_drmData_of_isFCCData`,
      `N_drmData_le_of_isFCCData`, `optimalRedundancyData_le_of_isDCode`,
      `optimalRedundancyData_eq_N_drmData` (headline result; `ISSUES.md` §11).
- [x] 3.2. `#theorem 3#`: `optimalRedundancyData_ge_N_subset`,
      `two_mul_le_optimalRedundancyData`, `optimalRedundancyData_ge_Nconst_sub`
      (the middle one uses `exists_hammingDist_one_ne`, the paper's unproved
      "some pair at distance 1 changes the value of `f`").
- [x] 3.14. Non-vacuity of the FCC set (`exists_isFCCData`, by repeating the
      message `max d_d d_f` times) — which is what let `#theorem 2#` drop its
      `hex` hypothesis (`ISSUES.md` §11(b)) and makes the optimum attained.
- [ ] 3.2 (next). `#corollary 1#` (`optimalRedundancy_ge_drm`,
      `two_mul_le_optimalRedundancy`), `#theorem 1#` (`optimalRedundancy_le_fdm`),
      `#corollary 2#` (`optimalRedundancy_eq_fdm`) — the §II analogues of
      `#theorem 2#`/`#theorem 3#` without data protection.
- [ ] 3.2 (statement fix, **do first**). Re-index the FDM of `#theorem 1#` and
      `#corollary 2#` by the image of `f` (`ι := Set.range f`) instead of by the
      ambient `α`: as transcribed they are false for an infinite `α`, see
      `ISSUES.md` §12 (with the counterexample and the provable replacement).
- [ ] Upgrade the examples that currently check "a witness exists / none exists"
      (`#example 1#`, `2`, `4`, `5`, `6`, `7`, `9`) to equalities about `N` and
      `minDist` with `N_eq_of`/`minDist_eq_of`, now that phase 3.0 is done.

## Housekeeping

- [ ] Fill in the full name in `CITATION.cff`.
- [ ] Set the repository description/topics on GitHub.
- [ ] Re-read `ONBOARDING.md` §2 and §3: it was written for the guide
      repository and still quotes a few paths from there.
- [x] After the first paper-specific theorem lands: add it to
      `scripts/headline_theorems.txt` **and** `FCC/AxiomCheck.lean` (the two are
      checked against each other).  `#theorem 2#` (`optimalRedundancyData_eq_N_drmData`)
      is the first entry of the `Phase 3.2` block of the manifest.
- [x] Keep `lake build` warning-free apart from the `sorry` stubs: deprecated
      `dif_pos`/`if_pos`/`if_neg`/`Set.mem_setOf_eq` replaced, and the unused
      section variables of the `sInf` API silenced with `omit … in`.
