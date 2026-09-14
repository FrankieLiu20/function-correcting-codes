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
- [ ] 1b. `IsSystematic`, `minDist`; Definition 1 (`IsFCC`,
      `optimalRedundancy`) and Definition 6 (`IsFCCData`).
      Every paper item written from here on goes into `FCC/Paper.lean`, in paper
      order (see `PLAN.md` §2 and `AGENTS.md` rule 2a); helpers stay in the
      `(internal, …)` modules.
- [ ] 1c. `drm` (`#definition 2#`), `drmData` (`#definition 11#`), `fDist`/`fdm` (`#definition 4#`,
      `#definition 5#`), `IsDCode`/`N`/`Nconst` (`#definition 3#`) and the `N` API.
- [ ] 1d. `cdrm` (`#definition 7#`), `codedFDist` (`#definition 8#`), `cfdm` (`#definition 9#`).
- [ ] 1e. `minDistGraph` (`#definition 12#`), `functionBall` (`#definition 13#`),
      `IsLocallyBinary` (`#definition 14#`), `IsLocallyBounded` (`#definition 15#`).
- [ ] 1f. `IsLinearFCC` (`#definition 16#`), `CosetCode`/`cosetCodeMinDist` (`#definition 17#`),
      `IsLinearFCCKernel` (`#definition 18#`).

## Phase 2 — statement catalogue

- [ ] Every non-`external` row of `PLAN.md` §1.1 as a `sorry`-stubbed statement
      with its paper label in the docstring.
- [ ] Flip `scripts/consistency_check.ps1 -Strict` on in CI (milestone M2).

## Housekeeping

- [ ] Fill in the full name in `CITATION.cff`.
- [ ] Set the repository description/topics on GitHub.
- [ ] Re-read `ONBOARDING.md` §2 and §3: it was written for the guide
      repository and still quotes a few paths from there.
- [ ] After the first paper-specific theorem lands: add it to
      `scripts/headline_theorems.txt` **and** `FCC/AxiomCheck.lean` (the two are
      checked against each other).
