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

- [ ] 1a. Words and distance algebra: `ball_card`, `card (Word F n) = q^n`,
      small `decide` sanity checks.
- [ ] 1b. `IsSystematic`, `minDist`; Definition 1 (`IsFCC`,
      `optimalRedundancy`) and Definition 6 (`IsFCCData`).
- [ ] 1c. `drm` (`def:2`), `drmData` (`def:11`), `fDist`/`fdm` (`def:4`,
      `def:5`), `IsDCode`/`N`/`Nconst` (`def:3`) and the `N` API.
- [ ] 1d. `cdrm` (`def:7`), `codedFDist` (`def:8`), `cfdm` (`def:9`).
- [ ] 1e. `minDistGraph` (`def:12`), `functionBall` (`def:13`),
      `IsLocallyBinary` (`def:14`), `IsLocallyBounded` (`def:15`).
- [ ] 1f. `IsLinearFCC` (`def:16`), `CosetCode`/`cosetCodeMinDist` (`def:17`),
      `IsLinearFCCKernel` (`def:18`).

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
