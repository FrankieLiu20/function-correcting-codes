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

## Phase 3.2 — the §II and §IV lower bounds proved (2026-09-20/22)

Verified:

| Check | Result |
| --- | --- |
| `lake build` | green (1818 jobs), warning-free apart from the `sorry` stubs |
| `scripts/consistency_check.ps1 -Strict` | green — 78 paper markers, all inventory rows, 73 rows stated, docstring convention, no orphan modules |
| `scripts/axioms_check.ps1` | green — 21 audited results; every one of them depends only on `propext`, `Classical.choice`, `Quot.sound` |
| `sorry` in the library | 39 (was 49: eight paper statements discharged, plus the two internal halves of `#theorem 2#`) |
| GitHub Actions | green on the push that carries this section |

Proved:

* §II (the `(f,t)`-FCC bounds quoted from [1]): `#corollary 1#` in both parts
  (`optimalRedundancy_ge_drm`, `two_mul_le_optimalRedundancy`), `#theorem 1#`
  (`optimalRedundancy_le_fdm`) and `#corollary 2#` (`optimalRedundancy_eq_fdm`);
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
