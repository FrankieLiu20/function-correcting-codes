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

## Not formalized (and why)

Nothing yet; this section is filled in as results are classified.

Planned to appear here: the paper's numbered **examples**
(`PLAN.md` §1.2 — they are illustrations, not theorems; some are used as
`decide` regression tests) and the **external** rows of `PLAN.md` §1.1
(`#lemma 1#`, `#lemma 4#`, `#lemma 12#`, `#corollary 3#`, `#corollary 5#`), which are quoted from other
papers and will be used as explicit hypotheses rather than assumed as axioms.

## Statement-level caveats

None yet.  `Notation.md` §5 lists the places where the paper's printed statement
needs care (the direction of `#theorem 15#`/`#theorem 16#`, the constants of `#lemma 1#`, the
missing `max(·,0)` in `#definition 11#`, the "similar proof" of `#theorem 4#` Case 2, the
covering argument of `#theorem 10#`, and the systematicity step in `#lemma 6#`); each entry
stays there until the corresponding phase resolves it, and the resolution is
recorded in `DEVLOG.md`.
