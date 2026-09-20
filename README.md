# FCC: Function-correcting codes with data protection, in Lean 4

> **Repository:** <https://github.com/FrankieLiu20/function-correcting-codes>

[![CI](https://github.com/FrankieLiu20/function-correcting-codes/actions/workflows/ci.yml/badge.svg)](https://github.com/FrankieLiu20/function-correcting-codes/actions/workflows/ci.yml)

This repository is a **Lean 4 + mathlib** formalization of

> C. Rajput, B. S. Rajan, R. Freij-Hollanti, C. Hollanti,
> "Function-Correcting Codes With Data Protection",
> *IEEE Trans. Inform. Theory* **72**(7), pp. 4860–4880, July 2026.
> DOI [10.1109/TIT.2026.3692458](https://doi.org/10.1109/TIT.2026.3692458).
> (Open Access, CC BY 4.0.)

The goal is to turn the paper's definitions, numbered results and proofs into
Lean code that the proof kernel checks mechanically, so that the argument is
either confirmed beyond doubt or a gap/typo in the paper surfaces.  The paper
introduces *function-correcting codes with data protection*: systematic
encodings that protect the data against `t_d` errors and a function `f` of the
data against `t_f > t_d` errors, reducing the optimal-redundancy question to the
minimal length `N(D)` of an irregular-distance code for a distance requirement
matrix `D`.

The repository layout, documentation practice, verification workflow and
labelling conventions follow Shenghao Yang's
[`n4code_lean_dev`](https://github.com/shhyang/n4code_lean_dev) (see
[`NOTICE`](NOTICE)); the Lean development here is original and uses mathlib's
`hammingDist` rather than a private re-derivation.

## New here? Read this first

* [`ONBOARDING.md`](ONBOARDING.md) — a from-zero guide (in Chinese): what
  Lean/mathlib/Lake/elan are, how to read Lean code, the daily
  edit → build → check → commit loop, and how to use the GitHub repository.
* [`PLAN.md`](PLAN.md) — the scope, the statement inventory (one row per
  numbered result of the paper) and the phase plan.
* [`Notation.md`](Notation.md) — the paper ↔ Lean dictionary, the modelling
  decisions, and the open questions.
* [`AGENTS.md`](AGENTS.md) — the short version of the rules, addressed to AI
  coding agents.

## Status

| Module | Contents | Status |
| --- | --- | --- |
| `FCC/Paper.lean` | **the main file**: every numbered item of the paper, in paper order, under the paper's section headings | All 65 numbered items are present: Definitions 1–18 stated, 12 of the 17 examples formalized, every theorem/lemma/corollary stated.  **Proved**: `#theorem 2#` (the central identity `r_f = N(DRM)`) and all three parts of `#theorem 3#`; the rest carry `sorry` (43 in total) |
| `FCC/Definitions.lean` | §I-E notation: `Word F n` (= `F_q^n`), `wt`, `ball` | Phase 0 — complete |
| `FCC/Basic.lean` | internal: `wt_le_wt_add_hammingDist`, `wt_zero`, `mem_ball_self` | Phase 0 — complete |
| `FCC/Balls.lean` | internal: `card_word`, `diffSet`, `sphere`, `ball_eq_biUnion_sphere`, `disjoint_sphere`, `ball_mono`, `ball_eq_univ_of_le`, `card_ball_univ` | Phase 1a — partly done (the closed form `Σ_{i≤t} C(n,i)(q-1)^i` is next) |
| `FCC/Internal.lean` | internal scaffolding for the example checks | Phase 1a |
| `FCC/AxiomCheck.lean` | `#print axioms` audit of the headline results | complete |

Phases 0 (infrastructure), 1 (modelling) and 2 (statement catalogue) are done,
and phase 3 (proofs) is under way: 3.0 (the `sInf`/attainment API for `N`, `r_f`,
`d_min`, `d(fᵢ,fⱼ)`), 3.1–3.2 (`#theorem 2#`, `#theorem 3#`) and 3.14 (an FCC
always exists) are finished; everything else carries a `sorry` stub.
`PLAN.md` §4 lists the phases — with a status column — and `PLAN.md` §1.1 is the
table of *all* 65 numbered items of the paper (18 definitions, 19 theorems, 14
lemmas and 14 corollaries) with their status; that table is the project's
checklist.

**Where to read the formalization.**  `FCC/Paper.lean` is the deliverable:
every numbered item of the paper appears there, once, in the paper's order, with
the paper's number at the head of its docstring.  Helpers that are not paper
items live in the other modules listed above and are free to be reorganised.

## Build

The toolchain is pinned in [`lean-toolchain`](lean-toolchain)
(`leanprover/lean4:v4.34.0-rc2`) and mathlib in
[`lake-manifest.json`](lake-manifest.json) (also pinned in `lakefile.toml`).

```bash
lake exe cache get   # fetch prebuilt mathlib oleans (only needed once)
lake build           # incremental build (seconds when up to date)
```

Individual modules build in isolation, e.g. `lake build FCC.Basic`.

**Build-performance rules** (important for mathlib-heavy projects): never run
bare `lake clean` (it deletes the prebuilt mathlib oleans and forces a long
source rebuild); restore them with `lake exe cache get` instead; keep imports
minimal and never `import Mathlib`.  Details in [`AGENTS.md`](AGENTS.md).

> **Windows/OneDrive note.**  A Lean project creates a multi-gigabyte `.lake/`
> build directory, so do not build inside a OneDrive-synced folder.  Keep the
> working copy outside sync (on this machine:
> `E:\lean\function-correcting-codes`) and keep the paper itself in `paper/`
> (git-ignored), not in version control.

## Verification

What "verified" means for this repository, the trusted axiom set, and how to
reproduce the checks from a fresh clone are recorded in
[`VERIFICATION.md`](VERIFICATION.md).  In short:

```powershell
powershell -ExecutionPolicy Bypass -File scripts\consistency_check.ps1 -Strict   # build + PLAN/Lean label coverage (both directions) + orphans + sorry count
powershell -ExecutionPolicy Bypass -File scripts\axioms_check.ps1        # per-theorem axiom audit (fails on sorryAx)
```

The same commands run in CI (GitHub Actions) on every push; see
`.github/workflows/ci.yml`.

## Repository layout

```text
FCC.lean                  # library root module (imports every module below)
FCC/                      # the formalization
PLAN.md                   # scope, statement inventory, phase plan
Notation.md               # paper <-> Lean dictionary
CONSISTENCY.md            # per-step paper/Lean consistency protocol
VERIFICATION.md           # what is verified and how to reproduce it
DEVLOG.md                 # dated development log
TODO.md                   # open work
PUBLISHING.md             # venue/artifact/Zenodo plan
ONBOARDING.md             # from-zero guide (Chinese)
AGENTS.md                 # rules for AI agents / contributors
NOTICE                    # third-party attribution
CITATION.cff              # machine-readable citation info
lakefile.toml             # libraries and dependencies
lean-toolchain            # pinned Lean version
lake-manifest.json        # pinned dependency revisions
scripts/                  # consistency + axiom checks (PowerShell)
paper/                    # the paper itself (local-only, gitignored)
```

## Citing

See [`CITATION.cff`](CITATION.cff).  If you build on this project, cite it *and*
the paper it formalizes.

## License

Apache-2.0 (see [`LICENSE`](LICENSE)).  The formalization is original work; the
theorem statements it formalizes belong to the paper's authors.
