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
| `FCC/Definitions.lean` | `Word F n` (= `F_q^n`), `wt`, `ball` | Phase 0 — complete |
| `FCC/Basic.lean` | `wt_le_wt_add_hammingDist`, `wt_zero`, `mem_ball_self` | Phase 0 — complete |
| `FCC/Statements.lean` | paper-numbered catalogue (Definitions 1–18 are phase 1, the statements are phase 2) | empty on purpose |
| `FCC/AxiomCheck.lean` | `#print axioms` audit of the headline results | complete |

Phase 0 (infrastructure) is done; the paper-specific definitions are phase 1.
`PLAN.md` §4 lists the phases and `PLAN.md` §1.1 is the table of *all* 65
numbered items of the paper (18 definitions, 19 theorems, 14 lemmas and 14
corollaries) with their status — that table is the project's checklist.

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
powershell -ExecutionPolicy Bypass -File scripts\consistency_check.ps1   # build + PLAN/Lean label coverage + orphans + sorry count
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
