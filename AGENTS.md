# AGENTS.md — rules for agents and contributors working in this repository

This repository is a Lean 4 + mathlib formalization of Rajput, Rajan,
Freij-Hollanti and Hollanti, *Function-Correcting Codes With Data Protection*,
IEEE Trans. Inform. Theory **72**(7), 2026 (DOI 10.1109/TIT.2026.3692458).

Read `PLAN.md` (§1.1 statement inventory, §4 phases) and `Notation.md` (the
paper ↔ Lean dictionary) **before writing code**.  The toolchain is pinned in
`lean-toolchain`, mathlib in `lake-manifest.json` / `lakefile.toml`.

The rules below are adapted from `AGENTS.md` in Shenghao Yang's
`n4code_lean_dev`, which is the model for this project.

## Workflow rules

1. **One step per session, one commit per step.**  A step is one sub-phase of
   `PLAN.md` §4 (or one numbered result of the paper).  Small commits make it
   possible to find the commit that introduced a wrong *statement*.

2. **Plan first.**  Before writing a theorem, add its row to `PLAN.md` §1.1
   (label, section, condensed statement, Lean name) and update
   `Notation.md` if it introduces notation.  The inventory is the source of
   truth; code follows it.

2a. **Paper items live in `FCC/Paper.lean`, in paper order.**  Every numbered
    item of the paper — definition, example, theorem, lemma, corollary — is
    declared exactly once, in that file, under its section heading, with the
    paper's number at the head of its docstring; that file is the deliverable
    (reading it top to bottom is reading the paper's formalization).  Everything
    that is not a numbered item is a helper and belongs in `FCC/Definitions.lean`
    (the §I-E notation), `FCC/Basic.lean`, `FCC/Balls.lean` or
    `FCC/Internal.lean`, with an `(internal, §…)` docstring; helpers may be
    reorganised freely, and a helper that turns out to be a paper item is moved
    into `FCC/Paper.lean`.

3. **State the paper's hypothesis literally.**  If a hypothesis can be
   weakened, state the paper's version as the catalogue entry and record the
   stronger version where it is used.  Never silently generalise a statement
   (that is statement drift) and never silently restrict it.

4. **A finite field is a parameter.**  Statements are over an arbitrary
   `F` with `[Field F] [Fintype F] [DecidableEq F]`; `q = Fintype.card F`.
   The binary rows of §IV/§VI are specialisations (`F = ZMod 2`), not the norm.

5. **Reuse mathlib before re-deriving.**  Hamming distance/weight come from
   `Mathlib.InformationTheory.Hamming`; binomial coefficients, `Finset`
   cardinality lemmas, `Matrix`/`LinearMap` and probability lemmas are in
   mathlib.  Search with `rg "def <name>" .lake/packages/mathlib/Mathlib/`
   before writing anything new.

6. **Cited results are hypotheses, never `axiom`s.**  `#lemma 1#`, `#lemma 4#`,
   `#lemma 12#`, `#corollary 3#`, `#corollary 5#` are quoted from [1], [10], [14] (see
   `Notation.md` §6).  Where a result is needed, add it as an explicit
   hypothesis of the statement, so `scripts/axioms_check.ps1` stays meaningful.

## Build-performance rules (must follow)

7. **Never run bare `lake clean`.**  With no arguments it deletes the build
   directory of every package in the workspace, including the prebuilt mathlib
   oleans under `.lake/packages/mathlib/.lake/build`, forcing a source rebuild
   of ~6000 modules.  To clean this package only: `lake clean FCC`.

8. **Never rebuild mathlib from source.**  If the mathlib oleans are missing or
   stale, restore them with `lake exe cache get` first, then `lake build`.  The
   local cache under `~/.cache/mathlib` makes this cheap after the first
   download.

9. **Build incrementally.**
   - `lake build` — normal incremental build (seconds when up to date);
   - `lake build FCC.<Module>` — rebuild one module;
   - `lake env lean FCC/<File>.lean` — type-check a single file.
   Do not add `lake clean` (or any cache-wiping step) to scripts or CI.

10. **Minimal imports, never `import Mathlib`.**  Import only the mathlib
    modules a file needs.  Workflow for a new file:
    a. start from a small candidate import list;
    b. compile; when the compiler reports an unknown identifier or notation,
       add the module that provides it (find it with `rg` under
       `.lake/packages/mathlib/Mathlib/`);
    c. optionally run `lake shake <file>` to minimise the list automatically.
    Keep imports dependency-ordered and delete ones that become unused.

11. **Keep modules small and the import graph shallow.**  Related lemmas belong
    in the same module; do not create one module per lemma.  Avoid tactics that
    blow up elaboration (`simp`/`aesop` over large `Finset.univ`, `native_decide`
    on big search spaces).  `decide` on a hand-written small instance (the
    examples of the paper) is encouraged.

12. **Respect the root-module layout.**  The library root module is `FCC.lean`
    at the package root and its module name must equal the library name.  New
    modules go under `FCC/` and must be imported from the root module, otherwise
    `lake build` silently skips them.  If the build fails with `some modules
    have bad imports`, check the root module.

13. **Docstrings.**  Every completed definition/lemma carries a one-line
    docstring.  The docstring of the declaration that owns a paper statement
    **opens with the backticked label**, e.g.

    ```lean
    /-- `#theorem 2#` (Theorem 2, §IV): `r_f(k,t_d,t_f) = N(D_f(t_d,t_f : u₁,…,u_{q^k}))`. -/
    ```

    `scripts/consistency_check.ps1` uses exactly this convention to decide
    whether a row of `PLAN.md` §1.1 is stated; a label mentioned only inside
    prose does not count.  Use section numbers, never PDF page numbers in code
    and never tex line numbers.

    Helpers that are *not* a numbered item of the paper open their docstring
    with `(internal, §… )` or `(paper notation, §…)` instead of a marker, and
    must name the paper part they serve — `(internal, §VI-C — used by
    `#lemma 6#`)` — so a bare `(internal)` never stands on its own.  Keep the
    text after the tag close to the paper's own wording: a reader must be able
    to compare the docstring with the PDF without translating.  The checker
    enforces this (a docstring with no marker and no tag fails the build gate),
    and `(internal, test scaffolding — no paper item)` is the only tag without
    a section, used for the `decide` scaffolding in `FCC/Examples.lean`.

14. **Never leave the build broken.**  `sorry` stubs are allowed while a phase
    is in progress, but every `sorry` must carry a comment naming the paper
    label it corresponds to, and the file must compile.  A module containing
    `sorry` is acceptable; a module with errors is not.

15. **Keep the worktree clean.**  `.lake/`, `build/`, `*.olean`, `*.pdf`,
    `reference/` and editor files are untracked; never commit build artefacts or
    the paper.  Commit only source: `*.lean`, `*.md`, `lakefile.toml`,
    `lean-toolchain`, `lake-manifest.json`, `scripts/*`, `CITATION.cff`,
    `NOTICE`, `LICENSE`.

## Verification workflow

1. After editing a module: `lake build FCC.<Module>`.
2. After every step (before committing):
   `powershell -ExecutionPolicy Bypass -File scripts\consistency_check.ps1 -Strict`
   and follow the checklist in `CONSISTENCY.md` — in particular the *manual*
   step: re-read the paper's statement in the PDF and compare it word by word
   with the Lean statement (there is no LaTeX source, so this cannot be
   automated).
3. Before reporting a phase complete: full `lake build` (must pass).
4. After any change to imports or the lakefile: full `lake build`.
5. Before any release: `powershell -ExecutionPolicy Bypass -File
   scripts\axioms_check.ps1` (fails on `sorryAx`), and fill in the verification
   report in `VERIFICATION.md`.

## Tooling rules (PowerShell, git)

16. **Never read a build's exit code through a pipe.**  The idiom
    `lake build 2>&1 | Select-String … ; if ($LASTEXITCODE -ne 0) { git checkout -- … }`
    is a trap: `$LASTEXITCODE` is then the *cmdlet's* status, and
    `Select-String` exits `1` when it finds no match, so the "failure" branch
    fires after a perfectly good build and silently reverts the file.  Capture
    the build's own status instead:

    ```powershell
    $out = lake build 2>&1; $code = $LASTEXITCODE; $out | Select-String 'error'
    ```

    This happened once (`DEVLOG.md`, 2026-09-20) and produced a *green build of
    the reverted file*, which is the worst kind of green.

17. **A green build is not evidence that the edit is present.**  Before
    reporting a step as done, `git status --short` and `git diff --stat` must
    show the files the step touched.  Committing is the only durable record:
    uncommitted work in the shared working copy can be reverted by another
    process.

18. **Keep the build warning-free apart from `sorry` stubs.**  In this mathlib
    pin `dif_pos`/`if_pos`/`if_neg` are deprecated
    (`dite_eq_left`/`ite_eq_left`/`ite_eq_right`) and `Set.mem_setOf_eq` is now
    `Set.mem_ofPred_eq`.  A declaration that does not use a section variable
    should silence the linter with `omit [<instance>] in` placed **before** its
    docstring (the form mathlib itself uses).

## Common failure modes

- `FCC: some modules have bad imports` — the library root module `FCC.lean` is
  missing from the package root, or an imported module name does not resolve.
- `unknown identifier` / `unknown namespace` — a missing import; find the module
  with `rg "def <name>" .lake/packages/mathlib/Mathlib/`.
- `failed to synthesize instance ... Fintype` — add
  `import Mathlib.Data.Fintype.Pi` (for function types), or instantiate
  `Fintype F` explicitly.
- `failed to synthesize ... LocallyFiniteOrder ℕ` — add
  `import Mathlib.Order.Interval.Finset.Nat` (needed for `Finset.Icc`).
- `Nat.Even`/`Nat.Odd` unknown — recent mathlib uses the generic `Even`/`Odd`
  from `Mathlib.Algebra.Ring.Parity`.
- `unknown identifier omega` — `omega` comes from Lean core; add the import the
  compiler asks for, or use `linarith`/`nlinarith`.
- `no goals to be solved` / `unsolved goals` after `decide` — check that the
  definitions involved are computable (no `noncomputable` on `N`, `sInf`,
  `Fintype.card`-heavy expressions) and that the indices match
  (`Notation.md` §2.3).
