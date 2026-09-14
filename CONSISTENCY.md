# Consistency protocol (paper ↔ Lean)

The machine checks *that the proof proves the statement*.  It cannot check that
**the statement is the paper's statement**.  That is this document's job, and it
is a manual step performed once per numbered result, at the moment that result is
written — first when it is `stated` (phase 2), again when it is `proved`.

The paper is available only as a PDF (`paper/…OA.pdf`, git-ignored), so unlike the
guide repository there is **no `\label`-level automatic comparison with the
paper**.  The automatic check (`scripts/consistency_check.ps1`) compares the
Lean docstrings with the inventory table in `PLAN.md` §1.1, in both directions;
the paper → inventory step is what this file describes.

## Checklist per result

1. **Read the paper's statement** in the PDF (not a summary, not the inventory
   row) and write down, in the commit message or `DEVLOG.md`: the label, the
   section, the hypotheses, the conclusion.
2. **Translate the symbols** through `Notation.md` §2.  If a symbol is missing
   there, that is the bug: add it first.
3. **Compare hypotheses one by one.**
   * every hypothesis of the paper is present in the Lean statement;
   * no extra hypothesis is present that the paper does not have
     (an extra hypothesis makes the theorem weaker than the paper's, which is
     statement drift in the safe-looking direction — the most common mistake);
   * the quantifier order matches (`∀ ε ∃ N` ≠ `∃ N ∀ ε`);
   * `≤` vs `<`, `0 ≤` vs `0 <`, `d_d ≤ d_f` vs `d_d < d_f`;
   * which parameter pair is used (`t_d/t_f` vs `d_d/d_f`, `Notation.md` §2.3).
4. **Check the direction of the inequality / the implication.**  For
   existence-vs-bound statements this is where the paper itself is sometimes
   mis-printed (`Notation.md` §5 records two suspects); if the Lean statement has
   to differ from the printed words, say so explicitly in `DEVLOG.md` and keep
   both readings.
5. **Check the constants** against the paper's displayed formula, and against a
   small instance when one exists (e.g. `cor:3` at `t = 2` gives `5.25`, quoted
   in `ex:8`; the printed `thm:4` matrices can be checked against `ex:7`).
6. **Re-derive one small case by hand** (or by `decide`) whenever the result is
   concrete enough.
7. **Record the outcome** in `Notation.md` §7 (review log) and, if anything was
   resolved, remove the corresponding entry from `Notation.md` §5.

## Per-step automatic gate

```powershell
powershell -ExecutionPolicy Bypass -File scripts\consistency_check.ps1
```

checks (1) `lake build`, (2) every paper label referenced by a docstring exists
in `PLAN.md` §1.1, (3) with `-Strict`, every catalogue row of §1.1 that is not
`external` is `stated` in the library, (4) every module under `FCC/` is imported
by the root module, (5) reports the remaining `sorry` count.

```powershell
powershell -ExecutionPolicy Bypass -File scripts\axioms_check.ps1
```

checks that each headline theorem depends only on `propext`, `Quot.sound`,
`Classical.choice`, that `FCC/AxiomCheck.lean` and
`scripts/headline_theorems.txt` agree in both directions, and that no `sorryAx`
leaks into a headline result.

## What this protocol does *not* cover

* The paper's *proofs* are not compared step by step with the Lean proofs: Lean
  is allowed to prove a statement differently (and usually must, e.g. via
  `Finset` counting instead of a displayed double sum).
* Results quoted from other papers (`Notation.md` §6) are not formalized; they
  are hypotheses.  `VERIFICATION.md` lists them, so a reader can see exactly what
  the formalization assumes.
