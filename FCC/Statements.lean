import FCC.Definitions
import FCC.Basic

/-!
# Paper theorem statements

The paper-numbered catalogue: every numbered definition, theorem, lemma,
corollary and proposition of

> C. Rajput, B. S. Rajan, R. Freij-Hollanti, C. Hollanti,
> "Function-Correcting Codes With Data Protection", IEEE TIT **72**(7), 2026

gets exactly one Lean declaration here (or in the phase module that owns its
proof).  The docstring of that declaration **opens with the backticked label**,
e.g.

```lean
    /-- `thm:2` (Theorem 2, §IV): the redundant-length identity. -/
    theorem optimalRedundancyData_eq_N_drmData : … := by sorry
```

(The example is indented so that this file's own docstring is not mistaken for
the statement it documents.)

so that `scripts/consistency_check.ps1` can check the paper ↔ Lean
correspondence in both directions (a label mentioned only inside prose does not
count as a stated result).

Label scheme (this paper has no LaTeX labels, only numbers):

* `def:N`, `thm:N`, `lem:N`, `cor:N`, `ex:N`, `rem:N` where `N` is the number
  the paper prints (definitions/theorems/lemmas/corollaries share a single
  counter, so `thm:10` is Theorem 10 and `lem:10` is Lemma 10).

Conventions:
* state the paper's hypotheses literally; when they can be weakened, keep the
  paper's version as the statement and record the stronger version where it is
  proved (`DEVLOG.md` explains the change);
* an unfinished proof is written `:= by sorry` **with the paper label in the
  docstring above it**; a module with `sorry` is acceptable, a module with
  errors is not;
* nothing is deleted from this catalogue once stated — it is the file reviewers
  read against the paper.  The manual fidelity checklist is `CONSISTENCY.md`.

The catalogue is filled in during phase 2 (`PLAN.md` §4); until then this file
is empty on purpose and the library still builds.
-/

namespace FCC

-- TODO(phase 2): add the paper's numbered statements here, in paper order.
-- The inventory to translate is the table in `PLAN.md` §1.1.
--
-- Template (copy, paste, fill in):
--
-- /-- `thm:example` (Theorem N) of §X: one-line statement of the theorem. -/
-- theorem example_statement {k r : ℕ} (f : Word F k → α) (C : Word F k → Word F (k + r))
--     (h : …) : … := by
--   sorry

end FCC
