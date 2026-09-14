import FCC.Definitions
import FCC.Basic

/-!
# Paper theorem statements

The paper-numbered catalogue: every numbered definition, theorem, lemma,
corollary and proposition of

> C. Rajput, B. S. Rajan, R. Freij-Hollanti, C. Hollanti,
> "Function-Correcting Codes With Data Protection", IEEE TIT **72**(7), 2026

gets exactly one Lean declaration here (or in the phase module that owns its
proof).  The docstring of that declaration **opens with the paper's own
number**, e.g.

```lean
    /-- `#theorem 2#` (§IV): `r_f(k, t_d, t_f) = N(D_f(t_d, t_f : u₁, …, u_{q^k}))`. -/
    theorem optimalRedundancyData_eq_N_drmData : … := by sorry
```

(The example is indented so that this file's own docstring is not mistaken for
the statement it documents.)

so that `scripts/consistency_check.ps1` can check the paper ↔ Lean
correspondence in both directions: a marker mentioned only in the middle of a
docstring does not count as a stated result, and a helper that is not a paper
item opens its docstring with `(internal)` instead.

Label scheme (the paper has no LaTeX labels, only numbers): `#definition N#`,
`#theorem N#`, `#lemma N#`, `#corollary N#`, `#example N#`, `#remark N#`, all
sharing the paper's single counter; `Notation.md` §1 has the full table.

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
