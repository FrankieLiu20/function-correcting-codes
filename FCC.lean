import FCC.Definitions
import FCC.Basic
import FCC.Balls
import FCC.Examples
import FCC.Statements
import FCC.AxiomCheck

/-!
# FCC

Library root module.  It must live at the package root and its module name must
equal the library name in `lakefile.toml`; `lake build` compiles the whole
formalization by importing the modules below.

This is a formalization of

> C. Rajput, B. S. Rajan, R. Freij-Hollanti, C. Hollanti,
> "Function-Correcting Codes With Data Protection",
> *IEEE Trans. Inform. Theory* **72**(7), July 2026,
> DOI 10.1109/TIT.2026.3692458.

Layout:
* `FCC/Definitions.lean` — the paper's mathematical universe (words, weight,
  Hamming balls; the code-theoretic definitions land here too).
* `FCC/Basic.lean` — paper-independent lemmas about that universe.
* `FCC/Balls.lean` — counting: `|F_q^n| = q^n`, spheres and balls.
* `FCC/Examples.lean` — `decide` regression tests from the paper's examples.
* `FCC/Statements.lean` — the paper-numbered statement catalogue (see
  `PLAN.md` §1.1).
* `FCC/AxiomCheck.lean` — `#print axioms` audit of the headline results.

Add one module per proof phase (see `PLAN.md` §4) and import it here, otherwise
`lake build` silently skips it.
-/
