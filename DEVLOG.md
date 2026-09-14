# Development log

Dated, newest last.  One entry per working session; the point is that a reader
(or an agent) can see *why* a decision was made without reading the git log.

## 2026-09-14 — Phase 0: repository, toolchain, plan, notation

**Set up.**  New repository `function-correcting-codes` (Lean library `FCC`),
scaffolded from the guide repository `lean-formalization-study` (same layout,
same documentation practice, same CI), with the working copy at
`E:\lean\function-correcting-codes` (off OneDrive, because `.lake/` is several
GB).  Toolchain and mathlib pins are copied from the guide repository so that
the prebuilt mathlib cache and CI stay valid.

**Read the paper.**  All 21 pages; the dictionary in `Notation.md` §2 and the
inventory in `PLAN.md` §1.1 come from that reading.  Checked by hand:

* `ex:6`'s CDRM (six pairwise distances `3,4,3,3,4,3` → entries `2,1,2,2,1,2`)
  agrees with the printed matrix, and the quoted `D`-code `{000,110,101,011}`
  satisfies every entry of it;
* `ex:7`'s 8×8 DRM was recomputed entry by entry for a non-trivial sample
  (`(u₁,u₂) = 4`, `(u₂,u₃) = 1`, `(u₁,u₅) = 3`, `(u₂,u₈) = 3`, `(u₅,u₈) = 4`)
  and agrees with the printed matrix — so the equal-function-value row really is
  the `2t_d+1` row;
* `cor:3` at `t = 2` gives `252/48 = 5.25`, matching the value quoted in `ex:8`.

**Suspected paper issues.**  Six recorded in `Notation.md` §5.  The most
substantive: `thm:15`/`thm:16` are printed as existence statements
("there exists an FCC … if `E ≤ q^n/|∪B|`") while their proofs and all their uses
(`ex:16` concluding `n ≥ 9`, `ex:17` concluding "must have length `n ≥ 9`",
`cor:13` reducing to the classical Hamming bound) are in the converse direction.
We will state them as bounds ("if an FCC of length `n` exists then …") and flag
the printed wording rather than silently "fixing" it.

**Design decisions.**  Recorded in `Notation.md` §3; the two that shape
everything else:

1. *the alphabet is a parameter* — `Word F n` for an arbitrary
   `[Field F] [Fintype F] [DecidableEq F]`, so `q` appears literally in the
   constants of §VI/§VIII, and the binary results of §IV are specialisations;
2. *`hammingDist` comes from mathlib*
   (`Mathlib.InformationTheory.Hamming`) instead of being re-derived, which also
   gives the metric-space API for free.

**Base layer.**  `FCC/Definitions.lean` (`Word`, `wt`, `ball`) and
`FCC/Basic.lean` (`wt_le_wt_add_hammingDist`, `wt_zero`, `mem_ball_self`) build,
and the axiom audit passes.  The first lemma is not decoration: `lem:6` uses
`d(u,v) ≥ wt(u) − wt(v)` explicitly.

**Next.**  Phase 1a: `ball_card`, `card (Word F n) = q^n`, and the `decide`
regression tests pinned by `PLAN.md` §1.2 (`ex:6`, `ex:7`), which lock the
indexing conventions down before any theorem is stated.
