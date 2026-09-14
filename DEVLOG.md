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

* `#example 6#`'s CDRM (six pairwise distances `3,4,3,3,4,3` → entries `2,1,2,2,1,2`)
  agrees with the printed matrix, and the quoted `D`-code `{000,110,101,011}`
  satisfies every entry of it;
* `#example 7#`'s 8×8 DRM was recomputed entry by entry for a non-trivial sample
  (`(u₁,u₂) = 4`, `(u₂,u₃) = 1`, `(u₁,u₅) = 3`, `(u₂,u₈) = 3`, `(u₅,u₈) = 4`)
  and agrees with the printed matrix — so the equal-function-value row really is
  the `2t_d+1` row;
* `#corollary 3#` at `t = 2` gives `252/48 = 5.25`, matching the value quoted in `#example 8#`.

**Suspected paper issues.**  Six recorded in `Notation.md` §5.  The most
substantive: `#theorem 15#`/`#theorem 16#` are printed as existence statements
("there exists an FCC … if `E ≤ q^n/|∪B|`") while their proofs and all their uses
(`#example 16#` concluding `n ≥ 9`, `#example 17#` concluding "must have length `n ≥ 9`",
`#corollary 13#` reducing to the classical Hamming bound) are in the converse direction.
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
and the axiom audit passes.  The first lemma is not decoration: `#lemma 6#` uses
`d(u,v) ≥ wt(u) − wt(v)` explicitly.

**Next.**  Phase 1a: `ball_card`, `card (Word F n) = q^n`, and the `decide`
regression tests pinned by `PLAN.md` §1.2 (`#example 6#`, `#example 7#`), which lock the
indexing conventions down before any theorem is stated.

## 2026-09-14 — Phase 1a (part 1): counting API and paper-example regression tests

**Added.**  `FCC/Balls.lean`: `diffSet`, `hammingDist_eq_card_diffSet`,
`card_word` (`|F_q^n| = q^n`), `sphere`, `mem_sphere`,
`ball_eq_biUnion_sphere`, `disjoint_sphere`, `ball_mono`, `ball_eq_univ_of_le`,
`card_ball_univ`.  `FCC/Examples.lean`: `decide` regression tests built from the
paper's own worked examples (ball and sphere sizes; Example 6 — the `[6,3,3]`
code, its CDRM, the `D`-code `{000,110,101,011}` and `N(D) = 3`; Example 7 —
the 8×8 DRM; Example 10 — the `[7,4,3]` Hamming code).  All of them pass, the
`sorry` count is 0 and the axiom audit is green (13 audited results, only
`propext`, `Classical.choice`, `Quot.sound`).

**Why the examples are worth the space.**  They are the only check that our
*transcription* of a definition agrees with the paper, and they paid for
themselves twice in this session:

1. My first transcription of Definition 11 omitted the `i = j` case (`0`), using
   the `2t_d+1` row on the diagonal instead.  The `ex7` test failed immediately
   and the printed matrix (diagonal all zeros) settled it.  This is precisely
   the silent-statement-drift failure mode that `Notation.md` warns about, and
   the paper's Example 7 matrix — not the prose of Definition 11 — is the
   evidence.  `Notation.md` §5.3 and §2.3.5 now record the resolution.
2. The same tests confirmed the rest of the convention: `ex6`'s CDRM, its
   `D`-code and the value `N(D) = 3` (no length-2 `D`-code exists: a `decide`
   search over the 256 candidates), and both Hamming codes' minimum distance 3.

**Implementation lessons (they will recur).**

* **`decide` needs a kernel-reducible alphabet.**  Over `ZMod 2` the tactic gets
  stuck (`ZMod.decidableEq` is not reducible by the kernel), so `hammingDist`
  never computes.  The regression tests therefore use `Bool`, which is `F₂` in
  mathlib's sense (`Mathlib.Algebra.Ring.BooleanRing`: `false = 0`, `true = 1`,
  `+` = xor) and whose `DecidableEq` *is* reducible; the `q = 3` ball test uses
  `Fin 3`.  The library itself keeps general-field statements, where proofs use
  mathlib lemmas instead of `decide`.
* **`decide` on an equality of functions is a trap.**  The `DecidableEq`
  instance for a nested function type (nested `Fintype`, `Multiset` machinery)
  blows the recursion depth.  State such checks pointwise
  (`∀ i j, f i j = g i j`), and raise `set_option maxRecDepth 100000` in a
  section when a search over a function space is involved (the 256-candidate
  `D`-code search).
* The `!![...]` matrix notation is not in scope by default; nested `![![…], …]`
  vector notation is, and is enough for these tests.

**Next.**  Finish phase 1a with the closed form `|B(u,t)| = Σ_{i≤t} C(n,i)(q-1)^i`
(`card_sphere`, then `ball_card` via `ball_eq_biUnion_sphere`); the proof builds
an equivalence between "word at distance `i` from `u`" and "set of the `i`
changed coordinates + the values taken on it", and `Finset.card_powersetCard`
plus `Fintype.card_ne_eq` supply the count.  It is needed by
`#theorem 15#`–`#theorem 19#` and `#corollary 13#`/`#corollary 14#`.

## 2026-09-14 — Labelling: paper markers at the head of every docstring

At the project owner's request, one must be able to see *at a glance* which item
of the paper a declaration formalizes, in the paper's own words.  The labelling
scheme was therefore unified to the paper's numbering:

* a declaration that formalizes a numbered item opens its docstring with
  `#definition N#`, `#theorem N#`, `#lemma N#`, `#corollary N#`, `#example N#` or
  `#remark N#`, followed by a paraphrase that stays close to the paper's text and
  the section number — e.g.
  ``/-- `#definition 7#` (§III) — the coded distance requirement matrix … -/``;
* a declaration that is *not* a paper item (helper, restatement of a mathlib
  lemma, notation) opens with `(internal)` or `(paper notation, §I-E)` instead,
  and names the paper item that consumes it;
* `PLAN.md` §1.1 and §1.2 use the identical strings, so a docstring and its
  inventory row can be compared character by character; the examples used as
  regression tests got their own rows (`#example 6#`, `#example 7#`,
  `#example 10#`) naming the test that owns them;
* `scripts/consistency_check.ps1` was rewritten accordingly.  It now
  (a) rejects any marker that is not an inventory row, and (b) requires each
  inventory row to be *stated*: the declaration listed in the row's "Lean name"
  column must exist **and** the docstring directly above it must carry the
  marker.  The old version accepted a marker mentioned anywhere in the file,
  which prose could satisfy by accident — and did: `#theorem 2#` appeared in an
  example inside `Statements.lean` and was counted as a stated result;
* `Notation.md` §1, `AGENTS.md` rule 13 and `FCC/Statements.lean` document the
  scheme, which is now the only label notation in the repository.

### Refinement the same day: no bare `(internal)`

The first pass left some helpers tagged with a bare `(internal)`, which reads as
"no connection to the paper" — the project owner opened `FCC/Balls.lean`, saw
`(internal)`, and reasonably concluded that the change had not been applied
there at all.  Every tag now carries an anchor:

| Tag | Meaning |
| --- | --- |
| `(paper notation, §I-E)` | the paper's own notation (a word, `wt`, `B(u,t)`) |
| `(internal, §I-E)` | a helper serving the §I-E layer |
| `(internal, §IV)` | a helper serving the `q^k` bookkeeping of §IV |
| `(internal, §VI-C — used by `#lemma 6#`)` | a helper whose consumer is known |
| `(internal, §VIII + App. — used by `#theorem 17#`–`#theorem 19#`)` | idem |
| `(internal, test scaffolding — no paper item)` | `decide` scaffolding only |

A helper whose anchor cannot be named is a smell: either it serves a numbered
item we can point at, or it does not belong in the library yet.

`scripts/consistency_check.ps1` now enforces this in step [5/5]: it fails if any
`/--` docstring opens with neither a paper marker nor an `(internal …)` /
`(paper notation …)` tag.  Two fixes went in with it: the script is ASCII-only
again (it had picked up `§`/`…` in its messages, which Windows PowerShell 5.1
mangles when reading a BOM-less `.ps1`), and it reads the Lean sources with
`-Encoding UTF8` so that non-ASCII text in docstrings is not mangled either.
