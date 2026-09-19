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

## 2026-09-14 — Restructure: one paper-order main file

The project owner asked for a single file holding the paper's numbered items in
paper order, with the internal lemmas kept elsewhere, so that the finished
formalization can be read in one place.  Done:

* **`FCC/Paper.lean` is now the main file.**  It opens with the citation, a
  statement of what lives where, and then follows the paper section by section:
  §I-E notation, §II, §III, §IV (with Examples 6 and 7), §V, §VI (with
  Example 10), §VII, §VIII, §IX, Appendix.  Each numbered item is declared there
  exactly once, in paper order, and the items not yet written appear as `TODO`
  lists under their section — so the file always shows the whole paper and the
  remaining work at a glance.  Reading it top to bottom is reading the paper's
  formalization, and it is the artifact the project delivers.
* the example checks (`ex6_*`, `ex7_*`, `ex10_*`) moved out of
  `FCC/Examples.lean` into their paper sections of `FCC/Paper.lean`; the
  scaffolding they need (`F₂`, `cdrmPaper`, `drmDataPaper`) moved to the new
  `FCC/Internal.lean`.
* `FCC/Statements.lean` is gone: the statement catalogue *is* `FCC/Paper.lean`.
  Phase 2 fills that file with `sorry`-stubbed statements in paper order, phase 3
  replaces the `sorry`s by proofs, item by item.
* `FCC/Examples.lean` is gone (split between the main file and `Internal.lean`).
* `AGENTS.md` (new rule 2a), `PLAN.md` §2, `README.md`, `Notation.md` §1 and
  `CONSISTENCY.md` state the layout.  The checker needed no change — it scans
  `FCC/*.lean` — and confirms: 63 markers used, all inventory rows; the three
  example rows stated; everything else still pending; no orphan modules.

A consequence worth recording: the paper's order is *not* the order in which the
proofs are easiest to do (the appendix counts, for instance, need no earlier
phase).  That is fine — an item may sit in `FCC/Paper.lean` as a stated theorem
whose proof is still `sorry` while its helper lemmas are being proved in
`FCC/Balls.lean`.

## 2026-09-14 — Phase 1: all 18 definitions formalized

`FCC/Paper.lean` now carries **every definition of the paper, in paper order**:
1–5 (§II), 6–9 (§III), 10–11 (§IV), 12 (§V), 13–15 (§VI), 16–18 (§VII).  Each
docstring opens with the paper's number and quotes the paper's own wording.
`PLAN.md` §1.1 marks those 18 rows `stated`; the checker confirms it.

Design decisions worth recording:

* **The combinatorial layer needs no field.**  Definitions 1–15 are stated for
  an arbitrary finite alphabet `[Fintype F] [DecidableEq F]` (plus `[Zero F]`
  for weights) and a codomain `[DecidableEq α]`; only §VII's linear layer takes
  `[Field F]`.  This is what lets the `decide` checks run with `Bool` (whose
  `DecidableEq` the kernel reduces) while the statements stay faithful.
* **`N`, `r_f`, `d(fᵢ,fⱼ)`, `d_min` are `sInf`s over `ℕ`** — the paper defines
  them as minima, and the *attained/minimal* API is phase 3.0.  Consequence for
  the examples: "`N(D) = 3`" is checked as the decidable pair "a `D`-code of
  length 3 exists" **and** "none of length 2 exists", and the equality follows
  once that API lands.
* **`IsFCC`/`IsFCCData` include systematicity.**  `#definition 6#` does not print
  the word, but the framework of §III-A and the proof of `#theorem 2#` use it;
  recorded in `Notation.md` §3.5 as a deliberate modelling decision.
* **The paper's `λ` is `lam` in Lean** (`λ` is the lambda binder) — as in
  `IsLocallyBounded f ρ lam`.
* Helpers added for these definitions: `IsSystematic`, `msgPart` and `minDist`
  (`FCC/Basic.lean`), `msgPartLinear` (§VII in the main file).
* `FCC/Internal.lean` shrank to just the test alphabet `F₂`: the example checks
  now call the real `cdrm` and `drmData`, so the temporary transcriptions are
  gone.
* `CosetCode` is kept as a set of cosets (`Set (Set C)`) rather than the
  quotient `C ⧸ D`, so that `#definition 17#` needs no quotient API.

**Still to do** (next sessions): the paper's examples (only 6, 7 and 10 are
formalized; `PLAN.md` §1.2 lists the rest, and 11/15/16/17 need the §VIII bounds
too), then phase 2 (all remaining statements with `sorry`) and phase 3 (proofs).

## 2026-09-19 — Phase 3.0: the `sInf` API, and what the scratch file taught us

Phase 2 finished (every numbered item of the paper is stated in `FCC/Paper.lean`
or recorded as an external input: the checker reports "every row with a Lean
name is stated").  Phase 3.0 then aims at the API of the `sInf`-defined
quantities `N`, `d_min`, `d(fᵢ,fⱼ)`, `r_f`.  The **upper** half is proved and
committed (`N_le_of_isDCode`, `minDist_le`, `fDist_le`,
`optimalRedundancy_le_of`, `optimalRedundancyData_le_of` — each `Nat.sInf_le`
with an explicit witness).  The **lower** half (`N(D) = r` from "a witness
exists and nothing smaller does") is *stated* and its proof resisted four
attempts; the scratch file (`import FCC.Paper`, then `lake env lean Scratch.lean`
— seconds instead of a full build) pinned down exactly why:

1. **A scratch file needs the library built first.**  `lake env lean` on a file
   importing `FCC.Paper` fails with "object file … Paper.olean does not exist"
   if the previous `lake build` failed; run `lake build` first.
2. **`dif_pos` is deprecated** (the replacement is `dite_eq_left`), and
   `Nat.find` needs a `DecidablePred`, which `classical` supplies — so the proof
   of `N_eq_of` must open with `classical`, and `rw [N]` then `exact dif_pos hne`
   does work for the three quantities whose hypotheses are plain existentials
   (`N`, `r_f`, `r_f(k:d_d,d_f)`).
3. **Do not rewrite the *set* inside `sInf`.**  `minDist` and `fDist` index
   `sInf` by a set-builder, and `rw [minDist, hs]` fails with *"motive is not
   type correct"*: ℕ's `sInf` is `if h : ∃ n, n ∈ s then Nat.find h else 0`, so
   changing the set changes the `Decidable` instance that `Nat.find` depends on.
   Likewise `Nat.sInf_def` under a type annotation mismatches "after
   simplification" because the annotated (folded) set and the elaborated
   (unfolded) predicate differ.

Two candidate fixes for that last obstacle, in order of preference:

* **(A) Change the form of the four definitions** to the `dite` form that ℕ's
   `sInf` *is*, e.g.
   `def minDist C := if h : ∃ d, d ∈ {d | …} then Nat.find h else 0`.
   Same mathematics, but `rw [minDist]; exact dif_pos hne` now works uniformly.
   Cost: the five already-proved `≤`-side lemmas use `Nat.sInf_le` and would
   need the one-line `dif_pos` proof instead.
* **(B) Keep `sInf`** and handle the dependent rewrite with `simp`/`conv` (the
   error message's own suggestion) instead of `rw`.

(A) is the cleaner of the two and is what the next session should try first;
whichever is chosen, the definition-form decision belongs in `ISSUES.md`, since
it is a change of *form* with no change of content.

## 2026-09-14 — Examples 1, 2 and 4 formalized

The §II/§III worked examples are now `decide` checks in `FCC/Paper.lean`, stated
against the real definitions and placed under their paper sections:

* `#example 1#`: `drm ex1F 1 ex1Vec` reproduces the printed 4×4 matrix;
* `#example 2#`: the `D`-code `{000,110,110,101}` (the repeat is in the paper —
  two messages with equal `f`-value may share a redundancy vector) satisfies the
  DRM, no length-2 `D`-code exists, the codewords `{00000,01110,10110,11101}`
  are as printed, and the code is an `(f,1)`-FCC;
* `#example 4#`: one function `f`, two codes, the same `t_f = 1` but minimum
  distances 1 and 2 — the example that motivates the `(f : d_d, d_f)` notation.

Two conventions for the remaining examples, decided here:

* **Min-distance and `N(D)` claims are stated as decidable facts** — "a bound
  plus an attained value" for `d_min`, "exists at length `k` plus none at
  `k − 1`" for `N` — because `minDist`, `N`, `r_f`, `fDist` are `sInf`-based
  until the phase-3.0 API lands.  The equality `N(D) = k` then follows in one
  line from that API.
* **`fdm`/`cfdm` cannot be `decide`-checked yet** for the same reason, which is
  why `#example 3#` (an FDM check) is deferred: it needs either the phase-3.0
  API or a computable restatement of the minimum over preimages.

Build-time note: the file-level `set_option maxRecDepth 100000` (needed by the
256-candidate search in `ex6_no_length_two`) makes the kernel work harder, and
this batch of `decide` proofs pushed a full build to ~5 minutes.  If the CI
wall-clock becomes a nuisance, the fix is to scope the option to the few
declarations that need it rather than the whole file.

## 2026-09-14 — Examples 5, 8, 9, 12, 13 and 14 formalized

Second batch of examples, all `decide` checks in `FCC/Paper.lean` under their
paper sections:

* `#example 5#` (§III): the least-frequent-bit function `f` on `F₂³` — the
  printed DRM (`drm ex5F 2 ex5Vec`), the `D`-code `{000000,111100,110011,001111}`
  for it, and the length-9 code of the paper, whose minimum distance is exactly
  `3`.
* `#example 8#` (§IV): the `D`-code `{000000,110110,101110,011110,011101,101101,
  110101,000011}` satisfies the 8×8 DRM of `#example 7#`.
* `#example 9#` (§V-A): `d_min({0000,0011,1100,1111}) = 2` and each codeword has
  exactly two codewords at that distance — the 4-cycle of the example.
* `#example 12#` (§VII): the *non-linear* `f(x₁,x₂,x₃) = x₁x₂` with the `[9,3,5]`
  code, including the paper's codeword table; `d_d = 3` and `d_f = 5`.
* `#example 13#` (§VII): the linear `(f : 2, 3)`-FCC with `ker f = {00,11}`.
* `#example 14#` (§VII-B): the `[10,3,4]` linear `(f : 4, 6)`-FCC of the §VII-B
  construction, with the message order of the paper's table.

Two things this batch clarified, both worth remembering for phase 2:

* the encoders in `#example 12#`/`#example 14#` are *not* systematic (`u ↦ uG`
  for a matrix that is not in standard form), so the checks are stated directly
  on the code, not through `IsFCC`/`IsFCCData` (which carry systematicity);
* `#example 13#` needed its message map spelled out (`ex13Msg`) because `f` is a
  function of the *message*, while the code lives in the longer ambient space —
  exactly the distinction that `#definition 18#`'s `kernelSubcode` formalizes.

Examples 1, 2, 4, 5, 6, 7, 8, 9, 10, 12, 13, 14 are now formalized: 12 of the
paper's 17.  The remaining five are blocked on purpose, not forgotten:
`#example 3#` and the FDM part of `#example 5#` need a computable form of the
minimum over preimages (or the phase-3.0 `fDist` API), `#example 5#`'s
`N(D) = 6` is the Plotkin bound of `#lemma 11#` (phase 3.11), and
`#example 11#`, `#example 15#`, `#example 16#`, `#example 17#` need the §VIII
bounds or a value quoted from [1].
