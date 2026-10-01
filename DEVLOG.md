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

## 2026-09-20 — Phase 3.2: `#theorem 2#` proved (the first paper result)

`sorry` count 49 → 46.  `optimalRedundancyData_eq_N_drmData` — the paper's
central identity `r_f(k,t_d,t_f) = N(D_f(t_d,t_f : u₁, …, u_{q^k}))` — is a
theorem, not a stub, and is registered as a headline result (`FCC/AxiomCheck.lean`
and `scripts/headline_theorems.txt`): its audit output is the standard trusted base
`propext`, `Classical.choice`, `Quot.sound`, no `sorryAx`.

**How it was split.**  Four `(internal, …)` bricks, now stored *before*
`#theorem 2#` in dependency order so that the paper's statement can cite them
(helpers may move freely; paper items may not):

| Brick | What it does |
| --- | --- |
| `hammingDist_eq_msg_add_red` | systematic ⇒ `d(C u, C v) = d(u,v) + d(p_u,p_v)` |
| `isDCode_drmData_of_isFCCData` | an FCC of redundancy `r` gives a DRM `D`-code of length `r` |
| `N_drmData_le_of_isFCCData` | hence `N(D_f) ≤ r` — the **≥** half |
| `optimalRedundancyData_le_of_isDCode` | a DRM `D`-code of length `r` gives `r_f ≤ r` — the **≤** half |

**Lesson 1 — the paper's `d_d ≤ d_f` is load-bearing.**  `#definition 6#`
demands data protection for *every* pair `u₁ ≠ u₂`, while the DRM records the
`2t_d+1` slack only on the pairs with `f(u₁) = f(u₂)`; for the other pairs it
supplies `2t_f+1 − d`.  So the `≤` half needs `2t_d+1 ≤ 2t_f+1` to transfer the
guarantee, and without it the identity is false (not merely hard).  The first
attempt wrote the proof without the hypothesis and `omega` refused — correctly;
the fix was to add the hypothesis to the statement, not to weaken the goal.
Recorded as `ISSUES.md` §11(a).

**Lesson 2 — `sInf` attainment has to be earned.**  The `≤` half needs a DRM
code of length *exactly* `N(D_f)`, i.e. `Nat.sInf_mem` plus nonemptiness of the
code set.  Nonemptiness comes from the FCC itself
(`isDCode_drmData_of_isFCCData`), which is why `#theorem 2#` carries an
existence hypothesis `hex`.  (The `≥` half is easier: there `Nat.find_spec`
hands over the FCC that attains `r_f`.)  Removing `hex` — by constructing an FCC
outright, e.g. by padding the message with copies of itself — is `PLAN.md` §4
phase 3.14.  Recorded as `ISSUES.md` §11(b).

**Lesson 3 — a stale pipeline reverted a file (worth remembering).**  A command
from the *previous* session of the form
`lake build 2>&1 | Select-String … ; if ($LASTEXITCODE -ne 0) { git checkout -- … }`
was still finishing when this session started.  `Select-String` exits with `1`
when it finds no match, so the "revert on failure" branch fired after a
*successful* build: the uncommitted proof silently vanished, and the next build
looked green precisely because the file was back at `HEAD`.  Two habits came out
of it: capture `$LASTEXITCODE` from `lake build` itself and never from a cmdlet
downstream of a pipe, and re-read `git status`/`git diff` before believing a
green build (a green build of the wrong file looks exactly like a green build).

**Lint cleanup, in the same session.**  `dif_pos`/`if_pos`/`if_neg` are
deprecated in this mathlib pin (`dite_eq_left`/`ite_eq_left`/`ite_eq_right`),
`Set.mem_setOf_eq` is now `Set.mem_ofPred_eq`, and the eight `sInf`-API lemmas
carried unused section variables, silenced with
`omit [Fintype F] in` / `omit [DecidableEq α] in` (the form mathlib itself uses:
the `omit` goes *before* the docstring).  `lake build` is now warning-free apart
from the remaining `sorry` stubs, which keeps the next sessions' output readable.

**Verification for this session.**  `lake build` green (1818 jobs),
`scripts/consistency_check.ps1` green (78 markers, 73 rows stated, 46 `sorry`),
`scripts/axioms_check.ps1` green (14 headline results), CI green on the push.

## 2026-09-20 (same day, second session) — phase 3.14 (non-vacuity) and `#theorem 3#`

`sorry` 46 → 43; headline results 14 → 17.

**Phase 3.14 — an FCC always exists (`exists_isFCCData`).**  For *any* function
`f` and *any* targets `d_d, d_f` there is an `(f : d_d, d_f)`-FCC of some
redundancy.  The construction is the cheapest one: write the message down
`m = max d_d d_f` times, i.e. take `C u = (u, u, …, u)` — the message followed by
`m` copies of itself.  Then `d(C u, C v) = d(u,v) + m·d(u,v) ≥ m ≥ d_d, d_f` for
`u ≠ v`, and `C` is systematic by construction.  Two internal bricks in
`FCC/Balls.lean` carry it:

* `repWord t u` — `t` copies of a word, in the shape `k * t` (recursion on `t`
  with `Fin.append`);
* `hammingDist_repWord` — `d(u…u, v…v) = t · d(u,v)`, by induction on `t` using
  `hammingDist_append`;
* `hammingDist_comp_cast` — re-indexing along a cardinality equality changes no
  distance.  This looks trivial but is what makes the induction step go through:
  the recursive definition shifts the shape `(t+1)*k ↔ k + t*k` by `Fin.cast`.

Consequences, and the reason this is a "base" step rather than a paper item:
`#theorem 2#` no longer needs its former `hex` hypothesis (its statement now
carries only the paper's own `d_d ≤ d_f`), and everywhere a lower bound needs the
optimum to be *attained* one may use `Nat.sInf_mem` / `Nat.find_spec`.

**`#theorem 3#`, all three parts.**

* `optimalRedundancyData_ge_N_subset` — the optimal FCC, restricted to any
  subfamily `u₁, …, u_m`, is a `D`-code of the same length.  This is why
  `isDCode_drmData_of_isFCCData` was generalised from the identity family to an
  arbitrary family `u : ι → Word F k` (for `i ≠ j` with `uᵢ = uⱼ` the DRM entry is
  `0` by definition, so there is nothing to prove there).
* `two_mul_le_optimalRedundancyData` — needs the paper's "if `|Im(f)| ≥ 2` then
  there exist `u, v` with `f(u) ≠ f(v)` and `d(u,v) = 1`", which the paper states
  without proof.  The formal proof walks from `u` to `v` changing one coordinate
  at a time (`exists_hammingDist_one_ne`): the walk starts at `f u` and ends at
  `f v`, so some step of it changes the value of `f`, and that step is the pair.
  On such a pair the DRM reads `max(2t_f + 1 − 1, 0) = 2t_f`, and a `D`-code of
  length `r` has pairwise distances at most `r`, so `2t_f ≤ N(D_f) ≤ r_f`.
* `optimalRedundancyData_ge_Nconst_sub` — the attaining FCC already has
  `d(C u, C v) ≥ 2t_d+1` for *every* pair (data protection), so enumerating the
  `q^k` messages turns it into a code of length `k + r_f` with `q^k` codewords and
  minimum distance `2t_d+1`; hence `N(q^k, 2t_d+1) ≤ k + r_f`.  This part is
  *cleaner* than the printed proof: it needs no `t_f ≥ t_d`, because it uses
  `#definition 6#`'s first clause directly instead of the DRM entries (the paper
  argues through `[D_f]_{i,j} ≥ max(2t_d+1 − d, 0)` and notes "as `t_f ≥ t_d`").

**Verification.**  `lake build` green, warning-free apart from the 43 `sorry`
stubs, `scripts/consistency_check.ps1 -Strict` green, `scripts/axioms_check.ps1`
green (17 headline results, standard trusted base).

## 2026-09-22 — the §II results proved, and two statements were *wrong* (fixed)

`sorry` 43 → 39; headline results 17 → 21.

**Two statements were wrong, not merely unproved (`ISSUES.md` §12).**
`#theorem 1#` and the upper-bound half of `#theorem 7#` handed `N` the FDM / CFDM
*indexed by the whole alphabet* `α`.  Because `fDist` (and `codedFDist`) are `0`
on empty preimages (the blanket conventions of `#definition 4#`/`#definition 8#`,
issue §8), every pair of values outside `Im(f)` then demands distance `2t+1`; an
infinite `α` cannot be placed in the finite space `Word F r`, so the code set is
empty, `N` collapses to `0` under the `sInf ∅ = 0` convention, and the inequality
is false — counterexample in §12: `F = ZMod 2`, `k = 1`, `α = ℕ`, `t = 1`, where
`r_f = 2` but the printed right-hand side is `0`.  Both are now indexed by
`Im(f)` (`Set.range f`), the paper's `f₁, …, f_E`.  `#corollary 1#` and
`#corollary 2#` were re-checked and are faithful as they stood: their right-hand
sides are DRMs indexed by *messages*.

**`#corollary 1#`, `#theorem 1#`, `#corollary 2#` are now proved.**  The §II
half of the paper's framework needed its own bricks, and the file was
reorganised so that they precede the statements that cite them (helpers may move,
paper items may not):

* `exists_isFCC` — an `(f,t)`-FCC always exists (write the message down `2t+1`
  times): the §II analogue of `exists_isFCCData`, and the reason
  `optimalRedundancy` is attained;
* `isDCode_drm_of_isFCC` — an `(f,t)`-FCC extracted to a DRM `D`-code of the same
  length (the §II analogue of `isDCode_drmData_of_isFCCData`);
* `hammingDist_eq_msg_add_red`, `N_le_of_isDCode`, `fDist_le`,
  `optimalRedundancy_le_of` and `exists_hammingDist_one_ne` were moved up from
  the §IV block into an "(internal, §II)" block before the §II results.

The proofs are the §II mirror images of `#theorem 2#`/`#theorem 3#`:
`optimalRedundancy_ge_drm` restricts the optimal FCC to a subfamily;
`two_mul_le_optimalRedundancy` uses the distance-one pair of
`exists_hammingDist_one_ne` (on that pair the DRM reads `max(2t+1−1,0) = 2t`);
`optimalRedundancy_le_fdm` turns an image-indexed FDM `D`-code `p` into the FCC
`C u = (u, p_{f(u)})`; and `optimalRedundancy_eq_fdm` sends a `D`-code of a
representative family to `C v = (v, p_{i(v)})` (the `hattain`/`hsurj`
hypotheses) and, in the other direction, restricts the optimal FCC.

**Why the corrected `#theorem 1#` is provable.**  The image-indexed FDM `D`-code
set is nonempty: choose a representative `u_a` of each value `a ∈ Im(f)` and take
`p a := u_a` repeated `2t+1` times (`repWord` again) — different values have
different representatives, so the repeated words are at distance `≥ 2t+1 ≥` any
FDM entry.  That is where the phase-3.14 machinery pays off a second time.

**Verification.**  `lake build` green, warning-free apart from the 39 `sorry`
stubs; `scripts/consistency_check.ps1 -Strict` green;
`scripts/axioms_check.ps1` green (21 headline results).

## 2026-09-22 (second session) — §IV two-step machinery: `#theorem 5#`, `#corollary 4#`, `#theorem 6#`

`sorry` 39 → 36; headline results 21 → 24.  As asked, every statement was compared
with the paper *before* proving; that found two deviations, one of which needed a
hypothesis the paper's proof uses.

**Statement check (the paper's §IV, pp. 4867–4868).**

* `#theorem 5#` — the paper's proof says "Without loss of generality, consider a
  *systematic* form of `C`, i.e. `c_u = (u, w_u)`".  That WLOG is legitimate for a
  linear code, but our `C` is an arbitrary labelling map, so systematicity is an
  extra hypothesis and is now explicit (`hCsys`).  It is used exactly there:
  `d(w_u,w_v) = d(c_u,c_v) − d(u,v)`.  Recorded as `ISSUES.md` §13(a).
* `#theorem 5#` is now stated for an arbitrary family `u : ι → Word F k` (the
  paper's `u₁,…,u_{q^k}` is `ι = Word F k`, `u = id`); `D_f`/`D_{C,f}` are
  family-indexed, and the generalization makes `#corollary 4#` a one-liner.
* `#corollary 4#` therefore carries `hCsys` and the standing `d_d ≤ d_f`
  (`hdf`), the latter inherited from `#theorem 2#` — `ISSUES.md` §13(c).
* `#theorem 6#` matches the paper as printed (only the min-distance hypothesis) —
  a nice contrast with `#theorem 5#`.
* `#theorem 7#` was re-read and is a **proxy**, not the paper's statement: its
  first conjunct is a definitional unfolding of `schemeRedundancy`, whereas the
  paper bounds the scheme redundancy `r_s = (n−k) + r'` from below.  Fixing it
  needs the second step (an `(f ∘ C⁻¹, t_f)`-FCC on the codeword set `Im(C)`) as
  a parameter; queued, `ISSUES.md` §13(d).

**Proofs.**  `#theorem 5#` is the heart of §III-A: from a `D₂`-code
`p₁,…,p_m` for the CDRM, the code `p̃ᵢ := (wᵢ, pᵢ)` of length `N(D₂) + r` is a
`D₁`-code for the DRM-data — the two cases being `f(uᵢ) = f(uⱼ)` (the redundancy
part alone carries `2t_d+1 − d(uᵢ,uⱼ)`, by systematicity plus the code's minimum
distance) and `f(uᵢ) ≠ f(uⱼ)` (the CDRM condition supplies
`2t_f+1 − d(cᵢ,cⱼ)`, which combines with `d(wᵢ,wⱼ)` to `2t_f+1 − d(uᵢ,uⱼ)`).
`#corollary 4#` is then `#theorem 2#` composed with `#theorem 5#`.

`#theorem 6#` needed a new kind of care: the paper's one-liner "the entries are
at most `2(t_f−t_d)`, therefore `N(D_{C,f}) ≤ N(M,2(t_f−t_d))`" implicitly uses
that the constant matrix's optimum is *attained*.  In Lean the proof splits on
whether the constant matrix has a code at all: if it does, `Nat.sInf_mem`
supplies it; if it does not, the alphabet must be a single letter
(`exists_isDCode_const`, built from `repWord`), all messages coincide, the CDRM
is identically `0` and both sides are `0`.

**New internal bricks.**  `cdrm_le` (CDRM entries `≤ 2(t_f−t_d)`) and
`exists_isDCode_const`.

**Verification.**  `lake build` green, warning-free apart from the 36 `sorry`
stubs; `consistency_check.ps1 -Strict` green; `axioms_check.ps1` green
(24 headline results).

## 2026-09-22 (third session) — `#theorem 7#` reworked to the paper's statement, and proved

`sorry` 36 → 35; headline results 24 → 25.

**Statement check first (as requested).**  §III-A of the paper ("A General Method
for Constructing `(f : D_d, d_f)`-FCCs") is a two-step scheme: Step 1 selects an
`[n,k,d_d]` linear code with generator matrix `G` (`c_u = uG`); Step 2 builds an
FCC **on the codeword set** `{c_u}`, i.e. a systematic `C'_f : C → F_q^{n+r'}`
with `d(C'_f(c_{u₁}), C'_f(c_{u₂})) ≥ d_f` whenever `f(u₁) ≠ f(u₂)`; then
`C_f(u) = C'_f(c_u)` is an `(f : d_d, d_f)`-FCC with total redundancy
`r_s = n − k + r'`.  The old Lean statement of `#theorem 7#` captured none of
this literally: it compared two `N`'s and its first conjunct was a definitional
unfolding of `schemeRedundancy`.  Reworked (`ISSUES.md` §13(d)):

* `twoStepCode C E` — the encoder `C_f(u) = (C u, E u)`, with `E` the second
  block; its shape is `k + (r + r')` so that `schemeRedundancy r r'` is the total
  redundancy (the reassociation `(k+r)+r' = k+(r+r')` is absorbed by
  `hammingDist_comp_cast`);
* `IsSecondStep f C tf E` — the paper's Step 2 condition for the *composite*
  codewords: `d(C u, C v) + d(E u, E v) ≥ 2t_f + 1` when `f u ≠ f v`.  Note it is
  genuinely weaker than "the block alone separates the values", which is why the
  CDRM/CFDM enter at all;
* `twoStep_isFCCData` — the paper's "straightforward verification": Step 1's
  minimum distance gives `2t_d+1` for `u₁ ≠ u₂`, Step 2 gives `2t_f+1`;
* the two bounds are now the paper's:
  * lower: for **every** second step, `N(D_{C,f}(u₁,…,u_M)) + n − k ≤ r_s` —
    because Step 2 makes the block `E` a `D`-code for the CDRM;
  * upper: **any** CFDM `D`-code of length `L` over the image values `Im(f)` gives
    a second step of block length `L`, hence a scheme with `r_s = L + (n−k)`;
    taking `L := N(CFDM)` (available in the paper's finite setting) is the printed
    upper bound.  This is where the new `codedFDist_le`
    (`d_C(a,b) ≤ d(C u,C v)` for a witness pair) is used.

The paper's clause "`n` denotes the minimum possible length of a linear code with
dimension `k` and minimum distance `≥ 2t_d+1`" is a remark about *which* first
step the scheme uses; both bounds hold for any systematic `[n,k,2t_d+1]` code, so
it is not a hypothesis of the Lean statement (recorded in the docstring).

**Verification.**  `lake build` green, warning-free apart from the 35 `sorry`
stubs; `consistency_check.ps1 -Strict` green; `axioms_check.ps1` green
(25 headline results).

## 2026-09-22 (fourth session) — `#theorem 4#`, the binary lower bound

`sorry` 35 → 34; headline results 25 → 26.

**Statement checked first, as usual:** the paper (p. 4866) states
`r_f(k,t_d,t_f) ≥ 2t_f + t_d` for any `f : F₂^k → Im(f)` with `2 ≤ |Im(f)| ≤ k` —
our statement matches as printed (with `|Im f|` as `(Finset.univ.image f).card`),
so no change was needed.

**The proof (the paper's argument, pp. 4866–4867).**  Take a message `u₁` with a
neighbour `u₂ = u₁ + e_j` at distance one and `f(u₂) ≠ f(u₁)`
(`exists_hammingDist_one_ne`).  The `k` neighbours `u₁ + eᵢ` together with `f(u₁)`
take at most `|Im f| ≤ k` values, so either two neighbours share a value `≠ f(u₁)`
(Case 1) or some neighbour has `f(u₁ + eᵢ) = f(u₁)` (Case 2).  In both cases the
three messages involved are at pairwise distances `1, 1, 2`, so the corresponding
*redundancy blocks* satisfy two lower bounds of `2t_f` (resp. `2t_f − 1` for the
distance-two pair) and one of `2t_d` (resp. `2t_d − 1`): the FCC conditions give
`d(Cu,Cv) ≥ 2t_f+1` (function values differ) and `≥ 2t_d+1` (data protection),
and the splitting identity turns those into bounds on the blocks.  Three *binary*
words of length `r` have pairwise distances summing to at most `2r` (each
coordinate contributes to at most two of the three pairs — three pairwise
different values do not fit into `ZMod 2`), so `4t_f + 2t_d − 1 ≤ 2r`, i.e.
`r ≥ 2t_f + t_d`.  Here `r` is the redundancy of the FCC attaining `r_f`, which
exists by `exists_isFCCData` — no non-vacuity side condition is needed.

**New internal bricks** (in `FCC/Balls.lean`, which therefore now imports
`Mathlib.Data.ZMod.Basic`): `flip` (the neighbour `u + eᵢ`), `flip_flip`,
`flip_ne_self`, `hammingDist_flip_self` (`d(u, u+eᵢ) = 1`),
`hammingDist_flip_flip` (`d(u+eᵢ, u+eⱼ) = 2`),
`eq_flip_of_hammingDist_eq_one` (a word at distance one *is* a flip — this is what
identifies the paper's `u₂` as `u₁ + e_j`), `hammingDist_three_le_two_mul` and the
pigeonhole `exists_ne_eq_of_card_lt`.  Two `ZMod 2` facts carry the arithmetic:
`zmod_two_add_one_ne_self` and `zmod_two_eq_add_one_of_ne` (the latter by `decide`
over the two elements).

**Verification.**  `lake build` green, warning-free apart from the 34 `sorry`
stubs; `consistency_check.ps1 -Strict` green; `axioms_check.ps1` green
(26 headline results).

## 2026-09-22 (fifth session) — §V-A: `#theorem 8#` and `#theorem 9#`

`sorry` 34 → 32; headline results 26 → 28.

**Statement check first, and it mattered again (`ISSUES.md` §14).**  In §V the
paper's `C` is a `(n, q^k, d)` code — exactly one codeword per message, "let `c_u`
denote the codeword that corresponds to the message vector `u`" — so the encoding
is a *bijection* onto `C`.  Our transcriptions only required `enc u ∈ C`, and that
is **false**: `C = {000, 001, 100}` (a `V`, hence connected, with `d_min = 1`),
`f` two-valued on `F₂¹`, `d_f = 2 > d = 1`, and `enc 0 = 001`, `enc 1 = 100` is a
systematic `(f : 1, 2)`-FCC whose codewords all lie in `C` (the paper's setting is
excluded because `|C| = 3 ≠ q^k = 2`).  Both statements now require the range to be
exactly `C` (`Set.range enc = ↑C`), which is the paper's `(n, q^k, d)` code with
its labelling.

**The proof.**  The whole of §V-A is one observation plus propagation: a codeword
cannot be the image of two messages carrying different values (`d_f ≤ d(x,x) = 0`),
and two codewords at distance `d_min(C) = d < d_f` cannot be images of messages with
different values either (`d_f ≤ d(x,y) = d`).  Hence the set of values carried by a
codeword is a subsingleton and is *constant on connected components*; different
values therefore live in different components.  `#theorem 8#` contradicts
connectedness directly; `#theorem 9#` exhibits `Q + 1` pairwise different values
(`|Im f| ≥ Q + 1`) and hence `Q + 1` distinct components, contradicting
`componentCount = Q` (the count is `Nat.card G.ConnectedComponent`, and the
injection `Fin (Q+1) → components` gives `Q + 1 ≤ Nat.card ...`).

Implementation notes worth keeping: the propagation goes by induction on
`SimpleGraph.Walk`, and the *explicit* constructor pattern `@cons x' z y' hxy p ih`
is what names the intermediate vertex (`induction w with | cons ...` leaves it
implicit, and then the membership hypotheses do not line up); the "same component ⇒
reachable" bridge is `SimpleGraph.ConnectedComponent.exact`, and the counting is
`Nat.card_le_card_of_injective` on `↥t ≤ Nat.card (minDistGraph C).ConnectedComponent`
for a `Finset t` of `Q + 1` values.

**Verification.**  `lake build` green, warning-free apart from the 32 `sorry`
stubs; `consistency_check.ps1 -Strict` green; `axioms_check.ps1` green
(28 headline results).

## 2026-09-29 — integrity audit, repository cleanup, and §V-B statement fixes

**Audit (the user suspected an accidental change).**  Nothing was damaged.
Evidence: `git status` clean, HEAD = `677691e` = remote `main`, no stray branches /
tags / PRs, all 31 tracked files present, and the full pipeline re-run green
(`lake build` exit 0 with 32 `sorry`s, `consistency_check.ps1 -Strict` green with
73 rows and the module graph, `axioms_check.ps1` green with 28 headline results);
the last CI runs on GitHub are green; the OneDrive side (notes + four papers) is
intact.

**One pre-existing defect found and fixed.**  The restructure that moved every
module into `FCC/` had left two stale copies at the package root: `Basic.lean`
(7 declarations vs 9 today) and `Paper.lean` (112 vs 156), both still tracked by
git but not part of the library (the root module `FCC.lean` imports only `FCC/*`),
so a reader could mistake the outdated root `Paper.lean` for the deliverable.  Both
are removed, and `scripts/consistency_check.ps1` now **fails** if any `.lean` file
other than `FCC.lean` sits at the package root, so this cannot come back unnoticed.

**§V-B statements checked against the PDF — two corrections (`ISSUES.md` §15).**

* `#corollary 7#`: the printed sum runs to `⌊(d_d−1)/2⌋` (the ball radius); the
  transcription used `d_d/2`, adding one spurious term for even `d_d`.  Fixed.
* `#corollary 8#`: the paper assumes the *existence* of an MDS `(n, q^k, d)` code,
  and the claim needs `|Im f| ≥ 2`.  With only the parameter relation and no
  `|Im f| ≥ 2` the statement is false: for constant `f`, `F = F₂`, `k = 1`,
  `d = 2`, `n = 2`, the encoding `u ↦ (u,u)` has redundancy `1 < 2 = d`.  The
  statement now takes `∃ C, IsMDS C d ∧ C.card = q^k` plus `|Im f| ≥ 2`.
* `#lemma 2#` matches the paper with `u ≠ v` made explicit (the paper's proof uses
  `d(u,v) ≥ d > 0`); its proof plan, including the observation that the *projection
  property* of MDS codes follows from the minimum-distance condition alone, is
  written out in `TODO.md` §3.6.

`#theorem 10#` (`G(C)` connected for perfect codes) and `#corollary 8#` are the
remaining §V-B proofs; `todo`/`proved` columns in `PLAN.md` are unchanged (32
`sorry`s, 12 paper items proved).

## 2026-09-29 (second session) — §V-B: `#lemma 2#` and `#theorem 11#` proved

`sorry` 32 → 30; headline results 28 → 30.

**`#lemma 2#`** (an MDS code has, for every pair of codewords `u ≠ v`, a neighbour
`u'` of `u` with `d(u',v) ≤ d(u,v) − 1`).  The proof is the paper's, with one
shortcut worth remembering: the *projection property* of MDS codes needs no linear
algebra — if two codewords agree on `n − d + 1` coordinates then they are at
distance `≤ d − 1 < d = d_min(C)` and hence equal, so the projection onto any `J`
of size `n − d + 1` is injective on `C`; since `|C| = q^{n−d+1}` it is bijective, by
`Fintype.card_lt_of_injective_not_surjective`.  Choose `J` through
`Finset.exists_subsuperset_card_eq` (a superset of the agreement set, of size
`n − d + 1`), pick `j ∈ J ∩ S` where `u` and `v` differ, and let `u'` be the
codeword agreeing with `u` on `J \ {j}` and with `v` at `j`; then
`d(u,u') ≤ 1 + |Jᶜ| = d` with `u' ≠ u` forces `d(u,u') = d`, and `Sᶜ ∪ {j}` are
agreements of `u'` and `v`, giving `d(u',v) ≤ d(u,v) − 1`.

**`#theorem 11#`** then follows by induction on `d(u,v)`: `#lemma 2#` supplies a
neighbour `u'` of `u` with `d(u',v) < d(u,v)`, and the walk is the edge `u–u'`
followed by the inductive one.

**Two modelling corrections found on the way (`ISSUES.md` §16).**  `minDistGraph C`
has the *ambient word space* as its vertex type (only codewords carry edges), so
`(minDistGraph C).Preconnected` is false for every proper code — it demands that the
isolated non-codewords be reachable.  "`G(C)` is connected" is therefore stated as
codeword reachability `∀ u ∈ C, ∀ v ∈ C, Reachable u v` in `#theorem 8#`/`#theorem 9#`
(hypotheses, re-proved) and `#theorem 10#`/`#theorem 11#` (conclusions).  And
`componentCount` had counted *all* components of the ambient graph (one extra
isolated component per non-codeword, making `#theorem 9#`'s `Q` about `q^n − |C|`
too large); it now counts the components that meet `C`.

**Verification.**  `lake build` green, warning-free apart from the 30 `sorry` stubs;
`consistency_check.ps1 -Strict` green; `axioms_check.ps1` green (30 headline
results).  Next: `#corollary 8#`, then `#theorem 10#`/`#corollary 7#` (perfect
codes).

## 2026-09-30 — the Singleton bound, proved from scratch (preparation for `#corollary 8#`)

`#corollary 8#` needs the Singleton bound `M ≤ q^{n−d+1}`, which the paper quotes
from [17].  Instead of assuming it, it is now proved in `FCC/Balls.lean` as
`card_le_pow_minDist`: two codewords that agree on `n − d_min + 1` coordinates are at
distance `≤ d_min − 1`, hence equal, so the projection onto a coordinate set of that
size is injective on `C` and `|C| ≤ q^{n − d_min + 1}`.  The lemma assumes a
non-empty alphabet (for the empty alphabet and `n = 0` the bound genuinely fails;
the paper's `F_q` is a field).  It is the first *external* result of the paper that
we prove rather than quote — registered as a headline result (31 audited).

To let `FCC/Balls.lean` use it, `minDist_le` (previously in `FCC/Paper.lean`, §II's
internal API) moved to `FCC/Basic.lean`, next to `minDist`: `Balls` is imported
before the paper items, so anything it needs must live below it.

**Next (recorded in `TODO.md` §3.6).**  `#corollary 8#`'s proof: take the FCC `C₂`
attaining `r = optimalRedundancyData f d df` and its codeword set `C'` (image of the
finite message space, so `|C'| = q^k` by injectivity and `d_min(C') ≥ d` by data
protection; `q ≥ 2` since two distinct function values are attained — and `d = 0`
makes the claim trivial).  If `r ≤ d − 2`, Singleton gives `q^k = |C'| ≤
q^{k + r − d + 1}` with exponent `< k`, contradicting `q ≥ 2`.  If `r = d − 1` then
`C'` has length `k + d − 1 = n` and is MDS (`|C'| = q^{n − d + 1}` and
`d_min(C') = d`), so `#theorem 11#` + `#theorem 8#` contradict the FCC's existence.

## 2026-09-30 (second session) — `#corollary 8#` proved; §V-B's MDS half complete

`mds_optimalRedundancyData_ge`: if an MDS `(n, q^k, d)` code exists and `|Im f| ≥ 2`,
then `d ≤ r_f(k : d, d_f)` for `d < d_f`.  The proof follows the plan recorded
above, with two cases on the optimum `r = optimalRedundancyData f d df`:

* `r = d − 1`: the encodings `C₂` attaining the optimum are injective
  (`hammingDist_self` + data protection), so its codeword set `C'` — the image of
  the finite message space — satisfies `|C'| = q^k` and `d ≤ d_min(C')`; the
  Singleton bound on `C'` (length `k + d − 1 = n`, using an MDS pair to get
  `d ≤ n`) then forces equality on both counts, i.e. `C'` *is* MDS, and
  `#theorem 11#` + `#theorem 8#` rule the FCC out;
* `r ≤ d − 2`: Singleton gives `q^k ≤ q^{k + r − d + 1}`, whose exponent is
  `< k`, contradicting `q ≥ 2` (`Nat.pow_lt_pow_right`).

**Lessons.**

1. **Unfold `optimalRedundancyData` on the hypothesis, not with it.**  The
   `dite` in its definition blocks rewriting once the `Prop` side condition is
   around; `rw [optimalRedundancyData, dite_eq_left hne] at hsmall` makes the
   `Nat.find`-form available, whereas `rw [hsmall, Nat.find_spec …]` does not.
2. **`card_le_pow_minDist` needed `1 ≤ q` explicitly.**  With the alphabet as an
   instance-argument `[Nonempty F]` the `n = 0` branch of the proof picks up an
   inconsistency the tactic could not unify; taking `(hq : 1 ≤ Fintype.card F)`
   as an explicit hypothesis keeps the bound honest (it is false for the empty
   alphabet, `n = 0`) and makes both call sites immediate.
3. Registering the result as a headline theorem (32 audited) caught nothing, but
   the axiom audit now covers the whole of §V-B.

**Verification.**  `lake build` green; `consistency_check.ps1 -Strict` green
(78 markers, 73 rows stated, 29 `sorry` statements, all modules imported); the
package root holds only `FCC.lean`.  With §V-B's MDS half (`#lemma 2#`,
`#theorem 11#`, `#corollary 8#`) complete, the remaining piece of §V-B is its
perfect-code half, 3.7 (`#theorem 10#`, `#corollary 7#`), which needs the
packing argument that `IsPerfect` already encodes.

## 2026-09-30 (third session) — `#theorem 10#` proved; the ball/sphere counts done

`isConnected_minDistGraph_of_perfect`: the minimum-distance graph of a perfect
`t`-error-correcting code is connected (as codeword reachability).  The paper's
proof moves from `u` towards `v` while strictly decreasing `d(·,v)`: pick `T` of
`t+1` coordinates where `u` and `v` differ, let `x` follow `v` on `T` and `u`
outside it (`d(x,u) = t+1`), take the codeword `u'` at distance `≤ t` from `x`
(covering), note `d(u,u') = 2t+1` — the minimum distance of a perfect code — so
`u u'` is an edge, and conclude `d(u',v) ≤ d(u,v) − 1` by the paper's
`m_in`/`m_out` count.  Everything it needs is now proved, not quoted:

* **Phase 1a part 3, at last**: the closed forms `card_sphere`
  (`|S(u,i)| = C(n,i)(q−1)^i`, via the bijection "word ↦ (disagreement set,
  values on it)", `card_sphere_fiber`) and `card_ball`
  (`Σ_{i≤t} C(n,i)(q−1)^i`), plus `card_ball_succ`/`card_ball_lt_succ`.  These
  were the oldest open item of the plan (2026-09-14); §VIII's bounds will reuse
  them;
* the **Hamming-bound packing inequality** `card_mul_card_ball_le`
  (`|C| · |B(0,t)| ≤ q^n` when the pairwise distances are `≥ 2t+1`), from
  `pairwiseDisjoint_ball` (triangle inequality) and the ball count;
* the **covering lemma** `exists_mem_ball_of_isPerfect`: the balls of radius `t`
  around a perfect code have total size `q^n`, so they tile the space —
  "the Hamming balls … cover the entire space without overlap", as the paper
  says;
* `minDist_eq_of_isPerfect`: a perfect code with at least two words has
  `d_min = 2t+1` (the paper reads this off silently when it writes "since `u` and
  `u'` both are different codewords of `C`, we have `d(u,u') = 2t+1`).  Proof: a
  word at distance `t+1` from a codeword is covered by a *different* codeword at
  distance `≤ 2t+1 < d_min` if `d_min ≥ 2t+2`;
* `hammingDist_lt_of_close`, the paper's step 5, as the set inclusion
  `D(u',v) ⊆ (D(u',x) ∩ T) ∪ (D(u,v) \ T) ∪ (D(u',x) \ T)` plus cardinalities
  (the paper's `m_in`, `m_out`);
* `exists_hammingDist_eq` (a word at a prescribed distance exists for `q ≥ 2`)
  and `exists_hammingDist_eq_minDist` (the minimum distance is attained).

**Statement review.**  Re-reading §V-B against the PDF found one more statement
defect, recorded in `ISSUES.md` §17: `#corollary 7#` needs `|Im f| ≥ 2`, the
hypothesis `#theorem 8#` carries.  Without it the claim is false — for `k = 0`
(one message) the redundancy is `0` while the corollary asks for `≥ n−k+1 ≥ 2`;
the printed derivation is itself "from Theorems 8 and 10", which needs it.  The
statement now carries it (as `#corollary 8#` and `#theorem 8#` already did).
`#theorem 10#` itself is faithful: "connected" is codeword reachability
(`ISSUES.md` §16), and `IsPerfect`'s two conditions are exactly what the proof
uses.

**Verification.**  `lake build` green (only the 28 `sorry` stubs warn);
`consistency_check.ps1 -Strict` green; `axioms_check.ps1` green with 33 audited
results.  Next: `#corollary 7#`, which needs the Hamming bound plus its strict
monotonicity in the length (both from `card_ball`).

## 2026-09-30 (fourth session) — `#corollary 7#` proved; §V complete

`perfect_optimalRedundancyData_ge`: if `q^{n−k} = Σ_{i≤t} C(n,i)(q−1)^i` with
`t = ⌊(d_d−1)/2⌋`, `|Im f| ≥ 2`, `1 ≤ d_d` and `k ≤ n`, then
`r_f(k : d_d, d_f) ≥ n − k + 1` for `d_f > d_d`.  The paper derives it "from
Theorems 8 and 10"; the formal proof splits on the length `m = k + r` of an FCC
attaining the optimum:

* the packing bound `card_mul_card_ball_le` on `C'` (injective, `q^k` words,
  pairwise distances `≥ d_d ≥ 2t+1`) gives `q^k·A_t(m) ≤ q^m`, i.e.
  `A_t(m) ≤ q^{m−k}` where `A_t(m) = Σ_{i≤t}C(m,i)(q−1)^i`;
* `m = n`: the printed equation turns the bound into equality, so `C'` *is* perfect,
  `#theorem 10#` makes `G(C')` connected and `#theorem 8#` forbids it (the
  hypothesis `d_min(C') = d_d` comes from `minDist_eq_of_isPerfect` plus `d_d ≥ 2t+1`);
* `m < n`: the strict monotonicity `A_t(n) < A_t(m)·q^{n−m}` (proved below) turns
  `A_t(n) = q^{n−k}` into `q^{n−k} < q^{n−k}`;
* `t > m`: the ball is the whole space, so the bound reads `q^k ≤ 1`, i.e. `k = 0`.

**New arithmetic (`FCC/Balls.lean`), the last piece of phase 1a's counting theme.**
The sequence `A_t(m)/q^m` is strictly decreasing in `m` (for `t ≤ m`, `q ≥ 2`),
which is the paper's implicit "the Hamming bound gets tighter as the code gets
longer".  Formalised through the Pascal recurrence
`sum_range_choose_mul_pow_succ` (`A_t(m+1) = A_t(m) + (q−1)A_{t−1}(m)`, from
`Nat.choose_succ_succ` and `Finset.sum_range_succ'`, i.e. a shift of the summation
index), then `sum_range_choose_mul_pow_le_succ`, the strict
`sum_range_choose_mul_pow_lt_succ` (the `t`-th term `C(m,t)(q−1)^t` is a positive
gap) and the iterated form `sum_range_choose_mul_pow_lt_add`.

**Statement review — two more hypotheses (`ISSUES.md` §17).**  The printed corollary
only asks for the equation; proving it showed that the transcription also needs
`1 ≤ d_d` and `k ≤ n`:

* `d_d = 0` is *false*: with `q = 2`, `k = 1`, `d_f = 1` and `f = id` the equation
  gives `n = 1`, so the claim is `r_f ≥ 1`, while the systematic encoding `u ↦ u`
  (redundancy `0`) is an `(f : 0, 1)`-FCC — data protection at distance `0` is
  vacuous and `f u ≠ f v` forces `u ≠ v`;
* `k > n` is consistent with the equation (`t = 0` makes the sum `1` for every `n`),
  and the claim then reduces to `1 ≤ r_f`, a statement about redundancy-`0` encodings
  that the paper's derivation does not cover.  In the paper's picture `n` is a
  perfect-code length holding `q^k` codewords, so `k ≤ n`.

**Verification.**  `lake build` green (only the 27 `sorry` stubs warn);
`consistency_check.ps1 -Strict` green; `axioms_check.ps1` green with 34 audited
results.  §V (both `#theorem 8#`–`#theorem 11#` and `#corollary 7#`/`#corollary 8#`)
is complete; §VI (locally binary/bounded functions, `#lemma 3#`, `#theorem 12#`,
`#lemma 6#`) is next.

## 2026-09-30 (fifth session) — §VI-A: `#lemma 3#` proved

`locallyBinary_redundancy_le`: for a `(d_f−1)`-locally binary function `f` and a
*systematic* code `C` of redundancy `r` and minimum distance `d_d`, the two-step
construction gives an `(f : d_d, d_f)`-FCC of redundancy `r + (d_f − d_d)`.

**The construction, order-free.**  The paper writes `p_u = 1…1` when
`f(u) = max B_f(u, d_f−1)` and `0…0` otherwise.  Our value type has no order, so
the marking uses a fixed global choice function on finite sets
(`pickElem : (s : Finset α) → s.Nonempty → α`), which depends on the *set*
`B_f(u,ρ)` only.  That is all the proof needs: if `d(u,v) ≤ ρ` and `f u ≠ f v` then
both `f u` and `f v` lie in `B_f(u,ρ)`, which has at most two elements by local
binarity, so `B_f(u,ρ) = {f u, f v}`; for the same reason
`B_f(v,ρ) = {f u, f v}`, the two balls are *equal*, hence get the same marked value,
and exactly one of `f u`, `f v` is marked (`ballMark_ne`).  Two parity blocks
therefore differ in every coordinate whenever the marks differ
(`hammingDist_locallyBinaryParity`), and the code realises the second step of
§III-A (`twoStepCode`, `twoStepCode_systematic`, `hammingDist_twoStepCode`).

**Statement corrections (`ISSUES.md` §18).**  Three implicit hypotheses were made
explicit, two of them applied now:

1. `hCsys : IsSystematic C` — the paper says "systematic `[n,k,d_d]` code"; the
   transcription had kept only the minimum distance, but Case 1 of the proof
   (`d(u,v) ≥ d_f`) needs `d(u,v) ≤ d(C u, C v)`, which is *systematicity*
   (`hammingDist_eq_msg_add_red`), not minimum distance;
2. `[Nontrivial F]` (⟺ `1 < q`) — the two parity blocks `1…1`/`0…0` must differ;
   for the paper's field this is automatic;
3. the paper's `max B_f(u,d_f−1)` needs an order on the values — replaced by the
   global choice function, so no order is required (recorded, not a weakening).
   The same review found that `#corollary 9#`–`#corollary 12#` need the *systematic
   form* of their perfect/MDS code, which this repository cannot yet produce (the
   linear-code theory is §VII, phase 3.10); those statements will carry the
   systematic encoder explicitly next session.

**Verification.**  `lake build` green (only the 26 `sorry` stubs warn);
`consistency_check.ps1 -Strict` green; `axioms_check.ps1` green with 35 audited
results.  Next: `#corollary 9#`–`#corollary 12#` (upper and optimality bounds for
locally binary functions), then §VI-B/C.

## 2026-09-30 (sixth session) — §VI-A complete: `#corollary 9#`–`#corollary 12#`

The four corollaries are the paper's perfect/MDS instantiations of `#lemma 3#`:
`#corollary 9#`/`#corollary 11#` bound `r_f` by `n − k + d_f − d_d` at a perfect
(resp. MDS) first-step code, and `#corollary 10#`/`#corollary 12#` add the matching
lower bounds (`#corollary 7#`/`#corollary 8#`) to conclude optimality for
`d_f = d_d + 1`.

**How the paper's "linear" hypothesis is handled (`ISSUES.md` §18).**  The proofs
need the *systematic* form of the perfect/MDS code (its standard generator matrix),
which the repository cannot yet produce — that is linear algebra for §VII.  The
statements therefore carry the paper's code together with its systematic encoder as
a single bundled existential

```text
hcode : ∃ (C : Finset (Word F (k+r))) (E : Word F k → Word F (k+r)),
  IsPerfect C t ∧ C.card = q^k ∧ IsSystematic E ∧ Set.range E = ↑C ∧
  ∀ v w, v ≠ w → d_d ≤ d(E v, E w)      -- (MDS twin: IsMDS C d_d, d_d = r + 1)
```

and the proof `obtain`s `E` and feeds it to `#lemma 3#` — exactly the paper's use of
the systematic form.  When §VII lands, the extra components become derivable and the
bundle can shrink.  The optimality corollaries carry `|Im f| ≥ 2` (their lower half
is `#corollary 7#`/`#corollary 8#`, `ISSUES.md` §17) and `#corollary 10#` also
`1 ≤ d_d`.

**A build note.**  These four declarations (and, in particular, the `Finset`-valued
Hamming-bound sums inside them) need more than Lean's default elaboration budget, so
they are wrapped in `set_option maxHeartbeats 1000000` (restored to the default
afterwards).  The `∃`-bundle also removed the unused-hypothesis warnings the first
transcription produced.

**Verification.**  `lake build` green (only the 22 remaining `sorry` stubs warn);
`consistency_check.ps1 -Strict` green; `axioms_check.ps1` green with 39 audited
results.  §VI-A is complete; §VI-B/C (`#lemma 5#`, `#theorem 12#`, `#lemma 6#`) is
next.

## 2026-09-30 (seventh session) — §VI-B: `#lemma 5#` (`N(4,2t) = 3t`) proved

The paper quotes from [14]: "let `N(λ,2t)` be the minimum length of a **binary**
error-correcting code with `λ` codewords and minimum distance `2t`; then
`N(4,2t) = 3t`".  Statement review first found that the transcription had dropped
the word *binary*: with an arbitrary alphabet the formula is false (for `q = 4`,
`t = 1` the four length-`2` words `(x,−x)` are pairwise at distance `2`, so
`N(4,2) ≤ 2 < 3`).  The statement is now `Nconst (F := F₂) 4 (2 * t) = 3 * t`
(`ISSUES.md` §19) and proved from scratch rather than quoted:

* **upper bound**: the four odd words of `F₂³` — `000, 011, 101, 110` (internal
  `base4`) — are pairwise at distance `≥ 2`; repeating them `t` times with
  `repWord` gives four words of length `3t` at pairwise distance `≥ 2t`
  (`hammingDist_repWord` multiplies the distance by `t`).
* **lower bound**: `three_binary_le` — three binary words at pairwise distance
  `≥ 2t` need length `≥ 3t`.  Double counting: at each coordinate three binary
  letters disagree in `a(3−a) ≤ 2` of the three pairs (a case analysis on the three
  bits), so the sum of the three distances is at most `2n`, while each is at least
  `2t`.  (This is the `M = 4` case of the Plotkin bound of §VIII, in the two-bit
  version; the appendix's general bound comes in phase 3.11.)

**Verification.**  `lake build` green (only the 21 remaining `sorry` stubs warn);
`consistency_check.ps1 -Strict` green; `axioms_check.ps1` green with 40 audited
results.  Next: `#theorem 12#` (locally bounded functions, with the external
`#lemma 4#` colouring as the hypothesis `hcol`) and `#lemma 6#` (Hamming weight).

## 2026-09-30 (eighth session) — §VI-B: `#theorem 12#` (locally bounded) proved

`locallyBounded_redundancy_le`: with the colouring `Col_f` that the external
`#lemma 4#` produces, a systematic first-step code of minimum distance `2t_d+1`
and `t_d ≤ t_f`, the two-step construction with second step
`p_u := c'_{Col_f(u)}` — `c'` an optimal `λ`-word code of minimum distance
`2(t_f − t_d)` — is an `(f : 2t_d+1, 2t_f+1)`-FCC of redundancy
`r + N(λ, 2(t_f − t_d))`.

The optimal second-step code of length *exactly* `N(λ, 2(t_f−t_d))` comes from the
attainment of `N` (`Nat.sInf_mem` after the non-emptiness supplied by
`exists_isDCode_const`), i.e. `N` is used through the phase-3.0 API rather than as
an abstract minimum.  The two cases are the paper's: `d(u,v) ≥ 2t_f+1` is handled by
the *systematicity* of the first step (`d(u,v) ≤ d(C u, C v)`), and `d(u,v) ≤ 2t_f`
by the colouring (`Col_f(u) ≠ Col_f(v)`, so the two second blocks are distinct
codewords of `c'`, at distance `≥ 2(t_f−t_d)`), giving
`(2t_d+1) + 2(t_f−t_d) = 2t_f+1`.

**Statement corrections (`ISSUES.md` §20).**  Three hypotheses the transcription had
left implicit: `hCsys : IsSystematic C` (Case 1), `htd : t_d ≤ t_f` (the standing
`d_d ≤ d_f` of `#definition 6#`, needed for the Case-2 arithmetic) and
`[Nontrivial F]` (`q ≥ 2`, needed because the second-step code of length `N(λ,·)`
is obtained by attainment, which requires two distinct letters).  The boundedness
hypothesis is kept but unused (`_hf`): it is `#lemma 4#` (external) that turns it
into `hcol`.

**Verification.**  `lake build` green (only the 20 remaining `sorry` stubs warn);
`consistency_check.ps1 -Strict` green; `axioms_check.ps1` green with 41 audited
results.  Next: `#lemma 6#` (the Hamming weight function; its statement needs the
paper's *second* bound `N(q^k, 2t_d+1) + N(2t_f+1, 2(t_f−t_d)) − k` added).

## 2026-09-30 (ninth session) — §VI-C: `#lemma 6#`'s statements fixed (proofs next)

`#lemma 6#` gives **two** bounds for the Hamming weight function `f(u) = wt(u)`;
the transcription had only the first and had dropped the word *systematic*.
Statement review (`ISSUES.md` §21) therefore:

* added `hCsys : IsSystematic C` and `htd : t_d ≤ t_f` (and `[Nontrivial F]`) to the
  first bound, exactly as in `#theorem 12#` (§20) — the case
  `|f(u) − f(v)| > 2t_f` needs `d(u,v) ≤ d(C u, C v)`, and Case 1 needs the
  key arithmetic `(2t_d+1) + 2(t_f−t_d) = 2t_f+1`;
* added the paper's second bound as its own declaration
  `hammingWeight_redundancy_le_optimal`:
  `r_f ≤ (N(q^k, 2t_d+1) − k) + N(2t_f+1, 2(t_f−t_d))` — the first step is then an
  *optimal* `q^k`-word code of minimum distance `2t_d+1`, so, as in §18, its
  systematic form will be bundled in the proof.

The proof of the first bound was developed to the last step and is recorded in
`TODO.md`: the second step `p_u := c'_{f(u) mod (2t_f+1)}` (with `c'` of length
exactly `N(2t_f+1, 2(t_f−t_d))`, from the attainment of `N`), the case split on
`|wt u − wt v|` — `wt_le_wt_add_hammingDist` in the large-difference case, and the
new internal residue lemma `mod_ne_of_sub_lt` (from `Nat.ModEq.dvd'`) in the
small-difference case, where `mod (2t_f+1)` makes the two indices different.  What
remains is a `Fin`-index/`let` bookkeeping step (`m := 2*t_f+1` versus
`Fin (2*t_f+1)`) that blocked this session's build.

**Verification.**  `lake build` green (the 21 `sorry` stubs warn — 20 plus the new
second bound); `consistency_check.ps1 -Strict` green; `axioms_check.ps1` green with
41 audited results.

## 2026-09-30 (tenth session) — §VI-C: both bounds of `#lemma 6#` proved; §VI complete

The block that stopped the previous session was pure bookkeeping: the second-step
encoder `p_u := c'_{f(u) mod (2t_f+1)}` mixed a `let m := 2*t_f+1` index with the
literal `Fin (2*t_f+1)`, which `simpa` would not unify.  Routing *every* index
through one local definition
`let idx : Word F k → Fin (2*t_f+1) := fun u => ⟨(wt u) % (2*t_f+1), …⟩` (and the
encoder through `let p := fun u => w (idx u)`) removed the mismatch, and both
bounds now go through:

* `hammingWeight_redundancy_le`: the two-step construction with second step `p`,
  where `c'` has length exactly `N(2t_f+1, 2(t_f−t_d))` (attainment of `N`).  For
  `f(u) ≠ f(v)`: if the residues differ, the blocks are distinct codewords of `c'`
  (distance `≥ 2(t_f−t_d)`) and `d(C u, C v) ≥ 2t_d+1` gives `2t_f+1` in total; if
  the residues agree, the weights differ by at least the modulus `2t_f+1` (the
  internal `mod_ne_of_sub_lt`), so `d(u,v) ≥ |wt u − wt v| ≥ 2t_f+1`
  (`wt_le_wt_add_hammingDist`) and systematicity transfers that to `d(C u, C v)`.
* `hammingWeight_redundancy_le_optimal`: the first bound applied to a systematic
  encoder of the optimal length `N(q^k, 2t_d+1)` (bundled in `hcode`, as in §18).

**Verification.**  `lake build` green (19 `sorry` stubs remain); consistency and
axiom audits green with 43 audited headline results.  §VI is now complete
(`#lemma 3#`, `#corollary 9#`–`#corollary 12#`, `#lemma 5#`, `#theorem 12#`,
`#lemma 6#`); §VII (linear FCCs) and §VIII / appendix (Plotkin and Hamming bounds)
are next.

## 2026-09-30 (eleventh session) — §VIII-B starts: `#corollary 13#` proved

`hamming_bound_fcc_sphere`: an `(f,t)`-FCC of length `n = k + r` forces
`|Im f| · |B(0,t)| ≤ q^n` — the Hamming bound in the form the paper's later
examples use.  The proof only had to assemble existing pieces: choose one message
per attained value of `f` (a `Classical.choose` over the preimages, indexed by the
subtype `{a // a ∈ Im f}` so that no default message is needed), observe that the
corresponding codewords are pairwise at distance `≥ 2t+1` (`IsFCC` plus the fact
that different values give different messages), and apply the packing inequality
`card_mul_card_ball_le` from `FCC/Balls.lean`; systemativity makes the map
`a ↦ C u_a` injective, so the code has exactly `|Im f|` words.

**Verification.**  `lake build` green (18 `sorry` stubs remain); consistency and
axiom audits green with 44 audited headline results.  Next: the union-of-balls
bounds (`#theorem 15#`/`#theorem 16#`, needing the appendix's `#theorem 17#`–`19#`
and `#corollary 14#`) and the Plotkin family (`#lemma 13#`, `#theorem 14#`).

## 2026-10-01 — statement review of the appendix counts (no changes needed)

Before proving them, the four appendix statements were re-read against the PDF,
line by line:

* `#theorem 17#` — `|B(u,t) ∪ B(v,t)| = 2Σ_{i≤t}C(n,i)(q−1)^i − qΣ_{i≤t−1}C(n−1,i)(q−1)^i`
  for `d(u,v) = 1`: matches (our `range (t+1)`/`range t` are `i ≤ t`/`i ≤ t−1`);
* `#lemma 14#` — over `F₂`, `d(u₁,u₂) = 2`:
  `|B(u₁,t) ∩ B(u₂,t)| = 2Σ_{i≤t−1}C(n−1,i)`: matches;
* `#theorem 18#` — three words with pairwise distances `1,1,2`:
  `3Σ_{i≤t}C(n,i) − 6Σ_{i≤t−1}C(n−1,i) + C(n−2,t−1) + 4Σ_{i≤t−2}C(n−2,i)`: matches;
* `#theorem 19#` — over `F₂`, `d(u₁,u₂) = 3`, `t ≥ 2`:
  `2Σ_{i≤t}C(n,i) − 8Σ_{i≤t−3}C(n−3,i) − 6C(n−3,t−2)`: matches.

No statement change was needed this time (a first).  The proofs are the next step;
the `d(u,v) = 1` case of `#theorem 17#` reduces to
`|B(u,t) ∩ B(v,t)| = q·Σ_{i≤t−1}C(n−1,i)(q−1)^i`: writing `c` for the single
differing coordinate and `a` for the number of coordinates `≠ c` where `x`
disagrees with `u`, the two distances are `a + 1` and `a` (when `x c ∈ {u c, v c}`)
or `a + 1` and `a + 1` (when `x c` differs from both), so in every case
`x ∈ B(u,t) ∩ B(v,t) ⟺ a + 1 ≤ t`; hence `x c` is free (`q` choices) and the
other coordinates contribute `Σ_{i≤t−1}C(n−1,i)(q−1)^i`.  Note the characterisation
must be stated as `a + 1 ≤ t` (not `a ≤ t − 1`): for `t = 0` the two differ, which
is exactly why the printed sum is empty there.
## 2026-10-01 — incident: a broken commit slipped through; `card_fiber_erase` re-landed

**What went wrong.**  The fibre count `card_fiber_erase` (written for `#theorem 17#`)
worked in a scratch file, but while landing it I broke one sub-proof (the
disjointness of the two fibres) while removing a style-lint suggestion.  Worse, I
had chained `lake build` and `git commit && git push` in a *single* shell command
with `;`, so the commit and the push ran **even though the build had failed**: the
tip of `main` briefly contained a file that no longer compiled.  This is the same
class of trap as `AGENTS.md` rule 17 (a green build is not evidence the edit is
present) — the lesson here is the mirror image:

> **Run `lake build` as its own command and read its result before committing.**
> Never chain the build and the commit/push in one shell line.

**Repair.**  The bad commit (`ccf963a`) was reverted (`09b3390`) and pushed the
same session, so `main` compiled again immediately.  The lemma was then re-derived
with a lint-free disjointness argument — `insert c S ≠ S` follows from
`c ∉ S` via `Finset.insert_eq_self`, and the fibre equality is closed by a `calc`
along the two defining equations — and re-landed after a *standalone* build and a
standalone `consistency_check.ps1 -Strict` (commit `797d2ea`).

**Result.**  `card_fiber_erase` is in `FCC/Balls.lean`: for `c ∉ S`,
`|{x | D(x,u) \ {c} = S}| = q·(q−1)^{|S|}`.  Together with
`exists_diffSet_eq_singleton` and `mem_ball_inter_iff_of_dist_one` this completes
the counting layer of `#theorem 17#`; what remains is summing over the `i`-subsets
of `{c}ᶜ` (`C(n−1,i)` of them) and the inclusion–exclusion with `card_ball`.

## 2026-10-01 — appendix: `#theorem 17#` proved

`#theorem 17#` (`card_ball_union_dist_one`): for `d(u,v) = 1`,
`|B(u,t) ∪ B(v,t)| = 2Σ_{i≤t}C(n,i)(q−1)^i − qΣ_{i<t}C(n−1,i)(q−1)^i`.
It is three lines once the intersection is known — inclusion–exclusion
(`Finset.card_union_add_card_inter`), two `card_ball`s, and the new internal
`card_ball_inter_dist_one` — and the intersection itself is where the work is:

* `exists_diffSet_eq_singleton` gives the single differing coordinate `c`;
* `mem_ball_inter_iff_of_dist_one` characterises the intersection as
  `{x | |D(x,u) \ {c}| + 1 ≤ t}` (the `+ 1 ≤ t` form, since `≤ t − 1` is wrong at
  `t = 0` — exactly where the printed sum is empty);
* `card_fiber_erase` counts one fibre (`q(q−1)^{|S|}`) and `card_filter_erase_le`
  sums them over the `i`-subsets of `{c}ᶜ`, giving `q·Σ_{i≤s}C(n−1,i)(q−1)^i`;
* finally `t = 0` (empty filter, empty sum) versus `t ≥ 1`
  (`+1 ≤ t ↔ ≤ t−1`, `t−1+1 = t`).

**Lean lessons** (all cost real time, so recorded): `Finset.card_biUnion` needs its
disjointness in the `Set`-coercion form, and the `Disjoint` goals produced by
`Set.PairwiseDisjoint` are unreduced `Function.onFun Disjoint …` terms, so they must
be `change`d to the explicit-filter form before `rw [Finset.disjoint_left]`;
the final arithmetic needs `Finset.card_singleton` in the `rw` chain, after which
that chain closes the goal (a trailing `ring` then fails with "no goals to be
solved").  Verifying each piece in an isolated `example` (and using `trace_state`
to see the real goal) was what finally unblocked the counting.

**Verification.**  Standalone `lake build` green, `consistency_check.ps1 -Strict`
green, `axioms_check.ps1` green with 45 audited results; commit `eba716d`.  17 `sorry`
stubs remain.  Next: `#lemma 14#`, `#theorem 18#`, `#theorem 19#`.

