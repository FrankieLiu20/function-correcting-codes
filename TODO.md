# TODO

Near-term, in the order the project works through `PLAN.md` §4.  Tick items off
in the same commit that does the work.

## Open question (deliberately deferred to the end, 2026-10-01)

- [ ] **Do the externally quoted results have to be *proved* as well?**
      `#lemma 1#` ([10]), `#lemma 4#` ([14]), `#lemma 12#` ([1]), `#corollary 3#`
      ([14]), `#corollary 5#` ([1, App.]) — and the quoted parts of `#lemma 11#` —
      are results of other papers.  Per `AGENTS.md` rule 6 they currently enter the
      statements as **explicit hypotheses** (`hbound`, `hcol`, …), never as `axiom`s.
      Whether the final deliverable should additionally *prove* them (by formalizing
      the quoted statements of [1], [10], [14]) or keep them as hypotheses is left
      open on purpose: the user wants to settle this **at the very end**, after every
      provable item of the paper is done.  The whole final-state question ("should
      `FCC/Paper.lean` end with zero `sorry`?") is to be revisited then too.

## Phase 0 — done

- [x] Create the repository, the toolchain pin and the CI workflow.
- [x] Base layer: `Word`, `wt`, `ball` + `wt_le_wt_add_hammingDist`, `wt_zero`,
      `mem_ball_self` (builds; axiom audit green).
- [x] `PLAN.md` §1.1: the full inventory of the paper's 45 numbered results.
- [x] `Notation.md`: the paper ↔ Lean dictionary and the design decisions.

## Phase 1 — model the paper (one commit per sub-step)

- [x] 1a (part 1). `card_word`, `diffSet`/`hammingDist_eq_card_diffSet`,
      `sphere`, `ball_eq_biUnion_sphere`, `disjoint_sphere`, `ball_mono`,
      `ball_eq_univ_of_le`, `card_ball_univ`.
- [x] 1a (part 2). `decide` regression tests (`FCC/Examples.lean`): the paper's
      Examples 6, 7 and 10 — the CDRM and DRM transcriptions, `N(D) = 3` for
      Example 6, the `[6,3,3]` and `[7,4,3]` minimum distances — plus ball sizes.
- [x] 1a (part 3, done 2026-09-30). The closed form `|B(u,t)| = Σ_{i≤t} C(n,i)(q-1)^i`
      (`card_sphere`/`card_ball`, with `card_sphere_fiber` for one prescribed
      disagreement set); the proof goes through the equivalence
      "word at distance `i` from `u` ↔ (set of `i` changed coordinates, values
      on it)".  Written when §V-B needed it; `#theorem 15#`–`#theorem 19#` and
      `#corollary 13#`/`#corollary 14#` will reuse it.
- [x] 1b. `IsSystematic`, `minDist`; Definition 1 (`IsFCC`,
      `optimalRedundancy`) and Definition 6 (`IsFCCData`).
      Every paper item written from here on goes into `FCC/Paper.lean`, in paper
      order (see `PLAN.md` §2 and `AGENTS.md` rule 2a); helpers stay in the
      `(internal, …)` modules.
- [x] 1c. `drm` (`#definition 2#`), `drmData` (`#definition 11#`), `fDist`/`fdm`
      (`#definition 4#`, `#definition 5#`), `IsDCode`/`N`/`Nconst`
      (`#definition 3#`).  (The `N` API — existence, attainment, monotonicity —
      is phase 3.0.)
- [x] 1d. `cdrm` (`#definition 7#`), `codedFDist` (`#definition 8#`), `cfdm`
      (`#definition 9#`).
- [x] 1e. `minDistGraph` (`#definition 12#`), `functionBall` (`#definition 13#`),
      `IsLocallyBinary` (`#definition 14#`), `IsLocallyBounded` (`#definition 15#`).
- [x] 1f. `IsLinearFCC` (`#definition 16#`), `CosetCode`/`cosetDist`/
      `cosetCodeMinDist` (`#definition 17#`), `kernelSubcode`/`IsLinearFCCKernel`
      (`#definition 18#`).

## Phase 1b — the paper's examples

- [ ] Examples 1, 2, 3, 4, 5 (the `F₂²`/`F₂³` worked examples of §II–§IV): the
      DRM, the FDM, the quoted `D`-codes and the printed matrices, as `decide`
      checks in `FCC/Paper.lean`.  (An `N(D) = k` claim needs the phase-3.0
      `N`-API; until then it is checked as the decidable pair "a `D`-code of
      length `k` exists / none of length `k−1` exists".)
- [ ] Examples 8, 9 (a `D`-code for the 8×8 DRM; the 4-cycle minimum-distance
      graph of `{0000,0011,1100,1111}`).
- [ ] Examples 12, 13, 14 (§VII: the non-linear `f`, the `(f:2,3)`-FCC, the
      `[10,3,4]` construction).
- [ ] Examples 11, 15, 16, 17 — these need the §VIII bounds (`#theorem 14#`–
      `#theorem 16#`) or a value quoted from [1]; do them together with those.

## Phase 2 — statement catalogue

- [x] Every non-`external` row of `PLAN.md` §1.1 as a `sorry`-stubbed statement
      with its paper label in the docstring (73 rows; the four `external` rows
      stay without a declaration and enter as hypotheses, `#remark 1#` has no
      declaration).
- [x] Flip `scripts/consistency_check.ps1 -Strict` on in CI (milestone M2).

## Phase 3 — proofs (`PLAN.md` §4)

- [x] 3.0. The `sInf` API: `N_le_of_isDCode`, `minDist_le`, `fDist_le`,
      `optimalRedundancy_le_of`, `optimalRedundancyData_le_of` and the five
      `…_eq_of` minimality lemmas.
- [x] 3.1/3.2. `#theorem 2#` — the central identity `r_f = N(D_f(t_d,t_f:u₁,…,u_{q^k}))`:
      `hammingDist_eq_msg_add_red`, `isDCode_drmData_of_isFCCData`,
      `N_drmData_le_of_isFCCData`, `optimalRedundancyData_le_of_isDCode`,
      `optimalRedundancyData_eq_N_drmData` (headline result; `ISSUES.md` §11).
- [x] 3.2. `#theorem 3#`: `optimalRedundancyData_ge_N_subset`,
      `two_mul_le_optimalRedundancyData`, `optimalRedundancyData_ge_Nconst_sub`
      (the middle one uses `exists_hammingDist_one_ne`, the paper's unproved
      "some pair at distance 1 changes the value of `f`").
- [x] 3.14. Non-vacuity of the FCC set (`exists_isFCCData`, by repeating the
      message `max d_d d_f` times) — which is what let `#theorem 2#` drop its
      `hex` hypothesis (`ISSUES.md` §11(b)) and makes the optimum attained.
- [x] 3.2. `#corollary 1#` (`optimalRedundancy_ge_drm`,
      `two_mul_le_optimalRedundancy`), `#theorem 1#` (`optimalRedundancy_le_fdm`)
      and `#corollary 2#` (`optimalRedundancy_eq_fdm`) — the §II analogues of
      `#theorem 2#`/`#theorem 3#` without data protection — with the internal
      bricks `exists_isFCC`, `isDCode_drm_of_isFCC` (`hammingDist_eq_msg_add_red`,
      `N_le_of_isDCode`, `fDist_le`, `optimalRedundancy_le_of` moved up so that
      the §II statements can cite them).
- [x] 3.2 (statement fix). Re-index the FDM/CFDM of `#theorem 1#` and
      `#theorem 7#` by `Im(f)` (`ι := Set.range f`) instead of by the ambient
      `α`, which was false for infinite `α` (`ISSUES.md` §12).  `#corollary 2#`
      was not affected.
- [x] 3.3. `#theorem 5#` (`N_drmData_le_N_cdrm_add`, with the paper's systematic
      form of `C` made explicit — `ISSUES.md` §13(a)), `#corollary 4#`
      (`optimalRedundancyData_le_N_cdrm_add`) and `#theorem 6#`
      (`N_cdrm_le_Nconst`), with the internal bricks `cdrm_le` (CDRM entries are
      at most `2(t_f−t_d)`) and `exists_isDCode_const` (a constant matrix has a
      code as soon as the alphabet has two letters).
- [x] 3.3 (statement rework). `two_step_redundancy_bounds` rewritten to the
      paper's form: `twoStepCode`/`IsSecondStep` model §III-A, `twoStep_isFCCData`
      is the scheme's correctness, the lower bound is
      `N(CDRM over the whole message space) + r ≤ schemeRedundancy r r'`, and the
      upper bound is attained by any CFDM `D`-code over `Im f`
      (`ISSUES.md` §13(d)).
- [x] 3.4. `#theorem 4#` (`binary_optimalRedundancyData_ge`): over `F₂`,
      `2 ≤ |Im f| ≤ k` gives `r_f(k,t_d,t_f) ≥ 2t_f + t_d`.
      **Statement checked against the PDF (2026-09-22): it matches as printed**
      (`2 ≤ |Im f| ≤ k`, bound `2t_f + t_d`).  Proof plan, from the paper's
      argument (pp. 4866–4867):
      1. `exists_hammingDist_one_ne` gives `u₁` with a neighbour `u₂` at distance
         one and `f u₂ ≠ f u₁`;
      2. pigeonhole over the `k` neighbours `u₁ + eᵢ`: `f u₁` plus those `k` values
         live in `Im f` of size `≤ k`, so either two neighbours share a value
         (Case 1, with that value `≠ f u₁` since otherwise Case 2 applies) or some
         neighbour has `f(u₁ + eᵢ) = f(u₁)` (Case 2);
      3. in either case the three messages `u₁,u₂,u₃` are at pairwise distances
         `1,1,2`, so the DRM of `#theorem 3#` reads
         `[[0, 2t_f, 2t_f], [2t_f, 0, 2t_d−1], [2t_f, 2t_d−1, 0]]` (Case 1) or
         `[[0, 2t_f, 2t_f−1], [2t_f, 0, 2t_d], [2t_f−1, 2t_d, 0]]` (Case 2);
      4. for three *binary* words of length `r`, `d(p₁,p₂) + d(p₁,p₃) + d(p₂,p₃)
         ≤ 2r` (each coordinate contributes at most `2`), which with the DRM
         entries gives `4t_f + (2t_d−1) ≤ 2r` resp. `4t_f − 1 + 2t_d ≤ 2r`, hence
         `r ≥ 2t_f + t_d`;
      5. conclusion via the FCC attaining `r_f` (`exists_isFCCData`) and
         `isDCode_drmData_of_isFCCData`, so no non-vacuity side condition is
         needed (the same trick as the other lower bounds).
      New internal bricks needed: distances of coordinate-flipped binary words
      (`d(w, flip w i) = 1`, `d(flip w i, flip w j) = 2` for `i ≠ j`) and the
      three-word sum bound `d(p₁,p₂) + d(p₁,p₃) + d(p₂,p₃) ≤ 2 * r`.
      **Done (2026-09-22)**; the bricks live in `FCC/Balls.lean`
      (`flip`, `hammingDist_flip_self`, `hammingDist_flip_flip`,
      `eq_flip_of_hammingDist_eq_one`, `hammingDist_three_le_two_mul`,
      `exists_ne_eq_of_card_lt`).
- [x] 3.5. `#definition 12#` (already stated) with `#theorem 8#` and `#theorem 9#`:
      the minimum-distance graph `G(C)` and the obstruction to being a strict FCC.
      Checking them against §V found that both statements had to require the
      encoding to have **range exactly `C`** (`Set.range enc = ↑C`, the paper's
      `(n, q^k, d)` code) instead of merely `enc u ∈ C` — the latter is false
      (`ISSUES.md` §14 has the counterexample).  Both are now proved, via the
      internal lemma `connectedComponentMk_ne_of_isFCCData` (function values are
      locally constant on `C`, hence constant on connected components).
- [x] 3.6 (part 1). `#lemma 2#` (`exists_mds_neighbor`) and `#theorem 11#`
      (`isConnected_minDistGraph_of_mds`): the MDS case of
      §V-B.  Proved 2026-09-29.  While proving them, two modelling points were
      found and fixed (`ISSUES.md` §16): `minDistGraph`'s vertex type is the
      ambient word space (so "connected" must be stated as codeword reachability,
      not `Preconnected`), and `componentCount` had to be redefined to count the
      components meeting `C`.
- [x] 3.6 (part 2, done 2026-09-30). `#corollary 8#` (`mds_optimalRedundancyData_ge`):
      combines `#theorem 11#` with `#theorem 8#` — an `(f : d, d_f)`-FCC of
      redundancy `r'` has codeword set `C'` with `|C'| = q^k` (injectivity) and
      `d_min(C') ≥ d` (data protection); for `r' = d − 1` Singleton forces
      `d_min(C') = d` and `|C'| = q^{n−d+1}`, so `C'` is MDS and `#theorem 8#`
      forbids it, while for `r' ≤ d − 2` the Singleton bound `card_le_pow_minDist`
      and `q ≥ 2` forbid it directly.  (Statement fixed for `ISSUES.md` §15(b).)

      The proofs of `#lemma 2#` and `#theorem 11#` are done (2026-09-29) and use the
      shortcut recorded here previously: the *projection property* of MDS codes
      follows from the minimum-distance condition alone — two codewords agreeing on
      `n − d + 1` coordinates are at distance `≤ d − 1 < d`, hence equal — so the
      projection onto any `J` of size `n − d + 1` is injective on `C` and, with
      `|C| = q^{n−d+1}`, bijective; then `#theorem 11#` iterates `#lemma 2#` by
      induction on `d(u,v)`.
      **Singleton bound done (2026-09-30)**: `card_le_pow_minDist` in
      `FCC/Balls.lean` (`|C| ≤ q^{n − d_min + 1}`, proved from the projection
      argument; it assumes a non-empty alphabet, as the paper's `F_q` is a field).
      **Proof of `#corollary 8#` as implemented (2026-09-30)**: let `C₂` attain the optimum with
      redundancy `r = optimalRedundancyData f d df` and let `C'` be its codeword set
      (an image of `Word F k`, hence `|C'| = q^k` by injectivity, and
      `d_min(C') ≥ d` by data protection; `q ≥ 2` because two distinct function
      values are attained).  If `r ≤ d − 2`, Singleton gives
      `q^k = |C'| ≤ q^{k + r − d + 1}` with `k + r − d + 1 < k`, contradicting
      `q ≥ 2`.  If `r = d − 1`, then `k + r = k + d − 1 = n` and `C'` is MDS
      (cardinality plus `d_min = d`, the latter from Singleton and `d_min ≥ d`), so
      `#theorem 11#` makes `G(C')` connected and `#theorem 8#` rules the FCC out —
      contradiction again.  Hence `d ≤ optimalRedundancyData f d df`.
- [x] 3.7 (part 1, done 2026-09-30). `#theorem 10#` (`isConnected_minDistGraph_of_perfect`)
      — the balls of radius `t` around the codewords of a perfect code tile the
      space, and the paper's walk (move to the codeword `u'` covering an
      intermediate `x` at distance `t+1` from `u`, which strictly decreases the
      distance to `v`) gives codeword reachability.  The counting it rests on is
      now proved in `FCC/Balls.lean`: the closed forms `card_sphere`/`card_ball`
      (`|S(u,i)| = C(n,i)(q−1)^i`, phase 1a part 3, planned since 2026-09-14),
      the packing bound `card_mul_card_ball_le` / `pairwiseDisjoint_ball` (the
      Hamming bound quoted in §V-B), and the §V-B consequences
      `exists_mem_ball_of_isPerfect` (covering), `minDist_eq_of_isPerfect` (a
      perfect code has `d_min = 2t+1`, cf. `ISSUES.md` §16/§17) and
      `hammingDist_lt_of_close` (the paper's step 5), plus
      `exists_hammingDist_eq` (`FCC/Balls.lean`) and
      `exists_hammingDist_eq_minDist` (`FCC/Basic.lean`) for the intermediate word.
- [x] 3.7 (part 2, done 2026-09-30). `#corollary 7#` (`perfect_optimalRedundancyData_ge`,
      `r_f ≥ n − k + 1` for `n` with `q^{n−k} = Σ_{i≤t}C(n,i)(q−1)^i`,
      `t = ⌊(d_d−1)/2⌋`).  The statement carries three hypotheses the printed
      one-liner does not supply — `|Im f| ≥ 2`, `1 ≤ d_d`, `k ≤ n`
      (`ISSUES.md` §17, each with a counterexample or a justification) — and the
      proof is the paper's: the packing bound `card_mul_card_ball_le` on the optimum
      gives `A_t(k+r) ≤ q^r`; `k + r = n` makes the code perfect (`#theorem 10#` +
      `#theorem 8#` rule the FCC out), `k + r < n` contradicts the strict
      monotonicity `A_t(n) < A_t(k+r)·q^{n−k−r}` (the new lemmas
      `sum_range_choose_mul_pow_le_succ`/`lt_succ`/`lt_add` in `FCC/Balls.lean`),
      and `t > k + r` forces `k = 0`.
- [x] 3.8 (part 1, done 2026-09-30). `#lemma 3#` (`locallyBinary_redundancy_le`) —
      the two-step construction for a `(d_f−1)`-locally binary `f`, with the
      paper's `max B_f(u,d_f−1)` replaced by a global choice function on finite
      sets (`pickElem`/`ballMax`/`ballMark`; no order is needed, `ISSUES.md` §18).
      Two hypotheses were made explicit: `IsSystematic C` (the paper's own word —
      Case 1 of the proof needs `d(u,v) ≤ d(C u, C v)`) and `[Nontrivial F]` (the
      two parity blocks `1…1`/`0…0` must differ).
- [x] 3.8 (part 2, done 2026-09-30). `#corollary 9#`–`#corollary 12#`.  Their
      statements carry the paper's perfect *linear* / MDS code **bundled with its
      systematic form** `E` (an existential `hcode`), which is exactly what the
      paper's linear algebra provides and what `#lemma 3#` consumes; `#corollary 9#`
      and `#corollary 11#` are then one-line consequences of `#lemma 3#`, and the
      optimality corollaries `#corollary 10#`/`#corollary 12#` add the matching
      lower bounds `#corollary 7#`/`#corollary 8#` (with their hypothesis
      `|Im f| ≥ 2`, `ISSUES.md` §17).  `ISSUES.md` §18 records the bundle and the
      `set_option maxHeartbeats 1000000` these four declarations need.
- [x] 3.9 (part 1, done 2026-09-30). `#lemma 5#` (`Nconst_four_two`): the paper's
      `N(4,2t) = 3t` is a *binary* statement and the earlier transcription over an
      arbitrary alphabet was false (`ISSUES.md` §19 — for `q = 4`, `t = 1` a
      length-`2` code with four codewords at distance `2` exists).  It is now
      `Nconst (F := F₂) 4 (2 * t) = 3 * t` and proved from scratch: the four words
      `000, 011, 101, 110` repeated `t` times give the upper bound (`base4`), and
      the Plotkin double counting `three_binary_le` gives the lower bound (three
      binary words at pairwise distance `≥ 2t` need length `≥ 3t`, as at each
      coordinate three binary letters disagree in `a(3−a) ≤ 2` of the three pairs).
- [x] 3.9 (part 2, done 2026-09-30). `#theorem 12#` (`locallyBounded_redundancy_le`):
      for a `(2t_f,λ)`-bounded `f` with the `#lemma 4#` colouring, a *systematic*
      first-step code of minimum distance `2t_d+1` and `t_d ≤ t_f`, the two-step
      construction with second step `u ↦ c'_{Col_f(u)}` (a code of length
      `N(λ,2(t_f−t_d))`, obtained from the attainment of `N`) gives
      `r_f ≤ r + N(λ,2(t_f−t_d))`.  The three hypotheses the printed statement left
      implicit are in `ISSUES.md` §20 (systematicity, `t_d ≤ t_f`, `q ≥ 2`).
      `_hf` (local boundedness) is kept for fidelity — it is `#lemma 4#` (external)
      that turns it into `hcol`.
- [x] 3.9 (part 3, done 2026-09-30). `#lemma 6#` (the Hamming weight function).  The
      *statements* are done (`ISSUES.md` §21): the first bound now carries the
      systematic form and `t_d ≤ t_f` (`hammingWeight_redundancy_le`), and the
      paper's **second** bound
      `r_f ≤ N(q^k,2t_d+1)+N(2t_f+1,2(t_f−t_d))−k` has been added
      (`hammingWeight_redundancy_le_optimal`).  Both are now **proved**: the second
      step `p_u := c'_{f(u) mod (2t_f+1)}` (with `c'` of length exactly
      `N(2t_f+1, 2(t_f−t_d))`, from the attainment of `N`), the case split on the
      residues (`mod_ne_of_sub_lt` plus `wt_le_wt_add_hammingDist` when they agree),
      and the second bound as the first one applied to the bundled systematic
      encoder of the optimal length.  (The `Fin`-index bookkeeping issue was solved
      by routing every index through a single `let idx : Word F k → Fin (2*t_f+1)`.)
- [ ] Upgrade the examples that currently check "a witness exists / none exists"
      (`#example 1#`, `2`, `4`, `5`, `6`, `7`, `9`) to equalities about `N` and
      `minDist` with `N_eq_of`/`minDist_eq_of`, now that phase 3.0 is done.

## Housekeeping

- [ ] Fill in the full name in `CITATION.cff`.
- [ ] Set the repository description/topics on GitHub.
- [ ] Re-read `ONBOARDING.md` §2 and §3: it was written for the guide
      repository and still quotes a few paths from there.
- [x] After the first paper-specific theorem lands: add it to
      `scripts/headline_theorems.txt` **and** `FCC/AxiomCheck.lean` (the two are
      checked against each other).  `#theorem 2#` (`optimalRedundancyData_eq_N_drmData`)
      is the first entry of the `Phase 3.2` block of the manifest.
- [x] Keep `lake build` warning-free apart from the `sorry` stubs: deprecated
      `dif_pos`/`if_pos`/`if_neg`/`Set.mem_setOf_eq` replaced, and the unused
      section variables of the `sInf` API silenced with `omit … in`.
- [x] 3.12 (part 1, done 2026-09-30). `#corollary 13#` (`hamming_bound_fcc_sphere`) —
      the Hamming bound `|Im f| · |B(0,t)| ≤ q^n` for an `(f,t)`-FCC.  Proof: choose
      one message per attained value (`Classical.choose` on the preimages, indexed by
      the subtype `{a // a ∈ Im f}`); their codewords are pairwise at distance `≥ 2t+1`
      by `IsFCC`, so the packing inequality `card_mul_card_ball_le` gives
      `|Im f| · |B(0,t)| ≤ q^n` (the code is systematic, so equal messages have equal
      codewords).
- [x] 3.12 (part 2, **done** 2026-10-01). `#theorem 15#` (`hamming_bound_fcc`),
      `#theorem 16#` (`hamming_bound_fcc_data`) and `#corollary 14#`
      (`hamming_bound_fcc_data_sphere`) — the union-of-balls bounds.  All three are
      the paper's ball-packing argument: over each attained value `a` of `f`, the
      ball-union `U_a` around the codewords of the preimage has at least
      `minUnionCard ℓ n t` words (pick `ℓ` of the preimage's codewords — they form ℓ
      distinct words, and for `#theorem 16#` they are pairwise at distance `≥ d_d` by
      `IsFCCData`), the `U_a` for different values are pairwise disjoint (`IsFCC`/
      `IsFCCData` plus the radius-distance link), and all of them sit in `q^n`.  For
      `#corollary 14#` the radius-`t_d` balls inside one preimage are themselves
      pairwise disjoint, so `|U_a| = |f⁻¹(a)| · |B(0,t_d)|` exactly.  `unionBalls`
      /`minUnionCard`/`minUnionCardDist` were refactored to take a *finset* of words
      (the paper minimises over distinct vectors).  **Statement fix**: the
      transcriptions had left the ball radius free of the distances; they now carry
      `2t_f+1 ≤ d_f` (resp. `2t_d+1 ≤ d_d, d_f`) — `ISSUES.md` §23 has the
      counterexample.
- [ ] 3.10 (in progress). §VII, the linear/algebraic side: `#lemma 7#`–`#lemma 10#`
      and `#theorem 13#`.  Done 2026-10-01:

      * `#lemma 8#` (`cosetDist_eq`) — the two sides are the same set of weights:
        `c₁ ∈ v_i + D`, `c₂ ∈ v_j + D` is `c₁ = x + d`, `c₂ = y`, and
        `c₁ - c₂ = (x - y) + ((c₁ - x) - (c₂ - y))`, so both `sInf`s are
        `sInf {wt ((x-y) + d) | d ∈ D}` (`Set.ext` + `abel`, then `rw [h, cosetDist]`).
        The printed hypothesis `v_i ≠ v_j` is **not needed** (`ISSUES.md` §25): at
        `v_i = v_j` both sides are `0`.
      * `#lemma 9#` (`wt_ge_of_not_mem_kernel`) — `d(C/D_f) ≥ d_f` (`hC.2`), the
        coset of `v` is one the minimum of `cosetCodeMinDist` ranges over (take
        `x = v`, `y = 0`), and `wt v = wt (v + 0)` with `0 ∈ D_f`, so
        `d_f ≤ cosetCodeMinDist ≤ cosetDist (D_f) v ≤ wt v` (three `Nat.sInf_le`).

      * `#lemma 10#` (`image_linear_concat`) — the encoding `u ↦ (C(u), D(f(u)))`
        is `IsLinearMap F`: `catWord = Fin.append` is additive and `F`-linear in
        both arguments (`append_add`/`append_smul`, new in `FCC/Basic.lean`), and
        `Cf`, `Df ∘ f` are linear (`simp only [catWord, map_add, append_add]`).
      * `#theorem 13#` (`isLinearFCC_concat`) — the two distance guarantees: the
        Hamming distance of a concatenated pair splits (`hammingDist_append`,
        `catWord`), so `dd ≤ d(Cu,Cv)` gives the first, and for the second
        `f u ≠ f v` forces `u ≠ v`, `d_f − d_d ≤ d(D(fu),D(fv))` plus
        `d_d ≤ d(Cu,Cv)` gives `d_f ≤ d(cat)` (`omega` with `hadd`).

      * `#lemma 7#` (`kernelSubcode_finrank`) — **statement fix first**
        (`ISSUES.md` §26): as transcribed in phase 2 it had no hypotheses and was
        *false* (take `C = span{(0,1)} ⊂ F_q²`: `msgPart` vanishes on `C`, so
        `dim D_f = 1` while `dim ker f` can be `0`).  It now carries the paper's
        `hC : IsLinearFCC f C dd df` and the "standard form" hypothesis
        `hstd : ∀ u, ∃ c ∈ C, msgPart c = u`.  Proof: `hstd` makes `msgPart` onto,
        and `dim C = k = dim F_q^k` (rank–nullity) makes it injective, so
        `C ≃ₗ F_q^k`; pulling `ker f` back along an equivalence preserves the
        dimension (`Submodule.map_comap_eq_self` + `LinearEquiv.finrank_map_eq`).

      **Done 2026-10-02** — the *dimension* half of `#lemma 10#`/`#theorem 13#`
      ("a linear code of
      dimension `k` and total redundancy `(n−k)+r'`"), which needs the encoders
      `C`, `D` as *injective* linear maps (the Lean statements currently take them
      as plain functions and state linearity/distances only — the gap is recorded
      in `VERIFICATION.md` §"Statement-level caveats").
- [x] 3.11 (**done** 2026-10-02). `#lemma 13#` (`plotkin_bound`) — `#theorem 14#`
      (`plotkin_bound_fcc`) is **done** (2026-10-01, new module
      `FCC/Plotkin.lean`); `#lemma 11#` (quoted from [1]) stays a hypothesis like
      the other external rows.

      `#theorem 14#` followed the plan recorded below, in the paper's own two
      steps, and cost no statement change (the printed statement has no removable
      hypothesis; the `k = 0` and `q = 1` corners are covered by the same
      statement because `q^{k−1}` then truncates to `1` — see `DEVLOG.md`):

      * `plotkin_total_ge`: `sum_erase_hammingDist_ge` is the per-message lower
        bound (`|f⁻¹(f u)| − 1` messages at distance `≥ d_d` from `C u`, the
        remaining `q^k − |f⁻¹(f u)|` at `≥ d_f`), `plotkin_row_le` is the
        arithmetic step replacing `|f⁻¹(f u)|` by `L = maxPreimageCard f`, and the
        sum over the `q^k` messages gives `q^k((L−1)d_d+(q^k−L)d_f) ≤ Σ_{x≠y} d(x,y)`;
      * `plotkin_total_le`: `plotkin_total_eq_sum_card_filter` writes the total
        pairwise distance as `Σ_j #(pairs of *messages* whose codewords differ in
        coordinate `j`)`, then `card_ne_pairs_mul_le` (Cauchy–Schwarz, generalised
        from `Fin M` to an arbitrary finite index type because the messages are
        indexed by `Word F k`) gives `q·Σ_{x≠y} d(x,y) ≤ (k+r)·q^{2k}(q−1)`;
      * `plotkin_bound_fcc_aux` compares the two, cancels the positive `q^k` (then
        `q`, using `q^k = q^{k−1}·q`) and finishes over `ℚ`; `FCC/Paper.lean`
        instantiates it at the **attained** value of `optimalRedundancyData`
        (`exists_isFCCData` + `Nat.find_spec`, the same idiom as `#theorem 2#`).

      The two bricks are in `FCC/Balls.lean` (2026-10-01, commits `1d5af92`,
      `f756e7f`): `sum_sq_le_card_mul_sum_sq` (`(Σn_ε)² ≤ q·Σn_ε²`, Cauchy–Schwarz
      from the doubled sum-of-squares identity) and `card_ne_pairs_mul_le`
      (`q·#{(i,j) : symbols differ} ≤ M²(q−1)`, the per-coordinate estimate).

      **3.11 (part 2, in progress).**  For `#lemma 13#` the sharp constant needs the
      balanced-distribution value `a⌈M/q⌉(M−⌈M/q⌉) + (q−a)⌊M/q⌋(M−⌊M/q⌋)`
      (`a = M % q`), i.e. the exact maximisation of `Σ_ε n_ε(M−n_ε)` over
      distributions; the weak `M²(q−1)/q` form above is not enough there.  The
      arithmetic heart landed 2026-10-01 as **`card_mul_sum_sq_ge`**
      (`FCC/Balls.lean`): for `M = Σ_ε n_ε` and `a = M % q`,
      `q·Σ_ε n_ε² ≥ M² + a(q−a)` — i.e. `Σ n_ε²` is minimal at the balanced
      distribution, with equality for `a` symbols `⌈M/q⌉` times and the rest
      `⌊M/q⌋` times.  The proof is short: with `t = M / q` the pointwise
      inequality `(n−t)(n−t−1) ≥ 0` (integrality!) says `n(2t+1) ≤ n² + t(t+1)`;
      summing and multiplying by `q` turns `(2t+1)M − q·t(t+1)` into `M² + a(q−a)`.

      Remaining for `#lemma 13#`: (a) the sharp per-coordinate pair count
      `q·#{(i,j) : symbols differ} ≤ M²(q−1) − a(q−a)` (the analogue of
      `card_ne_pairs_mul_le` with the correction term — `#ne = M² − Σn_ε²`,
      `M²(q−1) = qM² − M²`, then `Nat.sub_le_sub_left` against
      `card_mul_sum_sq_ge`); (b) the same double count as in `#theorem 14#` but
      over *unordered* pairs (the paper's `Σ_{i<j}`), giving
      `2q·Σ_{i<j}[D]_{i,j} ≤ r·(M²(q−1) − a(q−a))` for every `D`-code of length
      `r`; (c) the `ℚ`/`sInf` finish: every valid `r` satisfies the bound, and the
      set of valid lengths is nonempty (so `sInf` is a valid lower bound — the
      `A = M²(q−1) − a(q−a) = 0` cases, i.e. `M ≤ 1` or `q = 1`, are trivial).

      **Landed so far** (2026-10-01): `card_mul_sum_sq_ge` (the balanced-squared
      brick), `card_ne_pairs_mul_le_sharp` (the sharp per-coordinate count),
      `sum_erase_ite_eq_card_filter_gen`/`total_pair_eq_sum_coord` (the double
      count for an arbitrary index type — a `D`-code is indexed by `Fin M`), and
      `sum_lt_eq_sum_lt_i` (the paper's `Σ_{i<j}` as a sum of rows).

      **Next, concretely**: `two_mul_sum_lt_eq_sum_erase_for_linearOrder`
      (the factor `2` of the paper's constant): for symmetric `f`, prove
      `2 * Σ_{i<j} f i j = Σ_i Σ_{j∈erase i} f i j`.  The cheap route is *not* to
      split each row by `j < i` (which needs `Finset.sum_comm'` plus two
      filter-`ext`s); write both sides as iterated `ite` sums instead:
      `Σ_{i<j} f = Σ_i Σ_j if i < j then f i j else 0`
      (`Finset.sum_filter` + `sum_product`), and
      `Σ_i Σ_{j∈erase i} f = Σ_i Σ_j if i = j then 0 else f i j`
      (`Finset.erase_eq_filter` if available, else `Finset.sum_erase_add` with
      `Σ_j f i j - f i i`), then pull the `2` inside (`Finset.mul_sum`) and close
      pointwise per `(i,j)` with `rcases lt_trichotomy i j` (for `i ≠ j` exactly
      one of `i < j`, `j < i` holds and both terms are `f i j`; the `j < i` half is
      reindexed onto the `i < j` half by `Finset.sum_comm` plus `hsymm`).
      Then `plotkin_total_le_sharp` (the `q · Σ_i Σ_{j≠i} hammingDist ≤ r·A` bound,
      from `total_pair_eq_sum_coord` + `card_ne_pairs_mul_le_sharp`), and the
      `ℚ`/`sInf` finish in `FCC/Paper.lean` (`plotkin_bound`).

      **Landed 2026-10-02** (commit `1101cb8`): the factor-`2` bridge
      (`two_mul_sum_lt_eq_sum_filter_ne`, plus `sum_erase_eq_sum_filter_ne` to move
      between the row-sum and product-filter forms of the ordered-pair sum) and
      `plotkin_total_le_sharp`: `q · 2 · Σ_{i<j} d(p_i,p_j) ≤ n · (M²(q−1) − a(q−a))`
      for *any* family of words `p : ι → Word F n`.  The bridge works by *set
      algebra* on finsets (which is what finally worked): the pairs `i ≠ j` split
      into `i < j` and `j < i` (`Finset.filter_or`), and swapping the two
      coordinates is `Finset.sum_image` along `(a,b) ↦ (b,a)` — no `ite`, hence no
      `split_ifs`/`ite_eq_*` pitfalls.

      **Only the `ℚ`/`sInf` finish in `FCC/Paper.lean` (`plotkin_bound`) is left.**
      Two observations from thinking it through, which the next attempt should use:

      * **Avoid the truncated subtraction.**  The clean ℕ form of the sharp
        per-coordinate estimate is `q·(M² − Σn_ε²) + a(q−a) ≤ q·M²` … written in
        the form that needs no `ℕ`-subtraction on the right,
        `q·#(differing pairs) + a(q−a) ≤ M²(q−1) + a(q−a)`-style; then casting to
        `ℚ` never meets `Nat.cast_sub`.  (Equivalently: reprove the per-coordinate
        brick as `q*#ne + a*(q−a) ≤ M²*(q−1)`, a pure addition inequality.)
      * The statement's denominator `A_ℚ := M²(q−1) − a(q−a)` (a `ℚ` subtraction)
        is `≥ 0` and vanishes only when `M ≤ 1` or `q = 1`, cases in which also
        `Σ_{i<j} d = 0`; so the two cases `A_ℚ = 0` and `A_ℚ > 0` are enough, and in
        the second the `ℕ`-truncation is exact (`Nat.cast_sub` applies).
      * For the `sInf`: use the repo's `Nat.sInf_def hne` + `Nat.find_spec hne`
        idiom (there is **no** `Nat.le_sInf`, see the comment above `N_eq_of`), with
        nonemptiness `hne : ∃ n, IsDCode D n` from `exists_isDCode_const` applied to
        the constant matrix `Σ_{i,j} D i j` (needs `2 ≤ q`, i.e. the `A_ℚ > 0`
        case).

      **Attempted 2026-10-01 and rolled back** (repo left green at `7275bb5`):
      the `ite` route above was implemented once and hit these walls, which the
      next attempt should go around rather than rediscover:

      * `Finset.sum_congr rfl (fun j hj => …)` used *as a rewrite rule* leaves a
        metavariable for the summand (`f i j = ?m j`), and `split_ifs` then fails
        with "no if-then-else conditions to split".  State the desired equality as
        an explicit `have : ∑ … = ∑ …` and rewrite with that.
      * `if_pos`/`if_neg` are deprecated in this pin (use the `ite_eq_left`/
        `ite_eq_right` pair, cf. `AGENTS.md` rule 18), and `split_ifs with h` names
        a hypothesis only in the branches that *have* one — `intro`-style
        restructuring is more predictable.
      * The cleanest way to see `∑_{j ∈ univ.erase i} f i j = ∑ j, if i = j then 0
        else f i j` seems to be `Finset.sum_subset (Finset.erase_subset i univ)`
        with the vanishing condition `j = i → … = 0` proved by `subst` + `simp`
        (the "on the subset" direction then needs the per-`j` rewrite above, where
        `j ∈ erase i` gives `j ≠ i`).
      * The pointwise identity `if i = j then 0 else f i j = (if i < j then f i j
        else 0) + (if j < i then f i j else 0)` is best proved by
        `intro i j; split_ifs <;> omega` (no hypothesis naming needed).
- [x] Statement review of the appendix counts (2026-10-01): `#theorem 17#`,
      `#lemma 14#`, `#theorem 18#`, `#theorem 19#` were re-read against the PDF and
      match verbatim (`DEVLOG.md`); no change needed.  Their proofs are the next
      step, starting with `#theorem 17#`: `exists_diffSet_eq_singleton` (the unique
      differing coordinate of two words at distance one) is already in
      `FCC/Balls.lean`; next come the characterisation
      `x ∈ B(u,t) ∩ B(v,t) ⟺ |D(x,u) \ {c}| + 1 ≤ t` (stated with `+1 ≤ t`, which
      also covers `t = 0` correctly — see `DEVLOG.md`) and the count
      `q·Σ_{i≤t−1}C(n−1,i)(q−1)^i` by summing `card_sphere_fiber` over the
      `i`-subsets of `{c}ᶜ`, then inclusion–exclusion with `card_ball`.
- [x] 3.13 (part 1, done 2026-10-01). `#theorem 17#` (`card_ball_union_dist_one`) —
      `|B(u,t) ∪ B(v,t)| = 2Σ_{i≤t}C(n,i)(q−1)^i − qΣ_{i<t}C(n−1,i)(q−1)^i` for
      `d(u,v) = 1`, from `Finset.card_union_add_card_inter` and two `card_ball`s,
      the intersection coming from the internal `card_ball_inter_dist_one`
      (`mem_ball_inter_iff_of_dist_one` + `card_filter_erase_le`, with `t = 0` the
      empty filter against the empty sum).  Lean lessons: `Finset.card_biUnion`
      wants the disjointness in the `Set`-coercion form and the `Disjoint` goals
      must be `change`d to the explicit-filter form before `rw
      [Finset.disjoint_left]`; `Finset.card_singleton` must be in the final `rw`
      chain (which then closes the goal, so no trailing `ring`).
- [x] 3.13 (part 2, **done** 2026-10-01). `#lemma 14#` (`card_ball_inter_dist_two`) —
      `F₂`, `d(u₁,u₂) = 2`: `|B(u₁,t) ∩ B(u₂,t)| = 2Σ_{i<t}C(n−1,i)`.  Statement
      re-read against the PDF and matching verbatim (the paper's proof normalises to
      `0` and `(1,1,0,…,0)`; the formalisation does not need the normalisation, since
      the two special coordinates are found by `exists_diffSet_eq_pair`).

      Proof (the plan of part 2 was executed as written, one layer deeper): `a` is
      `|D(x,u) \ {c₁,c₂}|` and the pair `(d(x,u), d(x,v))` is `(a+k, a+2−k)` with
      `k = [c₁ ∈ D(x,u)] + [c₂ ∈ D(x,u)] ∈ {0,1,2}`; hence `x` is in both balls iff
      `a + (if c₁ and c₂ both disagree or both agree then 2 else 1) ≤ t`
      (`mem_ball_inter_iff_dist_two`).  Over `F₂` each disagreement set `D ⊆ Fin n`
      is realised by *exactly one* word (`card_sphere_fiber` at `q = 2`), so the
      intersection is counted by its admissible disagreement sets
      (`card_allowed_dist_two`): splitting on `c₁, c₂ ∈ D` gives two copies of
      `|S| + 1 ≤ t` and two of `|S| + 2 ≤ t` as `S` runs over the subsets of
      `{c₁,c₂}ᶜ`, i.e. `2Σ_{i<t}C(n−2,i) + 2Σ_{i<t−1}C(n−2,i)` by
      `card_powerset_filter_add_le`, and summed Pascal (`sum_range_choose_pred`)
      turns this into the printed `2Σ_{i<t}C(n−1,i)`.  New internal helpers in
      `FCC/Balls.lean`: `card_erase_erase_add`, `zmod2_ne_iff_eq`,
      `exists_diffSet_eq_pair`, `mem_ball_inter_iff_dist_two`,
      `card_powerset_filter_add_le`, `sum_range_choose_succ`, `sum_range_choose_pred`,
      `card_allowed_dist_two`.

      Three Lean lessons (each cost real time): `rw` matches the *beta-unreduced*
      form of a hypothesis (`(fun S => insert c₁ S) S`), so an injectivity
      hypothesis produced by `Finset.card_image_of_injOn` must be re-stated with an
      explicit type before it can rewrite anything; the robust way to use an
      equality of `insert`-sets is `congrArg (T ↦ T.erase c₁)` followed by
      `Finset.erase_insert`; and `by decide` proves the two-element facts about
      `ZMod 2` (`x ≠ a ↔ x = b` for `a ≠ b`), because the type is finite so the
      quantified proposition is decidable.
- [x] 3.13 (part 3, **done** 2026-10-01; the plan below was carried out as written).
      `#theorem 18#` (three balls at pairwise
      distances `1,1,2`) and `#theorem 19#` (`F₂`, distance `3`, `t ≥ 2`).
      **Statement fix first**: the printed `#theorem 18#` is false at `t = 0` in
      Lean's `ℕ` (`C(n−2,t−1)` becomes `C(n−2,0) = 1` instead of the paper's
      `C(n−2,−1) = 0`; at `n = 2` the two sides are `3` and `4`), so it now carries
      `(ht : 1 ≤ t)` — `ISSUES.md` §22, the same convention as the printed `t ≥ 2`
      of `#theorem 19#`.  **Machinery in place** (all proved, `FCC/Balls.lean`):
      `card_union_three_add` (subtraction-free 3-set inclusion–exclusion:
      `|A∪B∪C| + |A∩B| + |A∩C| + |B∩C| = |A| + |B| + |C| + |A∩B∩C|`, so no
      `ℕ`-truncation can arise in the paper's inclusion–exclusion step),
      `zmod2_eq_add_one_of_ne`, `zmod2_add_one_ne`, `diffSet_surjective`,
      `diffSet_injective`, `card_filter_diffSet` (over `F₂` a word and its
      disagreement set with `u` determine each other, so counting words reduces to
      counting sets), `erase_erase_eq_sdiff_pair`, and `card_filter_inter_eq_card`
      (the fibre `D ∩ T = P` is in bijection with the subsets of `Tᶜ` via
      `S ↦ S ∪ P`, preserving `|D \ T|`).

      **Plan for `#theorem 18#`** (following the paper): prove the triple
      intersection `|B(u₁,t) ∩ B(u₂,t) ∩ B(u₃,t)| = #₁ + 3#₂` with
      `#₁ = Σ_{i<t}C(n−2,i)` (the pattern "agree at both special coordinates",
      cost `1`) and `#₂ = Σ_{i<t−1}C(n−2,i)` (the other three patterns, cost `2`),
      i.e. `C(n−2,t−1) + 4Σ_{i<t−1}C(n−2,i)` for `t ≥ 1`.  Its coordinate model is
      `mem_ball_inter_iff_dist_two` with `c₁ ∈ D ↔ c₂ ∈ D` replaced by
      `c₁ ∈ D ∨ c₂ ∈ D` (cost `2` unless both special coordinates agree), and the
      count splits into "`D ∩ {c₁,c₂} = ∅`" — where the filter *is* the powerset
      filter, card `Σ_{i<t}C(n−2,i)` — plus the three non-empty patterns, each of
      card `Σ_{i<t−1}C(n−2,i)` by `card_filter_inter_eq_card`.  Then
      `card_union_three_add` + the two `card_ball_inter_dist_one`s +
      `card_ball_inter_dist_two` + `card_ball`, and the arithmetic identities
      `Σ_{i≤t}C(n,i) = Σ_{i≤t}C(n−1,i) + Σ_{i≤t−1}C(n−1,i)` (`sum_range_choose_succ`)
      and `C(n,t) = C(n−1,t−1) + C(n−1,t)` (`Nat.choose_succ_succ`) close it:
      `3Σ_{i≤t}C(n,i) − 6Σ_{i≤t−1}C(n−1,i) = 3C(n−1,t)`, and then
      `3C(n−1,t) + C(n−2,t−1) + 4Σ_{i≤t−2}C(n−2,i) = 4Σ_{i≤t−1}C(n−2,i) + 3C(n−2,t)`.
      `#theorem 19#` is the same pattern with three special coordinates (8 patterns:
      `#₁` for six of them, `#₂` for `000`/`111`) and the pairwise intersection
      replaced by `card_ball_inter_dist_three`.  These unlock
      `#theorem 15#`/`#theorem 16#`/`#corollary 14#`.
- [x] 3.13 (part 4, **done** 2026-10-01). `#theorem 19#` (`card_ball_union_dist_three`): two balls at
      distance `3`, `t ≥ 2` (the hypothesis is the paper's own, so `t − 2` is
      exact).  The paper computes the *intersection* first: with three special
      coordinates its table gives `6#₁ + 2#₂`, where `#₁ = Σ_{i<t−1}C(n−3,i)` covers
      the six patterns with one or two of the special coordinates in `D` and
      `#₂ = Σ_{i<t−2}C(n−3,i)` covers `000` and `111`, i.e.
      `8Σ_{i<t−2}C(n−3,i) + 6C(n−3,t−2)`; then the union is
      `|B(u,t)| + |B(v,t)| − |B(u,t) ∩ B(v,t)|` with `card_ball`.  What is needed
      is the three-coordinate analogue of the counting pair
      `card_filter_inter_eq_card`/`card_allowed_pair_three`: partition the
      admissible sets by `D ∩ T` with `T = {c₁,c₂,c₃}`.  The paper's table costs
      `3` when `D ∩ T` is `∅` or `T` (the patterns `000`, `111`) and `2` on the
      other six patterns, so the intersection is
      `2Σ_{i<t−2}C(n−3,i) + 6Σ_{i<t−1}C(n−3,i)` — the six cost-`2` patterns are
      counted by `#(T.powerset.filter (· ≠ ∅)) − 1 = 7 − 1`, with the fibres of
      `S ↦ S ∪ P` from `card_filter_inter_eq_card`, and the union is the two-set
      identity `|A| + |B| − |A∩B|` with `card_ball`.  Everything else
      (`diffSet_surjective`/`injective`, `card_filter_diffSet`, the `zmod2_*`
      facts) is already in place.
- [x] 3.13 (old note, superseded — finished 2026-10-01). `#theorem 17#`'s counting layer: three pieces
      are in `FCC/Balls.lean` (`exists_diffSet_eq_singleton`,
      `mem_ball_inter_iff_of_dist_one`, `card_fiber_erase`).  The next piece is
      `card_filter_erase_le`:
      `|{x | |D(x,u) \ {c}| ≤ s}| = q · Σ_{i≤s} C(n−1,i)(q−1)^i`, whose proof was
      developed but not finished — the split by the value of the invariant and the
      split of each fibre over `({c}ᶜ).powersetCard i` both work; the last step
      (`rw [hpartition, Finset.card_biUnion hdisj1]` and the analogous step inside)
      still leaves a goal in the scratch session, most likely because
      `Finset.card_biUnion` wants the pairwise disjointness in the `Set`-coercion
      form (`(↑s).PairwiseDisjoint t`, which `Set.PairwiseDisjoint (fun i => i ∈ s) t`
      is only defeq to).  After that: the `t ≥ 1` case of the intersection
      (`+1 ≤ t` ↔ `≤ t−1`), the `t = 0` case (both sides are `0`), and finally
      `#theorem 17#` by inclusion–exclusion with `card_ball`.

## `#lemma 13#` — the final `ℚ`/`sInf` step: what did *not* work (2026-10-02)

**Scratch workspace (outside the repo, so failures cannot redden the build):**
`C:\Users\lenovo\.codex\visualizations\2026\10\01\01a0f759-fefa-7482-b569-5892c3ba79e6\scratch13b.lean`
(checked with `lake env lean <path>` from the repo root).  It currently contains a
*verified* `plotkin_total_le_rat`-style lemma and a nearly complete
`plotkin_bound_scratch`; the remaining compile errors there are mechanical
(`Finset.single_le_sum` needs its summand named for the outer sum; `rw [N,
Nat.sInf_def hne]` must be an `exact`/`have` because `IsDCode` is a `def` and does not
match the unfolded pattern syntactically; `ring` after `simp only` may have no goals
left; `plotkin_const_cast` needs `omit [DecidableEq F] in`).  `plotkin_total_le_rat`
itself is already in `FCC/Plotkin.lean` (commit `fe9f221`).

Status of the scratch file at the end of 2026-10-02: the two `Finset.single_le_sum`
steps and the `Nat.sInf_def` step are fixed; still failing: (i) the
`hXY : a(q−a) < M²(q−1)` derivation (cast the ℚ inequality `Aq > 0` down to ℕ —
`plotkin_const_cast` + `exact_mod_cast` needs the two sides written in the *same*
cast shape, cf. the pitfall above), and (ii) `plotkin_total_le_rat`'s `hle` is stated
with `Fintype.card ι`, so it must be fed with `simpa [Fintype.card_fin] using hle`
when `ι = Fin M`.

Two attempts at the `ℚ` bridging lemma (`plotkin_total_le_rat`, to be used by
`plotkin_bound`) were rolled back; the repo is green at `b7434f4`.  Learned:

* The lemma **must** carry `hle : (M % q)*(q − M % q) ≤ M²(q−1)`: without it the
  statement is false (when the `ℕ` subtraction truncates, the `ℕ` bound
  `plotkin_total_le_sharp` says nothing and the `ℚ` right-hand side is negative).
  The `¬ hle` case belongs to `plotkin_bound` itself, where the constant is negative
  and the inequality is trivial.
* The cast mismatch is the whole difficulty: the paper's constant is written
  *pushed* (`(M:ℚ)^2 * ((q:ℚ)−1) − (a:ℚ) * ((q:ℚ)−(a:ℚ))`), while
  `plotkin_total_le_sharp` gives `↑(M²(q−1) − a(q−a))`, an atom that `nlinarith`
  cannot relate to `(↑M)^2 * (↑q − 1)`.  `push_cast at h` alone leaves `↑(X − Y)`
  untouched.  Instead: state an explicit `have` rewriting the *goal's* denominator
  into the `↑X − ↑Y` form (`rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hq1,
  Nat.cast_mul, Nat.cast_sub hale]` + `norm_num`), rewrite the goal with it, then
  `rw [Nat.cast_mul, Nat.cast_sub hle] at h` on the cast `ℕ` bound and close with
  `nlinarith`.
* `Nat.sub_add_le` does not exist in this pin (and `(X − Y) + Y ≤ X` is false
  without `Y ≤ X`); use `Nat.cast_sub`/`Nat.sub_add_cancel` with the explicit
  hypothesis rather than trying to get it from `omega`.

