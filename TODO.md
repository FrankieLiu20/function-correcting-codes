# TODO

Near-term, in the order the project works through `PLAN.md` §4.  Tick items off
in the same commit that does the work.

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
- [ ] 3.12 (part 2, next). `#theorem 15#` and `#theorem 16#` (the same bounds with
      the *union of balls* `minUnionCard`/`minUnionCardDist` instead of a single ball)
      and `#corollary 14#`; they need the appendix's counting of unions of balls
      (`#theorem 17#`–`#theorem 19#`, `#lemma 14#`), which is also the next thing to
      do for `#lemma 13#`/`#theorem 14#` (Plotkin bounds, phase 3.11).
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
- [ ] 3.13 (in progress, 2026-10-01). `#theorem 17#`'s counting layer: three pieces
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
