# Formal Proof Plan

**Paper.**

> C. Rajput, B. S. Rajan, R. Freij-Hollanti, C. Hollanti,
> "Function-Correcting Codes With Data Protection",
> *IEEE Trans. Inform. Theory* **72**(7), pp. 4860–4880, July 2026.
> DOI 10.1109/TIT.2026.3692458. 21 pages, Open Access (CC BY 4.0).

Local copy: `paper/Function-Correcting_Codes_With_Data_Protection_IEEE_TIT_2026_OA.pdf`
(git-ignored, kept locally because of publisher distribution habits; the paper is
CC BY 4.0).

**Goal.** A machine-checked Lean 4 + mathlib formalization of the paper's
definitions and numbered results, following the layout and workflow of
Shenghao Yang's `n4code_lean_dev` (see `README.md`, `ONBOARDING.md`).

**Toolchain.** Lean `leanprover/lean4:v4.34.0-rc2` (`lean-toolchain`), mathlib
pinned in `lakefile.toml` and `lake-manifest.json` (rev `70f3f134…`).

**Status.** Phase 0 (infrastructure + paper-independent base layer) is complete
and builds.  No paper-specific definition or statement is written yet: that is
phases 1–2 below, done one step per session.

---

## 1. Scope

### 1.1 Statement inventory

One row per numbered item of the paper.  "Lean name" is the declaration that
owns the statement (proposed; names may be refined while writing).  Status:
`todo` (not started) · `stated` (`sorry` stub in the library) · `proved` ·
`external` (a result quoted from another paper — *not* formalized here, and
therefore used as an explicit hypothesis by whatever needs it).

Labels are the paper's own numbers, written as `#definition N#`,
`#theorem N#`, `#lemma N#`, `#corollary N#`, `#example N#` and `#remark N#`
(one counter, so `#theorem 10#` is Theorem 10 and `#lemma 10#` is Lemma 10).
The convention — and what the checker does with it — is in `Notation.md` §1.

#### §II Preliminaries (the [1] layer, generalised later)

| Label | § | Statement | Lean name | Status |
| --- | --- | --- | --- | --- |
| `#definition 1#` | II | `(f,t)`-FCC: systematic `C : F_q^k → F_q^{k+r}` with `d(C(u₁),C(u₂)) ≥ 2t+1` whenever `f(u₁) ≠ f(u₂)`; `r_f(k,t)` = optimal redundancy | `IsFCC`, `optimalRedundancy` | stated |
| `#definition 2#` | II | Distance requirement matrix `D_f(t,u₁,…,u_M)`, entries `max(2t+1−d(uᵢ,uⱼ),0)` if `f(uᵢ) ≠ f(uⱼ)`, else `0` | `drm` | stated |
| `#definition 3#` | II | Irregular-distance code (`D`-code) for `D ∈ ℕ^{M×M}`; `N(D)` = minimal length; `N(M,D)` for a constant matrix | `IsDCode`, `N`, `Nconst` | stated |
| `#lemma 1#` | II | `N(M,D) ≤ 2(D−2)/(1−2/q)·ln D/D` for `D ≥ 10`, `M ≤ D²` | — | external ([10, Lem. 2]) |
| `#definition 4#` | II | `d(fᵢ,fⱼ) = min{d(u₁,u₂) | f(u₁)=fᵢ, f(u₂)=fⱼ}` | `fDist` | stated |
| `#definition 5#` | II | Function distance matrix (FDM), entries `max(2t+1−d(fᵢ,fⱼ),0)` off the diagonal | `fdm` | stated |
| `#corollary 1#` | II | `r_f(k,t) ≥ N(D_f(t,u₁,…,u_m))` for any subset; and `≥ 2t` when `|Im f| ≥ 2` | `optimalRedundancy_ge_drm`, `two_mul_le_optimalRedundancy` | todo |
| `#theorem 1#` | II | `r_f(k,t) ≤ N(FDM)` | `optimalRedundancy_le_fdm` | todo |
| `#corollary 2#` | II | equality in `#theorem 1#` when a representative set realises the FDM | `optimalRedundancy_eq_fdm` | todo |
| `#corollary 3#` | II | `r_wt(k,t) ≥ (10t³+30t²+20t+12)/(3t²+12t+12)` | — | external ([1, Cor. 3]) |

#### §III A construction procedure for FCCs with data protection

| Label | § | Statement | Lean name | Status |
| --- | --- | --- | --- | --- |
| `#definition 6#` | III | `(f:d_d,d_f)`-FCC: `d(C(u₁),C(u₂)) ≥ d_d` for `u₁ ≠ u₂` **and** `≥ d_f` for `f(u₁) ≠ f(u₂)`, with `d_d ≤ d_f` | `IsFCCData` | stated |
| `#definition 7#` | III | Coded DRM `D_{C,f}(t_f:u₁,…,u_M)`: like `#definition 2#` with `d(c_{uᵢ},c_{uⱼ})` | `cdrm` | stated |
| `#definition 8#` | III | coded distance `d_C(fᵢ,fⱼ)` | `codedFDist` | stated |
| `#definition 9#` | III | Coded FDM (CFDM) | `cfdm` | stated |
| — | III-A | Two-step construction: `[n,k,d_d]` code `C`, then an FCC on the codewords `c_u = uG`, giving `C_f(u) = C'_f(c_u)` by `r_s = n−k+r'` | (proved via `#theorem 5#`, `#corollary 4#` and the concrete constructions of §VI–VII) | todo |

#### §IV Bounds for optimal redundancy with data protection

| Label | § | Statement | Lean name | Status |
| --- | --- | --- | --- | --- |
| `#definition 10#` | IV | optimal redundancy `r_f(k:d_d,d_f) = r_f(k,t_d,t_f)` | `optimalRedundancyData` | stated |
| `#definition 11#` | IV | DRM `D_f(t_d,t_f:u₁,…,u_M)`: `max(2t_d+1−d,0)` if `f(uᵢ)=f(uⱼ)`, `max(2t_f+1−d,0)` if `f(uᵢ)≠f(uⱼ)`, `0` on the diagonal | `drmData` | stated |
| `#theorem 2#` | IV | `r_f(k,t_d,t_f) = N(D_f(t_d,t_f:u₁,…,u_{q^k}))` — **the central identity** | `optimalRedundancyData_eq_N_drmData` | todo |
| `#theorem 3#` | IV | `r_f ≥ N(D_f(t_d,t_f:u₁,…,u_m))` for any subset; `r_f ≥ 2t_f` if `|Im f| ≥ 2`; `r_f ≥ N(q^k,2t_d+1)−k` | `optimalRedundancyData_ge_N_subset`, `two_mul_le_optimalRedundancyData`, `optimalRedundancyData_ge_Nconst_sub` | todo |
| `#theorem 4#` | IV | over `F₂`, if `2 ≤ |Im f| ≤ k` then `r_f(k,t_d,t_f) ≥ 2t_f + t_d` | `binary_optimalRedundancyData_ge` | todo |
| `#theorem 5#` | IV | for an `[n,k,2t_d+1]` code `C`: `N(DRM) ≤ N(CDRM) + n − k` | `N_drmData_le_N_cdrm_add` | todo |
| `#corollary 4#` | IV | `r_f(k,t_d,t_f) ≤ N(D_{C,f}) + n − k` | `optimalRedundancyData_le_N_cdrm_add` | todo |
| `#corollary 5#` | IV | binary version with the explicit `t_d log k` redundancy of `C` (carries the [1, App.] bound as a hypothesis) | `binary_optimalRedundancyData_le` | todo |
| `#theorem 6#` | IV | `N(D_{C,f}(t_f:u₁,…,u_M)) ≤ N(M, 2(t_f−t_d))` | `N_cdrm_le_Nconst` | todo |
| `#corollary 6#` | IV | `N(M,2(t_f−t_d)) ≤ 4(t_f−t_d)−2 )/(1−√…)` for `t_f−t_d ≥ 5`, `M ≤ 4(t_f−t_d)²`; and `N(4,2(t_f−t_d)) = 3(t_f−t_d)` | `Nconst_le`, `Nconst_four` (first part needs `#lemma 1#`) | todo |
| `#theorem 7#` | IV | for `C` an optimal-length `[n,k,2t_d+1]` linear code: `N(CDRM) + n−k ≤ r_s ≤ N(CFDM) + n−k` | `two_step_redundancy_bounds` | todo |
| `#remark 1#` | IV | design remark (`N(D)` as the reduction target) | — | recorded here only |

#### §V Non-existence of strict `(f:d_d,d_f)`-FCCs

| Label | § | Statement | Lean name | Status |
| --- | --- | --- | --- | --- |
| `#definition 12#` | V | minimum-distance graph `G(C)`: vertices `C`, edges between codewords at distance `d_min(C)` | `minDistGraph` | stated |
| `#theorem 8#` | V | if `G(C)` is connected then `C` is not a strict `(f:d,d_f)`-FCC for any `f` with `|Im f| ≥ 2`, `d_f > d` | `not_isFCCData_of_connected` | todo |
| `#theorem 9#` | V | if `G(C)` has `Q` components then no `f` with `|Im f| ≥ Q+1` and `d_f > d` works | `not_isFCCData_of_components` | todo |
| `#theorem 10#` | V | `G(C)` is connected for every perfect `t`-error-correcting code | `isConnected_minDistGraph_of_perfect` | todo |
| `#corollary 7#` | V | `r_f(k:d_d,d_f) ≥ n−k+1` when a perfect code of length `n` exists | `perfect_optimalRedundancyData_ge` | todo |
| `#lemma 2#` | V | MDS codes: for all `u,v` there is `u'` with `d(u,u') = d` and `d(u',v) ≤ d(u,v)−1` | `exists_mds_neighbor` | todo |
| `#theorem 11#` | V | `G(C)` is connected for every MDS code | `isConnected_minDistGraph_of_mds` | todo |
| `#corollary 8#` | V | `r_f(k:d_d,d_f) ≥ d` given an MDS `(n,q^k,d)` code | `mds_optimalRedundancyData_ge` | todo |

#### §VI FCCs for specific functions

| Label | § | Statement | Lean name | Status |
| --- | --- | --- | --- | --- |
| `#definition 13#` | VI-A | function ball `B_f(u,ρ) = {f(u') | d(u,u') ≤ ρ}` | `functionBall` | stated |
| `#definition 14#` | VI-A | `ρ`-locally binary function: `|B_f(u,ρ)| ≤ 2` for all `u` | `IsLocallyBinary` | stated |
| `#lemma 3#` | VI-A | for `(d_f−1)`-locally binary `f` and a systematic `[n,k,d_d]` code: `r_f(k:d_d,d_f) ≤ n−k+d_f−d_d` (and `= 2(t_f−t_d)` in `t`-form) | `locallyBinary_redundancy_le` | todo |
| `#corollary 9#` | VI-A | the same with a perfect linear code in step 1 | `locallyBinary_perfect_redundancy_le` | todo |
| `#corollary 10#` | VI-A | optimality of the construction for `d_f = d_d+1` given a perfect code | `locallyBinary_perfect_optimal` | todo |
| `#corollary 11#` | VI-A | with an MDS `(n,q^k,d_d = n−k+1)` code in step 1: `r_f(k:d_d,d_f) ≤ n−k+d_f−d_d = d_f−1` | `locallyBinary_mds_redundancy_le` | todo |
| `#corollary 12#` | VI-A | optimality of the construction for `d_f = d_d+1` given an MDS code | `locallyBinary_mds_optimal` | todo |
| `#definition 15#` | VI-B | `(ρ,λ)`-bounded function: `|B_f(u,ρ)| ≤ λ` for all `u` | `IsLocallyBounded` | stated |
| `#lemma 4#` | VI-B | contiguous-block condition ⇒ a colouring `Col_f : F₂^k → [λ]` separating `f`-values at distance `≤ ρ` | — | external ([14]): hypothesis of `#theorem 12#` |
| `#lemma 5#` | VI-B | `N(4,2t) = 3t` | `Nconst_four_two` | todo |
| `#theorem 12#` | VI-B | for `(2t_f,λ)`-bounded `f` (with the `#lemma 4#` colouring): `r_f ≤ n−k+N(λ,2(t_f−t_d))`; for `q=2, λ=4`: `≤ n−k+3(t_f−t_d)` | `locallyBounded_redundancy_le` | todo |
| `#lemma 6#` | VI-C | Hamming-weight function: `r_f ≤ n−k+N(2t_f+1,2(t_f−t_d))`, and `≤ N(q^k,2t_d+1)+N(2t_f+1,2(t_f−t_d))−k` | `hammingWeight_redundancy_le` | todo |

#### §VII Linear `(f:d_d,d_f)`-FCCs

| Label | § | Statement | Lean name | Status |
| --- | --- | --- | --- | --- |
| `#definition 16#` | VII | linear FCC: a `k`-dimensional subspace of `F_q^n` satisfying the two distance conditions (standard-form generator matrix) | `IsLinearFCC` | stated |
| `#lemma 7#` | VII | `D_f = {(u,p) ∈ C | u ∈ ker f}` is a subspace of `C` of dimension `dim ker f` | `kernelSubcode` | todo |
| `#lemma 8#` | VII | `min{wt(c₁−c₂) | c₁ ∈ vᵢ+D, c₂ ∈ vⱼ+D} = min_{d∈D} wt(vᵢ−vⱼ+d)` | `cosetDist_eq` | todo |
| `#lemma 9#` | VII | in a linear `(f:d_d,d_f)`-FCC of a linear `f`: `wt v ≥ d_f` for all `v ∈ C \ D_f` | `wt_ge_of_not_mem_kernel` | todo |
| `#definition 17#` | VII | coset code `C/D` and its minimum distance `d(C/D)` | `CosetCode`, `cosetCodeMinDist` | stated |
| `#definition 18#` | VII | equivalent definition: `d(C) ≥ d_d` and `d(C/D_f) ≥ d_f` | `IsLinearFCCKernel` | stated |
| `#lemma 10#` | VII | `C_cat = {(C(u), D(f(u)))}` is a linear code of dimension `k` for linear `C`, `D`, `f` | `image_linear_concat` | todo |
| `#theorem 13#` | VII | correctness: `C_cat` is a linear `(f:d_d,d_f)`-FCC of dimension `k`, total redundancy `(n−k)+r'` | `isLinearFCC_concat` | todo |

#### §VIII Classical bounds extended to FCCs + Appendix

| Label | § | Statement | Lean name | Status |
| --- | --- | --- | --- | --- |
| `#lemma 11#` | VIII | Plotkin bound `N(D) ≥ 4/(M²)·Σ[D]ᵢⱼ` (`M` even) resp. `4/(M²−1)·Σ` (`M` odd) | `plotkin_bound_binary` | todo |
| `#lemma 12#` | VIII | Gilbert–Varshamov-type upper bound `N(D) ≤ min{r : 2^r > max_j Σ_{i<j} V(r,[D]−1)}` | — | external ([1]): used as hypothesis if needed |
| `#lemma 13#` | VIII | over `F_q`: `N(D) ≥ 2q/(M²(q−1)−a(q−a))·Σ_{i<j}[D]ᵢⱼ`, `a = M mod q` | `plotkin_bound` | todo |
| `#theorem 14#` | VIII-A | `r_f(k:d_d,d_f) ≥ ((L−1)d_d+(q^k−L)d_f)/(q^{k−1}(q−1)) − k`, `L = max_α |f⁻¹(α)|`, for `d_f > d_d` | `plotkin_bound_fcc` | todo |
| `#theorem 15#` | VIII-B | Hamming-type bound for `(f,t)`-FCCs: `E ≤ q^n/|∪_{j≤ℓ} B(v_j,t)|` (see the direction note in `Notation.md` §5) | `hamming_bound_fcc` | todo |
| `#corollary 13#` | VIII-B | `E ≤ q^n/Σ_{i≤t} C(n,i)(q−1)^i` | `hamming_bound_fcc_sphere` | todo |
| `#theorem 16#` | VIII-C | Hamming-type bound for `(f:d_d,d_f)`-FCCs, with `d(vᵢ,vⱼ) ≥ d_d` in the union | `hamming_bound_fcc_data` | todo |
| `#corollary 14#` | VIII-C | `E ≤ q^n/(ℓ·Σ_{i≤t_d} C(n,i)(q−1)^i)` | `hamming_bound_fcc_data_sphere` | todo |
| `#theorem 17#` | App. | `|B(u,t) ∪ B(v,t)| = 2Σ_{i≤t}C(n,i)(q−1)^i − qΣ_{i≤t−1}C(n−1,i)(q−1)^i` for `d(u,v)=1` | `card_ball_union_dist_one` | todo |
| `#lemma 14#` | App. | `|B(u₁,t) ∩ B(u₂,t)| = 2Σ_{i≤t−1}C(n−1,i)` for `d(u₁,u₂)=2` over `F₂` | `card_ball_inter_dist_two` | todo |
| `#theorem 18#` | App. | union of three balls at pairwise distances `1,1,2` | `card_ball_union_three` | todo |
| `#theorem 19#` | App. | `|B(u₁,t) ∪ B(u₂,t)| = 2Σ_{i≤t}C(n,i) − 8Σ_{i≤t−3}C(n−3,i) − 6C(n−3,t−2)` for `d(u₁,u₂)=3`, `t ≥ 2` | `card_ball_union_dist_three` | todo |

### 1.2 Numbered examples (optional, high value as regression tests)

The paper's 17 examples are **not** part of the catalogue, but several pin the
conventions down and are decidable, so they make excellent test cases once the
definitions exist (`#example 1#`, `#example 6#`, `#example 7#`, `#example 12#`, `#example 14#` in particular:
build the DRM/CDRM by `decide` and check the quoted D-codes satisfy it).  This is
the cheapest way to catch a modelling mistake (bit order, index base, which
matrix entry means what) before any proof is attempted.

The examples that are used as `decide` regression tests get their own rows, so
that the checker can tie a test to the paper item it exercises.  The "Test"
column names the declaration whose docstring carries the marker; further tests
of the same example are listed in `FCC/Examples.lean`.

| Label | § | What the test pins down | Test | Status |
| --- | --- | --- | --- | --- |
| `#example 1#` | II | the DRM of the paper's first worked example (`f` on `F₂²`, `t = 1`) against the printed 4×4 matrix | `ex1_drm_matches` | tested |
| `#example 2#` | II | the `D`-code `{000,110,110,101}` for that DRM, `N(D) = 3` (no length-2 code; the length-3 one is valid), and the resulting `(f,1)`-FCC `{00000,01110,10110,11101}` | `ex2_dcode_valid`, `ex2_no_length_two`, `ex2_codewords`, `ex2_is_fcc` | tested |
| `#example 4#` | III | two codes with the same function protection `t_f = 1` but minimum distances 1 and 2 — the example that motivates the `(f : d_d, d_f)` notation | `ex4_both_fcc`, `ex4_min_dists` | tested |
| `#example 6#` | IV | the `[6,3,3]` code of the two-step construction, its coded distance requirement matrix (`#definition 7#`), the `D`-code `{000,110,101,011}`, and `N(D) = 3` | `ex6_cdrm_matches` | tested |
| `#example 7#` | IV | the 8×8 distance requirement matrix (`#definition 11#`) for `f = wt` on `F₂³`, `t_d = 1`, `t_f = 2` | `ex7_drm_matches` | tested |
| `#example 10#` | VI-A | the `[7,4,3]` Hamming code used in the locally binary construction | `ex10_min_dist` | tested |

Still to be formalized: `#example 3#` (the FDM of `#example 1#` — `fdm` is
defined through the minimal distance `fDist`, so the check needs the
`fDist`/`N` API of phase 3.0, or a computable restatement of the minimum),
`#example 5#` (the FDM/CDRM/D-code of the `F₂³` Hamming-weight example; its
DRM/D-code parts are doable now, its `N(D) = 6` claim follows from
`#lemma 11#` in phase 3.11), `#example 8#`, `#example 9#`, `#example 12#`,
`#example 13#`, `#example 14#` (decidable data checks), and `#example 11#`,
`#example 15#`, `#example 16#`, `#example 17#`, which also depend on the §VIII
bounds (`#theorem 14#`–`#theorem 16#`) or on a numerical value quoted from [1].

Three of them are already transcribed by hand (phase 1a):

* `#example 6#` — `f = wt` on `F₂³` with `t_f = 2`, the `[6,3,3]` code with generator
  rows `100110, 010101, 001011`, representatives `000, 100, 011, 111`.  The
  CDRM `D_{C,f}(t_f : u₁,u₂,u₃,u₄)` is
  `[[0,2,1,2],[2,0,2,1],[1,2,0,2],[2,1,2,0]]`, `N(D) = 3`, and the quoted
  D-code `{000,110,101,011}` satisfies every entry.
* `#example 7#` — `f = wt` on `F₂³` with `t_d = 1`, `t_f = 2`, information vectors in
  the order `000, 100, 010, 001, 110, 101, 011, 111`.  The DRM
  `D_f(t_d,t_f : u₁,…,u₈)` is

  ```text
  0 4 4 4 3 3 3 2
  4 0 1 1 4 4 2 3
  4 1 0 1 4 2 4 3
  4 1 1 0 2 4 4 3
  3 4 4 2 0 1 1 4
  3 4 2 4 1 0 1 4
  3 2 4 4 1 1 0 4
  2 3 3 3 4 4 4 0
  ```

  (blue/red in the paper: entries for equal `f`-values use `2t_d+1 = 3`, for
  different `f`-values `2t_f+1 = 5`).  Cross-check: `(u₁,u₅) = max(5−3,0) = 3`,
  `(u₂,u₈) = max(5−2,0) = 3`, `(u₅,u₈) = max(5−1,0) = 4`, all matching.

### 1.3 Out of scope

* Computational claims obtained "by trial and error" in the paper (e.g. `N(D) = 6`
  in `#example 5#`) — formalizing them means writing a search algorithm plus a
  correctness proof; optional extension, not part of the core.
* Motivation, network/storage discussion, figures and the conclusion (§I, §IX).
* Results quoted from other papers (`#lemma 1#`, `#corollary 3#`, `#lemma 4#`, `#lemma 12#`) are
  *external inputs*: recorded here, and passed as explicit hypotheses to whatever
  uses them.  Formalizing them is a separate project.

---

## 2. Project setup

```text
FCC.lean                  # library root module (must be at the package root)
lakefile.toml             # library FCC; requires mathlib
lean-toolchain            # leanprover/lean4:v4.34.0-rc2 (must match mathlib)
lake-manifest.json        # dependency revisions
FCC/
  Paper.lean              # THE MAIN FILE: every numbered item, in paper order
  Definitions.lean        # §I-E notation: Word, wt, ball
  Basic.lean              # internal lemmas about words
  Balls.lean              # internal counting lemmas (spheres, balls)
  Internal.lean           # internal scaffolding for the example checks
  AxiomCheck.lean         # `#print axioms` audit
scripts/
  consistency_check.ps1   # build + PLAN/Lean label coverage + orphan modules + sorry count
  axioms_check.ps1        # per-theorem axiom audit
  headline_theorems.txt   # manifest of audited theorems
Notation.md               # paper <-> Lean dictionary, conventions, open questions
CONSISTENCY.md            # per-step protocol (manual fidelity checklist)
VERIFICATION.md           # release-level verification record
DEVLOG.md                 # dated development log
TODO.md                   # open work
PUBLISHING.md             # venue / artifact / DOI plan
ONBOARDING.md             # from-zero guide (Chinese)
AGENTS.md                 # rules for agents and contributors
paper/                    # the paper (local-only, gitignored)
```

**The main file is `FCC/Paper.lean`.**  Every numbered item of the paper —
definition, example, theorem, lemma, corollary — appears there exactly once, in
the paper's own order, with the paper's number at the head of its docstring; the
file's section headings follow the paper's sections, and each item still to be
written is listed as a `TODO` under its section.  Reading that one file from top
to bottom is reading the paper's formalization, and it is the artifact the
project delivers.

Declarations that are *not* numbered items of the paper (the notation layer, the
counting and weight lemmas, the temporary example transcriptions) live in
`FCC/Definitions.lean`, `FCC/Basic.lean`, `FCC/Balls.lean` and
`FCC/Internal.lean`; they carry `(internal, §…)` docstrings, may be reorganised
freely, and are imported by the main file.  `scripts/consistency_check.ps1`
enforces the inventory ↔ main-file mapping in both directions.

**Agents working in this repository must follow `AGENTS.md`.**

---

## 3. Formal model (design decisions)

Full rationale and the paper-symbol dictionary: `Notation.md`.  Summary:

```lean
abbrev Word (F : Type*) (n : ℕ) := Fin n → F    -- F_q^n, with q = Fintype.card F
abbrev wt [Zero F] [DecidableEq F] (u : Word F n) : ℕ := hammingNorm u
def ball (u : Word F n) (t : ℕ) : Finset (Word F n)              -- B(u,t)
```

* **The field is a parameter, not `ZMod q`.**  Everything is stated for an
  arbitrary `[Field F] [Fintype F] [DecidableEq F]`; `q = Fintype.card F`, and
  the binary specialisations are just `F = ZMod 2`.  This keeps the statements
  literal to the paper instead of silently restricting to `q = 2`.
* **Hamming distance is mathlib's `hammingDist`** (`Mathlib.InformationTheory.Hamming`)
  — no local re-derivation of coding theory.
* **Codes are sets of words** (`Finset`/`Set`), not matrices; the systematic
  encoding hypothesis of Definitions 1/6 is an explicit structure field.
* **`N(D)` is defined by minimality**, not as a `Nat.find` of a computable
  predicate: `N D = sInf {r | IsDCode D r}` (with an existence lemma for large
  `r`), so the "minimal length" reading of Definition 3 is what the theorems
  quantify over.

### 3.1 Conventions to lock down early (recorded in `Notation.md`)

* 0-based `Fin` indices vs 1-based paper coordinates;
* `d_d`/`d_f` (distances) as the primary parameters, with the `t_d`/`t_f`
  (error-correcting capability) versions as corollaries — the paper uses both and
  switches between them silently;
* `D`-codes are indexed by `Fin M` and the diagonal of a DRM is `0`, so the
  condition is stated for `i ≠ j`;
* which direction the "better code" comparison points in (`UniversalBetter`);
* the exact range of the channel/parameter tuple (`d_d ≤ d_f`, `t_d < t_f`).

---

## 4. Work breakdown

Phases are ordered by dependency, not by the paper's section order.  Each phase
ends with `lake build` green and one commit.

### Phase 0 — Infrastructure and base layer — DONE
Repository scaffold, toolchain pin, CI, the documentation set, and
`Word`/`wt`/`ball` with three proved lemmas (`wt_le_wt_add_hammingDist`,
`wt_zero`, `mem_ball_self`).

### Phase 1 — Modelling the paper (`FCC/Definitions.lean` + `Notation.md`)
All Definitions 1–18, in six sub-steps, each one commit:

1. **1a** words and distance algebra — **in progress** (`FCC/Balls.lean`,
   `FCC/Examples.lean`).  Done: `Fintype.card (Word F n) = q^n` (`card_word`),
   `hammingDist_eq_card_diffSet`, the sphere/ball API (`sphere`, `mem_sphere`,
   `ball_eq_biUnion_sphere`, `disjoint_sphere`, `ball_mono`,
   `ball_eq_univ_of_le`, `card_ball_univ`), and the `decide` regression tests
   for the paper's Examples 6, 7, 10 in `FCC/Examples.lean`.  Still to do: the
   closed form `|B(u,t)| = Σ_{i≤t} C(n,i)(q-1)^i` (`card_sphere`, `ball_card`);
2. **1b** codes: `IsCode`/minimum distance, `IsSystematic`, then Definition 1
   (`IsFCC`, `optimalRedundancy`) and Definition 6 (`IsFCCData`) — Definition 6 is
   the general one, Definition 1 its `t_d = 0` case;
3. **1c** distance matrices: `drm` (`#definition 2#`), `drmData` (`#definition 11#`), `fDist`/`fdm`
   (`#definition 4#`, `#definition 5#`), then `IsDCode`/`N`/`Nconst` (`#definition 3#`) and the basic API
   (`N_const_le`, monotonicity, `N` is attained);
4. **1d** coded matrices: `cdrm` (`#definition 7#`), `codedFDist` (`#definition 8#`), `cfdm`
   (`#definition 9#`);
5. **1e** graph and function classes: `minDistGraph` (`#definition 12#`),
   `functionBall` (`#definition 13#`), `IsLocallyBinary` (`#definition 14#`),
   `IsLocallyBounded` (`#definition 15#`);
6. **1f** linear side: `IsLinearFCC` (`#definition 16#`), `CosetCode`/`cosetCodeMinDist`
   (`#definition 17#`), `IsLinearFCCKernel` (`#definition 18#`).

Gate: `lake build` green, `decide` regression tests from §1.2 pass, `Notation.md`
updated in the same commit.

### Phase 2 — Statement catalogue (`FCC/Statements.lean`)
Every row of §1.1 that is not `external` as a Lean statement with a `sorry`
proof and the paper label in its docstring.  Gate: `consistency_check.ps1
-Strict` passes (label coverage in both directions).

### Phase 3 — Proof phases (one session per row, ordered below)

| # | Contents | Why this order |
| --- | --- | --- |
| 3.0 | `N`-API: existence, minimality, monotonicity, `N` of a constant matrix | everything else uses it |
| 3.1 | `#theorem 2#` (the central identity `r_f = N(DRM)`) | the framework's backbone |
| 3.2 | `#theorem 3#`, `#corollary 1#`, `#theorem 1#`, `#corollary 2#`, `#remark 1#` | corollaries of 3.1 |
| 3.3 | `#theorem 5#`, `#corollary 4#`, `#theorem 6#`, `#corollary 6#` | the two-step construction machinery |
| 3.4 | `#theorem 4#` | the first "real" combinatorial argument (binary, three words) |
| 3.5 | `#definition 12#` + `#theorem 8#`, `#theorem 9#` | graph argument, independent of §IV |
| 3.6 | `#lemma 2#`, `#theorem 11#`, `#corollary 8#` | MDS connectivity |
| 3.7 | `#theorem 10#`, `#corollary 7#` | perfect codes (needs the packing/covering argument) |
| 3.8 | `#lemma 3#`, `#corollary 9#`–`#corollary 12#` | locally binary construction |
| 3.9 | `#lemma 5#`, `#theorem 12#`, `#lemma 6#` | locally bounded + Hamming weight |
| 3.10 | `#lemma 7#`–`#lemma 10#`, `#theorem 13#` | the linear/algebraic side |
| 3.11 | `#lemma 13#`, `#lemma 11#`, `#theorem 14#` | Plotkin bounds (double counting) |
| 3.12 | `#theorem 15#`, `#corollary 13#`, `#theorem 16#`, `#corollary 14#` | Hamming bounds (sphere packing) |
| 3.13 | `#theorem 17#`, `#lemma 14#`, `#theorem 18#`, `#theorem 19#` | appendix: counting unions of balls |

Suggested *warm-up* before 3.1, if the first proof session should be gentle:
3.13 (`#theorem 17#`–`#theorem 19#`) is pure binomial counting over `Finset`, uses no
earlier phase, and is the same style of argument as `#lemma 13#`.

### Final — Assembly and documentation
Zero `sorry` outside `external`-hypothesised rows (`VERIFICATION.md` lists every
row that is deliberately not formalized); axiom audit; `VERIFICATION.md` report;
README status table; tagged release.

---

## 5. Dependency graph

```text
Definitions(§II/III: #definition 1#-#definition 11#, IsDCode, N)
   │
   ├─► #theorem 2# ─┬─► #theorem 3#, #corollary 1# ─► #theorem 1# ─► #corollary 2#
   │          └─► #theorem 5# ─► #corollary 4# ─► #theorem 7# ─► #corollary 5# (uses external [1, App.])
   │                 └─► #theorem 6# ─► #corollary 6# (uses external #lemma 1#)
   ├─► #theorem 4# (binary, needs 3-vector Plotkin)
   ├─► #definition 12# ─► #theorem 8# ─┬─► #theorem 10# ─► #corollary 7#
   │                    └─► #theorem 11# ─► #corollary 8#      (#theorem 11# ← #lemma 2#, MDS)
   ├─► #definition 13#/#definition 14# ─► #lemma 3# ─► #corollary 9# ─► #corollary 10#, #corollary 11#, #corollary 12#
   ├─► #definition 15# ─► #lemma 4#(external), #lemma 5# ─► #theorem 12# ─► #lemma 6#
   ├─► #definition 16# ─► #lemma 7# ─► #definition 17#/#definition 18# ─► #lemma 8#, #lemma 9# ─► #lemma 10# ─► #theorem 13#
   └─► #lemma 13# ─► #lemma 11#, #theorem 14#        (#theorem 14# also uses #theorem 2#)
       #definition 13#+#theorem 17#/18/19 ─► #theorem 15# ─► #corollary 13# ─► #theorem 16# ─► #corollary 14#
```

---

## 6. Validation & milestones

| Milestone | Gate |
| --- | --- |
| M0 — repo builds | `lake build` green; `axioms_check.ps1` green; CI green (Phase 0) |
| M1 — model compiles | every Definition 1–18 in the library; `decide` regression tests from §1.2 pass; `Notation.md` reviewed line by line against the PDF |
| M2 — catalogue complete | every non-external row of §1.1 `stated`; `consistency_check.ps1 -Strict` green |
| M3 — core proofs | phases 3.0–3.5 complete (the framework of §III–IV plus `#theorem 4#`); zero `sorry` there |
| M4 — full proofs | all rows `proved` or explicitly `external`-hypothesised; `axioms_check.ps1` green |
| M5 — release | `VERIFICATION.md` report filled in; tag + DOI; README status table final |

---

## 7. Risks & mitigations

* **Statement drift** (Lean statement ≠ paper statement) → `Notation.md` + the
  manual checklist in `CONSISTENCY.md`, reviewed at every commit.  The paper is
  available only as a PDF, so there is no `\label`-level automatic check against
  the paper; the automatic check is PLAN ↔ Lean, and the paper ↔ PLAN step is
  manual.
* **A paper statement is under-specified or mis-printed** → already suspected in
  two places (see `Notation.md` §5: the direction of `#theorem 15#`/`#theorem 16#`, and the
  constants in `#lemma 1#`); record the corrected version and keep both, as
  `DEVLOG.md` does.
* **A cited result is needed** (`#lemma 1#`, `#lemma 4#`, `#lemma 12#`, `#corollary 3#`) → these are
  handled as explicit hypotheses, never as `axiom`s, so `axioms_check.ps1` stays
  meaningful.
* **Elaboration time** → minimal imports (never `import Mathlib`), small modules,
  `decide` only on small instances.
* **Toolchain churn** → `lean-toolchain` + `lake-manifest.json` are committed;
  upgrading is a deliberate, separate commit.

---

## 8. Effort estimate

Rough, for a beginner working with an AI assistant, in the "one session per
row" rhythm the project uses:

* Phase 1 (Definitions 1–18): 3–5 sessions.
* Phase 2 (catalogue): 1–2 sessions.
* Phase 3.0–3.2 (the §IV core): 4–8 sessions.
* Phase 3.3–3.7: 4–8 sessions.
* Phase 3.8–3.13: 8–16 sessions (the appendix and the counting bounds are the
  most mechanical, the perfect-code and Hamming-bound rows the most delicate).

Budget one session per numbered result as a rule of thumb, and treat "the paper
needed a correction" as a legitimate outcome rather than a failure.
