import Mathlib.InformationTheory.Hamming

/-!
# Definitions: the paper's universe of words

**Paper.** C. Rajput, B. S. Rajan, R. Freij-Hollanti, C. Hollanti,
"Function-Correcting Codes With Data Protection", *IEEE Trans. Inform. Theory*
**72**(7), July 2026, DOI 10.1109/TIT.2026.3692458.

This module holds the carriers of the paper's mathematical universe:

* `Word F n` — the paper's `F_q^n`, a word of length `n` over the alphabet `F`;
  `F` is an arbitrary finite field, so `q = Fintype.card F`;
* `wt u` — the Hamming weight `wt(u)` (§I-E), the number of non-zero entries;
* `ball u t` — the Hamming ball `B(u,t) = {x | d(x,u) ≤ t}` (§I-E).

The Hamming distance `d(x,y)` itself is **mathlib's** `hammingDist` (module
`Mathlib.InformationTheory.Hamming`) rather than a local redefinition; it is
already `#{i | x i ≠ y i}`, it satisfies the triangle inequality, and it comes
with the full `dist`/`norm` API.  This choice (deliberately importing one small
mathlib module instead of re-deriving coding theory from scratch) is recorded in
`Notation.md` §2.

The paper's *code-theoretic* definitions (Definitions 1–18 of §II, §III, §IV,
§V, §VI, §VII: `(f,t)`-FCC, DRM, D-code, `N(D)`, FDM, CDRM, minimum-distance
graph, locally binary / bounded functions, coset codes, linear FCCs) are Phase 1
work — see `PLAN.md` §4.
-/

namespace FCC

/-- `(paper notation, §I-E)` — the paper's `F_q^n`: a word of length `n` over the
alphabet `F`.  Vectors are `Fin n`-indexed, i.e. 0-based, while the paper's
coordinates are 1-based; the dictionary is in `Notation.md` §2. -/
abbrev Word (F : Type*) (n : ℕ) := Fin n → F

/-- `(paper notation, §I-E)` — `wt(u)`, in the paper's words: "the number of
non-zero entries in the vector `u`".  Used by `#corollary 3#` and `#lemma 6#`. -/
abbrev wt [Zero F] [DecidableEq F] {n : ℕ} (u : Word F n) : ℕ := hammingNorm u

/-- `(paper notation, §I-E)` — the Hamming ball: "the Hamming ball of radius `t`
centered at `u` is defined as `B(u,t) = {x ∈ F_q^n | d(x,u) ≤ t}`".  Used by
`#theorem 15#`–`#theorem 19#`. -/
def ball [Fintype F] [DecidableEq F] {n : ℕ} (u : Word F n) (t : ℕ) :
    Finset (Word F n) :=
  Finset.univ.filter fun x => hammingDist x u ≤ t

end FCC
