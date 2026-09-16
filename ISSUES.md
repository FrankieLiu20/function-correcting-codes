# Statement-fidelity log

Every place where the Lean statement is **not** a literal transcription of the
paper, with the reason and the direction of the difference (a *stronger*
statement, i.e. fewer hypotheses, or a *weaker* one).  Transient problems —
things that are merely not written yet and will be written in the next session —
are not recorded here; they are `TODO`s in `FCC/Paper.lean`.

Each entry: where it is, what the paper says, what we do, why.

## 1. Definition 6 carries systematicity (stronger)

`#definition 6#` prints only the two distance conditions, but every encoding in
§III-A is systematic and `#theorem 2#`'s proof needs it (to split `d(Cu,Cv)` into
the message part and the redundancy part).  Our `IsFCCData` therefore includes
`IsSystematic`, exactly as `#definition 1#` does.  *If we ever want the literal
§III-vs-§II distinction, split off an `IsSystematicFCCData` and restate.*

## 2. §VI uses the codes only through their minimum distance (stronger)

`#lemma 3#`, `#corollary 9#`–`#corollary 12#`, `#theorem 12#` and `#lemma 6#`
assume a "systematic `[n,k,d_d]` linear code".  Our statements assume only
`2t_d+1 ≤ d(Cv,Cw)` for `v ≠ w` (and `n = k + r`).  Fewer hypotheses = a
*stronger* statement; nothing about the paper's conclusion is lost.

## 3. External results enter as hypotheses, never as `axiom`s

`#lemma 1#` ([10]), `#lemma 4#` ([14]), `#lemma 12#` ([1]) and the [1, Appendix]
bound behind `#corollary 5#` are **not** formalized.  Where a result is needed it
appears as an explicit hypothesis: `#theorem 12#` takes the colouring of
`#lemma 4#` as `hcol`, and `#corollary 5#`/`#corollary 6#` are therefore still
`todo` — they would be statements *about an unproved external bound*.

## 4. Perfect and MDS codes: prose in the paper, `(internal)` here

§V-B introduces both classes in prose ("a code that achieves the Hamming bound
is called a perfect code"; "an `(n,M,d)_q` code is MDS if and only if
`M = q^{n−d+1}`"), with no numbered definition.  Per the convention of
`Notation.md` §1 they are `(internal, §V-B)` declarations in `FCC/Basic.lean`:
`IsPerfect` = minimum distance `≥ 2t+1` **and** the Hamming bound met with
equality; `IsMDS` = `|C| = q^{n−d+1}` **and** `d_min(C) = d`.  The paper's
perfect-code discussion also uses "the balls of radius `t` cover the space,
without overlap", which our `IsPerfect` does **not** spell out — `#theorem 10#`
will have to derive it from the Hamming equality.

## 5. "Connected graph" is `SimpleGraph.Preconnected`

The paper's connectedness of `G(C)` is `G.Preconnected` in mathlib
(`∀ u v, G.Reachable u v`).  mathlib's `Connected` is a strictly stronger
notion (it also asks the vertex set to be non-empty), so we use `Preconnected`
and never the stronger one in the statements of §V.

## 6. `N`, `r_f`, `d_min`, `d(fᵢ,fⱼ)` are minima (`sInf`) — the "attained" API is phase 3.0

The paper defines all four as minima.  In Lean they are `sInf`s over `ℕ`, which
are not computable, so until phase 3.0 supplies "there is a code attaining it"
lemmas:

* the examples' `N(D) = k` and `d_min = k` claims are checked as the decidable
  pair "a witness exists" + "nothing smaller exists";
* the FDM checks of `#example 3#` and of `#example 5#` cannot be `decide`d at all
  (a `sInf` does not reduce) — they wait for the API or for a computable
  restatement of the minimum over preimages.

## 7. `d(C/D)` is defined through Lemma 8's equivalent form

`#definition 17#` defines the coset distance as a double minimum over cosets.
We define `cosetDist D z` as `min_{d ∈ D} wt(z + d)` — the form `#lemma 8#`
proves equal to the double minimum — and `CosetCode` as the *set of cosets*
(`Set (Set C)`) instead of the quotient `C ⧸ D`.  `#lemma 8#` therefore becomes
the bridge between the printed definition and ours, not a mere remark.

## 8. Not stated, and why (not merely "not yet")

* `#theorem 7#` speaks about the redundancy `r_s` of the two-step *scheme* —
  a construction-level quantity that §III-A introduces but neither §I–§II nor
  our phase 1 defines.  Stating it faithfully needs `r_s` as a definition first.
* `#theorem 9#` counts the connected components `Q` of `G(C)`; mathlib has
  `ConnectedComponent` but the paper's "cannot be an `(f : d, d_f)`-FCC for any
  `f` with `|Im(f)| ≥ Q + 1`" needs `Q` as a number, i.e. a component-count
  helper that phase 1 did not define.
* `#corollary 3#` is quoted from [1] and used only in the paper's discussion.
* `#remark 1#` is a design remark; it has no Lean declaration by convention
  (`PLAN.md` §1.1 marks it `recorded here only`).

## 9. Examples that depend on later results

`#example 11#` quotes `N(2⁸,3) = 12` from [1]; `#example 15#`, `#example 16#`
and `#example 17#` illustrate the §VIII bounds (Plotkin/Hamming) and their
conclusions ("`n ≥ 9`") are exactly those bounds.  They are completed together
with `#theorem 14#`–`#theorem 16#`.

## 10. Suspicious print in the paper (see `Notation.md` §5 for the details)

`#theorem 15#`/`#theorem 16#` are printed as existence statements while their
proofs and all their uses run the other way; `#lemma 1#`'s constants are
ambiguous in the PDF; `#definition 11#`'s printed case split omits `max(·,0)` in
two branches; `#theorem 4#`'s "similar proof" needs checking.  Each is resolved
when its phase is done, and the resolution is recorded in `DEVLOG.md`.
