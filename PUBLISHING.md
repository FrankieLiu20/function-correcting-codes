# Publishing Plan

Goal: turn the finished formalization into a citable, reproducible artifact,
and optionally into a peer-reviewed formalization paper.

## 1. Artifact (do this for every project, finished or not)

- Keep the repository public, with a README that states exactly what is proved
  and what is not.
- Tag releases (`git tag v1.0.0 && git push --tags`) once a phase or the whole
  formalization is complete; attach the filled-in `VERIFICATION.md` report.
- Mint a **Zenodo DOI** for the release and record it in `CITATION.cff` and
  `README.md`.
- Archive the history with Software Heritage.
- Disclose AI assistance explicitly in the README and in any paper (see the
  wording in `ONBOARDING.md` §9).

## 2. Paper

Formalization papers go to ITP (Interactive Theorem Proving) or CPP (Certified
Programs and Proofs), not to the original paper's venue.  A companion note
should cover:

* what was formalized, and the statement table (paper label → Lean name);
* the trusted base: `propext`, `Quot.sound`, `Classical.choice`, plus any use
  of `native_decide` (see `VERIFICATION.md` §2);
* discrepancies found in the paper (`Notation.md` §4);
* engineering: module layout, build times, how to reproduce.

Keep the paper's claims aligned with the repository's actual status; write it
so it is submittable the moment the last `sorry` disappears.

## 3. Sequence

```text
formalization green (no sorry, axiom audit passes)
   → VERIFICATION.md report + README status table
   → tag + Zenodo DOI + CITATION.cff
   → companion note (paper/CompanionNote.tex)
   → arXiv + venue submission
```

## 4. Risks and mitigations

- *Formalization incomplete* → publish a milestone artifact (a clean subset is
  still a result), or wait for completeness; never overstate what is proved.
- *Tools churn* → always pin `lean-toolchain` and `lake-manifest.json`, and
  record both in the artifact.
- *Copyright of the source paper* → link the DOI, do not redistribute the
  publisher's PDF (the `*.pdf` files in this repository are local-only and
  gitignored).
- *Reviewer skepticism about AI* → kernel-checked provenance framing plus
  disclosure; the theorem statements and design remain the author's
  responsibility.
