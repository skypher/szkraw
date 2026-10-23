# Independent review, round 27: the split of the manuscript into three papers

Repository: github.com/skypher/szkraw, commit 9c9e1e3. Read these files at that commit (raw URLs work: https://raw.githubusercontent.com/skypher/szkraw/9c9e1e3/<path>):
- papers/p1.tex, papers/p2.tex, papers/p3.tex: the three papers;
- paper.tex: the full manuscript they were generated from (its mathematics was reviewed in rounds 1-26, see REVIEW.md);
- papers/build_p1.py, build_p2.py, build_p3.py: the scripts that generated the papers by copying line ranges of paper.tex verbatim and applying asserted string edits (every edit is visible there);
- papers/concordance.txt, papers/FORMALIZATION.md, papers/DIAGNOSTICS.md.

The mathematics was reviewed before; this round reviews only the split. This is a mathematics and consistency review, not a Lean review. Verify every citation of a paper or book in its PDF; mark any you cannot open as unverified.

Check in particular:
1. **Paper 1 stands alone.** P1 should answer Szwarc's Problem 2 with complete proofs. It should use P2 and P3 only for context, never in a proof. Check every new or edited passage (listed as edits in build_p1.py):
   - the rewritten spectral argument in the proof of Lemma 2.1;
   - the definition of property (P) and the claim that the coefficients sum to one;
   - the definition of G_{N,q,r} and K_{N,r};
   - the edited remark after Theorem 3.1;
   - the proofs of Corollaries 3.6 and 3.7 through Theorem 3.1;
   - the symmetry argument inserted into the proof of Theorem 4.1;
   - the proof of Corollary 4.2: the direct N = 1 computation, and Theorem 3.1 for both components, the odd one with ratio r/q ≤ 1 and the parameter identification;
   - Theorem 4.3 and its proof;
   - the new proof of Lemma 5.1 in the cube model of Corollary 3.6;
   - the edits in Proposition 5.2 (detailed balance, π_N = r^{-N});
   - the definition of ρ_N(r) in Corollary 5.3, and that it agrees with the definition used in P3 Corollary 9.11;
   - the summary sentence after Corollary 5.3 (claims attributed to P3);
   - the sharpness paragraph;
   - the open problems;
   - the abstract and introduction. Is every claim proved in P1? Is every numbered result in P1 covered by its Lean table?
2. **Paper 2 depends only on P1.**
   - Lemma 2.1 is P1's Lemma 3.3 restated for a general sequence. Is the adapted proof correct, and is the restated form enough for all its uses in P2 (applied to φ, f, P_k)?
   - Is the Setting section correct and sufficient?
   - Do the citations of P1's Lemmas 3.2 and 3.4, Theorem 3.1 and Section 3 point to the right statements (xr labels P1-*)?
   - Does removing Proposition 8.10 of paper.tex leave any dangling dependence? Check the edited remark after Theorem 4.2.
   - Check the edited counterexample paragraph, the disclosure and the Lean table claims.
3. **Paper 3 depends only on P1.**
   - Check the new introduction roadmap and the added sentences in Sections 7 and 9 (exponential decay of the radius cited from P1).
   - Check the edited open problems, including the cut of the inexact LP numerics, the shortened K–G paragraph and the removed envelope estimate. Does the remaining text still make sense, with no references to cut material?
   - Are the duplicates with P1 consistent (finite realization, Krawtchouk range, geometric arrays, Theorem 7.1 = P1 Theorem 4.3, corner value)?
4. **Nothing lost or weakened.** Compare each moved result with paper.tex: are statements and hypotheses identical except where an edit is listed? Is the concordance correct?
5. **Overall.** Is the structure sensible for submission? Is anything in P1 still too long or missing for a reader coming from Szwarc's survey?

Answer format: PASS / PASS WITH MINOR FIXES / FAIL, every defect with an exact fix, and your independent checks. Be terse.
