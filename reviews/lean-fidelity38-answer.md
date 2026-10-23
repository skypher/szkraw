### (1) Random-set statement

**`union_card_law` — MATCH.** It gives precisely
\[
\Pr(|S\cup T|=k)=\binom nk\,\kappa_k
\]
when the independent marginal masses are \(\rho_{|A|}\) and \(\nu_{|B|}\). The product of the two masses encodes independence. The restriction \(k\le n\) loses no substantive case: for \(k>n\), both the union-cardinality mass and \(\binom nk\) are zero. The accepted identification of `kap` with the Newton coefficients supplies the intended meaning of \(\kappa\).

**`perm_invariant_card` and `random_sets_ulc` — MATCH.** The former states that permutation invariance makes the mass depend only on cardinality. Consequently, for \(|A|=i\le n\),
\[
\operatorname{cardLaw}(p)(i)=\binom ni\,p(A),
\]
so `ULC n (cardLaw p)` is exactly `LCNZ` of the size-dependent subset masses, extended by zero beyond \(n\). The conclusion is the required ultra-log-concavity of the independent union’s cardinality.

Omitting total mass one is a **harmless strengthening**, not a missing hypothesis: the theorem applies to unnormalized masses and specializes to probability laws. Nonnegativity of individual subset masses follows from **permutation invariance together with** the cardinality-ULC hypothesis, not from cardinality ULC alone. Both assumptions are present.

### (2) Double-binomial convolution

**`walkup_convolution` — MATCH.** Its bounds are \(0\le i\le k\) and \(0\le r\le i\), so \(k-r\) never involves truncated subtraction below zero. Substituting \(j=k-r\) gives
\[
\binom ki\binom i{k-j}\rho_i\nu_j.
\]
The resulting \(j\)-range is \(k-i\le j\le k\); the additional terms in `kap_nat` with \(j<k-i\) vanish because \(\binom i{k-j}=0\). Thus the statement expresses exactly \(h_k=\kappa_k\). Combined with the accepted `kap_LCNZ`, it also supplies the stated preservation property.

### (3) Documentation changes

**New P2 table row — MATCH.** The three claims correspond directly to the three listed declarations: the union-cardinality formula, preservation of ultra-log-concavity, and the convolution identity. The unnormalized formulation does not invalidate the probability-law wording.

**Changed not-formalized item — MATCH.** It correctly leaves unformalized the literature identification with Walkup’s conditionally uniform random sets and fundamental sequences, rather than the now-formalized random-set closure statement or convolution identity. Formalizing those mathematical statements does not itself formalize their attribution or comparison with Walkup’s terminology.

### Overall verdict: **PASS**

No replacement text is required.
