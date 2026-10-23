## (1) Operator identification — MATCH

The weights and displacements agree with the recurrence: straight \((1,0)\), \(A^\psi_j\) \((j+1,-2j-1)\), \(B_j\) \((j+1,-2j-2)\), and \(C'_j=C_j+C^\psi_j\) \((j+2,-2j-2)\). Weights are evaluated at the source and divided by \(c\) at the destination level. [1]

The parity splits, signed `opA`, and multiplication order give exactly
\[
G=\sum_{m=0}^{N}(P/2)^m,\qquad
S=U+P^2/4-Q+C+A,\qquad
M=GSG.
\]
`kernelRecV_iff`, `tmat_split`, and `opS_eq` state the appropriate connections to the existing recurrence—not merely identities for an unrelated matrix. The \(H,V\) decomposition is unnecessary for defining the signed \(A\)-operator. [2]

**The square index set is harmless here.** All non-straight moves preserve \(\Omega\). The only potential exit is a straight move from \(\ell+a=N\), whose weight is \(1-b_N-c_N=0\) for the normalized array. Thus `opM` represents the paper’s operator on \(\Omega\), with zero padding outside it. Arbitrary sequences need not satisfy these array conditions; the definitions do not assert that they do. [1]

## (2) Cubic data — MATCH

`cubC` and `cubB` encode precisely
\[
d_i=i/6,\quad
\rho(i)=\frac15+\frac1{200}\binom i3,\quad
c_i=\rho(i)d_i,\quad b_i=d_i-c_i.
\]
Thus \(r=1/5,\ t=\tau=0,\ \sigma=1/200\). “Cubic” describes the ratio, not \(c\). Padding the Newton sequences loses no constant term because \(c_0=b_0=0\); `cub_dd` states reproduction through index \(6\), the required range. [2]

## (3) Negative-entry statements — MATCH

`opM_negative_entry` states the exact entry
\[
M_{(2,2),(0,6)}=-9/32,
\]
with destination first and source second. Both indices lie in \(\Omega\). `opM_has_negative_entry` states the corresponding existential negativity for this same concrete operator. This formalizes the example, not a universal claim about every array with \(t=\tau=0\), and not negativity of a linearization coefficient. [2]

## (4) Paper changes

**Table row — MATCH.** It accurately identifies the concrete \(N=6\) negative-entry result and its two declarations. It does not claim a parameter-uniform theorem. [3]

**Shortened not-formalized paragraph — MATCH.** Removing the concrete negative entry is appropriate; retaining the sampled cubic-ratio and resummed-operator tests as unformalized finite-sample evidence preserves the distinction. [3]

**Added sampling clause — MATCH as a computational report.** “In these samples” restricts the \(u\le4,\ N\le13\) statement to tested arrays, consistent with the recorded diagnostic summary. It is not supplied by the new Lean theorems. [3][4]

**Moved obstruction/noncontradiction clause — MATCH.** The negative entry obstructs extending the argument that relies on entrywise nonnegativity of this \(M\); it does not invalidate the algebraic resummation identity or establish failure of nonnegative linearization. The cubic ratio lies outside Theorem 4.1’s affine-ratio hypothesis. [3]

**Exact replacements required: none.**

## Overall verdict: PASS

Sources:
[1] https://raw.githubusercontent.com/skypher/szkraw/4a03165/lean/Szkraw/VRMoves.lean
[2] https://raw.githubusercontent.com/skypher/szkraw/4a03165/lean/Szkraw/OperatorM.lean
[3] https://raw.githubusercontent.com/skypher/szkraw/4a03165/papers/p2.tex
[4] https://raw.githubusercontent.com/skypher/szkraw/4a03165/RESEARCH.md

