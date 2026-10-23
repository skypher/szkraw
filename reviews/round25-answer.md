# PASS WITH MINOR FIXES

**Theorem 8.17 survives the review.** I found no failed certificate or substantive gap in the detours, key inequality, or resummation. There are three false ancillary statements and several wording/boundary clarifications to fix.

## Defects and exact fixes

**1. The asserted cutoff at \(u=1\) is not established.**  
At the stated geometric configuration \((\ell,n)=(0,3)\), my independent expansion gives
\[
\kappa_{r\sigma}=-20q(4q^3+11q^2+9q+1),\qquad
\kappa_{t\tau}=20(q+1)(8q^3+33q^2+30q+6).
\]
The admissible multiplier is therefore bounded by
\[
\frac{\kappa_{t\tau}}{|\kappa_{r\sigma}|}
=1+\frac{\kappa_{r\sigma}+\kappa_{t\tau}}{|\kappa_{r\sigma}|}
\longrightarrow 2,
\]
not \(1\). The printed quotient is correct; its interpretation is wrong.

**Fix:** delete “cannot be pushed past \(r\sigma\le t\tau\)” after the theorem and “that argument stops at \(u=1\)” in Section 10. Replace with: “This geometric family obstructs this coefficientwise test for \(u>2\); it does not establish a cutoff at \(u=1\).” This does **not** prove that the argument works up to \(2\). [1]

**2. The B reduction is not generally concave in \(c\).**  
For the \(rt\)-coefficient at \((\ell,n,q,z)=(0,4,1,0)\), the \(y=c\) reduced polynomial is
\[
120+390c+126c^2-168c^3,
\]
whose second derivative at \(0\) is \(252>0\).

**Fix:** replace the claimed endpoint reduction in both \(y,c\) by:
\[
A\ge0,\qquad A+qG_0\ge0,\qquad
A+G_0c+G_1c^2+G_2c^3\ge0\quad(0\le c\le q).
\]
Concavity in \(y\) gives the two branches; the last cubic is certified over the **whole interval** by Bernstein coefficients. That is what `bdetour_cert.py` actually does.

Also clarify that \(u_{n-1}=1\) normalizes the **second block separately**. Replace “where the two blocks overlap” by “the exceptional low-index cases”: literal overlap continues through \(n=5\) for B and \(n=6\) for E, but the relaxed block argument remains valid there. [1]

**3. The universal \(q\to0\) limit following the \(\Phi_3^{\rm loc}\) bounds is false.**  
In the relaxed local domain, take \(a=3\) and
\[
(u_0,u_1,u_2,u_3)=(1/q,1,q,0).
\]
The displayed closed-form lower bound is
\[
5+9q+3q^2\longrightarrow5,
\]
whereas \(s\binom a2/3=1\).

**Fix:** delete this unused limit sentence, or qualify it as applying to geometric profiles \(u_k=q^{k-1}\), \(k\ge1\). The nonnegativity proof does not need it. [1]

**4. Corner wording:** “only \(\kappa_{t\sigma}\) changes” is literally false: adding \(8\varphi_3(0)\varphi_2(1)\) changes other coefficients too.

**Fix:** write “only \(\kappa_{t\sigma}\) requires a new check; the added quadratic form has nonnegative coefficients.” [1]

**5. Explicitly close the normalization boundary cases.**  
Add before the certificate reductions: “Divisions are initially made for positive entries; zero-tail cases follow by continuity within the local log-concavity constraints, keeping \(u_0=0\) when \(\ell=0\).” No new certificate is required.

## Certificate execution

All assertions passed with SymPy 1.14.0:

| Script | Result |
|---|---|
| `bdetour_cert.py` | `ALL CERTIFIED` — 349 checks |
| `corner_cert.py` | `CERTIFIED` |
| `edetour_cert.py` | `CERTIFIED` — constant 3, 124 checks |
| `phi2loc_cert.py` | `CERTIFIED`; no exact-arithmetic diagnostic violations |
| `phi3loc_cert.py` | `CERTIFIED` — four symbolic polynomial checks; no diagnostic violations |

**Execution qualification:** direct checkout/download was unavailable. I executed locally transcribed operative code from the pinned browser-retrieved sources, not a byte-verified checkout. Comments and unused helper diagnostics were omitted.

The random tests are only diagnostics. The universal assertions come from the symbolic sign/Bernstein checks and the mathematical reductions. For the two local-key certificates, \(n=a\) is handled by the paper’s direct argument, not by the four symbolic families.

## Independent mathematical checks

**Setup and detours.** The cubic Leibniz formula and \(v_n+e_n=\varphi_n-\rho(\ell+n)f_n\) are correct. I independently verified the splitting, the stated \(\Gamma\)-identity, and the B/E coefficient constructors against a separately written Leibniz expansion.

V gives \(9/2\). In E, retaining \(\binom a3\varphi_3\) in \(B_0\) is valid for **every** term: multiplication distributes, so this is not double-counting a limited resource. The factor \((a-2)/3\ge n/3\) and the residual weight \((j-2)(m-1)/j\) give the summed constant \(3\). For B, only \((\ell,m,j)=(0,4,1)\) needs repair; \(2(a-2)\binom a4\ge4\binom a4\) supplies exactly the extra corner term. H and \(C'\) carry over with constants \(10,6\). Thus \(P^2\ge4Q\). [1]

**Polarization and domain coverage.** The use of \(r\sigma\le t\tau\) is legitimate: the scripts establish both \(\kappa_{t\tau}\ge0\) and \(\kappa_{t\tau}+\kappa_{r\sigma}\ge0\). The \(t=\sigma=0\) B part is precisely the inherited quadratic inequality; its three coefficients need not be separately nonnegative. I also checked the inherited polynomial identity and all five discriminant-table rows.

The required end-coefficient signs are checked, and the substitutions \(u_{n-2}\ge1/x\), \(u_{n-3}\ge1/x^2\) have the correct direction. B covers \(n=2,3\) exactly, \(4,5\) separately, and \(n\ge6\) symbolically; E covers \(3,4\) exactly and \(n\ge5\) symbolically. The three \(z\)-regimes cover the domain. Non-affine cases use \(\zeta\in[0,1]\), including tensor Bernstein checks. I found no wrong interval, omitted sign assumption, or unsafe denominator.

**Key inequality (8.13).** All literal \(1\)'s are absorbed into \(\alpha\); monotonicity gives \(\alpha\ge sR_{\ell+a-1}\ge sz\), and its coefficient is at least \(\rho(\ell+1)K\ge0\). The polarized lower bound follows from nonnegative basis contributions to both \(A_0^\psi\)'s. The shifted convexity estimate is valid as printed because actual profiles have \(u_1\le1\); its scale-invariant stronger version contains \(D/u_1\).

The local decompositions agree with the V/E splittings. I independently checked \(\Phi_1=F(z)\), both decomposition identities, and the cubic closed form after subtracting its nonnegative \(DE_1^{\rm loc}\) contribution. The helper named `Phi3loc` computes this **lower bound**, which is sufficient.

The quadratic local certificate independently supports the inherited argument. The cubic lower bound has \(z^2\)-coefficient \(-4sH_*\le0\). Both endpoint coefficient formulas, the shifted terms, and the \(y_2\) balance \(s/3\) check out. The symbolic substitutions cover \(3\le n<a\); at \(n=a\), the potentially negative differences vanish and the remaining terms are nonnegative. [1]

**Resummation and boundaries.** The constants are sufficient, with survivals
\[
1-\frac{2}{9/2}-\frac12=\frac1{18},
\qquad
1-\frac23-\frac14=\frac1{12}.
\]
On \(\ell+a=N\), the last monotonicity increment is still available, and the outward straight weight is \(a_N=0\). Small \(a\) has no offending higher moves. Actual \(u_1=f_1(\ell)\ge\nu_1>0\), so \(u_1=0\) never arises where normalization is used. Zero tails, including \(q=0\), follow by the continuity clarification above; \(\ell=0,z=0\) is explicitly covered. Finally, \(r>0\) ensures \(c_i\ge rd_i>0\). The finite nilpotent-operator argument therefore includes the terminating row and degree sums exceeding \(N\).

## Literature

I found **no earlier statement of this cubic-ratio positivity theorem**. PDF-verified related results include Askey’s Part II maximum principle, Szwarc’s 2003 triangular-matrix criterion, and Miclo’s Theorem 31; none states this Newton-profile/cubic-ratio condition. This is a search conclusion, not a proof of priority. [2]

The coefficient inequality itself is familiar elsewhere: for positive coefficients, \(t\tau>r\sigma\) is the cubic Routh–Hurwitz condition for the **ordinary coefficient-generating polynomial** \(r+tz+\tau z^2+\sigma z^3\), not for the binomial-basis ratio \(\rho(x)\). That observation does not supply the claimed linearization theorem; I verified the criterion in Dey’s PDF, p. 10. [3]

Szwarc’s **Inzell survey: UNVERIFIED**—the PDF fetch repeatedly failed; no conclusion above depends on it.

[Execution logs and independent-check results](sandbox:/mnt/data/szkraw_review/review_checks.txt) · [Reproduction bundle, with provenance notice](sandbox:/mnt/data/szkraw_review_bundle.zip)

Sources:
[1] https://raw.githubusercontent.com/skypher/szkraw/faaa5a0/paper.tex — https://raw.githubusercontent.com/skypher/szkraw/faaa5a0/paper.tex
[2] https://ir.cwi.nl/pub/7741/7741D.pdf
[3] https://arxiv.org/pdf/2501.02375
