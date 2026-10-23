### (1) MATCH — `raise_direction`

Using the accepted identities \(w_0\pi_n=w_n\), \(a_n=(N-n)/N\), and \(c_n=rn/N\), the stated velocities are
\[
\delta b_n=(a_n-c_n)w_n-(a_n+c_n)w_0,
\qquad
\delta c_n=c_n(w_0+w_n).
\]
These are the derivatives with respect to **relative mass parameter \(\tau\)**, including both the factor \(w_0\) from \(\varepsilon=\tau w_0\) and the affine-normalization contributions. They match the stated deformation. [1]

The profile involves the actual binomial masses \(w_n\), with the additional \(w_0\) terms arising from normalization—not merely unweighted binomial coefficients. The \(b,c\) coordinates suffice for Definition 9.3; the normalized row-sum identity determines \(\delta a_n=-\delta b_n-\delta c_n\). Allowing \(r=1\) and stating a two-sided derivative do not leave any part of the paper’s \(0<r<1\), positive-\(\tau\) direction uncovered.

### (2) MATCH — `raise_not_uniform`

The statement excludes a single pair \((\beta,\gamma)\) representing the scaled velocities **on any tail \(N\ge N_0\)**, for every size-dependent nonzero scaling \(s_N\). Thus the eventual-size gap identified after round 33 is closed. [1]

The index ranges agree with Definition 9.3. Functions on \(\mathbb R\), rather than \([0,1]\), are harmless because only arguments in \([0,1]\) are sampled. Excluding arbitrary functions also excludes polynomial rules.

The parameter choices correctly cover relative mass, additive mass, and lowering. “Any parametrization” here is qualified by **nonzero first-order speed**; it does not include a zero-speed change such as \(\tau=t^3\). [1]

This establishes non-representability by a uniform rule, not admission itself. It is strong enough for the endpoint consistency remark without asserting that Theorem 9.4 applies at \(r<1\).

### (3) MATCH — restated `direction_not_uniform`

The coefficient expressions are exactly the affine-normalized direction displayed after Proposition 9.8. The statement now excludes every tail and every nonzero size-dependent rescaling. Its signs remain correct: \(s_N=1\) gives additive-mass lowering, and \(s_N=-1\) gives additive-mass raising. [2]

The two formulations are consistent: at \(r=1\), the relative-\(\tau\) raising direction in `raise_direction` is \(-2^{-N}\) times the displayed lowering direction.

### (4) MATCH — table row and quoted paragraph deletion

The new row accurately assigns the fixed-\(r\) direction and mass profile to `raise_direction`, and non-uniformity to `raise_not_uniform`. Deleting the quoted round-33 omission is warranted: that previously missing assertion is now covered. The row does not claim that these two theorems formalize the surrounding radius estimates. [1]

**Overall verdict: PASS. No replacement text is required.**

Sources:
[1] https://raw.githubusercontent.com/skypher/szkraw/ee6b5a6/lean/Szkraw/RaiseDirection.lean
[2] https://raw.githubusercontent.com/skypher/szkraw/ee6b5a6/lean/Szkraw/LambdaN.lean

