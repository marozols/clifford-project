import Verso
import VersoManual
import VersoBlueprint

import Mathlib.Analysis.SpecialFunctions.Complex.Circle

import CliffordProject.LaTeXMacros
import CliffordProject.Authors
import CliffordProject.Bibliography

open Verso.Genre
open Verso.Genre.Manual hiding citep citet citehere
open Informal

#doc (Manual) "Weyl representation" =>

:::group "Weyl_representation"
Weyl representation produces the Clifford group.
:::

As in the previous section, here we also assume that the dimension $`d` is an odd prime.

The following map $`\SL(2,ℤ_d) → \U(d)` that sends $`F` to $`V_F` is known as _Weyl_ or _metaplectic representation_ of $`\SL(2,ℤ_d)`.

:::definition "Weyl_representation_def" (parent := "Weyl_representation") (effort := "small")
Let $`d` be an odd prime.
For any matrix
$`F = \bigl(\begin{smallmatrix} \alpha & \beta \\ \gamma & \delta \end{smallmatrix}\bigr) \in \SL(2,ℤ_d)`,
let
$$`V_{F} = \frac{1}{\sqrt{d}} \sum_{r,s ∈ ℤ_d} \tau^{\beta^{-1} (\alpha s^2 - 2 r s + \delta r^2)} \ket{r} \bra{s}`
where $`\beta^{-1} \in \mathbb{Z}_{d}` is such that $`\beta^{-1} \beta = 1 \pmod{d}`.
:::

The matrix $`V_F` is unitary for all $`F`.
This is part of Lemma 2 of {citet Appleby}[].

:::theorem "Weyl_representation_unitarity" (parent := "Weyl_representation") (effort := "large")
Let $`d` be an odd prime.
For any $`F ∈ \SL(2,ℤ_d)`, the matrix $`V_F` in {uses "Weyl_representation_def"}[] is unitary, i.e.
$`V_F ∈ \U(d)`.
:::

:::proof "Weyl_representation_unitarity"
Given
$`F = \bigl(\begin{smallmatrix} \alpha & \beta \\ \gamma & \delta \end{smallmatrix}\bigr)`,
let
$`X' := D_{\alpha,\gamma}` and
$`Z' := D_{\beta,\delta}`
where $`D_\p` is the displacement operator from {uses "displacement"}[].
Observe from {uses "D_mul"}[] that
$$`\begin{aligned}
Z' X' &= \tau^{\langle(\beta,\delta),(\alpha,\gamma)\rangle} D_{\alpha+\beta,\,\gamma+\delta}, \\
X' Z' &= \tau^{\langle(\alpha,\gamma),(\beta,\delta)\rangle} D_{\alpha+\beta,\,\gamma+\delta}.
\end{aligned}`
Note from {uses "symplectic_inner_product"}[] that
$$`\langle(\beta,\delta),(\alpha,\gamma)\rangle = \alpha\delta - \beta\gamma = \det F = 1.`
Using {uses "symp_antisymmetric"}[],
$`\langle(\alpha,\gamma),(\beta,\delta)\rangle = -1`.
Putting these two observations together:
$$`Z' X'
= \tau D_{\alpha+\beta,\,\gamma+\delta}
= \tau^2 X' Z'.`
Recall from {uses "tau_sq_eq_omega"}[] that $`\omega = \tau^2` so
$$`Z' X' = \omega X' Z'.`

Define
$$`\ket{f_0} := \frac{1}{\sqrt{d}} \sum_{r \in \mathbb{Z}_d} (Z')^r \ket{0}.`
By {uses "D_pow_d_eq_one"}[], $`(Z')^d = I`, so the sum is $`d`-periodic and $`Z' \ket{f_0} = \ket{f_0}`.
Next, define
$$`\ket{f_r} := (X')^r \ket{f_0}`
for all $`r \in \mathbb{Z}_d` and note from $`(X')^d = I` ({uses "D_pow_d_eq_one"}[]) that
$$`X' \ket{f_r} = \ket{f_{r+1}}`
where $`r+1` is computed mod $`d`.
Applying the above commutation relation inductively gives
$$`Z' \ket{f_r} = \omega^r \ket{f_r}`
for all $`r`.

We next find an explicit formula for $`\ket{f_0}`.
By {uses "D_pow_nsmul"}[] and {uses "displacement"}[],
$$`(Z')^r = D_{r\beta,r\delta} = τ^{\beta \delta r^2} X^{r\beta} Z^{r\delta}.`
Note from {uses "Pauli_Z"}[] that $`Z^{r\delta} \ket{0} = \ket{0}` and from {uses "Pauli_X"}[] that $`X^{r\beta} \ket{0} = \ket{r\beta}`, so
$$`(Z')^r \ket{0} = τ^{\beta \delta r^2} X^{r\beta} Z^{r\delta} \ket{0} = \tau^{\beta\delta r^2} X^{r\beta} \ket{0} = \tau^{\beta\delta r^2} \ket{r\beta}.`
Writing $`\tau^{\beta\delta r^2} = \tau^{\beta^{-1}\delta(\beta r)^2}` (which holds since $`\tau^d = 1` from {uses "tau_pow_d_eq_one_of_odd"}[]) and substituting into the defining sum:
$$`\ket{f_0} = \frac{1}{\sqrt{d}} \sum_{r \in \mathbb{Z}_d} \tau^{\beta^{-1}\delta(\beta r)^2} \ket{r\beta}.`
Since $`d` is prime and $`\beta \neq 0`, as $`r` ranges over $`\mathbb{Z}_d` so does $`\beta r`, giving
$$`\ket{f_0} = \frac{1}{\sqrt{d}} \sum_{t \in \mathbb{Z}_d} \tau^{\beta^{-1}\delta t^2} \ket{t}.`

Let us now find a formula for $`\ket{f_r}`, for general $`r`.
Applying {uses "D_pow_nsmul"}[] to $`X' = D_{\alpha,\gamma}` gives $`(X')^r = D_{r\alpha,r\gamma}` (the same calculation as above for $`Z'`), so
$$`\ket{f_r} = (X')^r\ket{f_0} = D_{r\alpha,r\gamma}\ket{f_0}.`
By {uses "displacement"}[], {uses "Pauli_X"}[], and {uses "Pauli_Z"}[], the action on each basis state is $`D_{r\alpha,r\gamma}\ket{s} = \tau^{r^2\alpha\gamma + 2r\gamma s}\ket{s + r\alpha}`.
Substituting into the sum for $`\ket{f_0}`, re-indexing with $`t = s + r\alpha`, and expanding the exponent using $`\alpha\delta - \beta\gamma = 1`:
$$`\ket{f_r} = \frac{1}{\sqrt{d}} \sum_{t \in \mathbb{Z}_d} \tau^{\beta^{-1}(\delta t^2 - 2rt + \alpha r^2)} \ket{t}.`
Comparing with the definition of $`V_F` gives $`V_F = \sum_{r \in \mathbb{Z}_d} \ket{f_r}\bra{r}`, hence $`V_F \ket{r} = \ket{f_r}`.

We now verify that $`\{\ket{f_r}\}_{r \in \mathbb{Z}_d}` is orthonormal.
Since $`\ket{f_r}` and $`\ket{f_s}` are eigenvectors of $`Z'` with distinct eigenvalues $`\omega^r` and $`\omega^s` (which are distinct because $`\omega` has order exactly $`d` as $`d` is prime), we have $`\langle f_r | f_s \rangle = 0` for $`r \neq s`.
Unit norms follow from the explicit formula: $`\braket{f_0 | f_0} = \frac{1}{d}\sum_t |\tau^{\beta^{-1}\delta t^2}|^2 = 1` since $`|\tau| = 1`, and $`\braket{f_r | f_r} = \braket{f_0|(X')^{-r}(X')^r|f_0} = \braket{f_0|f_0} = 1` since $`X'` is unitary.
Hence $`V_F = \sum_{r}\ket{f_r}\bra{r}` is unitary.
:::

:::theorem "Weyl_representation_action" (parent := "Weyl_representation") (effort := "large")
Let $`d` be an odd prime.
The unitary $`V_F` from {uses "Weyl_representation_def"}[] satisfies
$$`V_{F}^{\vphantom{\dagger}} D_{\p}^{\vphantom{\dagger}} V_{F}^{\dagger} = D_{F \p}^{\vphantom{\dagger}}`
for all $`\p ∈ ℤ_d^2`.
In particular, $`V_F \in \Cliff(d)`.
:::

:::proof "Weyl_representation_action"
Continuing with the same notation as before, note that
$`V_F \ket{r} = \ket{f_r}`
and hence
$$`V_F Z V_F^\dagger \ket{f_r} = V_F Z \ket{r} = \omega^r V_F \ket{r} = \omega^r \ket{f_r} = Z' \ket{f_r},`
so $`V_F Z V_F^\dagger = Z'`, and similarly $`V_F X V_F^\dagger = X'`.
Using {uses "displacement"}[], {uses "D_pow_nsmul"}[], and {uses "D_mul"}[]:
$$`\begin{aligned}
V_F D_\p V_F^\dagger
&= \tau^{p_1 p_2}(V_F X V_F^\dagger)^{p_1}(V_F Z V_F^\dagger)^{p_2} \\
&= \tau^{p_1 p_2}(X')^{p_1}(Z')^{p_2} \\
&= \tau^{p_1 p_2} D_{p_1\alpha,p_1\gamma} D_{p_2\beta,p_2\delta}.
\end{aligned}`
Note that
$$`(p_1\alpha,\,p_1\gamma) + (p_2\beta,\,p_2\delta)
= \begin{pmatrix} \alpha & \beta \\ \gamma & \delta \end{pmatrix}
  \begin{pmatrix} p_1 \\ p_2 \end{pmatrix}
= F \p`
and
$$`\langle(p_1\alpha,\,p_1\gamma),(p_2\beta,\,p_2\delta)\rangle = p_1 p_2(\gamma\beta - \alpha\delta) = -p_1 p_2 \det F = -p_1 p_2.`
By {uses "D_mul"}[] and {uses "symplectic_inner_product"}[] we get
$$`V_F D_\p V_F^\dagger = \tau^{p_1 p_2 - p_1 p_2} D_{F\p} = D_{F\p}.`
In particular, $`V_F D_\p V_F^\dagger = D_{F\p}` is a displacement operator for all $`\p \in \mathbb{Z}_d^2`, so $`V_F \in \Cliff(d)` by {uses "Clifford_group"}[].
:::

The following corollary says that the product $`D_{\bchi} V_F` is also a Clifford group element, and describes exactly how it conjugates displacement operators: the matrix part $`F` permutes the displacement operators as before, while the displacement part $`\bchi` contributes an extra symplectic phase $`ω^{\langle \bchi, F\p\rangle}`.

:::corollary "Clifford_structure" (parent := "Weyl_representation") (effort := "small")
Let $`d` be an odd prime,
$`F = \bigl(\begin{smallmatrix} \alpha & \beta \\ \gamma & \delta \end{smallmatrix}\bigr) \in \SL(2,ℤ_d)`
with $`\beta \neq 0`, and let $`\bchi \in ℤ_d^2`.
Define $`U := D_{\bchi} V_F` where $`V_F` is the unitary from {uses "Weyl_representation_def"}[].
Then
$$`U D_{\p} U^{\dagger} = ω^{\langle \bchi,\, F\p \rangle} D_{F\p}`
for all $`\p \in ℤ_d^2`.
In particular, $`U \in \Cliff(d)`.
:::

:::proof "Clifford_structure"
By {uses "Weyl_representation_action"}[], $`V_F D_{\p} V_F^{\dagger} = D_{F\p}`, so
$$`U D_{\p} U^{\dagger} = D_{\bchi} D_{F\p} D_{\bchi}^{\dagger}.`
Using $`D_{\bchi}^{\dagger} = D_{-\bchi}` from {uses "D_conj"}[] and two applications of {uses "D_mul"}[],
$$`D_{\bchi} D_{F\p} D_{-\bchi} = τ^{\langle \bchi,\, F\p\rangle} D_{\bchi+F\p} D_{-\bchi} = \tau^{\langle \bchi,\, F\p\rangle + \langle \bchi+F\p,\, -\bchi\rangle} D_{F\p}.`
By {uses "symp_add_left"}[], {uses "symp_smul_right"}[], {uses "self_eq_zero"}[], and {uses "symp_antisymmetric"}[], the exponent equals
$$`\begin{aligned}
\langle \bchi,\, F\p\rangle + \langle \bchi + F\p,\, -\bchi\rangle
  &= \langle \bchi,\, F\p\rangle + \langle \bchi,\, -\bchi\rangle + \langle F\p,\, -\bchi\rangle \\
  &= \langle \bchi,\, F\p\rangle + 0 + \langle \bchi,\, F\p\rangle \\
  &= 2\langle \bchi,\, F\p\rangle.
\end{aligned}`
Since $`\omega = \tau^2` by {uses "tau_sq_eq_omega"}[],
$$`U D_{\p} U^{\dagger} = \omega^{\langle \bchi,\, F\p\rangle} D_{F\p}.`
As $`D_{F\p}` is a displacement operator (up to a scalar phase), $`U \in \Cliff(d)` according to {uses "Clifford_group"}[].
:::
