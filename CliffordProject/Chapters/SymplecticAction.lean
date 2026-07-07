import Verso
import VersoManual
import VersoBlueprint

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.LinearAlgebra.SymplecticGroup    -- symplecticGroup, J
import Mathlib.LinearAlgebra.UnitaryGroup       -- Matrix.unitaryGroup
import Mathlib.Data.Matrix.Basic                -- Matrix, transpose, mul
import Mathlib.Data.ZMod.Basic                  -- ZMod d
import Mathlib.Data.Complex.Basic               -- ℂ
import Mathlib.Data.Set.Operations

import CliffordProject.LaTeXMacros
import CliffordProject.Authors
import CliffordProject.Bibliography
import CliffordProject.Chapters.RootsOfUnity
import CliffordProject.Chapters.Pauli
import CliffordProject.Chapters.SymplecticForm
import CliffordProject.Chapters.Displacement
import CliffordProject.Chapters.Clifford

open Verso.Genre
open Verso.Genre.Manual hiding citep citet citehere
open Informal

#doc (Manual) "Symplectic action" =>

:::group "symplectic_action"
Symplectic action of the Clifford group.
:::

The following is adapted from Lemma 1 of {citet Appleby}[].
For simplicity, we assume that the dimension $`d` is an odd prime whereas Appleby's Lemma 1 is more general since it holds for any $`d ≥ 1`.

The result shows that under conjugation any Clifford group element $`U ∈ \Cliff(d)` acts on displacement operators $`D_{\p}` by multiplying their index $`\p ∈ ℤ_d^2` with some matrix $`F ∈ \SL(2,ℤ_d)` and introducing a phase that corresponds to a symplectic inner product with some vector $`\mathbf{χ} ∈ ℤ_d^2` (both $`F` and $`\mathbf{χ}` depend on $`U`).
Here we are dealing with only one quantum system $`ℂ^d`, but for $`n` systems the matrix $`F` would be symplectic: $`F ∈ \Sp(2n,ℤ_d)`.
Note that for $`n = 1` we have $`\SL(2,ℤ_d) = \Sp(2,ℤ_d)`.

:::theorem "clifford_symplectic_action" (parent := "symplectic_action") (effort := "large") (owner := "Carli_Bruinsma")
Let $`d` be an odd prime.
Then for each unitary $`U \in \Cliff(d)` there exists a matrix
$`F \in \SL(2,ℤ_d)` and a vector
$`\bchi \in ℤ_d^2` such that
$$`U D_{\p} U^\dagger = \omega^{\langle \bchi, F\p\rangle} D_{F\p}`
for all $`\p\in\mathbb{Z}^2`,
where $`\omega` is the $`d`-th root of unity from {uses "omega"}[] and $`\braket{\cdot,\cdot}` is the symplectic inner product from {uses "symplectic_inner_product"}[].
:::

:::proof "clifford_symplectic_action"
Since $`U \in \Cliff(d)`, by {uses "Clifford_group"}[] of the Clifford group, there exist functions $`f \colon \mathbb{Z}^2 \to \mathbb{Z}^2` and $`g \colon \mathbb{Z}^2 \to \mathbb{R}` such that
$$`U D_{\p} U^\dagger = e^{ig(\p)} D_{f(\p)}`
for all $`\p \in \mathbb{Z}^2`.
The proof proceeds in three stages:
1. $`f` is additive modulo $`d`,
2. the linear part of $`f` has determinant $`1` modulo $`d`,
3. the phase $`e^{ig(\p)}` must be an inner-product phase $`\omega^{\langle\bchi, F\p\rangle}`.

To show that $`f` is additive modulo $`d`, we compute $`(U D_{\p} U^\dagger)(U D_{\q} U^\dagger)` in two different ways.
On one hand, we first use {uses "Clifford_group"}[] twice and then apply {uses "D_mul"}[] to get
$$`(U D_{\p} U^\dagger)(U D_{\q} U^\dagger)
  = e^{ig(\p)} D_{f(\p)} \cdot e^{ig(\q)} D_{f(\q)}
  = e^{i(g(\p)+g(\q))} \tau^{\langle f(\p),f(\q)\rangle} D_{f(\p)+f(\q)}.`
On the other, we first use $`U^\dagger U = I` and then apply {uses "D_mul"}[] followed by {uses "Clifford_group"}[] to get
$$`U(D_{\p} D_{\q})U^\dagger
  = U(\tau^{\langle \p,\q\rangle} D_{\p+\q})U^\dagger
  = \tau^{\langle \p,\q\rangle} e^{ig(\p+\q)} D_{f(\p+\q)}.`
Equating both expressions gives
$$`e^{i(g(\p)+g(\q))} \tau^{\langle f(\p),f(\q)\rangle} D_{f(\p)+f(\q)} = \tau^{\langle \p,\q\rangle} e^{ig(\p+\q)} D_{f(\p+\q)}.`
Thanks to {uses "D_p_neq_D_q"}[], we can compare the subscripts of $`D` on both sides and get
$$`f(\p+\q) \equiv f(\p)+f(\q) \pmod{d}.`
In other words, $`f` modulo $`d` is an additive map $`\mathbb{Z}_d^2 \to \mathbb{Z}_d^2`.
This means it can be represented by a matrix:
$$`f(\p) = F'\p + d\,h(\p)`
for some integer matrix $`F'` and function $`h \colon \mathbb{Z}^2 \to \mathbb{Z}^2`.
Thanks to {uses "D_add_nsmul"}[] we can drop the second term and write
$`D_{f(\p)} = D_{F'\p}`.
We conclude that $`U` acts on displacement operators by conjugation as
$$`U D_{\p} U^\dagger = e^{ig'(\p)} D_{F'\p}`
for some phase function $`g'`.

Repeating the above argument for $`e^{ig'(\p)} D_{F'\p}` and comparing the phases gives
$$`e^{i(g'(\p+\q) - g'(\p) - g'(\q))} \tau^{\langle \p,\q\rangle - \langle F'\p,F'\q\rangle} = 1.`
Recall from {uses "symp_antisymmetric"}[] that the symplectic inner product $`\braket{\p,\q}` is antisymmetric in
$`\p,\q ∈ ℤ_d^2`.
Since $`g'(\p+\q) - g'(\p) - g'(\q)` is symmetric, swapping $`\p` and $`\q` and then dividing the above with the resulting equation gives
$$`\tau^{2(\langle \p,\q\rangle - \langle F'\p,F'\q\rangle)} = 1`
for all $`\p,\q ∈ ℤ_d^2`.
Using $`\omega = \tau^2` from {uses "tau_sq_eq_omega"}[],
$$`\omega^{\langle \p,\q\rangle - \langle F'\p,F'\q\rangle} = 1.`
Since $`\langle F'\p, F'\q\rangle = (\det F')\langle \p,\q\rangle` by {uses "symp_det"}[], this forces $`\det F' \equiv 1 \pmod{d}`.
Since $`d` is prime, there exists $`F \in \SL(2,\mathbb{Z}_d)` with $`F \equiv F' \pmod{d}`, and $`D_{F\p} = D_{F'\p}` for all $`\p`.

From {uses "D_pow_d_eq_one"}[], we have $`D_{\p}^d = I`.
Conjugating by $`U` gives $`e^{idg'(\p)} D_{F\p}^d = I`, so $`e^{idg'(\p)} = 1`.
Therefore $`e^{ig'(\p)} = \omega^{\tilde{g}(\p)}` for some function $`\tilde{g} \colon \mathbb{Z}^2 \to \mathbb{Z}_d`, and we have
$$`U D_{\p} U^\dagger = \omega^{\tilde{g}(\p)} D_{F\p}.`

Applying the above argument once more gives
$$`\omega^{\tilde{g}(\p+\q) - \tilde{g}(\p) - \tilde{g}(\q)} \tau^{\langle \p,\q\rangle - \langle F\p,F\q\rangle} = 1.`
Since $`F \in \SL(2,\mathbb{Z}_d)`, we have $`\langle F\p,F\q\rangle = (\det F)\langle \p,\q\rangle = \langle \p,\q\rangle` by {uses "symp_det"}[], so $`\tilde{g}(\p+\q) \equiv \tilde{g}(\p)+\tilde{g}(\q) \pmod{d}`.
Any additive function $`\mathbb{Z}^2 \to \mathbb{Z}_d` has the form $`\tilde{g}(\p) = \langle\bchi', \p\rangle` for some fixed $`\bchi' \in \mathbb{Z}_d^2`.
Setting $`\bchi = F\bchi'` and using {uses "symp_adjoint"}[], we conclude that
$$`U D_{\p} U^\dagger = \omega^{\langle\bchi, F\p\rangle} D_{F\p}`
for all $`\p \in \mathbb{Z}^2`.
:::

```lean "clifford_symplectic_action"
variable (d : ℕ) [NeZero d]
open Matrix in
theorem clifford_symplectic_action
    (hodd: Odd d)
    (U : cliffordGroup d) :
    ∃ F : Matrix.symplecticGroup (Fin 1) (ℤ),
    ∃ χ : ℤ × ℤ,
    ∀ p : Fin 1 ⊕ Fin 1 → ℤ,
    U.val.val * (D d (p (Sum.inl 0)) (p (Sum.inl 1)))
      * U.val.val.conjTranspose =
    ω d ^ (symp χ ⟨((F.val *ᵥ p) (Sum.inl 0)),
        ((F.val *ᵥ p) (Sum.inl 1))⟩) •
      D d ((F.val *ᵥ p) (Sum.inl 0))
        ((F.val *ᵥ p) (Sum.inl 1))
    := by
  sorry
  /-
  obtain ⟨U, hU⟩ := U
  have h := cliffordGroupAction d U hU
  specialize h ⟨0, 0⟩
  obtain ⟨f, g, hU⟩ := h
  -- f is additive modulo d
  have hf (p q : ZMod d × ZMod d) :
      (f (p + q)).1 = (f p).1 + (f q).1 ∧
      (f (p + q)).2 = (f p).2 + (f q).2 := by
    sorry
  -- f is equal to some linear map F' + d times some map h
  -- drop the second term when taking displacement operator of f in new form
  sorry
  -/



```
