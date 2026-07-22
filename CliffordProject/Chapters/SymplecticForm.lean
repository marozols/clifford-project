import Verso
import VersoManual
import VersoBlueprint

import CliffordProject.LaTeXMacros
import CliffordProject.Authors
import CliffordProject.Bibliography


import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

import CliffordProject.Chapters.RootsOfUnity
import CliffordProject.Tools.MatrixAlgebra

open MatrixAlgebraTools

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Symplectic form" =>

:::group "symplectic_form"
Basic properties of the symplectic inner product.
:::


Throughout this section we assume that $`\mathsf{R}` is a commutative Ring.

```lean "symplectic_ring"
variable {R : Type} [CommRing R]
```

Below we define the symplectic inner product or symplectic form on $`\mathsf{R}`.

:::definition "symplectic_inner_product" (parent := "symplectic_form") (owner := "Maris_Ozols")
The *symplectic inner product* of $`\p = (p_1, p_2)` and $`\q = (q_1, q_2)` in $`ℤ_d^2` is
$$`\braket{\p,\q} := p_2 q_1 - p_1 q_2.`
:::

```lean "symplectic_inner_product"
def symp {R : Type*} [CommRing R] (p q : R × R) : R :=
  p.2 * q.1 - p.1 * q.2

notation "⟨" a "," b "⟩" => symp a b
```


The symplectic inner product is antisymmetric.

:::lemma_ "symp_antisymmetric" (parent := "symplectic_form") (effort := "small") (owner := "Maris_Ozols")
For all $`\p,\q ∈ ℤ_d^2`,
$`\braket{\p,\q} = -\braket{\q,\p}.`
:::

:::proof "symp_antisymmetric"
$`\braket{\p,\q} = p_2 q_1 - p_1 q_2 = - (q_2 p_1 - q_1 p_2) = -\braket{\q,\p}.`
:::

```lean "symp_antisymmetric"
lemma symp_antisymmetric (p q : R × R) :
  ⟨p, q⟩ = -⟨q, p⟩ := by unfold symp; ring
```

Every vector is isotropic under the symplectic inner product.

:::lemma_ "self_eq_zero" (parent := "symplectic_form") (effort := "small") (owner := "Joppe_Stokvis")
For any $`\p ∈ ℤ_d^2`,
$`\braket{\p,\p} = 0.`
:::

:::proof "self_eq_zero"
$`\braket{\p,\p} = p_2 p_1 - p_1 p_2 = 0.`
:::


```lean "self_eq_zero"
@[simp]
lemma self_eq_zero (p : R × R) : ⟨p, p⟩ = 0 :=
  by unfold symp; ring
```


The symplectic inner product is additive in the first and second argument.

:::lemma_ "symp_add_left" (parent := "symplectic_form") (effort := "small") (owner := "Daan_Planken")
For all $`\p, \p', \q ∈ ℤ_d^2`,
$$`\braket{\p + \p', \q} = \braket{\p,\q} + \braket{\p',\q}.`
:::

```lean "symp_add_left"
@[simp]
lemma symp_add_left (p p' q : R × R) :
  ⟨p + p', q⟩ = ⟨p, q⟩ + ⟨p', q⟩  := by unfold symp; simp; ring
```


:::lemma_ "symp_add_right" (parent := "symplectic_form") (effort := "small") (owner := "William_Hasley")
For all $`\p, \q, \q' ∈ ℤ_d^2`,
$$`\braket{\p, \q + \q'} = \braket{\p,\q} + \braket{\p,\q'}.`
:::

```lean "symp_add_right"
@[simp]
lemma symp_add_right (p q q' : R × R) :
  ⟨p, (q + q')⟩ = ⟨p, q ⟩ + ⟨p, q'⟩ := by unfold symp; simp; ring
```

Constants can be pulled out of the first and second argument.


:::lemma_ "symp_smul_left" (parent := "symplectic_form") (effort := "small") (owner := "William_Hasley")
For all $`c ∈ ℤ_d` and $`\p, \q ∈ ℤ_d^2`,
$$`\braket{c\p, \q} = c\braket{\p,\q}.`
:::

```lean "symp_smul_left"
@[simp]
lemma symp_smul_left (c : R) (p q : R × R) :
  ⟨(c • p), q⟩ = c * ⟨p, q⟩ := by unfold symp; simp; ring
```


:::lemma_ "symp_smul_right" (parent := "symplectic_form") (effort := "small")  (owner := "William_Hasley")
For all $`c ∈ ℤ_d` and $`\p, \q ∈ ℤ_d^2`,
$$`\braket{\p, c\q} = c\braket{\p,\q}.`
:::

```lean "symp_smul_right"
@[simp]
lemma symp_smul_right (c : R) (p q : R × R) :
  ⟨p, (c • q)⟩ = c * ⟨p, q⟩ := by unfold symp; simp; ring
```

If both arguments of the symplectic inner product are transformed by a linear map $`F`, the value gets multiplied by $`\det F`.
We first rely on the usual coercion between tuples and two-dimensional vectors to define Matrix multiplication over $`\mathsf{R}^2`

```lean "pair_apply_map"
@[simp]
def pair_apply_mat (F : Matrix (Fin 2) (Fin 2) R) (p : R × R) : R × R
  := F.mulVec p

@[simp]
lemma pair_apply_mat_alg
  (F : Matrix (Fin 2) (Fin 2) R)
  (p : R × R) :
  pair_apply_mat F p = ((F 0 0) * p.1 + (F 0 1) * p.2,
                        (F 1 0) * p.1 + (F 1 1) * p.2)
  := by simp; rw[MatrixVectorProductRepresentation];
        simp; rw[MatrixVectorProductRepresentation]; simp
```


:::lemma_ "symp_det" (parent := "symplectic_form") (effort := "medium") (owner := "William_Hasley")
For any matrix $`F \in \mathrm{M}_2(ℤ_d)` and vectors $`\p, \q \in ℤ_d^2`,
$$`\langle F\p, F\q \rangle = (\det F) \langle \p, \q \rangle.`
:::

:::proof "symp_det"
If $`F = \bigl(\begin{smallmatrix} \alpha & \beta \\ \gamma & \delta \end{smallmatrix}\bigr)` and $`\p = (p_1, \, p_2)^T` then
$$`F\p = (\alpha p_1 + \beta p_2, \, \gamma p_1 + \delta p_2)^T.`
After applying $`F` the symplectic inner product evaluates to
$$`\begin{aligned}
\langle F\p, F\q\rangle
  &= (\gamma p_1 + \delta p_2)(\alpha q_1 + \beta q_2) - (\alpha p_1 + \beta p_2)(\gamma q_1 + \delta q_2) \\
  &= (\alpha\delta - \beta\gamma)(p_2 q_1 - p_1 q_2) \\
  &= (\det F)\langle \p, \q\rangle.
\end{aligned}`
:::

```lean "symp_det"
lemma symp_det (F : Matrix (Fin 2) (Fin 2) R)
  (p q : R × R) :
    ⟨(pair_apply_mat F p), (pair_apply_mat F q)⟩ =
      Matrix.det F * ⟨p, q⟩ :=
    by calc
      symp (pair_apply_mat F p) (pair_apply_mat F q) =
      symp ((F 0 0) * p.1 + (F 0 1) * p.2,
         (F 1 0) * p.1 + (F 1 1) * p.2)
         ((F 0 0) * q.1 + (F 0 1) * q.2,
         (F 1 0) * q.1 + (F 1 1) * q.2)
         := by rw[pair_apply_mat_alg, pair_apply_mat_alg];
      _ = (((F 1 0) * p.1 + (F 1 1) * p.2) *
        ((F 0 0) * q.1 + (F 0 1) * q.2)) -
        (((F 1 0) * q.1 + (F 1 1) * q.2) *
        ((F 0 0) * p.1 + (F 0 1) * p.2))
        := by unfold symp; simp; ring
      _ = ((F 0 0) * (F 1 1) - (F 1 0) * (F 0 1)) *
        (p.2 * q.1 - p.1 * q.2 )
        := by ring
      _ = (Matrix.det F) * (symp p q)
        := by symm; unfold symp; rw [Matrix.det_fin_two]; ring
```

Adjoint property of the symplectic inner product.
Properties on matrices of the Special Linear Group

```lean "special_linear_properties"
def SpecialLinearInverse (F : Matrix.SpecialLinearGroup (Fin 2) R)
  : Matrix.SpecialLinearGroup (Fin 2) R := Matrix.SpecialLinearGroup.hasInv.inv F

lemma MatrixMulToDoubleApply
  (F G : Matrix (Fin 2) (Fin 2) R)
  (p : R × R) : pair_apply_mat F (pair_apply_mat G p) = pair_apply_mat (F * G) p
  := by unfold pair_apply_mat; rw[<- Matrix.mulVec_mulVec]; rfl

@[simp]
lemma SpecialLinearDet
  (F : Matrix.SpecialLinearGroup (Fin 2) R):
  Matrix.det (CoeFun.coe F) = 1 := by apply F.prop

lemma FactorByInverse (F : Matrix.SpecialLinearGroup (Fin 2) R)
  (p : R × R) : pair_apply_mat ↑((F * F⁻¹) :
    Matrix.SpecialLinearGroup (Fin 2) R) p = p :=
  by rw[mul_inv_cancel F]; simp
```


:::lemma_ "symp_adjoint" (parent := "symplectic_form") (effort := "medium") (owner := "William_Hasley")
If $`F ∈ \SL(2,ℤ_d)` then
$$`\braket{\p,F\q} \equiv \braket{F^{-1}\p,\q} \pmod{d}`
for all $`\p,\q ∈ ℤ`.
:::

:::proof "symp_adjoint"
Since $`F` is invertible, one can write $`p = FF^{-1}p`. Hence,
$$`\begin{align*}
  \langle p, F q \rangle &= \langle FF^{-1}p , F q \rangle \\
  &= (\det F) \langle F^{-1}p, q \rangle\\
  &=\langle F^{-1}p, q \rangle
  \end{align*}`
:::

```lean "symp_adjoint"
lemma symp_adjoint
  (F : Matrix.SpecialLinearGroup (Fin 2) R)
  (p q : R × R) :
  (⟨p, (pair_apply_mat F q)⟩) =
    (⟨(pair_apply_mat (SpecialLinearInverse F) p), q⟩)
  := by calc
  ⟨p, (pair_apply_mat F q)⟩ =
  ⟨ (pair_apply_mat ((F * (SpecialLinearInverse F))
      : Matrix.SpecialLinearGroup (Fin 2) R) p)
    , (pair_apply_mat  F q)⟩
    := by symm; unfold SpecialLinearInverse; rw [FactorByInverse]
  _ = (Matrix.det
        (Matrix.SpecialLinearGroup.instCoeFun.coe F)) *
    symp (pair_apply_mat (SpecialLinearInverse F) p) q
    := by rw[Matrix.SpecialLinearGroup.coe_mul]; rw[<- MatrixMulToDoubleApply]; apply symp_det
  _ = symp (pair_apply_mat (SpecialLinearInverse F) p) q
    := by rw[SpecialLinearDet]; simp
```
