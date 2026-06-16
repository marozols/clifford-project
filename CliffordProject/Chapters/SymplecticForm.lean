import Verso
import VersoManual
import VersoBlueprint

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

import CliffordProject.LaTeXMacros
import CliffordProject.Authors
import CliffordProject.Bibliography

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Symplectic form" =>

:::group "symplectic_form"
Basic properties of the symplectic inner product.
:::

Throughout this section we assume that $`d ≥ 1`.

```lean "symplectic_dimension"
variable (d : ℕ) [NeZero d]
```

Below we define the symplectic inner product or symplectic form on $`ℤ_d^2`.

:::definition "symplectic_inner_product" (parent := "symplectic_form") (owner := "Maris_Ozols")
The *symplectic inner product* of $`\p = (p_1, p_2)` and $`\q = (q_1, q_2)` in $`ℤ_d^2` is
$$`\braket{\p,\q} := p_2 q_1 - p_1 q_2.`
:::

```lean "symplectic_inner_product"
def symp {R : Type*} [CommRing R] (p q : R × R) : R :=
  p.2 * q.1 - p.1 * q.2
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
omit [NeZero d] in
lemma symp_antisymmetric (p q : ZMod d × ZMod d) :
    symp p q = - symp q p := by
  unfold symp
  ring
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
lemma self_eq_zero (p : ZMod d × ZMod d) : symp p p = 0 :=
  by unfold symp; ring
```

The symplectic inner product is additive in the first argument.

:::lemma_ "symp_add_left" (parent := "symplectic_form") (effort := "small") (owner := "Daan_Planken")
For all $`\p, \p', \q ∈ ℤ_d^2`,
$$`\braket{\p + \p', \q} = \braket{\p,\q} + \braket{\p',\q}.`
:::

```lean "symp_add_left"
omit [NeZero d] in
lemma symp_add_left
    (p p' q : ZMod d × ZMod d) :
    symp (p + p') q =
    symp p q + symp p' q := by
      unfold symp
      simp
      ring
```

The symplectic inner product is additive in the second argument.

:::lemma_ "symp_add_right" (parent := "symplectic_form") (effort := "small") (owner := "William_Hasley")
For all $`\p, \q, \q' ∈ ℤ_d^2`,
$$`\braket{\p, \q + \q'} = \braket{\p,\q} + \braket{\p,\q'}.`
:::

```lean "symp_add_right"
omit [NeZero d] in
lemma symp_add_right
    (p q q' : ZMod d × ZMod d) :
    symp p (q + q') =
    symp p q + symp p q' :=
      by unfold symp; simp; ring
```

Constants can be pulled out of the first argument.

:::lemma_ "symp_smul_left" (parent := "symplectic_form") (effort := "small") (owner := "William_Hasley")
For all $`c ∈ ℤ_d` and $`\p, \q ∈ ℤ_d^2`,
$$`\braket{c\p, \q} = c\braket{\p,\q}.`
:::

```lean "symp_smul_left"
omit [NeZero d] in
lemma symp_smul_left
    (c : ZMod d) (p q : ZMod d × ZMod d) :
    symp (c • p) q = c * symp p q :=
      by unfold symp; simp; ring
```

Constants can be pulled out of the second argument.

:::lemma_ "symp_smul_right" (parent := "symplectic_form") (effort := "small")  (owner := "William_Hasley")
For all $`c ∈ ℤ_d` and $`\p, \q ∈ ℤ_d^2`,
$$`\braket{\p, c\q} = c\braket{\p,\q}.`
:::

```lean "symp_smul_right"
omit [NeZero d] in
lemma symp_smul_right
    (c : ZMod d) (p q : ZMod d × ZMod d) :
    symp p (c • q) = c * symp p q :=
     by unfold symp; simp; ring
```

If both arguments of the symplectic inner product are transformed by a linear map $`F`, the value gets multiplied by $`\det F`.

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
def pair_apply_mat (F : Matrix (Fin 2) (Fin 2) (ZMod d))
  (p : ZMod d × ZMod d) : ZMod d × ZMod d :=
  (vecForm 0, vecForm 1) where
  vecForm := (Matrix.vecMul (fun i :
    Fin 2 => if i.val = 0 then p.fst else p.snd) F)

lemma pair_apply_mat_alg
  (F : Matrix (Fin 2) (Fin 2) (ZMod d))
  (p : ZMod d × ZMod d) :
  pair_apply_mat d F p = ((F 0 0) * p.1 + (F 1 0) * p.2,
                          (F 0 1) * p.1 + (F 1 1) * p.2)
  := by unfold pair_apply_mat; unfold pair_apply_mat.vecForm; unfold Matrix.vecMul; simp; apply And.intro; ring; ring

lemma symp_det (F : Matrix (Fin 2) (Fin 2) (ZMod d))
  (p q : ZMod d × ZMod d) :
    symp (pair_apply_mat d F p) (pair_apply_mat d F q) =
      Matrix.det F * (symp p q) :=
    by calc
      symp (pair_apply_mat d F p) (pair_apply_mat d F q) =
      symp ((F 0 0) * p.1 + (F 1 0) * p.2,
         (F 0 1) * p.1 + (F 1 1) * p.2)
         ((F 0 0) * q.1 + (F 1 0) * q.2,
         (F 0 1) * q.1 + (F 1 1) * q.2)
         := by unfold pair_apply_mat; unfold pair_apply_mat.vecForm; unfold Matrix.vecMul; simp; ring
      _ = (((F 0 1) * p.1 + (F 1 1) * p.2) *
        ((F 0 0) * q.1 + (F 1 0) * q.2)) -
        (((F 0 1) * q.1 + (F 1 1) * q.2) *
        ((F 0 0) * p.1 + (F 1 0) * p.2))
        := by unfold symp; simp; ring
      _ = ((F 0 0) * (F 1 1) - (F 1 0) * (F 0 1)) *
        (p.2 * q.1 - p.1 * q.2 )
        := by ring
      _ = (Matrix.det F) * (symp p q)
        := by symm; unfold symp; rw [Matrix.det_fin_two]; ring
```

Adjoint property of the symplectic inner product.

:::lemma_ "symp_adjoint" (parent := "symplectic_form") (effort := "medium") (owner := "William_Hasley")
If $`F ∈ \SL(2,ℤ_d)` then
$$`\braket{\p,F\q} \equiv \braket{F^{-1}\p,\q} \pmod{d}`
for all $`\p,\q ∈ ℤ`.
:::

:::proof "symp_adjoint"
Since $`F` is invertible, one can write $`p = FF^{-1}p`. Hence,
$$`\begin{align*}
  \langle p, F q \rangle &= \langle FF^{-1}p , F q \rangle\
  &= (\det F) \langle F^{-1}p, q \rangle\\
  &=\langle F^{-1}p, q \rangle
  \end{align*}
`
:::

```lean "symp_adjoint"
def SpecialLinearInverse
  (F : Matrix.SpecialLinearGroup (Fin 2) (ZMod d))
  : Matrix.SpecialLinearGroup (Fin 2) (ZMod d) :=
    Matrix.SpecialLinearGroup.hasInv.inv F

lemma MatrixMulToDoubleApply
  (F G : Matrix (Fin 2) (Fin 2) (ZMod d))
  (p : ZMod d × ZMod d) :
    pair_apply_mat d F (pair_apply_mat d G p)
    = pair_apply_mat d (F * G) p
  := by rw[pair_apply_mat_alg]; rw[pair_apply_mat_alg]; rw[pair_apply_mat_alg]; simp; apply And.intro; sorry; sorry
    -- Find a way to unfold matrix product

lemma SpecialLinearDet
  (F : Matrix.SpecialLinearGroup (Fin 2) (ZMod d)):
  Matrix.det (CoeFun.coe F) = 1
  := by apply F.prop

lemma FactorByInverse
  (F : Matrix.SpecialLinearGroup (Fin 2) (ZMod d))
  (p : ZMod d × ZMod d) :
  pair_apply_mat d ↑((F * F⁻¹) :
    Matrix.SpecialLinearGroup (Fin 2) (ZMod d)) p = p :=
  by rw[mul_inv_cancel F]; simp; unfold pair_apply_mat;
     unfold pair_apply_mat.vecForm; simp

lemma symp_adjoint
  (F : Matrix.SpecialLinearGroup (Fin 2) (ZMod d))
  (p q : ZMod d × ZMod d) :
  (symp p (pair_apply_mat d F q)) =
    (symp (pair_apply_mat d (SpecialLinearInverse d F) p) q)
  := by calc
  symp p (pair_apply_mat d F q) =
  symp
    (pair_apply_mat d ((F * (SpecialLinearInverse d F))
      : Matrix.SpecialLinearGroup (Fin 2) (ZMod d)) p)
    (pair_apply_mat d F q)
    := by symm; unfold SpecialLinearInverse; rw [FactorByInverse]
  _ = (Matrix.det
        (Matrix.SpecialLinearGroup.instCoeFun.coe F)) *
    symp (pair_apply_mat d (SpecialLinearInverse d F) p) q
    := by rw[Matrix.SpecialLinearGroup.coe_mul]; rw[<- MatrixMulToDoubleApply]; apply symp_det
  _ = symp (pair_apply_mat d (SpecialLinearInverse d F) p) q
    := by rw[SpecialLinearDet]; simp
```
