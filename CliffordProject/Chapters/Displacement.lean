import Verso
import VersoManual
import VersoBlueprint

import CliffordProject.LaTeXMacros
import CliffordProject.Authors
import CliffordProject.Bibliography

import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.ZPow
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.LinearAlgebra.UnitaryGroup

import CliffordProject.Chapters.RootsOfUnity
import CliffordProject.Chapters.Pauli
import CliffordProject.Chapters.SymplecticForm

open Verso.Genre
open Verso.Genre.Manual hiding citep citet citehere
open Informal

#doc (Manual) "Displacement operators" =>

:::group "displacement_core"
Core properties of the single-qudit Pauli group.
:::

This section uses the generalized Pauli $`X` and $`Z` matrices to define the displacement operators $`D_{x,z}`.
These operators effectively constitute the generalized Pauli or Weyl–Heisenberg group on a single quantum system of dimension $`d`.
Unless stated otherwise, we assume that $`d ≥ 1`.

```lean "dimension_again2"
variable (d : ℕ) [NeZero d]
```

We use the generalized Pauli $`X` and $`Z` to define the displacement operators, see Eq. (8) in {citet Appleby}[].

:::definition "displacement" (parent := "displacement_core") (effort := "small") (owner := "Maris_Ozols")
The *displacement operator* corresponding to $`x,z ∈ ℤ` is defined as
$$`D_{x,z} = τ^{xz} X^x Z^z`
where $`τ` comes from {uses "tau"}[], $`X` comes from {uses "Pauli_X"}[], and $`Z` comes from {uses "Pauli_Z"}[].
:::

```lean "displacement"
noncomputable def D
  (p : ℤ × ℤ) : Matrix (ZMod d) (ZMod d) ℂ :=
  (τ d) ^ (p.1 * p.2) • (X d) ^ (p.1) * (Z d) ^ (p.2)
```

Displacement operators behave nicely under complex conjugation, see Eq. (9) in {citet Appleby}[].

:::lemma_ "D_conj" (parent := "displacement_core") (effort := "small")  (owner := "Gina_Muuss")
For all $`x,z ∈ ℤ`,
$$`D_{x,z}^† = D_{-x,-z}`
where $`\dagger` denotes the conjugate transpose.
:::

```lean "D_conj"
lemma conjTranspose_D (p : ℤ × ℤ) :
    (D d p).conjTranspose = D d (-p) := by
    unfold D; simp; sorry
```

Multiplication of displacement operators corresponds to adding their subscripts and introducing a phase given by the symplectic inner product, see Eq. (10) in {citet Appleby}[].

:::lemma_ "D_mul" (parent := "displacement_core") (effort := "small") (owner := "Daan_Planken")
For all $`\p, \q ∈ ℤ^2`,
$$`D_\p D_\q = τ^{\braket{\p,\q}} D_{\p+\q}`
where $`τ` is the root of unity from {uses "tau"}[] and $`\braket{\cdot,\cdot}` is the symplectic inner product from {uses "symplectic_inner_product"}[].
:::

```lean "D_mul"
lemma D_mul (p q : ℤ × ℤ) :
    (D d p) * (D d q) =
    τ d ^ (symp p q) •
    D d (p + q) := by
    unfold D; simp;  sorry
```
The $`n`-th power of a displacement operator is again a displacement operator.

:::lemma_ "D_pow_nsmul" (parent := "displacement_core") (owner := "Joppe_Stokvis")
For all $`\p \in ℤ^2` and $`n \geq 0`,
$$`D_\p^n = D_{n\p}.`
:::

:::proof "D_pow_nsmul"
We proceed by induction on $`n`. The base case $`n = 0` gives $`D_\p^0 = I = D_\mathbf{0}`. For the inductive step, assuming $`D_\p^n = D_{n\p}` we get
$$`D_\p^{n+1} = D_\p^n · D_\p = D_{n\p} \cdot D_\p = \tau^{\langle n\p,\p\rangle} D_{(n+1)\p},`
where the last step used {uses "D_mul"}[].
The result follows since $`\langle n\p,\p\rangle = n \langle\p,\p\rangle = 0` thanks to {uses "self_eq_zero"}[].
:::

```lean "D_pow_nsmul"
lemma D_pow_nsmul (p : ℤ × ℤ) (n : ℕ) :
    D d p ^ n = D d (n • p) := by
    unfold D; simp; sorry
```


If $`d` is odd, adding a multiple of $`d` to the index of a displacement operator does not change it, see Eq. (11) in {citet Appleby}[].

:::lemma_ "D_add_nsmul" (owner := "Carli_Bruinsma")
If $`d` is odd then $`D_{\p+d\q} = D_{\p}` for all $`\p, \q ∈ ℤ^2`.
:::

```lean "D_add_nsmul"
lemma D_add_nsmul (p q : ℤ × ℤ) (hodd : Odd d) :
    D d (p + d • q)
    = D d p := by
  unfold D; simp; sorry
  -- dsimp
  -- rw [Matrix.zpow_add (isUnit_X_det d), Matrix.zpow_mul (X d) (isUnit_X_det d), zpow_natCast, X_pow_d_eq_one d,
  --   Matrix.one_zpow, mul_one, Matrix.zpow_add (isUnit_Z_det d), Matrix.zpow_mul (Z d) (isUnit_Z_det d), zpow_natCast,
  --   Z_pow_d_eq_one, Matrix.one_zpow, mul_one, zpow_mul]
  -- nth_rewrite 2 [zpow_add' (by left; exact (tau_ne_zero d))]
  -- rw [zpow_mul, zpow_natCast, tau_pow_d_eq_one_of_odd d hodd, one_zpow, mul_one, ← zpow_mul, mul_comm, add_comm,
  --   add_mul, zpow_add' (by left; exact (tau_ne_zero d)), mul_assoc, zpow_mul, zpow_natCast,
  --   tau_pow_d_eq_one_of_odd d hodd, one_zpow, one_mul, mul_comm]
```

If $`d` is odd, the index $`\p` of a displacement operator $`D_\p` can be treated modulo $`d`.
In other words, it makes sense to write $`\p \in ℤ_d^2`.

:::lemma_ "D_mod_d" (parent := "displacement_core") (effort := "small") (owner := "William_Hasley")
If $`d` is odd, then for all $`\p \in ℤ^2`,
$$`D_\p = D_{\p \pmod d}.`
:::

:::proof "D_mod_d"
This is a direct consequence of {uses "D_add_nsmul"}[]
:::

```lean "D_mod_d"
@[default_instance]
instance : EuclideanDomain ℤ := Int.euclideanDomain

lemma D_mod_d (p : ℤ × ℤ) (hodd : Odd d):
    D d p = D d ⟨p.1 % d, p.2 % d⟩ :=
    by unfold D; simp; sorry
    /-
    by calc
      D d p.1 p.2 =
      D d (p.1 % d + d * (p.1 / d))
        (p.2 % d + d * (p.2 / d))

      := by rw[EuclideanDomain.mod_add_div p.1];
            rw[EuclideanDomain.mod_add_div p.2]
    _ = D d (p.1 % d) (p.2 % d)
      := D_add_nsmul d (p.1 % d, p.2 % d)
          (p.1 / d, p.2 / d) hodd
    -/
```


The displacement operators have order $`d`.

:::lemma_ "D_pow_d_eq_one" (parent := "displacement_core") (effort := "small") (owner := "William_Hasley")
If $`d` is odd, then for all $`\p \in ℤ^2`,
$$`D_\p^d = I.`
:::

:::proof "D_pow_d_eq_one"
By {uses "D_pow_nsmul"}[], $`D_\p^d = D_{d\p} = D_\mathbf{0} = I`, using $`d\p = \mathbf{0}` in $`ℤ_d^2`.
:::

```lean "D_pow_d_eq_one"
lemma D_pow_d_eq_one (p : ℤ × ℤ) (hOdd : Odd d) :
    D d p ^ d = 1 :=
    by unfold D; simp; sorry
```

Displacement operators with different $`\p` (modulo $`d`) are indeed different.

:::lemma_ "D_p_neq_D_q" (parent := "displacement_core") (effort := "medium") (owner := "Carli_Bruinsma")
Let $`\p,\q \in ℤ^2` and assume $`α,β ∈ ℂ` are both non-zero.
If
$$`α D_\p = β D_\q`
then $`\p \equiv \q \pmod{d}`.
:::

:::proof "D_p_neq_D_q"
This theorem always holds when $`d = 1`.
For $`d > 1`, (to be continues... from the assumption, you work out the matrices, take the diagonal entries at 0 and 1, and find your proof)
:::

```lean "D_p_neq_D_q"
lemma D_p_neq_D_q
    (p q : ℤ × ℤ)
    (α β : ℂ) [NeZero α] [NeZero β] :
    α • (D d p) = β • (D d q) →
    p = q := by
  sorry
```

Displacement operators with phases that are arbitrary powers of $`τ` form a group.

:::definition "Pauli_group" (parent := "displacement_core") (owner := "William_Hasley")
The *generalized Pauli group* or *discrete Weyl–Heisenberg group* consists of
$$`\GP(d) = \{τ^a D_\p : a ∈ ℤ_d, \p ∈ ℤ_d^2\}`
where $`τ` is from {uses "tau"}[] and $`D_\p` is from {uses "displacement"}[].
:::

```lean "Pauli_group"
def pauliGroup (d : ℕ) [NeZero d] :
    Subgroup (Matrix.unitaryGroup (ZMod d) ℂ) where
  carrier := {U | ∃ (a : ℤ) (p : ℤ × ℤ),
    (U : Matrix (ZMod d) (ZMod d) ℂ) =
      (τ d) ^ a • D d p}

  one_mem' := by use 0; use (0,0); simp; unfold D; simp
  mul_mem' := @fun A B A' B' => sorry -- Need 5.30
  inv_mem' := sorry


```

We could have equivalently written
$$`\GP(d) = \{τ^a X^x Z^z : a,x,z ∈ ℤ_d\}`
where $`X` and $`Z` are the generalized Pauli matrices.
The generalized Pauli group $`\GP(d)` modulo its center $`\{\tau^a I : a \in \Z_d\}` is isomorphic to $`ℤ_d^2`.
