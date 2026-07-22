import Verso
import VersoManual
import VersoBlueprint

import CliffordProject.LaTeXMacros
import CliffordProject.Authors
import CliffordProject.Bibliography

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.ZPow
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.ZPow

import CliffordProject.Chapters.RootsOfUnity
import CliffordProject.Chapters.SymplecticForm
import CliffordProject.Tools.MatrixAlgebra

open MatrixAlgebraTools


open Verso.Genre
open Verso.Genre.Manual hiding citep citet citehere
open Informal

#doc (Manual) "Pauli matrices" =>

:::group "Pauli_core"
Core properties of the single-qudit Pauli matrices.
:::

This section defines the generalized Pauli $`X` and $`Z` matrices on $`ℂ^d` and proves some basic fats about them.
Throughout this section we assume that $`d ≥ 1`.

```lean "dimension_again"
variable (d : ℕ) [hd : NeZero d]
```

The generalized Pauli $`X` matrix corresponds to adding one modulo $`d`.
This transformation is defined as the permutation matrix associated to a cyclic permutation of the basis.

```lean "Zmod_shift_equiv"
omit [NeZero d] in
def ZmodShift (i : ZMod d) : (ZMod d) ≃ (ZMod d) :=
  .mk (fun x => x - i) (fun x => x + i)
  (by unfold Function.LeftInverse; intro x; simp)
  (by unfold Function.RightInverse; unfold Function.LeftInverse; intro x; simp)

omit [NeZero d] in
lemma ZmodShiftOne (hd : d = 1) : (ZmodShift d 1) = Equiv.refl (ZMod d)
  := by unfold ZmodShift; rw[hd]; ext x; simp; rw[ZMod.one_eq_zero_iff]

omit [NeZero d] in
lemma ZmodShiftMul (i j : ZMod d) :
  (ZmodShift d i) * (ZmodShift d j) = (ZmodShift d (i + j)) :=
  by ext x; simp; unfold ZmodShift; simp; ring

omit [NeZero d] in
lemma ZmodShiftInv (i : ZMod d) :
  (ZmodShift d i)⁻¹ = (ZmodShift d (- i)) :=
  by ext x; simp; unfold ZmodShift; simp;

omit [NeZero d] in
lemma ZmodShiftInv' (i : ZMod d) :
  (ZmodShift d i).symm = (ZmodShift d (- i)) :=
  by ext x; unfold ZmodShift; simp;
```


:::definition "Pauli_X" (parent := "Pauli_core") (owner := "Maris_Ozols")
The $`d`-dimensional *Pauli $`X` matrix* acts as follows:
$$`X \ket{k} = \ket{k+1}`
where $`k ∈ ℤ_d` and addition is modulo $`d`.
:::

```lean "Pauli_X"
-- NOTE : Permutation matrices are reverted, have to transpose to get the expected result!
-- Hence the definition of ZmodShift that ends up reversed from the expected matrix action
def X : Matrix (ZMod d) (ZMod d) ℂ :=
  (Equiv.Perm.permMatrix ℂ (ZmodShift d 1))
```

Basic properties of $`X`

:::lemma_ "X_one" (parent := "Pauli_core") (effort := "small") (owner := "William_Hasley")
When $`d = 1`, $`X` is the Identity matrix
:::

```lean "X_one"
lemma X_one (hd : d = 1) (n : ℕ) : (X d) ^ n = 1 := by
  unfold X; rw[ZmodShiftOne]; simp; apply hd
```

:::lemma_ "X_inv" (parent := "Pauli_core") (effort := "small") (owner := "William_Hasley")
Let $`M^{\dagger}` denote the usual conjugate transpose of $`M`. Then $`X^{\dagger} = X^{-1}`
:::

```lean "X_inv"
@[simp]
lemma X_inv : (X d)† = (X d)⁻¹ := by
  unfold X; simp; symm; rw[Matrix.inv_eq_left_inv];
  rw[<- Matrix.permMatrix_mul]; simp
```

Powers of the Pauli $`X` matrix.

```lean "X_pow_n"
lemma X_pow_pos_n (n : ℕ) : X d ^ n =
  Equiv.Perm.permMatrix ℂ ((ZmodShift d n)) :=
  by induction n with
  | zero => simp; ext i j; unfold ZmodShift; simp; rfl
  | succ n hind => rw [pow_succ, hind]; unfold X; simp;
                   rw[<- Matrix.permMatrix_mul, ZmodShiftMul, add_comm];
```

The Pauli $`X` matrix has order $`d`.

:::lemma_ "X_pow_d_eq_one" (parent := "Pauli_core")  (owner := "Gina_Muuss")
The $`d`-th power of the $`d`-dimensional Pauli $`X` matrix is the identity matrix:
$$`X^d = I.`
:::

```lean "X_pow_d_eq_one"
@[simp]
lemma X_pow_d_eq_one : X d ^ d = 1 := by
  rw [X_pow_pos_n]; simp; unfold ZmodShift; simp; ext x; simp; rfl
```

```lean "isUnit_X_det"
lemma isUnit_X_det : IsUnit (X d).det := by
  unfold X; rw[Matrix.det_permutation]; simp
```

The generalized Pauli $`Z` matrix is diagonal and introduces a phase $`ω` to each standard basis vector $`\ket{k}`.
This transformation is defined as the Diagonal matrix where the $`i`-th entry is $`\omega^i`

```lean "Z_diag_fun"
omit [NeZero d] in
@[reducible]
noncomputable def diag_omega_pow : (ZMod d → ℂ)ˣ :=
  .mk (fun i => (ω d).val ^ i.val) (fun i => (ω d).val ^ (-i).val)
    (by ext i; simp; rw[<- pow_add, omega_val_pow_n_mod_d d (i.val + (-i).val), <- ZMod.val_add]; simp)
    (by ext i; simp; rw[<- pow_add, omega_val_pow_n_mod_d d ((-i).val + i.val), <- ZMod.val_add]; simp)

@[simp]
lemma diag_omega_pow_inv :
  Ring.inverse (diag_omega_pow d).val = fun i => (ω d).val ^ (-i).val
  := by rw[Ring.inverse_unit]; rfl
```

:::definition "Pauli_Z" (parent := "Pauli_core") (owner := "Maris_Ozols")
The $`d`-dimensional *Pauli $`Z` matrix* acts as follows:
$$`Z \ket{k} = ω^k \ket{k}`
where $`k ∈ ℤ_d` and $`ω` is the primitive $`d`-th root of unity from {uses "omega"}[].
:::


```lean "Pauli_Z"
omit [NeZero d] in
noncomputable def Z : Matrix (ZMod d) (ZMod d) ℂ :=
  Matrix.diagonal (diag_omega_pow d)
```

Basic properties of $`Z`

:::lemma_ "Z_one" (parent := "Pauli_core") (effort := "small") (owner := "William_Hasley")
When $`d = 1`, $`Z` is the Identity matrix
:::

```lean "Z_one"
@[simp]
lemma Z_one (hd : d = 1) : (Z d) = 1 := by
  unfold Z; simp; ext x; rw[omega_one']; simp; apply hd
```
:::lemma_ "Z_inv" (parent := "Pauli_core") (effort := "small") (owner := "William_Hasley")
Much like $`X`, $`Z` is a unitary transformation. That is, $`Z^{\dagger} = Z^{-1}`
:::

``` lean "Z_inv"
@[simp]
lemma Z_inv : (Z d)† = (Z d)⁻¹ := by
  unfold Z; simp; rw[Matrix.inv_diagonal]; simp; intro i;
  rw[diag_omega_pow_inv]
```

The Pauli $`Z` matrix also has order $`d`.

```lean "Z_pow_n"
lemma Z_pow_n (n : ℕ) :
    Z d ^ n = Matrix.diagonal (fun i => (((ω d) ^ (n * i.val)) : ℂ)) :=
  by induction n with
  | zero => simp;
  | succ k ih => rw [pow_succ, ih]; unfold Z; rw[Matrix.diagonal_mul_diagonal]; simp; intro i; ring
```

:::lemma_ "Z_pow_d_eq_one" (parent := "Pauli_core") (owner := "Carli_Bruinsma")
The $`d`-th power of the $`d`-dimensional Pauli $`Z` matrix is the identity matrix:
$$`Z^d = I.`
:::

```lean "Z_pow_d_eq_one"
@[simp]
lemma Z_pow_d_eq_one : (Z d) ^ d = 1 := by
  rw [Z_pow_n]; simp; ext i
  rw [pow_mul, omega_val_pow_d_eq_one, one_pow]
  rfl
```

Pauli $`X` and $`Z` commute up to a phase.

:::lemma_ "ZX_eq_omega_mul_XZ" (parent := "Pauli_core") (owner := "Gina_Muuss")
Pauli $`X` and $`Z` matrices satisfy the following commutation relation:
$$`Z X = ω X Z.`
:::

```lean "ZX_eq_omega_mul_XZ"
lemma ZX_eq_omega_mul_XZ :
  Z d * X d = (ω d).val • (X d * Z d) := by
  ext i j; unfold Z; rw[Matrix.diagonal_mul]; simp; unfold X ZmodShift; simp
  rw[<- pow_succ', ite_eq_iff']; simp; apply And.intro; intro h; rw[h]; simp;
  have h' : i = j + 1 := by rw[<- h]; simp
  rw[h', ZMod.val_add, <- omega_val_pow_n_mod_d]; by_cases hd' : (d = 1)
  · nth_rw 1 [hd']; simp; nth_rw 1 [hd']; simp
  · rw[ZMod.val_one'']; apply hd';
  intro h h'; contradiction
```

And so do their powers.


:::lemma_ "Z_pow_X_pow_eq_omega_mul_X_pow_Z_pow" (parent := "Pauli_core") (owner := "Daan_Planken")
Pauli $`X` and $`Z` matrices satisfy the following commutation relation:
$$`Z^k X^ℓ = ω^{k·ℓ} X^ℓ Z^k.`
:::

```lean "Z_pow_X_pow_eq_omega_mul_X_pow_Z_pow"
lemma ZX_pow_eq_omega_mul_XZ (ℓ : ℕ) :
  Z d * (X d) ^ ℓ = ((ω d).val)^ℓ • ((X d)^ℓ * Z d) :=
  by induction ℓ with
  | zero => simp
  | succ n ih => rw[pow_succ, <- mul_assoc (Z d) (X d ^ n) (X d), ih];
                  rw[Matrix.smul_mul, mul_assoc (X d ^ n) (Z d) (X d)];
                  rw[ZX_eq_omega_mul_XZ]; simp; rw[mul_assoc, smul_smul];
                  rw[<- pow_succ];


lemma Z_pow_X_pow_eq_omega_mul_X_pow_Z_pow (k : ℕ) (ℓ : ℕ) :
  (Z d) ^ k * (X d) ^ ℓ = (ω d).val ^ (k * ℓ) • ((X d) ^ ℓ * (Z d) ^ k)
  := by induction k with
    | zero => simp
    | succ n ih => rw[pow_succ', mul_assoc, ih]; simp;
                   rw[<- mul_assoc, ZX_pow_eq_omega_mul_XZ]; simp;
                   rw[smul_smul, <- pow_add,  add_mul n 1 ℓ]; simp;
                   rw[mul_assoc]
```


And also backwards

```lean "X_pow_Z_pow_eq_omega_mul_Z_pow_X_pow"
lemma X_pow_Z_pow_eq_omega_mul_Z_pow_X_pow (k : ZMod d) (l : ZMod d) :
  (X d) ^ k.val * (Z d) ^ l.val = (ω d) ^ (-(k * l)).val •
  ((Z d) ^ l.val * (X d) ^ k.val) := by
  rw [(Z_pow_X_pow_eq_omega_mul_X_pow_Z_pow d l.val k.val)];
  sorry
  -- simp [smul_smul]
  -- nth_rw 2 [omega_pow_n_mod_d]
  -- rw [← ZMod.val_mul, ← pow_add]
  -- rw [omega_pow_n_mod_d, ← ZMod.val_add]
  -- rw [mul_comm, neg_add_cancel, ZMod.val_zero]
  -- rw [pow_zero, one_smul]
```

:::lemma_ "X_pow_n_mod_d and Z_pow_n_mod_d" (parent := "Pauli_core") (owner := "Carli_Bruinsma")
Powers of Pauli $`X` and $`Z` satisfy
$$`X^n = X^{n \mod d}`
$$`Z^n = Z^{n \mod d}`
:::

```lean "X_pow_n_mod_d and Z_pow_n_mod_d"
theorem X_pow_n_mod_d (n : ℕ): X d ^ n = X d ^ (n % d) :=
  pow_eq_pow_mod n (X_pow_d_eq_one d)

theorem Z_pow_n_mod_d (n : ℕ): Z d ^ n = Z d ^ (n % d) :=
  pow_eq_pow_mod n (Z_pow_d_eq_one d)
```

```lean "X_pow_eq_mod_d"
lemma X_pow_eq_mod_d (x y : ℕ) :
  (x % d = y % d → X d ^ x = X d ^ y ) := by
    intro h
    rw [← Nat.div_add_mod x d ]
    rw [← Nat.div_add_mod y d ]
    rw [pow_add, pow_add, pow_mul, pow_mul]
    rw [X_pow_d_eq_one]
    simp only [one_pow, one_mul]
    congr
```

```lean "X_inv_pow"
lemma X_inv_pow (x : ZMod d) :
  ((X d)^(x.val)).conjTranspose =
  (X d)^((-x).val):= by
  simp; rw[ZMod.neg_val]; by_cases hx : x = 0
  · rw[hx]; simp
  · sorry
-- Matrix.zpow_neg_natCast,
```

```lean "Z_pow_eq_mod_d"
lemma Z_pow_eq_mod_d :  (x: ℕ) → (y: ℕ) →
  (x % d = y % d → Z d ^ x = Z d ^ y ) := by
  -- This is exactly the same proof as for X,
  -- maybe we can consolidate
    intro x y h
    rw [← Nat.div_add_mod x d ]
    rw [← Nat.div_add_mod y d ]
    rw [pow_add, pow_add, pow_mul, pow_mul]
    rw [Z_pow_d_eq_one]
    simp only [one_pow, one_mul]
    congr
```

```lean "Z_inv_pow"
lemma Z_inv_pow : (x: ZMod d) →
  ((Z d)^(x.val)).conjTranspose  =
  (Z d)^((-x).val):= by
  -- This is exactly the same proof as for X,
  -- maybe we can consolidate
  intro x; simp; sorry
  --rw [(Nat.mod_eq_of_lt (ZMod.val_lt (-x)))]
```

```lean "isUnit_Z_det"
lemma isUnit_Z_det : IsUnit (Z d).det := by
  unfold Z; rw[Matrix.det_diagonal]; apply (IsUnit.prod_iff).mpr;
  intro a; simp
```
