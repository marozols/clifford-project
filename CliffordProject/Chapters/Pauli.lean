import Verso
import VersoManual
import VersoBlueprint

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

import CliffordProject.LaTeXMacros
import CliffordProject.Authors
import CliffordProject.Bibliography
import CliffordProject.Chapters.RootsOfUnity
import CliffordProject.Chapters.SymplecticForm

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
variable (d : ℕ) [NeZero d]
```

The generalized Pauli $`X` matrix corresponds to adding one modulo $`d`.

:::definition "Pauli_X" (parent := "Pauli_core") (owner := "Maris_Ozols")
The $`d`-dimensional *Pauli $`X` matrix* acts as follows:
$$`X \ket{k} = \ket{k+1}`
where $`k ∈ ℤ_d` and addition is modulo $`d`.
:::

```lean "Pauli_X"
def X : Matrix (ZMod d) (ZMod d) ℂ :=
  Matrix.of fun i j => if j + 1 = i then 1 else 0
```

Powers of the Pauli $`X` matrix.

:::lemma_ "X_pow_n" (parent := "Pauli_core") (owner := "Carli_Bruinsma")
The $`n`-th power of the $`d`-dimensional Pauli $`X` matrix acts on basis vectors as
$$`X^n \ket{k} = \ket{k + n \mod d}.`
:::

```lean "X_pow_n"
lemma X_pow_pos_n (n : ℕ) : X d ^ n =
    Matrix.of (fun i j => if j + (n : ZMod d) = i then 1
    else 0) := by
  induction n with
  | zero =>
    ext i j
    have hij : i = j ↔ j = i := ⟨Eq.symm, Eq.symm⟩
    simp [pow_zero, Matrix.one_apply, hij]
  | succ n hind =>
    ext i j
    rw [pow_succ, hind, Matrix.mul_apply]
    have hfun : ∀ (x : ZMod d), x ≠ (j + (1 : ZMod d)) →
        X d x j = 0 := by
      unfold X
      intro x h
      simp
      by_contra h'
      symm at h'
      contradiction
    have hfun'  : ∀ (x : ZMod d), x ≠ (j + (1 : ZMod d)) →
        Matrix.of (fun i j => if j + (n : ZMod d) = i
        then 1 else 0) i x * X d x j = 0 := by
        intro x h
        specialize hfun x h
        rw [hfun, mul_zero]
    rw [Fintype.sum_eq_single (j + 1) hfun']
    by_cases h : j + ((n + 1) : ZMod d) = i <;>
      simp [h];
      rw [add_comm (n : ZMod d), ← add_assoc] at h;
      simp [h, X]
    intro hj
    rw [add_assoc, add_comm 1] at hj
    contradiction
```

The Pauli $`X` matrix has order $`d`.

:::lemma_ "X_pow_d_eq_one" (parent := "Pauli_core")  (owner := "Gina_Muuss")
The $`d`-th power of the $`d`-dimensional Pauli $`X` matrix is the identity matrix:
$$`X^d = I.`
:::

```lean "X_pow_d_eq_one"
lemma X_pow_d_eq_one : X d ^ d = 1 := by
  rw [X_pow_pos_n]
  ext i j
  simp only [CharP.cast_eq_zero, add_zero, Matrix.of_apply]
  simp only [eq_comm]
  rfl
```

The generalized Pauli $`Z` matrix is diagonal and introduces a phase $`ω` to each standard basis vector $`\ket{k}`.

:::definition "Pauli_Z" (parent := "Pauli_core") (owner := "Maris_Ozols")
The $`d`-dimensional *Pauli $`Z` matrix* acts as follows:
$$`Z \ket{k} = ω^k \ket{k}`
where $`k ∈ ℤ_d` and $`ω` is the primitive $`d`-th root of unity from {uses "omega"}[].
:::

```lean "Pauli_Z"
noncomputable def Z : Matrix (ZMod d) (ZMod d) ℂ :=
  Matrix.of fun i j => if i = j then ω d ^ i.val else 0
```

The Pauli $`Z` matrix also has order $`d`.

:::lemma_ "Z_pow_d_eq_one" (parent := "Pauli_core") (owner := "Carli_Bruinsma")
The $`d`-th power of the $`d`-dimensional Pauli $`Z` matrix is the identity matrix:
$$`Z^d = I.`
:::

```lean "Z_pow_n"
lemma Z_pow_n (n : ℕ) :
    Z d ^ n = Matrix.diagonal
    (fun i => ω d ^ (i.val * n)):= by
  have hdiag : (Z d) =
    Matrix.diagonal (fun i => ω d ^ i.val) := rfl
  rw [hdiag, Matrix.diagonal_pow]
  simp
  intro i
  rw [← pow_mul]
```

```lean "Z_pow_d_eq_one"
lemma Z_pow_d_eq_one : (Z d) ^ d = 1 := by
  rw [Z_pow_n]
  simp
  ext i
  rw [mul_comm, pow_mul, omega_pow_d_eq_one, one_pow]
  rfl
```

Pauli $`X` and $`Z` commute up to a phase.

:::lemma_ "ZX_eq_omega_mul_XZ" (parent := "Pauli_core") (owner := "Gina_Muuss")
Pauli $`X` and $`Z` matrices satisfy the following commutation relation:
$$`Z X = ω X Z.`
:::

```lean "ZX_eq_omega_mul_XZ"

lemma ZX_eq_omega_mul_XZ :
  Z d * X d = ω d • (X d * Z d) := by
  ext i j
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.mul_apply]
  unfold X Z
  simp only [Matrix.of_apply, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    ↓reduceIte, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', smul_eq_mul]
  simp only [eq_comm]
  by_cases h : i = j + 1
  /- Case 1: h : i = j + 1-/
  . rw [if_pos h, if_pos h, h, ← pow_succ', ZMod.val_add,
    (omega_pow_k_mod_d_eq_pow_k d (j.val + 1)),
    ZMod.val_one_eq_one_mod, Nat.add_mod_mod]
  /- Case 2: h : i ≠ j + 1-/
  rw [if_neg h, if_neg h]

```


```lean "X_pow_n_mod_d"
theorem X_pow_n_mod_d (n : ℕ): X d ^ n = X d ^ (n % ↑d) :=
  pow_eq_pow_mod n (X_pow_d_eq_one d)
```

```lean "Z_pow_n_mod_d"
theorem Z_pow_n_mod_d (n : ℕ): Z d ^ n = Z d ^ (n % ↑d) :=
  pow_eq_pow_mod n (Z_pow_d_eq_one d)
```
