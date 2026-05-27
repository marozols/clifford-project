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

The Pauli $`X` matrix has order $`d`.

:::lemma_ "X_pow_d_eq_one" (parent := "Pauli_core")
The $`d`-th power of the $`d`-dimensional Pauli $`X` matrix is the identity matrix:
$$`X^d = I.`
:::

```lean "X_pow_d_eq_one"
lemma X_pow_d_eq_one : X d ^ d = 1 := by
  sorry
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

```lean "Z_pow_d_eq_one"
lemma Z_pow_d_eq_one : (Z d) ^ d = 1 := by
  unfold Z
  have hZ : ∀ (n : ℕ) (i j : ZMod d),
    ((Z d) ^ (n + 1)) i j =
    (if i = j then ω d ^ (i.val * (n + 1)) else 0) := by
    intro n
    induction n with
    | zero =>
      intro i j
      rw [zero_add, pow_one, mul_one]
      rfl
    | succ n hn =>
      intro i j
      rw [pow_succ, Matrix.mul_apply]
      simp_rw [hn]
      have h : ∀ (x : ZMod d), x ≠ j →
          Z d x j = 0 := by
        rintro x hx
        unfold Z
        simp
        intro hx2
        contradiction
      have h2 : ∀ (x : ZMod d), x ≠ j →
          (if i = x then ω d ^ (i.val * (n + 1)) else 0)
          * Z d x j = 0 := by
        rintro x hx
        specialize h x hx
        rw [h, mul_zero]
      rw [Fintype.sum_eq_single j h2]
      simp
      sorry

  ext i j
  have hd1 : 1 ≤ d := NeZero.one_le
  apply Nat.sub_add_cancel at hd1
  symm at hd1

  -- rw [hd1]
  -- apply hZ (d - 1) i j
  sorry



```

Pauli $`X` and $`Z` commute up to a phase.

:::lemma_ "ZX_eq_omega_mul_XZ" (parent := "Pauli_core")
Pauli $`X` and $`Z` matrices satisfy the following commutation relation:
$$`Z X = ω X Z.`
:::

```lean "ZX_eq_omega_mul_XZ"
lemma ZX_eq_omega_mul_XZ :
  Z d * X d = ω d • (X d * Z d) := by
  sorry
```
