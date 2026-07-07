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
    (omega_pow_n_mod_d d (j.val + 1)),
    ZMod.val_one_eq_one_mod, Nat.add_mod_mod]
  /- Case 2: h : i ≠ j + 1-/
  rw [if_neg h, if_neg h]

```


And so do their powers.

:::lemma_ "Z_pow_X_pow_eq_omega_mul_X_pow_Z_pow" (parent := "Pauli_core") (owner := "Daan_Planken")
Pauli $`X` and $`Z` matrices satisfy the following commutation relation:
$$`Z^k X^ℓ = ω^{k·ℓ} X^ℓ Z^k.`
:::

```lean "Z_pow_X_pow_eq_omega_mul_X_pow_Z_pow"
lemma Z_pow_X_pow_eq_omega_mul_X_pow_Z_pow (k : ZMod d) (ℓ : ZMod d) :
  (Z d) ^ k.val * (X d) ^ ℓ.val = (ω d) ^ (k.val * ℓ.val) •
  ((X d) ^ ℓ.val * (Z d) ^ k.val) := by
    induction ℓ.val with
    | zero => simp
    | succ ℓ ih =>
      nth_rw 1 [pow_succ']
      nth_rw 1 [← mul_assoc]
      have h (m : ℕ) (n : ℕ) : Z d ^ m * X d * X d ^ n =  ω d ^ m • X d * Z d ^ m * X d ^ n := by
        induction m with
        | zero => simp
        | succ m ih2 =>
          nth_rw 1 [pow_succ']
          nth_rw 1 [mul_assoc]
          nth_rw 1 [mul_assoc]
          nth_rw 2 [← mul_assoc]
          rw [ih2]
          simp
          nth_rw 1 [← mul_assoc]
          nth_rw 1 [← mul_assoc]
          rw [ZX_eq_omega_mul_XZ]
          simp
          nth_rw 2 [mul_assoc]
          rw [← pow_succ']
          rw [smul_smul]
          rw [← pow_succ]

      rw [h]
      nth_rw 1 [mul_assoc]
      rw [Matrix.smul_mul]
      rw [← Matrix.mul_smul]
      rw [ih]
      rw [smul_smul]
      simp
      rw [← pow_add]
      rw [← mul_one_add]
      rw [← mul_assoc]
      rw [← pow_succ']
      rw [add_comm]

```

And also backwards

```lean "X_pow_Z_pow_eq_omega_mul_Z_pow_X_pow"
lemma X_pow_Z_pow_eq_omega_mul_Z_pow_X_pow (k : ZMod d) (l : ZMod d) :
  (X d) ^ k.val * (Z d) ^ l.val = (ω d) ^ (-(k * l)).val •
  ((Z d) ^ l.val * (X d) ^ k.val) := by
  rw [(Z_pow_X_pow_eq_omega_mul_X_pow_Z_pow d l k)]
  simp [smul_smul]
  nth_rw 2 [omega_pow_n_mod_d]
  rw [← ZMod.val_mul, ← pow_add]
  rw [omega_pow_n_mod_d, ← ZMod.val_add]
  rw [mul_comm, neg_add_cancel, ZMod.val_zero]
  rw [pow_zero, one_smul]
```

```lean "X_pow_Z_pow_eq_omega_mul_Z_pow_X_pow_int"
lemma X_pow_Z_pow_eq_omega_mul_Z_pow_X_pow_int (k : ℤ) (l : ℤ) :
  (X d) ^ (l : ZMod d).val * (Z d) ^ (k : ZMod d).val =
  (ω d) ^ (-(k * l)) •
  ((Z d) ^ (k : ZMod d).val * (X d) ^ (l : ZMod d).val) := by
  rw [(Z_pow_X_pow_eq_omega_mul_X_pow_Z_pow d (k : ZMod d) (l : ZMod d) )]
  rw [smul_smul, ← zpow_natCast]
  nth_rw 1 [omega_pow_k_mod_d_eq_pow_k_zmod]
  rw [← zpow_natCast]
  rw [ ← (zpow_add₀ (omega_ne_zero d))]
  rw [← Nat.cast_add]
  rw [omega_pow_k_mod_d_eq_pow_k_int]
  rw [← Int.natCast_emod]
  rw [Nat.add_mod]
  rw [← ZMod.val_mul]
  simp only [Int.cast_neg, Int.cast_mul, Nat.mod_add_mod, Int.natCast_emod, Nat.cast_add]
  rw [← Nat.cast_add]
  rw [← omega_pow_k_mod_d_eq_pow_k_int]
  rw [zpow_natCast]
  rw [omega_pow_n_mod_d]

  rw [← ZMod.val_add]
  simp only [neg_add_cancel, ZMod.val_zero, pow_zero, one_smul]

```

:::lemma_ "X_pow_n_mod_d and Z_pow_n_mod_d" (parent := "Pauli_core") (owner := "Carli_Bruinsma")
Powers of Pauli $`X` and $`Z` satisfy
$$`X^n = X^{n \mod d}`
$$`Z^n = Z^{n \mod d}`
:::

```lean "X_pow_n_mod_d and Z_pow_n_mod_d"
theorem X_pow_n_mod_d (n : ℕ): X d ^ n = X d ^ (n % ↑d) :=
  pow_eq_pow_mod n (X_pow_d_eq_one d)

theorem Z_pow_n_mod_d (n : ℕ): Z d ^ n = Z d ^ (n % ↑d) :=
  pow_eq_pow_mod n (Z_pow_d_eq_one d)
```


:::lemma_ "X_dagger" (parent := "Pauli_core") (owner := "Gina_Muuss")
$$`X^{†} = X^(-1).`
:::


```lean "X_dagger"
lemma X_inv : (X d).conjTranspose  =
(X d)^((-1 : ZMod d).val) := by
  ext i j
  rw [X_pow_pos_n]
  rw [Matrix.conjTranspose_apply]
  unfold X
  simp
  have hfalso: (k: ZMod d) →
    k + 1 + ↑((-1 : ℤ) % d).toNat = k := by
      intro k
      have h3 : 0 ≤ ((-1 : ℤ) % d) := by
        apply Int.emod_nonneg
        apply (Int.natCast_ne_zero.2 (NeZero.ne d))
      rw [ZMod.natCast_toNat d h3]
      simp only [Int.reduceNeg, ZMod.intCast_mod,
      Int.cast_neg, Int.cast_one, add_neg_cancel_right]
  split_ifs with h1 h2 h2; rfl
  . exfalso
    rw [← h1] at h2
    simp only [add_neg_cancel_right,
      not_true_eq_false] at h2
  . exfalso
    rw [← h2, add_assoc] at h1
    nth_rw 2 [add_comm] at h1
    rw [← add_assoc] at h1
    simp only [add_neg_cancel_right,
      not_true_eq_false] at h1
  . rfl

```

```lean "X_pow_eq_mod_d"
lemma X_pow_eq_mod_d :  (x: ℕ) → (y: ℕ) →
  (x % d = y % d → X d ^ x = X d ^ y ) := by
    intro x y h
    rw [← Nat.div_add_mod x d ]
    rw [← Nat.div_add_mod y d ]
    rw [pow_add, pow_add, pow_mul, pow_mul]
    rw [X_pow_d_eq_one]
    simp only [one_pow, one_mul]
    congr
```

```lean "X_inv_pow"
lemma X_inv_pow : (x: ZMod d) →
  ((X d)^(x.val)).conjTranspose  =
  (X d)^((-x).val):= by
  intro x
  rw [Matrix.conjTranspose_pow, X_inv, ← pow_mul]
  apply X_pow_eq_mod_d
  rw [← ZMod.val_mul, neg_mul, one_mul]
  rw [(Nat.mod_eq_of_lt (ZMod.val_lt (-x)))]
```


```lean "Z_inv"
lemma Z_inv : (Z d).conjTranspose  =
(Z d)^((-1 : ZMod d).val) := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  have hdiag : (Z d) =
    Matrix.diagonal (fun i => ω d ^ i.val) := rfl
  rw [hdiag, Matrix.diagonal_pow,
    Matrix.diagonal_apply,
    Matrix.diagonal_apply]
  simp only [RCLike.star_def, Pi.pow_apply]
  split_ifs with h1 h2 h2
  . rw [h1]
    simp
    rw [← pow_mul, mul_comm, pow_mul]
    have homega :
      (starRingEnd ℂ ) (ω d) = ω d ^ (-1 : ℤ) := by
      unfold ω
      rw [← Complex.exp_conj, ← Complex.exp_int_mul]
      rw [starRingEnd_apply]
      simp
      rw [neg_div]
    rw [homega, omega_pow_k_mod_d_eq_pow_k_zmod]
    congr
    simp only [Int.reduceNeg, Int.cast_neg, Int.cast_one]
  . exfalso
    exact (h2 h1.symm)
  . exfalso
    exact (h1 h2.symm)
  simp only [map_zero]
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
  intro x
  rw [Matrix.conjTranspose_pow, Z_inv, ← pow_mul]
  apply Z_pow_eq_mod_d
  rw [← ZMod.val_mul, neg_mul, one_mul]
  rw [(Nat.mod_eq_of_lt (ZMod.val_lt (-x)))]
```
