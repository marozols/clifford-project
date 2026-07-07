import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.LinearAlgebra.Matrix.Permutation

import CliffordProject.Chapters.RootsOfUnity
import CliffordProject.Chapters.SymplecticForm
import CliffordProject.Tools.MatrixAlgebra

open MatrixAlgebraTools

variable (d : ℕ) [NeZero d]

omit [NeZero d] in
def ZmodShift (i : ZMod d) : (ZMod d) ≃ (ZMod d) :=
  .mk (fun x => x - i) (fun x => x + i)
  (by unfold Function.LeftInverse; intro x; simp)
  (by unfold Function.RightInverse; unfold Function.LeftInverse; intro x; simp)

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

-- NOTE : Permutation matrices are reverted, have to transpose to get the expected result!
-- Hence the definition of ZmodShift that ends up reversed from the expected matrix action
def X : Matrix (ZMod d) (ZMod d) ℂ :=
  (Equiv.Perm.permMatrix ℂ (ZmodShift d 1))


lemma X_pow_pos_n (n : ℕ) : X d ^ n =
  Equiv.Perm.permMatrix ℂ ((ZmodShift d n)) :=
  by induction n with
  | zero => simp; ext i j; unfold ZmodShift; simp; rfl
  | succ n hind => rw [pow_succ, hind]; unfold X; simp;
                   rw[<- Matrix.permMatrix_mul, ZmodShiftMul, add_comm];

@[simp]
lemma X_pow_d_eq_one : X d ^ d = 1 := by
  rw [X_pow_pos_n]; simp; unfold ZmodShift; simp; ext x; simp; rfl


noncomputable def Z : Matrix (ZMod d) (ZMod d) ℂ :=
  Matrix.diagonal (fun i => (ω d) ^ i.val)

-- Matrix.diagonal_mul_diagonal
lemma Z_pow_n (n : ℕ) :
    Z d ^ n = Matrix.diagonal (fun i => (((ω d) ^ (n * i.val)) : ℂ)) :=
  by induction n with
  | zero => simp;
  | succ k ih => rw [pow_succ, ih]; unfold Z; rw[Matrix.diagonal_mul_diagonal]; simp; intro i; ring
--

@[simp]
lemma Z_pow_d_eq_one : (Z d) ^ d = 1 := by
  rw [Z_pow_n]; simp; ext i
  rw [pow_mul, omega_val_pow_d_eq_one, one_pow]
  rfl


lemma ZX_eq_omega_mul_XZ :
  Z d * X d = (ω d).val • (X d * Z d) := by
  ext i j; unfold Z; rw[Matrix.diagonal_mul]; simp; unfold X ZmodShift; simp
  rw[<- pow_succ']; sorry



lemma Z_pow_X_pow_eq_omega_mul_X_pow_Z_pow (k : ℕ) (ℓ : ℕ) :
  (Z d) ^ k * (X d) ^ ℓ = (ω d) ^ (k * ℓ) • ((X d) ^ ℓ * (Z d) ^ k)
  := by induction ℓ with
    | zero => simp
    | succ ℓ ih =>
      nth_rw 1 [pow_succ']
      nth_rw 1 [← mul_assoc]
      have h : Z d ^ k * X d * X d ^ ℓ =
          ω d ^ k • X d * Z d ^ k * X d ^ ℓ := by
        sorry
      rw [h]
      nth_rw 1 [mul_assoc]
      --nth_rw 1 [mul_comm]
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


lemma X_pow_Z_pow_eq_omega_mul_Z_pow_X_pow (k : ZMod d) (l : ZMod d) :
  (X d) ^ k.val * (Z d) ^ l.val = (ω d) ^ (-(k * l)).val •
  ((Z d) ^ l.val * (X d) ^ k.val) := by
  rw [(Z_pow_X_pow_eq_omega_mul_X_pow_Z_pow d l.val k.val)]
  simp [smul_smul]
  nth_rw 2 [omega_pow_n_mod_d]
  rw [← ZMod.val_mul, ← pow_add]
  rw [omega_pow_n_mod_d, ← ZMod.val_add]
  rw [mul_comm, neg_add_cancel, ZMod.val_zero]
  rw [pow_zero, one_smul]



theorem X_pow_n_mod_d (n : ℕ): X d ^ n = X d ^ (n % ↑d) :=
  pow_eq_pow_mod n (X_pow_d_eq_one d)

theorem Z_pow_n_mod_d (n : ℕ): Z d ^ n = Z d ^ (n % ↑d) :=
  pow_eq_pow_mod n (Z_pow_d_eq_one d)


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


lemma X_pow_eq_mod_d :  (x: ℕ) → (y: ℕ) →
  (x % d = y % d → X d ^ x = X d ^ y ) := by
    intro x y h
    rw [← Nat.div_add_mod x d ]
    rw [← Nat.div_add_mod y d ]
    rw [pow_add, pow_add, pow_mul, pow_mul]
    rw [X_pow_d_eq_one]
    simp only [one_pow, one_mul]
    congr

lemma X_inv_pow : (x: ZMod d) →
  ((X d)^(x.val)).conjTranspose  =
  (X d)^((-x).val):= by
  intro x
  rw [Matrix.conjTranspose_pow, X_inv, ← pow_mul]
  apply X_pow_eq_mod_d
  rw [← ZMod.val_mul, neg_mul, one_mul]
  rw [(Nat.mod_eq_of_lt (ZMod.val_lt (-x)))]

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
