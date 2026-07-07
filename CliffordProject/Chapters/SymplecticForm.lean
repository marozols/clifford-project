
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

import CliffordProject.Chapters.RootsOfUnity
import CliffordProject.Tools.MatrixAlgebra

open MatrixAlgebraTools

variable (d : ℕ) [hnezero : NeZero d]
variable {R : Type} [CommRing R]

def symp {R : Type*} [CommRing R] (p q : R × R) : R :=
  p.2 * q.1 - p.1 * q.2

notation "⟨" a "," b "⟩" => symp a b

omit [NeZero d] in
lemma symp_antisymmetric (p q : R × R) :
  ⟨p, q⟩ = - ⟨q, p⟩ := by unfold symp; ring

omit [NeZero d] in
@[simp]
lemma self_eq_zero (p : R × R) : ⟨p, p⟩ = 0 :=
  by unfold symp; ring

omit [NeZero d] in
@[simp]
lemma symp_add_left (p p' q : R × R) :
  ⟨p + p', q⟩ = ⟨p, q⟩ + ⟨p', q⟩  := by unfold symp; simp; ring


omit [NeZero d] in
@[simp]
lemma symp_add_right (p q q' : R × R) :
  ⟨p, (q + q')⟩ = ⟨p, q ⟩ + ⟨p, q'⟩ := by unfold symp; simp; ring

omit [NeZero d] in
@[simp]
lemma symp_smul_left (c : R) (p q : R × R) :
  ⟨(c • p), q⟩ = c * ⟨p, q⟩ := by unfold symp; simp; ring


omit [NeZero d] in
@[simp]
lemma symp_smul_right (c : R) (p q : R × R) :
  ⟨p, (c • q)⟩ = c * ⟨p, q⟩ := by unfold symp; simp; ring

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
