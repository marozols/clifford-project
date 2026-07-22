import Verso
import VersoManual
import VersoBlueprint

import CliffordProject.LaTeXMacros
import CliffordProject.Authors
import CliffordProject.Bibliography


/-
    A file aimed at implementing Algebra tools relative to matrices :
    Auto equality check for finite dimension
-/


import Mathlib.Algebra.Ring.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Data.Matrix.Reflection

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Complex.Basic

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

namespace MatrixAlgebraTools

/-
    Finite matrix computation
-/

public theorem MatrixProductRepresentation {R : Type} [Ring R] {m n o : ℕ}
  (M : Matrix (Fin m) (Fin n) R) (N : Matrix (Fin n) (Fin o) R) :
  ∀ i : (Fin m), ∀ k : (Fin o), (M * N) i k = ∑ j : (Fin n), (M i j) * (N j k) :=
  by intro i j; rfl

public theorem MatrixVectorProductRepresentation {R : Type} [Ring R] {m n : ℕ}
  (M : Matrix (Fin m) (Fin n) R) (v : Fin n → R) :
  ∀ i : (Fin m), (M.mulVec v) i = ∑ j : (Fin n), (M i j) * (v j) :=
  by intro i; rfl

macro "matrix_equality" : tactic => `(tactic| ext i j <;> simp <;> rw[MatrixProductRepresentation, MatrixProductRepresentation] <;> apply Complex.ext <;> fin_cases i <;> fin_cases j )


/-
    Tuple to vector coercion
-/


variable {R : Type} [CommRing R]

@[default_instance]
public instance : Coe (R × R) ((Fin 2) → R) where
  coe := fun p => ![p.1, p.2]


@[default_instance]
public instance : Coe ((Fin 2) → R) (R × R) where
  coe := fun f => (f 0, f 1)


/-
    Matrix indexed by (Fin d) extensionality
-/

public def FinBasisVector {d : ℕ} [NeZero d] (i : ZMod d) :
  ZMod d → R := fun k => if (k = i) then 1 else 0
notation "e_" i => FinBasisVector i

public def MatrixFromBasisImage {d : ℕ} [NeZero d]
  (f : (ZMod d) → ((ZMod d) → R)) : Matrix (ZMod d) (ZMod d) R :=
  (Matrix.of f).transpose

omit [CommRing R] in
public theorem FinMatrixBasisExt {d : ℕ} [NeZero d]
  (f1 f2 : (ZMod d) → ((ZMod d) → R)) :
  ((MatrixFromBasisImage f1) = (MatrixFromBasisImage f2)) ↔ (f1 = f2) :=
  by apply Iff.intro; intro h; unfold MatrixFromBasisImage at h; simp at h; apply h; intro h; rw[h]


/-
    Notations
-/

postfix:max "†" => Matrix.conjTranspose

end MatrixAlgebraTools
