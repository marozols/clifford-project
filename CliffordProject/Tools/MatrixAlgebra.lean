/-
    A file aimed at implementing Algebra tools relative to matrices :
    Auto equality check
-/
module

public import Mathlib.Algebra.Ring.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Data.Matrix.Reflection

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Complex.Basic

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.RingTheory.RootsOfUnity.Complex
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

end MatrixAlgebraTools
