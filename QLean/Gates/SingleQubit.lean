/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
import QLean.Gates.FullRegister.Embeddings
import QLean.Gates.FullRegister.Hadamard
import QLean.Tactic.MatrixCompute

/-!
# Standard Finite-Dimensional Gates

This file contains the small matrix gates used throughout the examples. Full-register
embeddings and basis-indexed matrix constructions live in `Gates/FullRegister.lean`.
-/

namespace QLean

noncomputable section

open scoped Matrix ComplexOrder
open Matrix Complex

/-! ## Single- and two-qubit operators -/

/-- Single-qubit operator (2x2 complex matrix). -/
abbrev Qubit.Op := Operator 2

/-- Two-qubit operator (4x4 complex matrix). -/
abbrev TwoQubit.Op := Operator 4

/-! ## Standard gate matrices -/

namespace Gate

/-- View a `Fin 2` bit as the corresponding one-qubit full-register basis index. -/
private def singleQubitIndex (b : Fin 2) : Q[1] :=
  fun _ => b

private def singleQubitIndexEquiv : Q[1] ≃ Fin 2 where
  toFun x := x 0
  invFun := singleQubitIndex
  left_inv x := by
    funext i
    fin_cases i
    rfl
  right_inv b := rfl

/-- The Pauli-X (NOT) gate: `X = [[0,1],[1,0]]`. -/
def X : Qubit.Op :=
  !![0, 1; 1, 0]

/-- The Pauli-Y gate: `Y = [[0, -i],[i, 0]]`. -/
def Y : Qubit.Op :=
  !![0, -I; I, 0]

/-- The Pauli-Z gate: `Z = [[1, 0],[0, -1]]`. -/
def Z : Qubit.Op :=
  !![1, 0; 0, -1]

/-- The Hadamard gate: `H = (1 / sqrt 2) [[1, 1], [1, -1]]`. -/
def H : Qubit.Op :=
  Matrix.reindex singleQubitIndexEquiv singleQubitIndexEquiv (QMat.hadamardLayer 1)

@[simp]
theorem H_apply (i j : Fin 2) :
    H i j = (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) *
      (if i = (1 : Fin 2) ∧ j = (1 : Fin 2) then (-1 : ℂ) else 1) := by
  fin_cases i <;> fin_cases j <;>
    norm_num [H, singleQubitIndexEquiv, singleQubitIndex, QMat.hadamardLayer,
      QMat.hadamardAmplitude, QIndex.bitDotMod2, QIndex.bitVal]

/-- The phase gate: `S = [[1, 0], [0, i]]`. -/
def S : Qubit.Op :=
  !![1, 0; 0, I]

/-- The T gate: `T = [[1, 0], [0, exp(i*pi/4)]]`. -/
def T : Qubit.Op :=
  !![1, 0; 0, Complex.exp (I * ↑(Real.pi / 4))]

/-- Phase rotation `diag(1, exp(i*theta))`. -/
def phaseRotation (θ : ℝ) : Qubit.Op :=
  Matrix.of fun i j =>
    if i = j then
      if i = (1 : Fin 2) then Complex.exp (Complex.I * (θ : ℂ)) else 1
    else
      0

/-- The CNOT gate on two qubits. -/
def CNOT : TwoQubit.Op :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 0, 1;
     0, 0, 1, 0]

/-! ## Gate facts -/

theorem X_unitary : Operator.IsUnitary X := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Gate.X]
  · norm_num [Matrix.mul_apply, dotProduct]
  · norm_num [Matrix.mul_apply, Fin.sum_univ_succ]
  · norm_num [Matrix.mul_apply, Fin.sum_univ_succ]
  · norm_num [Matrix.mul_apply]

theorem Y_unitary : Operator.IsUnitary Y := by
  unfold Operator.IsUnitary Y
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Complex.ext_iff]

theorem Z_unitary : Operator.IsUnitary Z := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Gate.Z]
  · norm_num [Matrix.mul_apply]
  · norm_num [Matrix.mul_apply, Fin.sum_univ_succ]
  · norm_num [Matrix.mul_apply]
  · norm_num [Matrix.mul_apply]

theorem H_unitary : Operator.IsUnitary H := by
  have h := congr_arg (Matrix.reindexAlgEquiv ℂ ℂ singleQubitIndexEquiv)
    (QMat.hadamardLayer_unitary 1).1
  simpa [Operator.IsUnitary, H, Matrix.conjTranspose_reindex] using h

theorem S_unitary : Operator.IsUnitary S := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Gate.S]
  · norm_num [Matrix.mul_apply, Complex.ext_iff]
  · norm_num [Matrix.mul_apply, Complex.ext_iff]
  · norm_num [Matrix.mul_apply, Complex.ext_iff]
  · norm_num [Matrix.mul_apply, Complex.ext_iff]

private theorem phase_exp_unit (θ : ℝ) :
    (starRingEnd ℂ) (Complex.exp (Complex.I * (θ : ℂ))) *
        Complex.exp (Complex.I * (θ : ℂ)) = 1 := by
  change star (Complex.exp (Complex.I * (θ : ℂ))) *
      Complex.exp (Complex.I * (θ : ℂ)) = 1
  rw [Complex.star_def]
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
    Complex.norm_exp_I_mul_ofReal]
  norm_num

private theorem t_phase_exp_unit :
    (starRingEnd ℂ) (Complex.exp (Complex.I * ((Real.pi : ℂ) / 4))) *
        Complex.exp (Complex.I * ((Real.pi : ℂ) / 4)) = 1 := by
  simpa [Complex.ofReal_div] using phase_exp_unit (Real.pi / 4)

theorem T_unitary : Operator.IsUnitary T := by
  unfold Operator.IsUnitary T
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, t_phase_exp_unit]

theorem phaseRotation_unitary (θ : ℝ) : Operator.IsUnitary (phaseRotation θ) := by
  unfold Operator.IsUnitary
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [phaseRotation, Matrix.mul_apply, phase_exp_unit]

theorem CNOT_unitary : Operator.IsUnitary CNOT := by
  unfold Operator.IsUnitary CNOT
  simp only [MatrixCompute.matrixMul, MatrixCompute.matrixMulReflect]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Complex.ext_iff]

theorem X_hermitian : X.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Gate.X]

theorem Y_hermitian : Y.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Gate.Y]

theorem Z_hermitian : Z.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Gate.Z]

/-- Pauli X is an involution: `X^2 = I`. -/
theorem X_squared : X * X = (1 : Qubit.Op) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Gate.X, Matrix.mul_apply]

/-- Pauli Z is an involution: `Z^2 = I`. -/
theorem Z_squared : Z * Z = (1 : Qubit.Op) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Gate.Z]

/-- Hadamard is an involution: `H^2 = I`. -/
theorem H_squared : H * H = (1 : Qubit.Op) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Gate.H, singleQubitIndexEquiv, singleQubitIndex, QMat.hadamardLayer,
      QMat.hadamardAmplitude, QIndex.bitDotMod2, QIndex.bitVal, Matrix.mul_apply,
      Complex.ext_iff] <;>
    ring_nf <;>
    norm_num

/-- `X |0>` = `|1>`. -/
theorem X_ket0 :
    Operator.applyToState X (QState.basis 2 0) = QState.basis 2 1 := by
  ext i
  simp only [Operator.applyToState, Gate.X, QState.basis, MatrixCompute.matrixVecMul,
    MatrixCompute.matrixVecMulReflect]
  fin_cases i <;> norm_num [Complex.ext_iff]

/-- `X |1>` = `|0>`. -/
theorem X_ket1 :
    Operator.applyToState X (QState.basis 2 1) = QState.basis 2 0 := by
  ext i
  simp only [Operator.applyToState, Gate.X, QState.basis, MatrixCompute.matrixVecMul,
    MatrixCompute.matrixVecMulReflect]
  fin_cases i <;> norm_num [Complex.ext_iff]

end Gate

namespace QMat

/-! ## Embedded named one-qubit gates -/

/-- Hadamard embedded on one target qubit of an `n`-qubit register. -/
def H (n : ℕ) (q : Fin n) : QMat n :=
  QMat.applySingle q Gate.H

/-- Pauli-X embedded on one target qubit of an `n`-qubit register. -/
def X (n : ℕ) (q : Fin n) : QMat n :=
  QMat.applySingle q Gate.X

/-- Pauli-Z embedded on one target qubit of an `n`-qubit register. -/
def Z (n : ℕ) (q : Fin n) : QMat n :=
  QMat.applySingle q Gate.Z

end QMat

end

end QLean
