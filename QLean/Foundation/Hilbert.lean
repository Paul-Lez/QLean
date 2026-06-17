/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Quantum Hilbert Space Foundations

This file establishes the mathematical foundations for quantum formal verification:

* **`QState n`**: The type of quantum state vectors in an `n`-dimensional Hilbert space over `ℂ`,
  represented as `EuclideanSpace ℂ (Fin n)`.
* **`Operator n`**: Linear operators on the Hilbert space, represented as `n × n` complex matrices.
-/

namespace QLean

noncomputable section

open scoped Matrix ComplexOrder Kronecker
open Matrix

/-! ## State Vectors -/

/-- A quantum state vector in an `n`-dimensional Hilbert space over `ℂ`. -/
abbrev QState (n : ℕ) := EuclideanSpace ℂ (Fin n)

/-- Complex `n × n` matrices as operators on the Hilbert space. -/
abbrev Operator (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

namespace QState

/-- The standard computational basis vector `|i⟩`. -/
def basis (n : ℕ) (i : Fin n) : QState n :=
  EuclideanSpace.single i 1

notation "|" i "⟩_" n => QState.basis n i

/-- The inner product `⟨ψ|φ⟩` of two state vectors. -/
def inner' {n : ℕ} (ψ φ : QState n) : ℂ :=
  @inner ℂ (EuclideanSpace ℂ (Fin n)) _ ψ φ

notation "⟪" ψ "|" φ "⟫" => QState.inner' ψ φ

/-- A state vector is normalised when `⟨ψ|ψ⟩ = 1`. -/
def IsNormalized {n : ℕ} (ψ : QState n) : Prop :=
  ⟪ψ|ψ⟫ = 1

/-- Expand the inner product of finite Euclidean-space states as a sum. -/
theorem inner'_eq_sum {n : ℕ} (ψ φ : QState n) : ⟪ψ|φ⟫ = ∑ i, φ i * star (ψ i) :=
  rfl

/-- Normalisation expanded as the usual sum of squared amplitudes. -/
theorem isNormalized_iff_sum_mul_star {n : ℕ} {ψ : QState n} :
    ψ.IsNormalized ↔ (∑ i, ψ i * star (ψ i)) = 1 := by
  rw [IsNormalized, inner'_eq_sum]

/-- The computational-basis states are normalised. -/
theorem basis_normalized (n : ℕ) [NeZero n] (i : Fin n) :
    IsNormalized (basis n i) := by
  simp [isNormalized_iff_sum_mul_star, basis]

end QState

/- Operators and Special Classes -/

namespace Operator

/-- An operator is unitary when `U† U = 1`. -/
def IsUnitary {n : ℕ} (U : Operator n) : Prop :=
  Uᴴ * U = 1

/-- An operator is a projection when it is Hermitian and idempotent: `P² = P`. -/
def IsProjection {n : ℕ} (P : Operator n) : Prop :=
  Matrix.IsHermitian P ∧ P * P = P

/-- The outer product `|ψ⟩⟨φ|` as a matrix. -/
def outerProduct {n : ℕ} (ψ φ : QState n) : Operator n :=
  Matrix.vecMulVec (fun i => ψ i) (fun j => star (φ j))

-- Notation |ψ⟩⟨φ| omitted to avoid parser conflicts with anonymous constructors.
-- Use `Operator.outerProduct ψ φ` directly.

/-- The projector onto a single state: `|ψ⟩⟨ψ|`. -/
def proj {n : ℕ} (ψ : QState n) : Operator n :=
  outerProduct ψ ψ

/-- Taking the adjoint swaps the two sides of an outer product. -/
theorem outerProduct_conjTranspose {n : ℕ} (ψ φ : QState n) :
    (outerProduct ψ φ)ᴴ = outerProduct φ ψ := by
  ext i j
  simp [outerProduct, Matrix.vecMulVec, Matrix.conjTranspose, mul_comm]

/-- Composition of rank-one outer products contracts their middle states. -/
theorem outerProduct_mul_outerProduct {n : ℕ} (ψ φ χ η : QState n) :
    outerProduct ψ φ * outerProduct χ η =
      (∑ k, star (φ k) * χ k) • outerProduct ψ η := by
  ext i j
  simp [outerProduct, Matrix.vecMulVec, Matrix.mul_apply, Finset.mul_sum, mul_comm,
    mul_left_comm]

/-- The projector onto a normalised state is indeed a projection. -/
theorem proj_isProjection {n : ℕ} (ψ : QState n) (hψ : ψ.IsNormalized) :
    IsProjection (proj ψ) := by
  constructor
  · simpa [proj] using outerProduct_conjTranspose ψ ψ
  · calc
      proj ψ * proj ψ = (∑ k, star (ψ k) * ψ k) • proj ψ := by
        simpa [proj] using outerProduct_mul_outerProduct ψ ψ ψ ψ
      _ = proj ψ := by
        rw [show (∑ k, star (ψ k) * ψ k) = 1 by
          simpa [mul_comm] using (QState.isNormalized_iff_sum_mul_star.mp hψ)]
        simp

/-- Apply an operator to a state vector (matrix-vector multiplication). -/
def applyToState {n : ℕ} (U : Operator n) (ψ : QState n) : QState n :=
  (EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin n)).symm (U.mulVec (EuclideanSpace.equiv _ _ ψ))

notation U " |⬝⟩ " ψ => Operator.applyToState U ψ

/-- Pointwise form of matrix-vector application to a quantum state. -/
theorem applyToState_apply {n : ℕ} (U : Operator n) (ψ : QState n) (i : Fin n) :
    applyToState U ψ i = ∑ j, U i j * ψ j :=
  rfl

/-- Columns of a unitary matrix are orthonormal, in the convention used by norm sums. -/
theorem unitary_column_sum_mul_star {n : ℕ} {U : Operator n} (hU : IsUnitary U)
    (j k : Fin n) :
    (∑ i, U i j * star (U i k)) = if j = k then 1 else 0 := by
  have h_entry : (∑ i, star (U i j) * U i k) = if j = k then 1 else 0 := by
    simpa only [Matrix.mul_apply, Matrix.one_apply, Matrix.conjTranspose_apply] using
      congr_fun (congr_fun hU j) k
  convert congr_arg Star.star h_entry using 1 <;> simp [mul_comm]

/-- Squared norm after applying an operator, expanded against its column Gram matrix. -/
private theorem applyToState_norm_sq {n : ℕ} (U : Operator n) (ψ : QState n) :
    (∑ i, (applyToState U ψ) i * star ((applyToState U ψ) i)) =
      ∑ j, ∑ k, ψ j * star (ψ k) * (∑ i, U i j * star (U i k)) := by
  simpa only [applyToState_apply] using
    (show
      (∑ i,
          (∑ j, U i j * ψ.ofLp j) *
            starRingEnd ℂ (∑ k, U i k * ψ.ofLp k)) =
        ∑ j, ∑ k, ψ.ofLp j * starRingEnd ℂ (ψ.ofLp k) *
          (∑ i, U i j * starRingEnd ℂ (U i k)) from by
      simp only
        [Finset.sum_mul _ _ _, mul_assoc, Finset.mul_sum _ _ _, mul_comm, mul_left_comm]
      rw [Finset.sum_comm]
      simp only [map_sum, map_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm)

/-- Unitary operators preserve normalisation. -/
theorem unitary_preserves_norm {n : ℕ} (U : Operator n) (ψ : QState n)
    (hU : IsUnitary U) (hψ : ψ.IsNormalized) :
    (applyToState U ψ).IsNormalized := by
  rw [QState.isNormalized_iff_sum_mul_star] at hψ ⊢
  rw [applyToState_norm_sq]
  simp_rw [unitary_column_sum_mul_star hU]
  simpa using hψ

end Operator

end

end QLean
