/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
import QLean.Foundation.Hilbert
import QLean.Foundation.Bitstring
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Full-Register Matrix Foundations

This file contains the core matrix types and operations used by the syntax and proof layers:
full-register density matrices, expectations, unitary evolution, measurement projectors, and
small generic linear-algebra helpers. Reusable concrete gate constructions live under
`QLean.Gates`.
-/

namespace QLean

noncomputable section

open scoped Matrix ComplexOrder
open Matrix Complex

/-  Full-register state and matrix types -/

/-- The quantum state of `n` qubits: a vector in `C^(2^n)`. -/
abbrev QuantumState (n : ℕ) := QState (2 ^ n)

/-- Matrices acting on the full `n`-qubit computational basis. -/
abbrev QMat (n : ℕ) := Matrix Q[n] Q[n] ℂ

namespace QMat

/-- A full-register operator is unitary when its conjugate transpose is its inverse. -/
def Unitary {n : ℕ} (U : QMat n) : Prop :=
  U ∈ Matrix.unitaryGroup Q[n] ℂ

/-- A full-register operator with a left inverse given by its adjoint is unitary. -/
theorem unitary_of_star_mul_eq_one {n : ℕ} {U : QMat n} (h : star U * U = 1) :
    U.Unitary :=
  ⟨h, mul_eq_one_comm.mp h⟩

/-- A full-register operator with a right inverse given by its adjoint is unitary. -/
theorem unitary_of_mul_star_eq_one {n : ℕ} {U : QMat n} (h : U * star U = 1) :
    U.Unitary :=
  ⟨mul_eq_one_comm.mp h, h⟩

/-- Trace of a full-register quantum matrix. -/
def trace {n : ℕ} (A : QMat n) : ℂ :=
  Matrix.trace A

/-- Real-valued expectation of an observable-like matrix against a quantum matrix. -/
def expect {n : ℕ} (A ρ : QMat n) : ℝ :=
  (Matrix.trace (A * ρ)).re

/-- The branchwise action of a unitary on a density matrix. -/
def evolve {n : ℕ} (U : QMat n) (ρ : QMat n) : QMat n :=
  U * ρ * star U

/-- Read the computational-basis bit at a target qubit. -/
def bitAt {n : ℕ} (target : Fin n) (x : Q[n]) : Bool :=
  decide (x target = (1 : Fin 2))

/-- The computational-basis projector for a single measured outcome. -/
def measProjector {n : ℕ} (target : Fin n) (outcome : Bool) : QMat n :=
  Matrix.of fun x y =>
    if x = y ∧ bitAt target x = outcome then 1 else 0

/-- Unitary evolution preserves matrix trace. -/
theorem trace_evolve_of_unitary {n : ℕ} (U : QMat n) (hU : U.Unitary) (ρ : QMat n) :
    Matrix.trace (QMat.evolve U ρ) = Matrix.trace ρ := by
  rw [QMat.evolve, ← Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU.1, Matrix.one_mul]

set_option linter.flexible false in
/-- Splitting one computational-basis measurement preserves total branch trace. -/
theorem trace_measure_split {n : ℕ} (q : Fin n) (ρ : QMat n) :
    Matrix.trace (QMat.measProjector q false * ρ * QMat.measProjector q false) +
      Matrix.trace (QMat.measProjector q true * ρ * QMat.measProjector q true) =
    Matrix.trace ρ := by
  simp [measProjector, Matrix.mul_assoc]
  simp +decide [Matrix.trace, Matrix.mul_apply]
  simp +decide [Finset.sum_ite, Finset.filter_eq, Finset.filter_and, bitAt]
  rw [← Finset.sum_add_distrib]
  congr
  ext x
  split_ifs <;> simp_all +decide [Finset.filter_eq']

set_option linter.flexible false in
/-- Unitary evolution preserves positive semidefiniteness. -/
theorem pos_evolve_of_unitary {n : ℕ} (U : QMat n) (_hU : U.Unitary) {ρ : QMat n}
    (hρ : ρ.PosSemidef) :
    (QMat.evolve U ρ).PosSemidef := by
  simpa [QMat.evolve, Matrix.star_eq_conjTranspose] using
    hρ.conjTranspose_mul_mul_same (star U)

/-- Computational-basis measurement branches preserve positive semidefiniteness. -/
theorem pos_measure {n : ℕ} (q : Fin n) (b : Bool) {ρ : QMat n}
    (hρ : ρ.PosSemidef) :
    (QMat.measProjector q b * ρ * QMat.measProjector q b).PosSemidef := by
  have h_measure_projector : ∀ (A : QMat n), A.IsHermitian → (A * ρ * A).PosSemidef := by
    intro A hA
    convert hρ.conjTranspose_mul_mul_same A using 1
    rw [hA]
  convert h_measure_projector _ ?_
  ext i j
  simp +decide [measProjector]
  grind

/-- Sums of positive semidefinite full-register matrices are positive semidefinite. -/
theorem pos_add {n : ℕ} {ρ₁ ρ₂ : QMat n}
    (hρ₁ : ρ₁.PosSemidef) (hρ₂ : ρ₂.PosSemidef) :
    (ρ₁ + ρ₂).PosSemidef :=
  hρ₁.add hρ₂

/-- The identity full-register operator is unitary. -/
theorem unitary_one {n : ℕ} : QMat.Unitary (1 : QMat n) :=
  Submonoid.one_mem _

/-- Products of full-register unitaries are unitary. -/
theorem unitary_mul {n : ℕ} {U V : QMat n} (hU : U.Unitary) (hV : V.Unitary) :
    QMat.Unitary (U * V) :=
  Submonoid.mul_mem _ hU hV

/-- Powers of a full-register unitary are unitary. -/
theorem unitary_pow {n : ℕ} (U : QMat n) (hU : U.Unitary) (k : ℕ) :
    (U ^ k).Unitary :=
  pow_mem hU k

/-- A diagonal matrix whose entries have unit modulus is unitary. -/
theorem diagonal_unitary_of_unit_entries {n : ℕ} (f : Q[n] → ℂ)
    (hf : ∀ x, star (f x) * f x = 1 ∧ f x * star (f x) = 1) :
    QMat.Unitary (Matrix.diagonal f) := by
  change Matrix.diagonal f ∈ Matrix.unitaryGroup Q[n] ℂ
  rw [Matrix.mem_unitaryGroup_iff]
  calc
    Matrix.diagonal f * star (Matrix.diagonal f) =
        Matrix.diagonal (fun x => f x * (star f) x) := by
      rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
        Matrix.diagonal_mul_diagonal]
    _ = 1 := by
      ext x y
      by_cases hx : x = y
      · subst y
        simpa using (hf x).2
      · simp [hx]

end QMat

/- Matrix constructions from basis maps -/

namespace Matrix

/-- Pointwise Kronecker product over a finite family of matrices. -/
def piKronecker {ι R : Type*} [CommRing R] {n : ι → Type*} {m : ι → Type*} [Fintype ι]
    (M : {i : ι} → Matrix (n i) (m i) R) : Matrix (Π i, n i) (Π i, m i) R :=
  Matrix.of fun a b => ∏ i, M (a i) (b i)

end Matrix

end

end QLean
