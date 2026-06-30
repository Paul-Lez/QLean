/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
import QLean.Foundation.QMat

/-!
# Computational-Basis State Helpers
-/

namespace QLean

noncomputable section

open scoped Matrix ComplexOrder

namespace QMat

/-! ## Basis states and densities -/

/-- The scalar `1 / sqrt 2`, coerced to complex amplitudes. -/
def invSqrt2 : ℂ :=
  ((1 / Real.sqrt 2 : ℝ) : ℂ)

/-- The rank-one computational-basis projector `|x><x|`. -/
def projBasis {n : ℕ} (x : Q[n]) : QMat n :=
  Matrix.of fun y z => if y = x ∧ z = x then 1 else 0

/-- The rank-one projector for a Boolean bitstring. -/
def projBits {n : ℕ} (bits : Fin n → Bool) : QMat n :=
  projBasis (QIndex.basisOfBits bits)

/-- The all-zero computational-basis density matrix on `n` qubits. -/
def zeroDensity (n : ℕ) : QMat n :=
  projBits fun _ => false

/-- The computational-basis amplitude vector supported at a single index. -/
def basisAmp {n : ℕ} (x : Q[n]) : Q[n] → ℂ :=
  fun y => if y = x then 1 else 0

/-- A pure-state density matrix from an amplitude function on computational-basis indices. -/
def pureDensity {n : ℕ} (amp : Q[n] → ℂ) : QMat n :=
  Matrix.of fun x y => amp x * star (amp y)

/-- The one-qubit computational-basis index `|b>`. -/
def basis1 (b : Bool) : Q[1] :=
  QIndex.basisOfBits fun _ => b

/-- The two-qubit computational-basis index `|b0 b1>`. -/
def basis2 (b0 b1 : Bool) : Q[2] :=
  QIndex.basisOfBits fun q => if q = (0 : Fin 2) then b0 else b1

/-- The three-qubit computational-basis index `|b0 b1 b2>`. -/
def basis3 (b0 b1 b2 : Bool) : Q[3] :=
  QIndex.basisOfBits fun q =>
    if q = (0 : Fin 3) then b0 else
    if q = (1 : Fin 3) then b1 else
    b2

/-- The five-qubit computational-basis index `|b0 b1 b2 b3 b4>`. -/
def basis5 (b0 b1 b2 b3 b4 : Bool) : Q[5] :=
  QIndex.basisOfBits fun q =>
    if q = (0 : Fin 5) then b0 else
    if q = (1 : Fin 5) then b1 else
    if q = (2 : Fin 5) then b2 else
    if q = (3 : Fin 5) then b3 else
    b4

/-- Matrix-vector multiplication over the full-register computational basis. -/
def matVec {n : ℕ} (U : QMat n) (ψ : Q[n] → ℂ) : Q[n] → ℂ :=
  fun out => ∑ inn : Q[n], U out inn * ψ inn

/-- The all-zero density is the pure density of the all-zero basis amplitude. -/
theorem zeroDensity_eq_pureDensity_basisAmp_zero (n : ℕ) :
    zeroDensity n = pureDensity (basisAmp (0 : Q[n])) := by
  have hzero :
      QIndex.basisOfBits (fun _ : Fin n => false) = (0 : Q[n]) := by
    funext i
    simp [QIndex.basisOfBits, QIndex.boolBit]
  ext x y
  by_cases hx : x = (0 : Q[n]) <;> by_cases hy : y = (0 : Q[n])
  all_goals
    simp [zeroDensity, projBits, projBasis, pureDensity, basisAmp, hzero, hx, hy]

/-- Matrix-vector multiplication by the identity is the identity on amplitudes. -/
theorem matVec_one {n : ℕ} (amp : Q[n] → ℂ) :
    matVec (1 : QMat n) amp = amp := by
  ext x
  unfold matVec
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _hy hyx
    have hxy : x ≠ y := fun h => hyx h.symm
    simp [hxy]
  · intro hmem
    exact (hmem (Finset.mem_univ x)).elim

/-- Matrix-vector multiplication composes with matrix multiplication. -/
theorem matVec_mul {n : ℕ} (U V : QMat n) (amp : Q[n] → ℂ) :
    matVec (U * V) amp = matVec U (matVec V amp) := by
  ext x
  unfold matVec
  calc
    (∑ y, (U * V) x y * amp y) =
        ∑ y, (∑ z, U x z * V z y) * amp y := by
      apply Finset.sum_congr rfl
      intro y _hy
      rw [Matrix.mul_apply]
    _ =
        ∑ y, ∑ z, U x z * (V z y * amp y) := by
      apply Finset.sum_congr rfl
      intro y _hy
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro z _hz
      ring
    _ = ∑ z, ∑ y, U x z * (V z y * amp y) := by
      rw [Finset.sum_comm]
    _ = ∑ z, U x z * ∑ y, V z y * amp y := by
      apply Finset.sum_congr rfl
      intro z _hz
      rw [Finset.mul_sum]

/-- Multiplying a pure density on the left computes the evolved left amplitude. -/
theorem mul_pureDensity_apply {n : ℕ} (U : QMat n) (amp : Q[n] → ℂ)
    (a b : Q[n]) :
    (U * pureDensity amp) a b = matVec U amp a * star (amp b) := by
  unfold pureDensity matVec
  rw [Matrix.mul_apply]
  simp [Finset.sum_mul, mul_assoc]

/-- Unitary-style evolution of a pure density evolves the amplitudes on both sides. -/
theorem evolve_pureDensity_apply {n : ℕ} (U : QMat n) (amp : Q[n] → ℂ)
    (a b : Q[n]) :
    QMat.evolve U (pureDensity amp) a b = matVec U amp a * star (matVec U amp b) := by
  unfold QMat.evolve
  rw [Matrix.mul_apply]
  calc
    (∑ x, (U * pureDensity amp) a x * (star U) x b)
        = ∑ x, (matVec U amp a * star (amp x)) * star (U b x) := by
          apply Finset.sum_congr rfl
          intro x _hx
          rw [mul_pureDensity_apply]
          simp
    _ = ∑ x, matVec U amp a * (star (amp x) * star (U b x)) := by
          apply Finset.sum_congr rfl
          intro x _hx
          simp [mul_assoc]
    _ = matVec U amp a * (∑ x, star (amp x) * star (U b x)) := by
          rw [Finset.mul_sum]
    _ = matVec U amp a * (∑ x, star (U b x * amp x)) := by
          congr 1
          apply Finset.sum_congr rfl
          intro x _hx
          simp [star_mul', mul_comm]
    _ = matVec U amp a * star (∑ x, U b x * amp x) := by
          rw [star_sum]
    _ = matVec U amp a * star (matVec U amp b) := by
          rfl

/-- Evolution of a pure density is the pure density of the evolved amplitudes. -/
theorem evolve_pureDensity_eq_pureDensity {n : ℕ} (U : QMat n) (amp : Q[n] → ℂ) :
    QMat.evolve U (pureDensity amp) = pureDensity (matVec U amp) := by
  ext a b
  rw [evolve_pureDensity_apply]
  rfl

/- Effects and measurement branches -/

/-- Postcondition/effect that counts exactly one returned classical value. -/
def returns {n : ℕ} {σ α : Type} [DecidableEq α] (expected : α) :
    α → σ → QMat n
  | actual, _ => if actual = expected then 1 else 0

/-- Effect that counts exactly one returned classical value. -/
def returnEffect {n : ℕ} {α : Type} [DecidableEq α] (expected : α) :
    α → QMat n
  | actual => if actual = expected then 1 else 0

/-- Post-measurement branch for one computational-basis outcome. -/
def measured {n : ℕ} (target : Fin n) (outcome : Bool) (ρ : QMat n) : QMat n :=
  QMat.measProjector target outcome * ρ * QMat.measProjector target outcome

/-- A full-register matrix maps one computational-basis vector to another. -/
def MapsBasis {n : ℕ} (U : QMat n) (input output : Q[n]) : Prop :=
  ∀ z : Q[n], U z input = if z = output then 1 else 0

end QMat

end

end QLean
