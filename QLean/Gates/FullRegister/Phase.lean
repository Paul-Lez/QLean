/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/

import QLean.Gates.FullRegister.Support

/-! # Controlled phases, phase oracles, and Grover operators -/

namespace QLean

noncomputable section

open scoped Matrix ComplexOrder
open Matrix Complex

namespace QMat

private theorem phase_exp_star_mul (θ : ℝ) :
    star (Complex.exp (Complex.I * (θ : ℂ))) * Complex.exp (Complex.I * (θ : ℂ)) = 1 := by
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
    Complex.norm_exp_I_mul_ofReal]
  norm_num

private theorem phase_exp_mul_star (θ : ℝ) :
    Complex.exp (Complex.I * (θ : ℂ)) * star (Complex.exp (Complex.I * (θ : ℂ))) = 1 := by
  simpa [mul_comm] using phase_exp_star_mul θ

private theorem bool_phase_unit (b : Bool) :
    star (if b then (-1 : ℂ) else 1) * (if b then (-1 : ℂ) else 1) = 1 ∧
      (if b then (-1 : ℂ) else 1) * star (if b then (-1 : ℂ) else 1) = 1 := by
  cases b <;> norm_num

/--
Controlled phase gate: multiply `|11>` on `(control,target)` by `exp(i*theta)`.
If `control = target`, this intentionally degenerates to a one-qubit phase on `|1>`.
-/
def controlledPhaseMatrix {n : ℕ} (control target : Fin n) (θ : ℝ) : QMat n :=
  Matrix.diagonal fun x =>
    if x control = (1 : Fin 2) ∧ x target = (1 : Fin 2) then
      Complex.exp (Complex.I * (θ : ℂ))
    else
      1

theorem controlledPhaseMatrix_unitary {n : ℕ} (control target : Fin n) (θ : ℝ) :
    (controlledPhaseMatrix control target θ).Unitary := by
  apply QMat.diagonal_unitary_of_unit_entries
  intro x
  by_cases h : x control = (1 : Fin 2) ∧ x target = (1 : Fin 2)
  · simpa [h] using ⟨phase_exp_star_mul θ, phase_exp_mul_star θ⟩
  · simp [h]

/-- Phase oracle for a Boolean marked-set predicate: marked basis states get phase `-1`. -/
def phaseOracle {n : ℕ} (marked : Q[n] → Bool) : QMat n :=
  Matrix.diagonal fun x => if marked x then (-1 : ℂ) else 1

theorem phaseOracle_unitary {n : ℕ} (marked : Q[n] → Bool) :
    (phaseOracle marked).Unitary :=
  QMat.diagonal_unitary_of_unit_entries _ fun x => bool_phase_unit (marked x)

/-- Density matrix of the uniform state, represented directly as a full-register matrix. -/
def uniformDensity (n : ℕ) : QMat n :=
  Matrix.of fun _ _ => ((1 / (2 ^ n : ℝ)) : ℂ)

private theorem uniformDensity_norm (n : ℕ) :
    (∑ _ : Q[n], ((1 / (2 ^ n : ℝ)) : ℂ) * ((1 / (2 ^ n : ℝ)) : ℂ)) =
      ((1 / (2 ^ n : ℝ)) : ℂ) := by
  norm_num [Finset.sum_const, Finset.card_univ, QIndex.card]

private theorem uniformDensity_star (n : ℕ) :
    star (uniformDensity n) = uniformDensity n := by
  ext i j
  simp [uniformDensity, Matrix.star_apply]

private theorem uniformDensity_mul (n : ℕ) :
    uniformDensity n * uniformDensity n = uniformDensity n := by
  ext i j
  rw [Matrix.mul_apply]
  change (∑ _ : Q[n], ((1 / (2 ^ n : ℝ)) : ℂ) * ((1 / (2 ^ n : ℝ)) : ℂ)) =
    ((1 / (2 ^ n : ℝ)) : ℂ)
  exact uniformDensity_norm n

/-- Grover diffusion operator, `2 |s><s| - I`, specialized to the uniform state. -/
def diffusion (n : ℕ) : QMat n :=
  (2 : ℂ) • uniformDensity n - 1

private theorem diffusion_mul_self (n : ℕ) :
    diffusion n * diffusion n = 1 := by
  rw [diffusion]
  calc
    ((2 : ℂ) • uniformDensity n - 1) * ((2 : ℂ) • uniformDensity n - 1)
        = (4 : ℂ) • uniformDensity n - (2 : ℂ) • uniformDensity n -
            (2 : ℂ) • uniformDensity n + 1 := by
      rw [sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, uniformDensity_mul,
        Matrix.mul_one, Matrix.one_mul, smul_smul]
      module
    _ = 1 := by
      ext i j
      simp
      ring

theorem diffusion_unitary (n : ℕ) :
    (diffusion n).Unitary := by
  apply unitary_of_mul_star_eq_one
  simpa [diffusion, uniformDensity_star] using diffusion_mul_self n

/-- One Grover iterate as a full-register matrix: oracle then diffusion. -/
def groverIterate {n : ℕ} (marked : Q[n] → Bool) : QMat n :=
  diffusion n * phaseOracle marked

theorem groverIterate_unitary {n : ℕ} (marked : Q[n] → Bool) :
    (groverIterate marked).Unitary :=
  unitary_mul (diffusion_unitary n) (phaseOracle_unitary marked)

theorem groverIterate_pow_unitary {n : ℕ} (marked : Q[n] → Bool) (k : ℕ) :
    ((groverIterate marked) ^ k).Unitary :=
  unitary_pow (groverIterate marked) (groverIterate_unitary marked) k

/-- Projector/effect for successful readout of a marked basis state. -/
def successEffect {n : ℕ} (marked : Q[n] → Bool) : QMat n :=
  Matrix.diagonal fun x => if marked x then (1 : ℂ) else 0

end QMat

end

end QLean
