/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
import QLean.Examples.Algorithms.Grover.LinearAlgebra

/-!
# General Grover Search
-/

namespace QLean

noncomputable section

open scoped Matrix ComplexOrder

namespace QProg
namespace GroverWP

/-! ## Program Ingredients and Success Statements -/

/-- The usual one-solution Grover promise: exactly `target` is marked. -/
def UniqueMarked {n : ℕ} (marked : Marked n) (target : Q[n]) : Prop :=
  ∀ x, marked x = true ↔ x = target

/-- Standard Grover lower bound for an `n`-qubit search space. -/
def successLowerBound (n : ℕ) : ℝ :=
  1 - 1 / (2 ^ n : ℝ)

/-- Grover rotation angle used by the usual one-solution iteration count. -/
def groverAngle (n : ℕ) : ℝ :=
  LinearAlgebra.groverAngle n

/--
Usual Grover iteration count, obtained by rounding `pi / (4 theta) - 1/2` to the
nearest natural number with half-ties rounded upward.

This is equivalently `floor (pi / (4 theta))`, and keeps the final angle within `theta`
of `pi / 2`, which is the form used by the standard `1 - 1/N` success bound.
-/
def optimalIterations (n : ℕ) : ℕ :=
  Nat.floor (Real.pi / (4 * groverAngle n))

/-- Success probability of the prepared `k`-round Grover program from `|0...0><0...0|`. -/
def successProbability {n : ℕ} (marked : Marked n) (k : ℕ) : ℝ :=
  QMat.expect (QMat.successEffect marked) (programEvolve marked k (QMat.zeroDensity n))

/-- The usual one-solution Grover amplitude formula, stated as a success probability. -/
def GroverAmplitudeFormula {n : ℕ} (marked : Marked n) (k : ℕ) : Prop :=
  successProbability marked k = Real.sin ((2 * (k : ℝ) + 1) * groverAngle n) ^ 2

/-- The quantitative one-solution Grover bound. -/
def OptimalGroverSuccessBound {n : ℕ} (marked : Marked n) : Prop :=
  successLowerBound n ≤ successProbability marked (optimalIterations n)

/-- General one-solution amplitude-amplification theorem as a proposition. -/
def OneSolutionAmplitudeAmplification (n : ℕ) : Prop :=
  ∀ marked target, UniqueMarked (n := n) marked target → 1 < 2 ^ n →
    OptimalGroverSuccessBound marked

/-! ## General One-Solution Proof -/

/-- With the corrected Grover iteration count, the final angle is near `pi / 2`. -/
theorem optimalIterations_groverAngle_window (n : ℕ) :
    Real.pi / 2 - groverAngle n ≤ (2 * (optimalIterations n : ℝ) + 1) * groverAngle n ∧
      (2 * (optimalIterations n : ℝ) + 1) * groverAngle n ≤ Real.pi / 2 + groverAngle n := by
  have hθpos : 0 < groverAngle n := by
    unfold groverAngle LinearAlgebra.groverAngle
    rw [Real.arcsin_pos]
    positivity
  have hden : 0 < 4 * groverAngle n := mul_pos (by norm_num) hθpos
  have hq_nonneg : 0 ≤ Real.pi / (4 * groverAngle n) := by positivity
  have hk_le : (optimalIterations n : ℝ) ≤ Real.pi / (4 * groverAngle n) := by
    unfold optimalIterations
    exact Nat.floor_le hq_nonneg
  have hq_lt : Real.pi / (4 * groverAngle n) < (optimalIterations n : ℝ) + 1 := by
    unfold optimalIterations
    simpa using Nat.lt_floor_add_one (Real.pi / (4 * groverAngle n))
  have hk_le_mul : (optimalIterations n : ℝ) * (4 * groverAngle n) ≤ Real.pi :=
    (le_div_iff₀ hden).mp hk_le
  have hq_lt_mul : Real.pi < ((optimalIterations n : ℝ) + 1) * (4 * groverAngle n) :=
    (div_lt_iff₀ hden).mp hq_lt
  constructor <;> nlinarith

private theorem cos_sq_le_sin_sq_of_window {θ x : ℝ} (hθ0 : 0 ≤ θ)
    (hθle : θ ≤ Real.pi / 2) (hxlo : Real.pi / 2 - θ ≤ x) (hxhi : x ≤ Real.pi / 2 + θ) :
    Real.cos θ ^ 2 ≤ Real.sin x ^ 2 := by
  let δ := Real.pi / 2 - x
  have hδ_abs : |δ| ≤ θ := by
    rw [abs_le]
    constructor <;> dsimp [δ] <;> linarith
  have hθlepi : θ ≤ Real.pi := by linarith [Real.pi_pos]
  have hcos_le : Real.cos θ ≤ Real.cos δ := by
    calc
      Real.cos θ ≤ Real.cos |δ| :=
        Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg δ) hθlepi hδ_abs
      _ = Real.cos δ := Real.cos_abs δ
  have hcosθ_nonneg : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hθle⟩
  have hδ_mem : δ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    rw [Set.mem_Icc]
    have hδ_le : δ ≤ θ := (abs_le.mp hδ_abs).2
    have hneg_leδ : -θ ≤ δ := (abs_le.mp hδ_abs).1
    constructor <;> linarith
  have hcosδ_nonneg : 0 ≤ Real.cos δ := Real.cos_nonneg_of_mem_Icc hδ_mem
  have hsq : Real.cos θ ^ 2 ≤ Real.cos δ ^ 2 := by
    rw [sq_le_sq, abs_of_nonneg hcosθ_nonneg, abs_of_nonneg hcosδ_nonneg]
    exact hcos_le
  have hsin : Real.sin x = Real.cos δ := by
    dsimp [δ]
    have h := Real.sin_pi_div_two_sub (Real.pi / 2 - x)
    simpa using h
  simpa [hsin]

/-- The Grover angle satisfies `cos^2(theta) = 1 - 1 / N`. -/
theorem cos_sq_groverAngle_eq_successLowerBound (n : ℕ) :
    Real.cos (groverAngle n) ^ 2 = successLowerBound n := by
  have hNpos : 0 < (2 ^ n : ℝ) := by positivity
  have hsqrt_pos : 0 < Real.sqrt (2 ^ n : ℝ) := Real.sqrt_pos_of_pos hNpos
  have hx_le_one : 1 / Real.sqrt (2 ^ n : ℝ) ≤ 1 := by
    have hsqrt_ge_one : 1 ≤ Real.sqrt (2 ^ n : ℝ) := by
      rw [← sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1) (Real.sqrt_nonneg _)]
      norm_num [Real.sq_sqrt (le_of_lt hNpos)]
      exact_mod_cast Nat.one_le_pow n 2 (by norm_num)
    exact (div_le_one hsqrt_pos).2 hsqrt_ge_one
  have hx_nonneg : 0 ≤ 1 / Real.sqrt (2 ^ n : ℝ) := by positivity
  have hsin : Real.sin (groverAngle n) = 1 / Real.sqrt (2 ^ n : ℝ) := by
    unfold groverAngle LinearAlgebra.groverAngle
    exact Real.sin_arcsin (le_trans (by norm_num : (-1 : ℝ) ≤ 0) hx_nonneg) hx_le_one
  have hsq : (1 / Real.sqrt (2 ^ n : ℝ)) ^ 2 = 1 / (2 ^ n : ℝ) := by
    calc
      (1 / Real.sqrt (2 ^ n : ℝ)) ^ 2 =
          1 / (Real.sqrt (2 ^ n : ℝ)) ^ 2 := by
        ring
      _ = 1 / (2 ^ n : ℝ) := by
        rw [Real.sq_sqrt (le_of_lt hNpos)]
  have htrig := Real.cos_sq_add_sin_sq (groverAngle n)
  unfold successLowerBound
  nlinarith

theorem optimalGroverSuccessBound_of_amplitude_formula {n : ℕ} {marked : Marked n}
    (hformula : GroverAmplitudeFormula marked (optimalIterations n)) :
    OptimalGroverSuccessBound marked := by
  unfold OptimalGroverSuccessBound
  rw [hformula, ← cos_sq_groverAngle_eq_successLowerBound n]
  have hangle_nonneg : 0 ≤ groverAngle n := by
    unfold groverAngle LinearAlgebra.groverAngle
    rw [Real.arcsin_nonneg]
    positivity
  exact cos_sq_le_sin_sq_of_window hangle_nonneg (Real.arcsin_le_pi_div_two _)
    (optimalIterations_groverAngle_window n).1 (optimalIterations_groverAngle_window n).2

theorem oneSolutionAmplitudeAmplification_of_amplitude_formula
    (n : ℕ) (hformula : ∀ marked target, UniqueMarked (n := n) marked target →
      GroverAmplitudeFormula marked (optimalIterations n)) :
    OneSolutionAmplitudeAmplification n :=
  fun marked target hmarked _hn =>
    optimalGroverSuccessBound_of_amplitude_formula (hformula marked target hmarked)

/-- One marked basis state satisfies the Grover amplitude formula. -/
theorem groverAmplitudeFormula_of_uniqueMarked {n : ℕ} {marked : Marked n}
    {target : Q[n]} (hmarked : UniqueMarked marked target) (hn : 1 < 2 ^ n) (k : ℕ) :
    GroverAmplitudeFormula marked k := by
  unfold GroverAmplitudeFormula successProbability
  rw [LinearAlgebra.programEvolve_zeroDensity_eq_pure_analyticAmp hmarked hn k,
    LinearAlgebra.expect_successEffect_pureDensity_unique hmarked]
  unfold LinearAlgebra.analyticAmp LinearAlgebra.groverPhase groverAngle LinearAlgebra.groverAngle
  simp only [↓reduceIte]
  rw [Complex.normSq_ofReal]
  ring

theorem oneSolutionAmplitudeAmplification (n : ℕ) : OneSolutionAmplitudeAmplification n :=
  fun _ _ hmarked hn =>
    optimalGroverSuccessBound_of_amplitude_formula
    (groverAmplitudeFormula_of_uniqueMarked hmarked hn (optimalIterations n))

end GroverWP
end QProg

end

end QLean
