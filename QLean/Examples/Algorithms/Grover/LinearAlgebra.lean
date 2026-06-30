/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
import QLean.Examples.Algorithms.Grover.Verification
import QLean.Examples.AuxiliaryResults.Grover4

/-!
# Grover Linear-Algebra Prerequisites
-/

namespace QLean

noncomputable section

open scoped Matrix ComplexOrder

namespace QProg
namespace GroverWP
namespace LinearAlgebra

/-! ## General One-Solution Amplitudes -/

/-- Grover rotation angle used by the usual one-solution iteration count. -/
def groverAngle (n : ℕ) : ℝ :=
  Real.arcsin (1 / Real.sqrt (2 ^ n : ℝ))

private theorem sin_groverAngle_eq_inv_sqrt (n : ℕ) :
    Real.sin (groverAngle n) = 1 / Real.sqrt (2 ^ n : ℝ) := by
  have hNpos : 0 < (2 ^ n : ℝ) := by positivity
  have hsqrt_pos : 0 < Real.sqrt (2 ^ n : ℝ) := Real.sqrt_pos_of_pos hNpos
  have hx_nonneg : 0 ≤ 1 / Real.sqrt (2 ^ n : ℝ) := by positivity
  have hx_le_one : 1 / Real.sqrt (2 ^ n : ℝ) ≤ 1 := by
    have hsqrt_ge_one : 1 ≤ Real.sqrt (2 ^ n : ℝ) := by
      rw [← sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1) (Real.sqrt_nonneg _)]
      norm_num [Real.sq_sqrt (le_of_lt hNpos)]
      exact_mod_cast Nat.one_le_pow n 2 (by norm_num)
    exact (div_le_one hsqrt_pos).2 hsqrt_ge_one
  unfold groverAngle
  exact Real.sin_arcsin (le_trans (by norm_num : (-1 : ℝ) ≤ 0) hx_nonneg) hx_le_one

private theorem cos_groverAngle_eq_sqrt_pred_div_sqrt {n : ℕ} (_hn : 1 < 2 ^ n) :
    Real.cos (groverAngle n) = Real.sqrt ((2 ^ n : ℝ) - 1) / Real.sqrt (2 ^ n : ℝ) := by
  have hNpos : 0 < (2 ^ n : ℝ) := by positivity
  have hNge1 : (1 : ℝ) ≤ (2 ^ n : ℝ) := by
    exact_mod_cast Nat.one_le_pow n 2 (by norm_num)
  have hNm1_nonneg : 0 ≤ (2 ^ n : ℝ) - 1 := by linarith
  have hx_sq : (1 / Real.sqrt (2 ^ n : ℝ)) ^ 2 = 1 / (2 ^ n : ℝ) := by
    calc
      (1 / Real.sqrt (2 ^ n : ℝ)) ^ 2 =
          1 / (Real.sqrt (2 ^ n : ℝ)) ^ 2 := by
        ring
      _ = 1 / (2 ^ n : ℝ) := by
        rw [Real.sq_sqrt (le_of_lt hNpos)]
  rw [groverAngle, Real.cos_arcsin, hx_sq, ← Real.sqrt_div hNm1_nonneg (2 ^ n : ℝ)]
  congr 1
  field_simp [ne_of_gt hNpos]

private theorem scalar_target_step {N M sN sM θ φ : ℝ}
    (_hNpos : 0 < N) (_hMpos : 0 < M)
    (hsNpos : 0 < sN) (hsMpos : 0 < sM)
    (hM : M = N - 1)
    (hsN : sN ^ 2 = N) (hsM : sM ^ 2 = M)
    (hs : Real.sin θ = 1 / sN) (hc : Real.cos θ = sM / sN) :
    (2 / N) * (M * (Real.cos φ / sM) - Real.sin φ) + Real.sin φ =
      Real.sin (φ + 2 * θ) := by
  rw [Real.sin_add, Real.sin_two_mul, Real.cos_two_mul]
  grind

private theorem scalar_unmarked_step {N M sN sM θ φ : ℝ}
    (_hMpos : 0 < M)
    (hsNpos : 0 < sN) (hsMpos : 0 < sM)
    (hM : M = N - 1)
    (hsN : sN ^ 2 = N) (hsM : sM ^ 2 = M)
    (hs : Real.sin θ = 1 / sN) (hc : Real.cos θ = sM / sN) :
    (2 / N) * (M * (Real.cos φ / sM) - Real.sin φ) - Real.cos φ / sM =
      Real.cos (φ + 2 * θ) / sM := by
  rw [Real.cos_add, Real.sin_two_mul, Real.cos_two_mul]
  grind

private theorem grover_target_step {n : ℕ} (hn : 1 < 2 ^ n) (φ : ℝ) :
    (2 / (2 ^ n : ℝ)) * (((2 ^ n : ℝ) - 1) * (Real.cos φ / Real.sqrt ((2 ^ n : ℝ) - 1)) -  Real.sin φ) +
      Real.sin φ = Real.sin (φ + 2 * groverAngle n) := by
  have hNpos : 0 < (2 ^ n : ℝ) := by positivity
  have hNgt1 : (1 : ℝ) < (2 ^ n : ℝ) := by exact_mod_cast hn
  have hMpos : 0 < (2 ^ n : ℝ) - 1 := by linarith
  exact scalar_target_step hNpos hMpos (Real.sqrt_pos_of_pos hNpos)
    (Real.sqrt_pos_of_pos hMpos) rfl (Real.sq_sqrt (le_of_lt hNpos))
    (Real.sq_sqrt (le_of_lt hMpos)) (sin_groverAngle_eq_inv_sqrt n)
    (cos_groverAngle_eq_sqrt_pred_div_sqrt hn)

private theorem grover_unmarked_step {n : ℕ} (hn : 1 < 2 ^ n) (φ : ℝ) :
    (2 / (2 ^ n : ℝ)) * (((2 ^ n : ℝ) - 1) * (Real.cos φ / Real.sqrt ((2 ^ n : ℝ) - 1)) -
      Real.sin φ) - Real.cos φ / Real.sqrt ((2 ^ n : ℝ) - 1) =
        Real.cos (φ + 2 * groverAngle n) / Real.sqrt ((2 ^ n : ℝ) - 1) := by
  have hNpos : 0 < (2 ^ n : ℝ) := by positivity
  have hNgt1 : (1 : ℝ) < (2 ^ n : ℝ) := by exact_mod_cast hn
  have hMpos : 0 < (2 ^ n : ℝ) - 1 := by linarith
  exact scalar_unmarked_step hMpos (Real.sqrt_pos_of_pos hNpos)
    (Real.sqrt_pos_of_pos hMpos) rfl (Real.sq_sqrt (le_of_lt hNpos))
    (Real.sq_sqrt (le_of_lt hMpos)) (sin_groverAngle_eq_inv_sqrt n)
    (cos_groverAngle_eq_sqrt_pred_div_sqrt hn)

def groverPhase (n k : ℕ) : ℝ :=
  (2 * (k : ℝ) + 1) * groverAngle n

private def uniformAmp (n : ℕ) : Q[n] → ℂ :=
  fun _ => ((1 / Real.sqrt (2 ^ n : ℝ) : ℝ) : ℂ)

def analyticAmp {n : ℕ} (target : Q[n]) (k : ℕ) : Q[n] → ℂ :=
  fun x =>
    if x = target then
      ((Real.sin (groverPhase n k) : ℝ) : ℂ)
    else
      ((Real.cos (groverPhase n k) / Real.sqrt ((2 ^ n : ℝ) - 1) : ℝ) : ℂ)

private theorem groverPhase_succ (n k : ℕ) :
    groverPhase n k + 2 * groverAngle n = groverPhase n (k + 1) := by
  grind [groverPhase]

private theorem matVec_hadamardLayer_basisAmp_zero (n : ℕ) :
    QMat.matVec (QMat.hadamardLayer n) (QMat.basisAmp (0 : Q[n])) = uniformAmp n := by
  ext out
  unfold QMat.matVec QMat.hadamardLayer QMat.hadamardAmplitude QMat.basisAmp uniformAmp
  rw [Finset.sum_eq_single (0 : Q[n])]
  · simp [QIndex.bitDotMod2, QIndex.bitVal]
  · intro y _hy hy
    simp [hy]
  · intro hzero
    exact (hzero (Finset.mem_univ _)).elim

private theorem analyticAmp_zero_eq_uniformAmp {n : ℕ} (hn : 1 < 2 ^ n)
    (target : Q[n]) : analyticAmp target 0 = uniformAmp n := by
  ext x
  unfold analyticAmp uniformAmp groverPhase
  by_cases hx : x = target
  · simp [hx, sin_groverAngle_eq_inv_sqrt]
  · simp only [hx, if_false, CharP.cast_eq_zero, mul_zero, zero_add, one_mul, Complex.ofReal_sin,
      Complex.ofReal_div, Complex.ofReal_cos, one_div, Complex.ofReal_inv]
    rw [← Complex.ofReal_cos, cos_groverAngle_eq_sqrt_pred_div_sqrt hn]
    have hNpos : 0 < Real.sqrt (2 ^ n : ℝ) :=
      Real.sqrt_pos_of_pos (by positivity)
    have hMpos : 0 < Real.sqrt ((2 ^ n : ℝ) - 1) := by
      have hNgt1 : (1 : ℝ) < (2 ^ n : ℝ) := by exact_mod_cast hn
      exact Real.sqrt_pos_of_pos (by linarith)
    field_simp [ne_of_gt hNpos, ne_of_gt hMpos]
    rw [← Complex.ofReal_mul]
    congr 1
    field_simp [ne_of_gt hNpos]

private theorem matVec_phaseOracle_unique {n : ℕ} {marked : Marked n}
    {target : Q[n]} (hmarked : ∀ x, marked x = true ↔ x = target)
    (amp : Q[n] → ℂ) (x : Q[n]) :
    QMat.matVec (QMat.phaseOracle marked) amp x = if x = target then -amp x else amp x := by
  unfold QMat.matVec QMat.phaseOracle
  by_cases hx : x = target
  · subst x
    have hm : marked target = true := (hmarked target).mpr rfl
    simp [Matrix.diagonal, hm]
  · have hm : marked x = false := by
      rw [Bool.eq_false_iff]
      exact fun htrue => hx ((hmarked x).mp htrue)
    simp [Matrix.diagonal, hx, hm]

private theorem matVec_diffusion_apply {n : ℕ} (amp : Q[n] → ℂ) (x : Q[n]) :
    QMat.matVec (QMat.diffusion n) amp x =
      ((2 / (2 ^ n : ℝ) : ℝ) : ℂ) * (∑ y : Q[n], amp y) - amp x := by
  unfold QMat.matVec QMat.diffusion QMat.uniformDensity
  calc
    (∑ y : Q[n],
        (((2 : ℂ) • Matrix.of (fun _ _ : Q[n] => ((1 / (2 ^ n : ℝ)) : ℂ)) - 1)
          x y * amp y)) =
        ∑ y : Q[n],
          (((2 / (2 ^ n : ℝ) : ℝ) : ℂ) * amp y -
            (if x = y then (1 : ℂ) else 0) * amp y) := by
          apply Finset.sum_congr rfl
          intro y _hy
          split_ifs with hxy
          · subst y
            simp
            ring_nf
          · have hone : (1 : QMat n) x y = 0 := by simp [hxy]
            simp only [Matrix.sub_apply, hone, Complex.ofReal_pow, Complex.ofReal_ofNat,
              one_div, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, sub_zero,
              Complex.ofReal_div, zero_mul]
            ring_nf
    _ = ((2 / (2 ^ n : ℝ) : ℝ) : ℂ) * (∑ y : Q[n], amp y) - amp x := by
          simp [Finset.mul_sum]

private theorem sum_target_else {n : ℕ} (target : Q[n]) (a b : ℂ) :
    (∑ x : Q[n], if x = target then a else b) = a + ((2 ^ n - 1 : ℕ) : ℂ) * b := by
  have h := Finset.univ.sum_erase_add
    (fun x => if x = target then a else b) (Finset.mem_univ target)
  refine h.symm.trans ?_
  have herase :
      (∑ x ∈ (Finset.univ : Finset Q[n]).erase target,
          if x = target then a else b) =
        ∑ x ∈ (Finset.univ : Finset Q[n]).erase target, b := by
    apply Finset.sum_congr rfl
    intro x hx
    simp [Finset.mem_erase.mp hx]
  simp [herase, Finset.sum_const, Finset.card_erase_of_mem]
  ring_nf

theorem trace_successEffect_pureDensity_unique {n : ℕ} {marked : Marked n}
    {target : Q[n]} (hmarked : ∀ x, marked x = true ↔ x = target)
    (amp : Q[n] → ℂ) :
    Matrix.trace (QMat.successEffect marked * QMat.pureDensity amp) =
      amp target * star (amp target) := by
  unfold QMat.successEffect QMat.pureDensity
  calc
    Matrix.trace
        (Matrix.diagonal (fun x : Q[n] => if marked x then (1 : ℂ) else 0) *
          Matrix.of (fun x y : Q[n] => amp x * star (amp y))) =
        ∑ x : Q[n], if marked x then amp x * star (amp x) else 0 := by
      simp [Matrix.trace, Matrix.mul_apply, Matrix.diagonal]
    _ = ∑ x : Q[n], if x = target then amp x * star (amp x) else 0 := by
      apply Finset.sum_congr rfl
      intro x _hx
      by_cases hx : x = target
      · subst x
        simp [(hmarked target).mpr rfl]
      · have hm : marked x = false := by
          rw [Bool.eq_false_iff]
          exact fun htrue => hx ((hmarked x).mp htrue)
        simp [hm, hx]
    _ = amp target * star (amp target) := by
      simp

theorem expect_successEffect_pureDensity_unique {n : ℕ} {marked : Marked n}
    {target : Q[n]} (hmarked : ∀ x, marked x = true ↔ x = target)
    (amp : Q[n] → ℂ) :
    QMat.expect (QMat.successEffect marked) (QMat.pureDensity amp) =
      Complex.normSq (amp target) := by
  simp [QMat.expect, trace_successEffect_pureDensity_unique hmarked amp, Complex.mul_conj]

private theorem sum_phaseOracle_analyticAmp {n : ℕ} (target : Q[n]) (k : ℕ) :
    (∑ y : Q[n],
        if y = target then -analyticAmp target k y else analyticAmp target k y) =
      (((2 ^ n : ℝ) - 1) *
          (Real.cos (groverPhase n k) / Real.sqrt ((2 ^ n : ℝ) - 1)) -
        Real.sin (groverPhase n k) : ℝ) := by
  calc
    (∑ y : Q[n],
        if y = target then -analyticAmp target k y else analyticAmp target k y) =
        ∑ y : Q[n],
          if y = target then
            -((Real.sin (groverPhase n k) : ℝ) : ℂ)
          else
            ((Real.cos (groverPhase n k) /
              Real.sqrt ((2 ^ n : ℝ) - 1) : ℝ) : ℂ) := by
      apply Finset.sum_congr rfl
      intro y _hy
      by_cases hy : y = target <;> simp [analyticAmp, hy]
    _ =
        -((Real.sin (groverPhase n k) : ℝ) : ℂ) +
          ((2 ^ n - 1 : ℕ) : ℂ) *
            ((Real.cos (groverPhase n k) /
              Real.sqrt ((2 ^ n : ℝ) - 1) : ℝ) : ℂ) := by
      rw [sum_target_else]
    _ =
      (((2 ^ n : ℝ) - 1) *
          (Real.cos (groverPhase n k) / Real.sqrt ((2 ^ n : ℝ) - 1)) -
        Real.sin (groverPhase n k) : ℝ) := by
      have hNatReal : ((2 ^ n - 1 : ℕ) : ℝ) = (2 ^ n : ℝ) - 1 := by
        rw [Nat.cast_sub]
        · norm_num
        · exact Nat.one_le_pow n 2 (by norm_num)
      have hNatComplex :
          ((2 ^ n - 1 : ℕ) : ℂ) = (((2 ^ n : ℝ) - 1 : ℝ) : ℂ) := by
        norm_num [hNatReal]
      grind [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_add]

private theorem matVec_groverIterate_analyticAmp {n : ℕ} {marked : Marked n}
    {target : Q[n]} (hmarked : ∀ x, marked x = true ↔ x = target)
    (hn : 1 < 2 ^ n) (k : ℕ) :
    QMat.matVec (QMat.groverIterate marked) (analyticAmp target k) =
      analyticAmp target (k + 1) := by
  ext x
  simp_rw [QMat.groverIterate, QMat.matVec_mul, matVec_diffusion_apply,
    matVec_phaseOracle_unique hmarked, sum_phaseOracle_analyticAmp target k]
  by_cases hx : x = target
  · subst x
    have h := congrArg (fun r : ℝ => (r : ℂ)) (grover_target_step hn (groverPhase n k))
    simpa [analyticAmp,  ← groverPhase_succ n k] using h
  · have h := congrArg (fun r : ℝ => (r : ℂ)) (grover_unmarked_step hn (groverPhase n k))
    simpa [analyticAmp, hx, ← groverPhase_succ n k] using h

private theorem matVec_groverIterate_pow_uniformAmp {n : ℕ} {marked : Marked n}
    {target : Q[n]} (hmarked : ∀ x, marked x = true ↔ x = target) (hn : 1 < 2 ^ n) (k : ℕ) :
    QMat.matVec ((QMat.groverIterate marked) ^ k) (uniformAmp n) =
      analyticAmp target k := by
  induction k with
  | zero =>
      rw [pow_zero, QMat.matVec_one]
      exact (analyticAmp_zero_eq_uniformAmp hn target).symm
  | succ k ih =>
      rw [pow_succ', QMat.matVec_mul, ih]
      exact matVec_groverIterate_analyticAmp hmarked hn k

theorem programEvolve_zeroDensity_eq_pure_analyticAmp {n : ℕ}
    {marked : Marked n} {target : Q[n]}
    (hmarked : ∀ x, marked x = true ↔ x = target) (hn : 1 < 2 ^ n) (k : ℕ) :
    programEvolve marked k (QMat.zeroDensity n) =
      QMat.pureDensity (analyticAmp target k) := by
  unfold programEvolve
  rw [QMat.zeroDensity_eq_pureDensity_basisAmp_zero,
    QMat.evolve_pureDensity_eq_pureDensity,
    matVec_hadamardLayer_basisAmp_zero, QMat.evolve_pureDensity_eq_pureDensity,
    matVec_groverIterate_pow_uniformAmp hmarked hn k]

/-! ## Exact Four-Element Helpers -/

theorem basisOfBits_injective {n : ℕ} :
    Function.Injective (@QIndex.basisOfBits n) := by
  intro x y hxy
  funext i
  have hi := congrFun hxy i
  cases hx : x i <;> cases hy : y i <;>
    simp [QIndex.basisOfBits, QIndex.boolBit, hx, hy] at hi ⊢

theorem exec_evolve_mul {n : ℕ} (U V ρ : QMat n) :
    QMat.evolve (U * V) ρ = QMat.evolve U (QMat.evolve V ρ) := by
  simp [QMat.evolve, star_mul, Matrix.mul_assoc]

end LinearAlgebra
end GroverWP
end QProg

end

end QLean
