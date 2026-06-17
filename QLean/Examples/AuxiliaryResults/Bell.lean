/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
import QLean.Foundation.Basis
import QLean.Gates.FullRegister.BasisMaps
import QLean.Gates.SingleQubit

/-!
# Bell-State Linear Algebra Obligations

This file contains the Bell-demo matrix/probability facts used by the algorithm files.
It deliberately stays below the `QProg` syntax/WP layer.
-/

namespace QLean

noncomputable section

open scoped Matrix ComplexOrder

namespace QMat

@[simp] theorem expect_zero_left {n : ℕ} (ρ : QMat n) :
    QMat.expect (0 : QMat n) ρ = 0 := by
  simp [QMat.expect]

@[simp] theorem expect_zero_right {n : ℕ} (A : QMat n) :
    QMat.expect A (0 : QMat n) = 0 := by
  simp [QMat.expect]

@[simp] theorem expect_add_left {n : ℕ} (A B ρ : QMat n) :
    QMat.expect (A + B) ρ = QMat.expect A ρ + QMat.expect B ρ := by
  simp [QMat.expect, Matrix.add_mul, Matrix.trace_add]

@[simp] theorem expect_add_right {n : ℕ} (A ρ σ : QMat n) :
    QMat.expect A (ρ + σ) = QMat.expect A ρ + QMat.expect A σ := by
  simp [QMat.expect, Matrix.mul_add, Matrix.trace_add]

@[simp] theorem expect_neg_left {n : ℕ} (A ρ : QMat n) :
    QMat.expect (-A) ρ = -QMat.expect A ρ := by
  simp [QMat.expect]

@[simp] theorem expect_neg_right {n : ℕ} (A ρ : QMat n) :
    QMat.expect A (-ρ) = -QMat.expect A ρ := by
  simp [QMat.expect]

@[simp] theorem expect_real_smul_left {n : ℕ} (r : ℝ) (A ρ : QMat n) :
    QMat.expect ((r : ℂ) • A) ρ = r * QMat.expect A ρ := by
  simp [QMat.expect]

@[simp] theorem expect_real_smul_right {n : ℕ} (r : ℝ) (A ρ : QMat n) :
    QMat.expect A ((r : ℂ) • ρ) = r * QMat.expect A ρ := by
  simp [QMat.expect]

theorem expect_evolve {n : ℕ} (A U ρ : QMat n) :
    QMat.expect A (QMat.evolve U ρ) = QMat.expect (star U * A * U) ρ := by
  unfold QMat.expect QMat.evolve
  calc
    (A * (U * ρ * star U)).trace.re = (((A * U) * ρ) * star U).trace.re := by
      simp [Matrix.mul_assoc]
    _ = (star U * ((A * U) * ρ)).trace.re := by
      rw [Matrix.trace_mul_comm]
    _ = ((star U * A * U) * ρ).trace.re := by
      simp [Matrix.mul_assoc]

theorem expect_measProjector {n : ℕ} (A : QMat n) (target : Fin n) (outcome : Bool)
    (ρ : QMat n) :
    QMat.expect A (QMat.measProjector target outcome * ρ * QMat.measProjector target outcome) =
      QMat.expect (QMat.measProjector target outcome * A * QMat.measProjector target outcome)
        ρ := by
  unfold QMat.expect
  calc
    (A * (QMat.measProjector target outcome * ρ * QMat.measProjector target outcome)).trace.re =
        (((A * QMat.measProjector target outcome) * ρ) *
          QMat.measProjector target outcome).trace.re := by
      simp [Matrix.mul_assoc]
    _ = (QMat.measProjector target outcome *
        ((A * QMat.measProjector target outcome) * ρ)).trace.re := by
      rw [Matrix.trace_mul_comm]
    _ = ((QMat.measProjector target outcome * A * QMat.measProjector target outcome) *
        ρ).trace.re := by
      simp [Matrix.mul_assoc]

/-- The matrix unit `|x⟩⟨y|` in the computational basis. -/
def basisOuter {n : ℕ} (x y : Q[n]) : QMat n :=
  Matrix.of fun a b => if a = x ∧ b = y then 1 else 0

@[simp] theorem basisOuter_apply {n : ℕ} (x y a b : Q[n]) :
    basisOuter x y a b = if a = x ∧ b = y then 1 else 0 :=
  rfl

@[simp] theorem basisOuter_mul_basisOuter {n : ℕ} (x y z w : Q[n]) :
    basisOuter x y * basisOuter z w = if y = z then basisOuter x w else 0 := by
  ext a b
  by_cases hyz : y = z
  · subst z
    by_cases hax : a = x
    · subst a
      by_cases hbw : b = w
      · subst b
        simp [basisOuter, Matrix.mul_apply]
      · simp [basisOuter, Matrix.mul_apply, hbw]
    · simp [basisOuter, Matrix.mul_apply, hax]
  · simp only [basisOuter, Matrix.mul_apply, Matrix.of_apply]
    rw [if_neg hyz]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hzi : z = i
    · by_cases hyi : y = i
      · exact (hyz (hyi.trans hzi.symm)).elim
      · simp [hzi, hyi, eq_comm]
    · simp [hzi, eq_comm]

@[simp] theorem trace_basisOuter {n : ℕ} (x y : Q[n]) :
    QMat.trace (basisOuter x y) = if x = y then 1 else 0 := by
  unfold QMat.trace basisOuter
  by_cases hxy : x = y
  · subst y
    simp [Matrix.trace]
  · simp [Matrix.trace, hxy]

@[simp] theorem expect_basisOuter_basisOuter {n : ℕ} (x y z w : Q[n]) :
    QMat.expect (basisOuter x y) (basisOuter z w) =
      if y = z ∧ w = x then 1 else 0 := by
  unfold QMat.expect
  by_cases hyz : y = z
  · subst z
    rw [basisOuter_mul_basisOuter, if_pos rfl]
    change (QMat.trace (basisOuter x w)).re = if y = y ∧ w = x then 1 else 0
    rw [trace_basisOuter]
    by_cases hwx : w = x
    · subst w
      simp
    · have hxw : x ≠ w := fun h => hwx h.symm
      simp [hwx, hxw]
  · rw [basisOuter_mul_basisOuter, if_neg hyz]
    simp [hyz]

theorem mul_basisOuter_apply {n : ℕ} (A : QMat n) (x y a b : Q[n]) :
    (A * basisOuter x y) a b = if b = y then A a x else 0 := by
  unfold basisOuter
  simp only [Matrix.mul_apply, Matrix.of_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single x]
  · by_cases hby : b = y <;> simp [hby]
  · intro z _ hz
    simp [hz]
  · intro hx
    exact (hx (Finset.mem_univ x)).elim

theorem basisOuter_mul_apply {n : ℕ} (A : QMat n) (x y a b : Q[n]) :
    (basisOuter x y * A) a b = if a = x then A y b else 0 := by
  unfold basisOuter
  simp only [Matrix.mul_apply, Matrix.of_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single y]
  · by_cases hax : a = x <;> simp [hax]
  · intro z _ hz
    simp [hz]
  · intro hy
    exact (hy (Finset.mem_univ y)).elim

theorem measProjector_mul_basisOuter {n : ℕ} (target : Fin n) (outcome : Bool)
    (x y : Q[n]) :
    QMat.measProjector target outcome * basisOuter x y =
      if QMat.bitAt target x = outcome then basisOuter x y else 0 := by
  ext a b
  rw [mul_basisOuter_apply]
  by_cases hby : b = y
  · subst b
    by_cases hx : QMat.bitAt target x = outcome
    · by_cases hax : a = x <;> simp [QMat.measProjector, basisOuter, hx, hax]
    · by_cases hax : a = x <;> simp [QMat.measProjector, hx, hax]
  · by_cases hx : QMat.bitAt target x = outcome
    · simp [basisOuter, hx, hby]
    · simp [hx, hby]

theorem basisOuter_mul_measProjector {n : ℕ} (target : Fin n) (outcome : Bool)
    (x y : Q[n]) :
    basisOuter x y * QMat.measProjector target outcome =
      if QMat.bitAt target y = outcome then basisOuter x y else 0 := by
  ext a b
  rw [basisOuter_mul_apply]
  by_cases hax : a = x
  · subst a
    by_cases hy : QMat.bitAt target y = outcome
    · by_cases hby : b = y
      · simp [QMat.measProjector, basisOuter, hy, hby]
      · have hyb : y ≠ b := fun h => hby h.symm
        simp [QMat.measProjector, basisOuter, hy, hby, hyb]
    · by_cases hby : b = y <;> simp [QMat.measProjector, hy, hby]
  · by_cases hy : QMat.bitAt target y = outcome
    · simp [basisOuter, hy, hax]
    · simp [hy, hax]

theorem measProjector_mul_basisOuter_mul {n : ℕ} (target : Fin n) (outcome : Bool)
    (x y : Q[n]) :
    QMat.measProjector target outcome * basisOuter x y * QMat.measProjector target outcome =
      if QMat.bitAt target x = outcome ∧ QMat.bitAt target y = outcome then
        basisOuter x y
      else
        0 := by
  rw [measProjector_mul_basisOuter]
  by_cases hx : QMat.bitAt target x = outcome
  · rw [if_pos hx, basisOuter_mul_measProjector]
    by_cases hy : QMat.bitAt target y = outcome <;> simp [hx, hy]
  · rw [if_neg hx]
    simp [hx]

namespace Bell

/-- Interpret a measurement bit as the corresponding computational-basis index. -/
def boolBit : Bool → Fin 2 :=
  QIndex.boolBit

/-- The two-qubit computational-basis bitstring `|b0 b1⟩`. -/
def basis2 (b0 b1 : Bool) : Q[2] :=
  fun q => if q = (0 : Fin 2) then boolBit b0 else boolBit b1

def ket00 : Q[2] :=
  basis2 false false

def ket10 : Q[2] :=
  basis2 true false

def ket11 : Q[2] :=
  basis2 true true

private theorem fin_two_cases (b : Fin 2) : b = 0 ∨ b = 1 := by
  fin_cases b <;> simp

private theorem qindex_two_cases (x : Q[2]) :
    x = ket00 ∨ x = basis2 false true ∨ x = ket10 ∨ x = ket11 := by
  rcases fin_two_cases (x 0) with h0 | h0 <;>
    rcases fin_two_cases (x 1) with h1 | h1
  · left
    funext i
    fin_cases i <;> simp [ket00, basis2, boolBit, QIndex.boolBit, h0, h1]
  · right
    left
    funext i
    fin_cases i <;> simp [basis2, boolBit, QIndex.boolBit, h0, h1]
  · right
    right
    left
    funext i
    fin_cases i <;> simp [ket10, basis2, boolBit, QIndex.boolBit, h0, h1]
  · right
    right
    right
    funext i
    fin_cases i <;> simp [ket11, basis2, boolBit, QIndex.boolBit, h0, h1]

private theorem qindex_two_univ :
    (Finset.univ : Finset Q[2]) =
      { fun _ => 0,
        fun _ => 1,
        fun q => if q = 0 then 0 else 1,
        fun q => if q = 0 then 1 else 0 } := by
  ext x
  simp only [Finset.mem_univ, true_iff]
  rcases qindex_two_cases x with rfl | rfl | rfl | rfl
  · have h : ket00 = (fun _ : Fin 2 => (0 : Fin 2)) := by
      funext i
      fin_cases i <;> rfl
    rw [h]
    simp
  · have h : basis2 false true = (fun q : Fin 2 => if q = 0 then 0 else 1) := by
      funext i
      fin_cases i <;> rfl
    rw [h]
    simp
  · have h : ket10 = (fun q : Fin 2 => if q = 0 then 1 else 0) := by
      funext i
      fin_cases i <;> rfl
    rw [h]
    simp
  · have h : ket11 = (fun _ : Fin 2 => (1 : Fin 2)) := by
      funext i
      fin_cases i <;> rfl
    rw [h]
    simp

private theorem real_sqrt_two_sq :
    (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
  rw [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]

private theorem complex_inv_sqrt_two_mul :
    (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = (2 : ℂ)⁻¹ := by
  have hmul : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    rw [← Complex.ofReal_mul]
    norm_num [← pow_two, real_sqrt_two_sq]
  rw [← mul_inv_rev, hmul]

/-- The rank-one computational-basis projector `|x⟩⟨x|`. -/
def projBasis (x : Q[2]) : QMat 2 :=
  Matrix.of fun y z => if y = x ∧ z = x then 1 else 0

/-- The initial density matrix `|00⟩⟨00|`. -/
abbrev proj00 : QMat 2 :=
  projBasis (basis2 false false)

/-- The density matrix `|11⟩⟨11|`. -/
abbrev proj11 : QMat 2 :=
  projBasis (basis2 true true)

abbrev proj10 : QMat 2 :=
  projBasis ket10

/-- Hadamard on qubit `0`, embedded into the two-qubit register. -/
def H_on_0 : QMat 2 :=
  QMat.applySingle (0 : Fin 2) Gate.H

/-- The full-register CNOT matrix with control `0` and target `1`. -/
def CNOT_0_1 : QMat 2 :=
  QMat.cnotMatrix (0 : Fin 2) (1 : Fin 2)

/-- Matrix state after Bell preparation. -/
def prepared (H CNOT ρ : QMat 2) : QMat 2 :=
  QMat.evolve CNOT (QMat.evolve H ρ)

/-- Post-measurement branch for measuring one qubit. -/
def measured (target : Fin 2) (outcome : Bool) (ρ : QMat 2) : QMat 2 :=
  QMat.measProjector target outcome * ρ * QMat.measProjector target outcome

theorem expect_measured (A : QMat 2) (target : Fin 2) (outcome : Bool) (ρ : QMat 2) :
    QMat.expect A (measured target outcome ρ) =
      QMat.expect (QMat.measProjector target outcome * A * QMat.measProjector target outcome)
        ρ := by
  rw [measured, QMat.expect_measProjector]

@[simp] theorem projBasis_apply (x y z : Q[2]) :
    projBasis x y z = if y = x ∧ z = x then 1 else 0 :=
  rfl

theorem projBasis_eq_basisOuter (x : Q[2]) :
    projBasis x = QMat.basisOuter x x :=
  rfl

@[simp] theorem expect_projBasis (x : Q[2]) (ρ : QMat 2) :
    QMat.expect (projBasis x) ρ = (ρ x x).re := by
  suffices Matrix.trace (projBasis x * ρ) = ρ x x by
    simpa [QMat.expect] using congrArg Complex.re this
  unfold projBasis
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply, ite_mul,
    one_mul, zero_mul]
  rw [Finset.sum_eq_single x]
  · rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hy
      simp [hy]
    · intro hx
      exact (hx (Finset.mem_univ x)).elim
  · intro y _ hy
    simp [hy]
  · intro hx
    exact (hx (Finset.mem_univ x)).elim

@[simp] theorem expect_projBasis_projBasis (x y : Q[2]) :
    QMat.expect (projBasis x) (projBasis y) = if x = y then 1 else 0 := by
  rw [expect_projBasis]
  by_cases h : x = y <;> simp [projBasis, h, eq_comm]

@[simp] theorem expect_one_projBasis (x : Q[2]) :
    QMat.expect (1 : QMat 2) (projBasis x) = 1 := by
  unfold QMat.expect projBasis
  simp [Matrix.trace]

theorem expect_projBasis_nonneg_of_posSemidef (x : Q[2]) {ρ : QMat 2}
    (hρ : ρ.PosSemidef) :
    0 ≤ QMat.expect (projBasis x) ρ := by
  rw [expect_projBasis]
  have hx : 0 ≤ (ρ x x).re ∧ 0 = (ρ x x).im := by
    simpa [Finsupp.sum_single_index, Complex.le_def] using hρ.2 (Finsupp.single x 1)
  exact hx.1

@[simp] theorem bitAt_basis2_zero (b0 b1 : Bool) :
    QMat.bitAt (0 : Fin 2) (basis2 b0 b1) = b0 := by
  cases b0 <;> cases b1 <;> simp [basis2, boolBit, QIndex.boolBit, QMat.bitAt]

@[simp] theorem bitAt_basis2_one (b0 b1 : Bool) :
    QMat.bitAt (1 : Fin 2) (basis2 b0 b1) = b1 := by
  cases b0 <;> cases b1 <;> simp [basis2, boolBit, QIndex.boolBit, QMat.bitAt]

@[simp] theorem measured_add (target : Fin 2) (outcome : Bool) (ρ σ : QMat 2) :
    measured target outcome (ρ + σ) =
      measured target outcome ρ + measured target outcome σ := by
  unfold measured
  simp [Matrix.mul_add, Matrix.add_mul]

@[simp] theorem measured_smul (c : ℂ) (target : Fin 2) (outcome : Bool) (ρ : QMat 2) :
    measured target outcome (c • ρ) = c • measured target outcome ρ := by
  unfold measured
  simp

@[simp] theorem measured_real_smul (r : ℝ) (target : Fin 2) (outcome : Bool) (ρ : QMat 2) :
    measured target outcome (((r : ℂ) • ρ)) = (r : ℂ) • measured target outcome ρ :=
  measured_smul (r : ℂ) target outcome ρ

@[simp] theorem measured_basisOuter (target : Fin 2) (outcome : Bool) (x y : Q[2]) :
    measured target outcome (QMat.basisOuter x y) =
      if QMat.bitAt target x = outcome ∧ QMat.bitAt target y = outcome then
        QMat.basisOuter x y
      else
        0 := by
  rw [measured, QMat.measProjector_mul_basisOuter_mul]

@[simp] theorem measured_projBasis (target : Fin 2) (outcome : Bool) (x : Q[2]) :
    measured target outcome (projBasis x) =
      if QMat.bitAt target x = outcome then projBasis x else 0 := by
  rw [measured, projBasis_eq_basisOuter, QMat.measProjector_mul_basisOuter_mul]
  by_cases h : QMat.bitAt target x = outcome <;> simp [h]

@[simp] theorem measured_proj00_one_false :
    measured (1 : Fin 2) false proj00 = proj00 := by
  rw [proj00, measured_projBasis, bitAt_basis2_one]
  simp

@[simp] theorem measured_proj00_one_true :
    measured (1 : Fin 2) true proj00 = 0 := by
  rw [proj00, measured_projBasis, bitAt_basis2_one]
  simp

@[simp] theorem measured_proj11_one_false :
    measured (1 : Fin 2) false proj11 = 0 := by
  rw [proj11, measured_projBasis, bitAt_basis2_one]
  simp

@[simp] theorem measured_proj11_one_true :
    measured (1 : Fin 2) true proj11 = proj11 := by
  rw [proj11, measured_projBasis, bitAt_basis2_one]
  simp

private def bellAmp : Q[2] → ℂ :=
  fun x => if x = ket00 ∨ x = ket11 then (Real.sqrt 2 : ℂ)⁻¹ else 0

private theorem ket00_ne_ket11 : ket00 ≠ ket11 := by
  intro h
  have h0 := congrFun h (0 : Fin 2)
  norm_num [ket00, ket11, basis2, boolBit, QIndex.boolBit] at h0

private theorem proj00_eq_pure_basisAmp_ket00 :
    proj00 = QMat.pureDensity (QMat.basisAmp ket00) := by
  ext x y
  by_cases hx : x = basis2 false false <;> by_cases hy : y = basis2 false false <;>
    simp [proj00, projBasis, QMat.pureDensity, QMat.basisAmp, ket00, hx, hy, and_comm]

private theorem matVec_bell_prepared_basisAmp :
    QMat.matVec CNOT_0_1 (QMat.matVec H_on_0 (QMat.basisAmp ket00)) = bellAmp := by
  ext y
  rcases qindex_two_cases y with rfl | rfl | rfl | rfl
  all_goals
    simp +decide [QMat.matVec, H_on_0, CNOT_0_1, QMat.applySingle, QMat.cnotMatrix,
      QMat.basisMapMatrix, QMat.flipBit, QMat.basisAmp, bellAmp, ket00, ket10, ket11,
      basis2, Gate.H_apply, Matrix.piKronecker, Matrix.one_apply, qindex_two_univ,
      QIndex.boolBit, boolBit]

private theorem pureDensity_bellAmp :
    QMat.pureDensity bellAmp =
      ((1 / 2 : ℂ) •
        (QMat.basisOuter ket00 ket00 + QMat.basisOuter ket00 ket11 +
          QMat.basisOuter ket11 ket00 + QMat.basisOuter ket11 ket11)) := by
  ext a b
  have h1100 : ket11 ≠ ket00 := ket00_ne_ket11.symm
  by_cases ha0 : a = ket00 <;> by_cases ha1 : a = ket11 <;>
    by_cases hb0 : b = ket00 <;> by_cases hb1 : b = ket11 <;>
    simp [QMat.pureDensity, QMat.basisOuter, bellAmp, ha0, ha1, hb0, hb1,
      ket00_ne_ket11, h1100] at *
  all_goals simpa using complex_inv_sqrt_two_mul

@[simp] theorem bell_prepared_proj00 :
    prepared H_on_0 CNOT_0_1 proj00 =
      ((1 / 2 : ℂ) •
        (QMat.basisOuter ket00 ket00 + QMat.basisOuter ket00 ket11 +
          QMat.basisOuter ket11 ket00 + QMat.basisOuter ket11 ket11)) := by
  rw [prepared, proj00_eq_pure_basisAmp_ket00, QMat.evolve_pureDensity_eq_pureDensity,
    QMat.evolve_pureDensity_eq_pureDensity, matVec_bell_prepared_basisAmp,
    pureDensity_bellAmp]

@[simp] theorem measured_bell_false :
    measured (0 : Fin 2) false (prepared H_on_0 CNOT_0_1 proj00) =
      (((1 / 2 : ℝ) : ℂ) • proj00) := by
  rw [bell_prepared_proj00]
  simp [measured_smul, measured_add, measured_basisOuter, bitAt_basis2_zero, proj00,
    projBasis_eq_basisOuter, ket00, ket11]

@[simp] theorem measured_bell_true :
    measured (0 : Fin 2) true (prepared H_on_0 CNOT_0_1 proj00) =
      (((1 / 2 : ℝ) : ℂ) • proj11) := by
  rw [bell_prepared_proj00]
  simp [measured_smul, measured_add, measured_basisOuter, bitAt_basis2_zero, proj11,
    projBasis_eq_basisOuter, ket00, ket11]

theorem remote_collapse_total_effect (ρ : QMat 2) :
    QMat.expect proj00 (measured (0 : Fin 2) false (prepared H_on_0 CNOT_0_1 ρ)) +
        QMat.expect proj11 (measured (0 : Fin 2) true (prepared H_on_0 CNOT_0_1 ρ)) =
      QMat.expect (proj00 + proj10) ρ := by
  simp +decide [prepared, H_on_0, CNOT_0_1, proj00, proj10, proj11, projBasis,
    QMat.expect, QMat.evolve, measured, QMat.measProjector, QMat.applySingle,
    QMat.cnotMatrix, QMat.basisMapMatrix, QMat.flipBit, QMat.bitAt, ket10, Gate.H_apply,
    Matrix.mul_apply, Matrix.trace, Matrix.diag_apply, Matrix.one_apply, Matrix.piKronecker,
    qindex_two_univ]
  ring_nf
  rw [real_sqrt_two_sq]
  ring

/-
Bell remote-collapse matrix obligation: after preparing from `|00><00|` and measuring
qubit `0`, the branch-dependent `|00>`/`|11>` effect has total expectation `1`.
-/
-- Reduces to the two half-probability measurement branches and projector orthonormality.
theorem remote_collapse :
    let ρBell := prepared H_on_0 CNOT_0_1 proj00
    QMat.expect proj00 (measured (0 : Fin 2) false ρBell) +
      QMat.expect proj11 (measured (0 : Fin 2) true ρBell) = 1 := by
  dsimp only
  rw [measured_bell_false, measured_bell_true]
  simp [-one_div, -Complex.ofReal_div, -Complex.coe_smul]

/-
Positivity-aware Bell remote-collapse inequality for arbitrary input matrices.
-/
-- Pulls the total effect back to `proj00 + proj10`, then uses positivity of the extra diagonal.
theorem remote_collapse_total
    (ρ : QMat 2) (hρ : ρ.PosSemidef) :
    let ρBell := prepared H_on_0 CNOT_0_1 ρ
    QMat.expect proj00 ρ ≤
      QMat.expect proj00 (measured (0 : Fin 2) false ρBell) +
        QMat.expect proj11 (measured (0 : Fin 2) true ρBell) := by
  dsimp only
  rw [remote_collapse_total_effect, QMat.expect_add_left]
  have h10 : 0 ≤ QMat.expect proj10 ρ := by
    rw [proj10]
    exact expect_projBasis_nonneg_of_posSemidef ket10 hρ
  exact le_add_of_nonneg_right h10

/-
The `false` branch of the left-qubit Bell measurement has probability `1 / 2`.
-/
-- Uses that the false branch is `(1 / 2) • proj00` and the zero effect contributes nothing.
theorem left_false_probability :
    let ρBell := prepared H_on_0 CNOT_0_1 proj00
    QMat.expect (1 : QMat 2) (measured (0 : Fin 2) false ρBell) +
      QMat.expect (0 : QMat 2) (measured (0 : Fin 2) true ρBell) = (1 / 2 : ℝ) := by
  dsimp only
  rw [measured_bell_false, measured_bell_true]
  simp [-one_div, -Complex.ofReal_div, -Complex.coe_smul]

/-
The `true` branch of the left-qubit Bell measurement has probability `1 / 2`.
-/
-- Uses that the true branch is `(1 / 2) • proj11` and the zero effect contributes nothing.
theorem left_true_probability :
    let ρBell := prepared H_on_0 CNOT_0_1 proj00
    QMat.expect (0 : QMat 2) (measured (0 : Fin 2) false ρBell) +
      QMat.expect (1 : QMat 2) (measured (0 : Fin 2) true ρBell) = (1 / 2 : ℝ) := by
  dsimp only
  rw [measured_bell_false, measured_bell_true]
  simp [-one_div, -Complex.ofReal_div, -Complex.coe_smul]

/-
Both computational-basis measurements of the Bell pair return equal bits with total
probability `1`.
-/
-- Measures the already-collapsed branches on the second qubit.
theorem both_correlated :
    let ρBell := prepared H_on_0 CNOT_0_1 proj00
    let ρ0 := measured (0 : Fin 2) false ρBell
    let ρ1 := measured (0 : Fin 2) true ρBell
    (QMat.expect (1 : QMat 2) (measured (1 : Fin 2) false ρ0) +
        QMat.expect (0 : QMat 2) (measured (1 : Fin 2) true ρ0)) +
      (QMat.expect (0 : QMat 2) (measured (1 : Fin 2) false ρ1) +
        QMat.expect (1 : QMat 2) (measured (1 : Fin 2) true ρ1)) = 1 := by
  dsimp only
  rw [measured_bell_false, measured_bell_true]
  simp [-one_div, -Complex.ofReal_div, -Complex.coe_smul]

end Bell
end QMat

end

end QLean
