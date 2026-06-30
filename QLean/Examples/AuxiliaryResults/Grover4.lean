/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
import QLean.Examples.AuxiliaryResults.Common
import QLean.Gates.FullRegister.Hadamard
import QLean.Gates.FullRegister.Phase
import QLean.Syntax.Gates

/-!
# Exact Four-Element Grover Search Prerequisites
-/

namespace QLean

noncomputable section

open scoped Matrix ComplexOrder

namespace QMat
namespace Canonical

/-- The concrete phase oracle for the exact four-element Grover search. -/
def grover4Oracle (marked : QIndex.BitVec 2) : QMat 2 :=
  QMat.phaseOracle fun x => x = QIndex.basisOfBits marked

/-- Final density matrix for the exact four-element Grover search before measurement. -/
def grover4Final (marked : QIndex.BitVec 2) : QMat 2 :=
  QMat.evolve (QMat.diffusion 2)
    (QMat.evolve (grover4Oracle marked)
      (QMat.evolve (QMat.hadamardLayer 2) (QMat.zeroDensity 2)))

private theorem bitvec_two_cases (bits : QIndex.BitVec 2) :
    bits = (fun _ : Fin 2 => false) ∨
      bits = (fun i : Fin 2 => if i = 0 then false else true) ∨
      bits = (fun i : Fin 2 => if i = 0 then true else false) ∨
      bits = (fun _ : Fin 2 => true) := by
  cases h0 : bits 0 <;> cases h1 : bits 1
  · left
    funext i
    fin_cases i <;> simp [h0, h1]
  · right
    left
    funext i
    fin_cases i <;> simp [h0, h1]
  · right
    right
    left
    funext i
    fin_cases i <;> simp [h0, h1]
  · right
    right
    right
    funext i
    fin_cases i <;> simp [h0, h1]

private theorem fin_two_cases (b : Fin 2) : b = 0 ∨ b = 1 := by
  fin_cases b <;> simp

private theorem qindex_two_cases (x : Q[2]) :
    x = QIndex.basisOfBits (fun _ : Fin 2 => false) ∨
      x = QIndex.basisOfBits (fun i : Fin 2 => if i = 0 then false else true) ∨
      x = QIndex.basisOfBits (fun i : Fin 2 => if i = 0 then true else false) ∨
      x = QIndex.basisOfBits (fun _ : Fin 2 => true) := by
  rcases fin_two_cases (x 0) with h0 | h0 <;>
    rcases fin_two_cases (x 1) with h1 | h1
  · left
    funext i
    fin_cases i <;> simp [QIndex.basisOfBits, QIndex.boolBit, h0, h1]
  · right
    left
    funext i
    fin_cases i <;> simp [QIndex.basisOfBits, QIndex.boolBit, h0, h1]
  · right
    right
    left
    funext i
    fin_cases i <;> simp [QIndex.basisOfBits, QIndex.boolBit, h0, h1]
  · right
    right
    right
    funext i
    fin_cases i <;> simp [QIndex.basisOfBits, QIndex.boolBit, h0, h1]

private theorem qindex_two_univ :
    (Finset.univ : Finset Q[2]) =
      { QIndex.basisOfBits (fun _ : Fin 2 => false),
        QIndex.basisOfBits (fun i : Fin 2 => if i = 0 then false else true),
        QIndex.basisOfBits (fun i : Fin 2 => if i = 0 then true else false),
        QIndex.basisOfBits (fun _ : Fin 2 => true) } := by
  ext x
  simp only [Finset.mem_univ, true_iff]
  rcases qindex_two_cases x with rfl | rfl | rfl | rfl <;> simp

private abbrev basisAmp (x : Q[2]) : Q[2] → ℂ :=
  QMat.basisAmp x

private def uniformAmp : Q[2] → ℂ :=
  fun _ => (1 / 2 : ℂ)

private def groverPhasedAmp (marked : QIndex.BitVec 2) : Q[2] → ℂ :=
  fun x => if x = QIndex.basisOfBits marked then -(1 / 2 : ℂ) else (1 / 2 : ℂ)

private theorem zeroDensity_two_eq_pure_basis00 :
    QMat.zeroDensity 2 =
      QMat.pureDensity (basisAmp (QIndex.basisOfBits (fun _ : Fin 2 => false))) := by
  have hzero :
      QIndex.basisOfBits (fun _ : Fin 2 => false) = (0 : Q[2]) := by
    funext i
    simp [QIndex.basisOfBits, QIndex.boolBit]
  ext x y
  by_cases hx : x = (0 : Q[2]) <;>
    by_cases hy : y = (0 : Q[2])
  all_goals
  simp +decide [QMat.zeroDensity, QMat.projBits, QMat.projBasis,
    QMat.pureDensity, basisAmp, QMat.basisAmp, hzero, hx, hy, and_comm]

private theorem matVec_hadamardLayer_two_basis00 :
    QMat.matVec (QMat.hadamardLayer 2)
        (basisAmp (QIndex.basisOfBits (fun _ : Fin 2 => false))) =
      uniformAmp := by
  ext y
  rcases qindex_two_cases y with rfl | rfl | rfl | rfl
  all_goals
  simp +decide [QMat.matVec, basisAmp, QMat.basisAmp, uniformAmp, QMat.hadamardLayer,
    QMat.hadamardAmplitude]

private theorem matVec_oracle_uniformAmp (marked : QIndex.BitVec 2) :
    QMat.matVec (grover4Oracle marked) uniformAmp = groverPhasedAmp marked := by
  rcases bitvec_two_cases marked with rfl | rfl | rfl | rfl <;>
    ext y <;>
    rcases qindex_two_cases y with rfl | rfl | rfl | rfl <;>
    simp +decide [grover4Oracle, QMat.phaseOracle, QMat.matVec, uniformAmp,
      groverPhasedAmp, qindex_two_univ, Matrix.diagonal]

private theorem matVec_diffusion_two_apply (amp : Q[2] → ℂ) (x : Q[2]) :
    QMat.matVec (QMat.diffusion 2) amp x = ((1 / 2 : ℂ) * ∑ y, amp y) - amp x := by
  unfold QMat.matVec QMat.diffusion QMat.uniformDensity
  simp only [Complex.ofReal_pow, Complex.ofReal_ofNat, one_div, Matrix.smul_of,
    Matrix.sub_apply, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  have hdelta :
      (∑ y : Q[2], (if x = y then (1 : ℂ) else 0) * amp y) = amp x := by
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hy
      have hxy : x ≠ y := fun h => hy h.symm
      simp [hxy]
    · intro hx
      exact (hx (Finset.mem_univ x)).elim
  calc
    (∑ y : Q[2], (2 * (2 ^ 2)⁻¹ - if x = y then 1 else 0) * amp y) =
        (∑ y : Q[2], (2⁻¹ : ℂ) * amp y) -
          ∑ y : Q[2], (if x = y then (1 : ℂ) else 0) * amp y := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro y _
      by_cases hxy : x = y
      · subst y
        simp
        ring_nf
      · simp [hxy]
        norm_num
    _ = (∑ y : Q[2], (2⁻¹ : ℂ) * amp y) - amp x := by
      rw [hdelta]

private theorem sum_groverPhasedAmp (marked : QIndex.BitVec 2) :
    (∑ x, groverPhasedAmp marked x) = 1 := by
  rcases bitvec_two_cases marked with rfl | rfl | rfl | rfl <;>
    simp +decide [groverPhasedAmp, qindex_two_univ]
  all_goals norm_num

private theorem matVec_diffusion_groverPhasedAmp (marked : QIndex.BitVec 2) :
    QMat.matVec (QMat.diffusion 2) (groverPhasedAmp marked) =
      basisAmp (QIndex.basisOfBits marked) := by
  ext y
  rw [matVec_diffusion_two_apply, sum_groverPhasedAmp]
  by_cases hy : y = QIndex.basisOfBits marked <;>
    simp [groverPhasedAmp, basisAmp, QMat.basisAmp, hy]
  · norm_num

/-- The exact four-element Grover state is the marked computational-basis projector. -/
theorem grover4Final_eq_projBits
    (marked : QIndex.BitVec 2) :
    grover4Final marked = QMat.projBits marked := by
  unfold grover4Final
  rw [zeroDensity_two_eq_pure_basis00, QMat.evolve_pureDensity_eq_pureDensity,
    matVec_hadamardLayer_two_basis00, QMat.evolve_pureDensity_eq_pureDensity,
    matVec_oracle_uniformAmp marked, QMat.evolve_pureDensity_eq_pureDensity,
    matVec_diffusion_groverPhasedAmp marked]
  ext x y
  by_cases hx : x = QIndex.basisOfBits marked <;>
    by_cases hy : y = QIndex.basisOfBits marked
  all_goals
  simp [QMat.projBits, QMat.projBasis, QMat.pureDensity, basisAmp,
    QMat.basisAmp, hx, hy, and_comm]

/-- The marked-basis success effect has expectation `1` on the marked projector. -/
theorem expect_successEffect_projBits (marked : QIndex.BitVec 2) :
    QMat.expect (QMat.successEffect (fun x => x = QIndex.basisOfBits marked))
      (QMat.projBits marked) = 1 := by
  rcases bitvec_two_cases marked with rfl | rfl | rfl | rfl <;>
    simp +decide [QMat.successEffect, QMat.expect, QMat.projBits, QMat.projBasis,
      Matrix.trace, Matrix.mul_apply, qindex_two_univ]

private theorem wpMeasBitVecCont_projBits (marked : QIndex.BitVec 2) :
    QProg.QHoare.wpMeasBitVecCont (fun i : Fin 2 => i)
      (fun out ρ => QMat.expect (if out = marked then (1 : QMat 2) else 0) ρ)
      (QMat.projBits marked) = 1 := by
  rcases bitvec_two_cases marked with rfl | rfl | rfl | rfl <;>
    simp +decide [QProg.QHoare.wpMeasBitVecCont, QProg.QHoare.wpMeasQubitsCont,
      List.finRange,
      QMat.measProjector, QMat.bitAt, QMat.expect,
      QMat.projBits, QMat.projBasis, Matrix.trace,
      Matrix.mul_apply, qindex_two_univ]

/--
Exact Grover-4 measurement success: after one marked phase query and diffusion step, measuring
all two qubits returns the marked bitstring with probability `1`.
-/
theorem grover4_correct
    (marked : QIndex.BitVec 2) :
    QProg.QHoare.wpMeasBitVecCont (fun i : Fin 2 => i)
      (fun out ρ => QMat.expect (if out = marked then (1 : QMat 2) else 0) ρ)
      (grover4Final marked) = 1 := by
  rw [grover4Final_eq_projBits marked]
  exact wpMeasBitVecCont_projBits marked

end Canonical
end QMat

end

end QLean
