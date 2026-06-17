/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
import QLean.Syntax.Gates
import QLean.Syntax.WP
import QLean.Examples.AuxiliaryResults.Bell

/-!
# Bell Measurement Demos for the WP Layer

This file gives small fixed-register examples for the current `QProg σ n` weakest-precondition
infrastructure.  The examples prepare a Bell pair from `|00⟩` and then measure either one
qubit or both qubits.

The key non-local point is the single-measurement theorem: after measuring qubit `0`, the
returned classical bit determines the full two-qubit post-measurement branch, including the
unmeasured qubit.
-/

namespace QLean

noncomputable section

open scoped Matrix ComplexOrder

namespace QProg
namespace Bell

/-! ## Demo 1: prepare a Bell pair, then measure the left qubit -/

/--
Prepare `( |00⟩ + |11⟩ ) / sqrt 2` from `|00⟩`, then measure qubit `0`.

The classical state `σ` is threaded through unchanged by this program.
-/
def bellMeasureLeft {σ : Type} : QProg σ 2 Bool := do
  QProg.applyUnitary (σ := σ) QMat.Bell.H_on_0
    (QMat.applySingle_unitary (0 : Fin 2) Gate.H Gate.H_unitary)
  QProg.applyUnitary (σ := σ) QMat.Bell.CNOT_0_1
    (QMat.cnotMatrix_unitary (0 : Fin 2) (1 : Fin 2) (by decide))
  QProg.meas (σ := σ) (0 : Fin 2)

/--
Branch-dependent remote-collapse postcondition.

If the measured bit is `false`, the final branch should be `|00⟩⟨00|`; if it is `true`,
the final branch should be `|11⟩⟨11|`.
-/
def sameBitPost {σ : Type} : Bool → σ → QMat 2
  | false, _ => QMat.Bell.proj00
  | true, _ => QMat.Bell.proj11

/-- Postcondition that only counts the `false` measurement branch. -/
def returnedFalse {σ : Type} : Bool → σ → QMat 2
  | false, _ => 1
  | true, _ => 0

/-- Postcondition that only counts the `true` measurement branch. -/
def returnedTrue {σ : Type} : Bool → σ → QMat 2
  | false, _ => 0
  | true, _ => 1

/--
Remote collapse for a Bell pair.

Starting from `|00⟩⟨00|`, the branch-dependent postcondition has total expectation `1`:
the returned bit determines whether the full post-measurement state is `|00⟩⟨00|` or
`|11⟩⟨11|`.
-/
theorem bellMeasureLeft_remote_collapse {σ : Type} (s : σ) :
    QHoare.wpTotal (bellMeasureLeft (σ := σ)) (sameBitPost (σ := σ)) s
      QMat.Bell.proj00 = 1
    := by
  unfold bellMeasureLeft
  rw [QHoare.wpTotal_applyUnitary_bind]
  rw [QHoare.wpTotal_applyUnitary_bind]
  rw [QHoare.wpTotal_meas]
  simpa [sameBitPost, QProg.Exec.evolve, QMat.measProjector, QMat.Bell.prepared,
    QMat.Bell.measured] using
    QMat.Bell.remote_collapse

/--
Pointwise positive-state form of the same remote-collapse specification.

Under that side condition, the `|00⟩⟨00|`
pre-expectation is bounded by the branch-dependent remote-collapse post-expectation.
-/
theorem bellMeasureLeft_remote_collapse_total {σ : Type} (s : σ) (ρ : QMat 2)
    (hρ : ρ.PosSemidef) :
    QMat.expect QMat.Bell.proj00 ρ ≤
      QHoare.wpTotal (bellMeasureLeft (σ := σ)) (sameBitPost (σ := σ)) s ρ
    := by
  unfold bellMeasureLeft
  rw [QHoare.wpTotal_applyUnitary_bind]
  rw [QHoare.wpTotal_applyUnitary_bind]
  rw [QHoare.wpTotal_meas]
  simpa [sameBitPost, QProg.Exec.evolve, QMat.measProjector, QMat.Bell.prepared,
    QMat.Bell.measured] using
    QMat.Bell.remote_collapse_total ρ hρ

/-- Physical Hoare-total form over subnormalised input states. -/
theorem bellMeasureLeft_remote_collapse_physicalTotal {σ : Type} :
    QHoare.PhysicalTotal (fun _ : σ => QMat.Bell.proj00)
      (bellMeasureLeft (σ := σ)) (sameBitPost (σ := σ)) := by
  intro s ρ hρ
  exact bellMeasureLeft_remote_collapse_total s ρ hρ.1

/-- The left-qubit measurement of the Bell pair returns `false` with probability `1 / 2`. -/
theorem bellMeasureLeft_false_prob {σ : Type} (s : σ) :
    QHoare.wpTotal (bellMeasureLeft (σ := σ)) (returnedFalse (σ := σ)) s
      QMat.Bell.proj00 =
      (1 / 2 : ℝ)
    := by
  unfold bellMeasureLeft
  rw [QHoare.wpTotal_applyUnitary_bind]
  rw [QHoare.wpTotal_applyUnitary_bind]
  rw [QHoare.wpTotal_meas]
  simpa [returnedFalse, QProg.Exec.evolve, QMat.measProjector, QMat.Bell.prepared,
    QMat.Bell.measured] using
    QMat.Bell.left_false_probability

/-- The left-qubit measurement of the Bell pair returns `true` with probability `1 / 2`. -/
theorem bellMeasureLeft_true_prob {σ : Type} (s : σ) :
    QHoare.wpTotal (bellMeasureLeft (σ := σ)) (returnedTrue (σ := σ)) s
      QMat.Bell.proj00 =
      (1 / 2 : ℝ)
    := by
  unfold bellMeasureLeft
  rw [QHoare.wpTotal_applyUnitary_bind]
  rw [QHoare.wpTotal_applyUnitary_bind]
  rw [QHoare.wpTotal_meas]
  simpa [returnedTrue, QProg.Exec.evolve, QMat.measProjector, QMat.Bell.prepared,
    QMat.Bell.measured] using
    QMat.Bell.left_true_probability

/-! ## Demo 2: prepare a Bell pair, then measure both qubits -/

/-- Prepare a Bell pair and measure both qubits in the computational basis. -/
def bellMeasureBoth {σ : Type} : QProg σ 2 (Bool × Bool) := do
  QProg.applyUnitary (σ := σ) QMat.Bell.H_on_0
    (QMat.applySingle_unitary (0 : Fin 2) Gate.H Gate.H_unitary)
  QProg.applyUnitary (σ := σ) QMat.Bell.CNOT_0_1
    (QMat.cnotMatrix_unitary (0 : Fin 2) (1 : Fin 2) (by decide))
  let b0 ← QProg.meas (σ := σ) (0 : Fin 2)
  let b1 ← QProg.meas (σ := σ) (1 : Fin 2)
  pure (b0, b1)

/-- Postcondition that accepts exactly the equal-bit measurement outcomes. -/
def correlatedPost {σ : Type} : Bool × Bool → σ → QMat 2
  | (b0, b1), _ => if b0 = b1 then 1 else 0

/-- Measuring both qubits of the Bell pair always returns equal bits. -/
theorem bellMeasureBoth_correlated {σ : Type} (s : σ) :
    QHoare.wpTotal (bellMeasureBoth (σ := σ)) (correlatedPost (σ := σ)) s
      QMat.Bell.proj00 = 1
    := by
  unfold bellMeasureBoth
  rw [QHoare.wpTotal_applyUnitary_bind]
  rw [QHoare.wpTotal_applyUnitary_bind]
  rw [QHoare.wpTotal_meas_bind]
  simp only [QHoare.wpTotal_meas_bind, QHoare.wpTotal_pure]
  simpa [correlatedPost, QProg.Exec.evolve, QMat.measProjector, QMat.Bell.prepared,
    QMat.Bell.measured] using
    QMat.Bell.both_correlated

end Bell
end QProg

end

end QLean
