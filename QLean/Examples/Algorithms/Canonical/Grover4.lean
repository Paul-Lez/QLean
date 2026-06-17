/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
import QLean.Examples.AuxiliaryResults.Canonical.Grover4
import QLean.Syntax.Gates
import QLean.Syntax.WP

/-!
# Exact Four-Element Grover Search
-/

namespace QLean

noncomputable section

open scoped Matrix ComplexOrder

namespace QProg
namespace Algorithms
namespace Canonical

/-! ## Exact Grover Search for Four Elements -/

/--
Exact four-element Grover search with one marked item.

The oracle is supplied as an abstract marked phase unitary; one diffusion step is exact for
`N = 4`.
-/
def grover4 {σ : Type} (Umark : QMat 2) (hUmark : Umark.Unitary) :
    QProg σ 2 (QIndex.BitVec 2) := do
  QProg.applyHadamards (σ := σ) 2
  QProg.applyUnitary (σ := σ) Umark hUmark
  QProg.applyUnitary (σ := σ) (QMat.diffusion 2) (QMat.diffusion_unitary 2)
  QProg.measAll (σ := σ) 2

private theorem qprog_bind_pure_map_comp
    {σ α β γ : Type} {n : ℕ}
    (prog : QProg σ n β) (g : β → γ) (f : γ → α) :
    (((Cslib.FreeM.bind prog fun x => pure (g x)).bind fun y => pure (f y)) :
        QProg σ n α) =
      (Cslib.FreeM.bind prog fun x => pure (f (g x))) := by
  rw [Cslib.FreeM.bind_assoc]
  simp

private theorem wpTotal_measQubits_map_eq_wpMeasQubitsCont
    {σ α : Type} {n : ℕ} (qs : List (Fin n)) (f : List Bool → α)
    (post : α → σ → QMat n) (s : σ) (ρ : QMat n) :
    QHoare.wpTotal
        (do
          let bits ← QProg.measQubits (σ := σ) qs
          pure (f bits) : QProg σ n α)
        post s ρ =
      QMat.Canonical.wpMeasQubitsCont qs
        (fun bits ρ => QMat.expect (post (f bits) s) ρ) ρ := by
  induction qs generalizing f ρ with
  | nil =>
      simpa [QProg.measQubits, QMat.Canonical.wpMeasQubitsCont,
        Cslib.FreeM.bind_eq_bind] using
        (QHoare.wpTotal_pure (n := n) (σ := σ) (α := α) (f []) post s ρ)
  | cons q qs ih =>
      simp only [QProg.measQubits, QMat.Canonical.wpMeasQubitsCont,
        Cslib.FreeM.bind_eq_bind]
      rw [Cslib.FreeM.bind_assoc]
      change QHoare.wpTotal
          (QProg.meas (σ := σ) q >>= fun x =>
            ((Cslib.FreeM.bind (QProg.measQubits (σ := σ) qs)
                fun bs => pure (x :: bs)).bind fun bits => pure (f bits)) :
              QProg σ n α)
          post s ρ =
        QMat.Canonical.wpMeasQubitsCont qs
            (fun bits ρ => QMat.expect (post (f (false :: bits)) s) ρ)
            (QMat.measured q false ρ) +
          QMat.Canonical.wpMeasQubitsCont qs
            (fun bits ρ => QMat.expect (post (f (true :: bits)) s) ρ)
            (QMat.measured q true ρ)
      rw [QHoare.wpTotal_meas_bind]
      rw [qprog_bind_pure_map_comp]
      rw [qprog_bind_pure_map_comp]
      have hfalse :
          QHoare.wpTotal
              (Cslib.FreeM.bind (QProg.measQubits (σ := σ) qs)
                fun bits => pure (f (false :: bits)))
              post s (QMat.measProjector q false * ρ * QMat.measProjector q false) =
            QMat.Canonical.wpMeasQubitsCont qs
              (fun bits ρ => QMat.expect (post (f (false :: bits)) s) ρ)
              (QMat.measProjector q false * ρ * QMat.measProjector q false) := by
        simpa [Cslib.FreeM.bind_eq_bind] using
          ih (fun bits => f (false :: bits))
            (QMat.measProjector q false * ρ * QMat.measProjector q false)
      have htrue :
          QHoare.wpTotal
              (Cslib.FreeM.bind (QProg.measQubits (σ := σ) qs)
                fun bits => pure (f (true :: bits)))
              post s (QMat.measProjector q true * ρ * QMat.measProjector q true) =
            QMat.Canonical.wpMeasQubitsCont qs
              (fun bits ρ => QMat.expect (post (f (true :: bits)) s) ρ)
              (QMat.measProjector q true * ρ * QMat.measProjector q true) := by
        simpa [Cslib.FreeM.bind_eq_bind] using
          ih (fun bits => f (true :: bits))
            (QMat.measProjector q true * ρ * QMat.measProjector q true)
      rw [hfalse, htrue]
      rfl

private theorem wpTotal_measAll_eq
    {σ : Type} (post : QIndex.BitVec 2 → σ → QMat 2) (s : σ) (ρ : QMat 2) :
    QHoare.wpTotal (QProg.measAll (σ := σ) 2) post s ρ =
      QMat.Canonical.wpMeasBitVecCont (fun i : Fin 2 => i)
        (fun out ρ => QMat.expect (post out s) ρ) ρ := by
  unfold QProg.measAll QProg.measBitVec
  simpa [QMat.Canonical.wpMeasBitVecCont] using
    wpTotal_measQubits_map_eq_wpMeasQubitsCont
      ((List.finRange 2).map fun i : Fin 2 => i)
      (fun bits => QIndex.bitVecOfList bits) post s ρ

/--
Linear-algebra claim behind exact four-element Grover: from the all-zero two-qubit state,
one marked phase oracle and diffusion step rotate exactly to the marked basis state.
-/
theorem grover4_correct_linearAlgebra
    {σ : Type} (s : σ)
    (marked : QIndex.BitVec 2)
    (Umark : QMat 2)
    (hUmark : QMat.Canonical.Grover4OracleSpec Umark marked) :
    QHoare.wpTotal
      (grover4 (σ := σ) Umark hUmark.unitary)
      (QMat.returns (n := 2) marked)
      s (QMat.zeroDensity 2) = 1 := by
  unfold grover4 QProg.applyHadamards
  repeat rw [QHoare.wpTotal_applyUnitary_bind]
  rw [wpTotal_measAll_eq]
  simpa [QMat.Canonical.grover4Final, QMat.returns] using
    QMat.Canonical.grover4_correct marked Umark hUmark

/--
Grover-4 correctness: from `|00>`, one Grover iteration returns the marked item with
probability `1`.
-/
theorem grover4_correct
    {σ : Type} (s : σ)
    (marked : QIndex.BitVec 2)
    (Umark : QMat 2)
    (hUmark : QMat.Canonical.Grover4OracleSpec Umark marked) :
    QHoare.wpTotal
      (grover4 (σ := σ) Umark hUmark.unitary)
      (QMat.returns (n := 2) marked)
      s (QMat.zeroDensity 2) = 1 :=
  grover4_correct_linearAlgebra (s := s) marked Umark hUmark

end Canonical
end Algorithms
end QProg

end

end QLean
