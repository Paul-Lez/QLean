/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
import QLean.Syntax.WP
import QLean.Gates.FullRegister.BasisMaps
import QLean.Gates.FullRegister.RegisterLift
import QLean.Gates.SingleQubit

/-!
# Gate Conveniences for QProg

This file keeps gate-specific combinators out of the core `QProg` syntax and semantics.
-/

namespace QLean

noncomputable section

open scoped Matrix ComplexOrder

namespace QProg

/-! ## Gate Combinators -/

/-- Apply an embedded single-qubit unitary. -/
def applySingle {σ : Type} {n : ℕ} (i : Fin n) (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : QMat.Unitary (QMat.applySingle i U)) : QProg σ n Unit :=
  applyUnitary (QMat.applySingle i U) hU

/-- Apply an embedded single-qubit gate. -/
def applySingleGate {σ : Type} {n : ℕ} (q : Fin n)
    (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : Operator.IsUnitary U) : QProg σ n Unit :=
  QProg.applySingle q U (QMat.applySingle_unitary q U hU)

/-- Apply Hadamard to one qubit. -/
def applyH {σ : Type} {n : ℕ} (q : Fin n) : QProg σ n Unit :=
  applySingleGate q Gate.H Gate.H_unitary

/-- Apply Pauli-X to one qubit. -/
def applyX {σ : Type} {n : ℕ} (q : Fin n) : QProg σ n Unit :=
  applySingleGate q Gate.X Gate.X_unitary

/-- Apply Pauli-Z to one qubit. -/
def applyZ {σ : Type} {n : ℕ} (q : Fin n) : QProg σ n Unit :=
  applySingleGate q Gate.Z Gate.Z_unitary

/-- Apply CNOT with an explicit distinct-control/target proof. -/
def applyCNOT {σ : Type} {n : ℕ}
    (control target : Fin n) (hct : control ≠ target) : QProg σ n Unit :=
  QProg.applyUnitary (QMat.cnotMatrix control target) (QMat.cnotMatrix_unitary control target hct)

/-- Apply the full-register Hadamard layer. -/
def applyHadamards {σ : Type} (n : ℕ) : QProg σ n Unit :=
  QProg.applyUnitary (QMat.hadamardLayer n) (QMat.hadamardLayer_unitary n)

/-- Apply Hadamards to the first register and identity to the remaining work register. -/
def applyFirstHadamards {σ : Type} (m work : ℕ) : QProg σ (m + work) Unit :=
  QProg.applyUnitary
    (QMat.liftFirstRegisterMatrix m work (QMat.hadamardLayer m))
    (QMat.liftFirstRegisterMatrix_unitary m work
      (QMat.hadamardLayer m) (QMat.hadamardLayer_unitary m))

/-! ## Measurement Combinators -/

/-- Measure a list of qubits in order and collect the resulting bits. -/
def measQubits {σ : Type} {n : ℕ} : List (Fin n) → QProg σ n (List Bool)
  | [] => pure []
  | q :: qs => do
      let b ← QProg.meas q
      let bs ← measQubits qs
      pure (b :: bs)

/-- Measure qubits selected by `idx` and return their results as a `QIndex.BitVec`. -/
def measBitVec {σ : Type} {n m : ℕ} (idx : Fin m → Fin n) :
    QProg σ n (QIndex.BitVec m) := do
  let bits ← measQubits ((List.finRange m).map idx)
  pure (QIndex.bitVecOfList bits)

/-- Measure the first register of an `m + work` register. -/
def measFirstRegister {σ : Type} (m work : ℕ) : QProg σ (m + work) (QIndex.BitVec m) :=
  measBitVec (σ := σ) (fun i => QIndex.firstRegisterIndex m work i)

/-- Measure the second register of an `m + work` register. -/
def measSecondRegister {σ : Type} (m work : ℕ) : QProg σ (m + work) (QIndex.BitVec work) :=
  measBitVec (σ := σ) (fun i => QIndex.secondRegisterIndex m work i)

/-- Measure every qubit in a register. -/
def measAll {σ : Type} (n : ℕ) : QProg σ n (QIndex.BitVec n) :=
  measBitVec (σ := σ) (fun i => i)

namespace QHoare

/-! ## Measurement WP Lemmas -/

/-- Weakest-precondition recursion for measuring a list of qubits in order. -/
def wpMeasQubitsCont {n : ℕ} : List (Fin n) → (List Bool → QMat n → ℝ) → QMat n → ℝ
  | [], post, ρ => post [] ρ
  | q :: qs, post, ρ =>
      wpMeasQubitsCont qs (fun bits => post (false :: bits))
          (QMat.measProjector q false * ρ * QMat.measProjector q false) +
        wpMeasQubitsCont qs (fun bits => post (true :: bits))
          (QMat.measProjector q true * ρ * QMat.measProjector q true)

/-- Weakest-precondition recursion for measuring qubits into a bitvector. -/
def wpMeasBitVecCont {n m : ℕ} (idx : Fin m → Fin n)
    (post : QIndex.BitVec m → QMat n → ℝ) (ρ : QMat n) : ℝ :=
  wpMeasQubitsCont ((List.finRange m).map idx) (fun bits => post (QIndex.bitVecOfList bits)) ρ

/--
The total-correctness WP of `measQubits`, followed by pure classical post-processing, is the
direct branch recursion over the measured qubits.
-/
theorem wpTotal_measQubits_map_eq_wpMeasQubitsCont
    {σ α : Type} {n : ℕ} (qs : List (Fin n)) (f : List Bool → α)
    (post : α → σ → QMat n) (s : σ) (ρ : QMat n) :
    wpTotal
        (do
          let bits ← QProg.measQubits (σ := σ) qs
          pure (f bits) : QProg σ n α)
        post s ρ =
      wpMeasQubitsCont qs (fun bits ρ => QMat.expect (post (f bits) s) ρ) ρ := by
  induction qs generalizing f ρ with
  | nil =>
      simpa [QProg.measQubits, wpMeasQubitsCont, Cslib.FreeM.bind_eq_bind] using
        (wpTotal_pure (n := n) (σ := σ) (α := α) (f []) post s ρ)
  | cons q qs ih =>
      simp only [QProg.measQubits, wpMeasQubitsCont, Cslib.FreeM.bind_eq_bind]
      rw [Cslib.FreeM.bind_assoc]
      change wpTotal
          (QProg.meas (σ := σ) q >>= fun x =>
            ((Cslib.FreeM.bind (QProg.measQubits (σ := σ) qs)
                fun bs => pure (x :: bs)).bind fun bits => pure (f bits)) :
              QProg σ n α)
          post s ρ =
        wpMeasQubitsCont qs
            (fun bits ρ => QMat.expect (post (f (false :: bits)) s) ρ)
            (QMat.measProjector q false * ρ * QMat.measProjector q false) +
          wpMeasQubitsCont qs
            (fun bits ρ => QMat.expect (post (f (true :: bits)) s) ρ)
            (QMat.measProjector q true * ρ * QMat.measProjector q true)
      rw [wpTotal_meas_bind]
      have hfalse :
          wpTotal
              (((Cslib.FreeM.bind (QProg.measQubits (σ := σ) qs)
                fun bs => pure (false :: bs)).bind fun bits => pure (f bits)) :
                QProg σ n α)
              post s (QMat.measProjector q false * ρ * QMat.measProjector q false) =
            wpMeasQubitsCont qs
              (fun bits ρ => QMat.expect (post (f (false :: bits)) s) ρ)
              (QMat.measProjector q false * ρ * QMat.measProjector q false) := by
        simpa [Cslib.FreeM.bind_eq_bind, Cslib.FreeM.bind_assoc] using
          ih (fun bits => f (false :: bits))
            (QMat.measProjector q false * ρ * QMat.measProjector q false)
      have htrue :
          wpTotal
              (((Cslib.FreeM.bind (QProg.measQubits (σ := σ) qs)
                fun bs => pure (true :: bs)).bind fun bits => pure (f bits)) :
                QProg σ n α)
              post s (QMat.measProjector q true * ρ * QMat.measProjector q true) =
            wpMeasQubitsCont qs
              (fun bits ρ => QMat.expect (post (f (true :: bits)) s) ρ)
              (QMat.measProjector q true * ρ * QMat.measProjector q true) := by
        simpa [Cslib.FreeM.bind_eq_bind, Cslib.FreeM.bind_assoc] using
          ih (fun bits => f (true :: bits))
            (QMat.measProjector q true * ρ * QMat.measProjector q true)
      rw [hfalse, htrue]

/-- The total-correctness WP of `measBitVec` is the direct bitvector measurement recursion. -/
theorem wpTotal_measBitVec_eq_wpMeasBitVecCont
    {σ : Type} {n m : ℕ} (idx : Fin m → Fin n)
    (post : QIndex.BitVec m → σ → QMat n) (s : σ) (ρ : QMat n) :
    wpTotal (QProg.measBitVec (σ := σ) idx) post s ρ =
      wpMeasBitVecCont idx (fun out ρ => QMat.expect (post out s) ρ) ρ := by
  unfold QProg.measBitVec
  simpa [wpMeasBitVecCont] using
    wpTotal_measQubits_map_eq_wpMeasQubitsCont
      ((List.finRange m).map idx) QIndex.bitVecOfList post s ρ

/-- The total-correctness WP of `measAll` is the direct full-register measurement recursion. -/
theorem wpTotal_measAll_eq_wpMeasBitVecCont
    {σ : Type} (n : ℕ)
    (post : QIndex.BitVec n → σ → QMat n) (s : σ) (ρ : QMat n) :
    wpTotal (QProg.measAll (σ := σ) n) post s ρ =
      wpMeasBitVecCont (fun i : Fin n => i)
        (fun out ρ => QMat.expect (post out s) ρ) ρ := by
  unfold QProg.measAll
  exact wpTotal_measBitVec_eq_wpMeasBitVecCont (fun i : Fin n => i) post s ρ

end QHoare

end QProg

end

end QLean
