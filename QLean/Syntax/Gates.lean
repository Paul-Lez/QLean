/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
import QLean.Syntax.Core
import QLean.Gates.FullRegister.BasisMaps
import QLean.Gates.FullRegister.RegisterLift
import QLean.Gates.SingleQubit

/-!
# Gate Conveniences for QProg

This file keeps gate-specific convenience combinators out of the core `QProg` syntax and semantics.
Import it when programs use embedded one-qubit gates such as `QProg.applyH`.
-/

namespace QLean

noncomputable section

open scoped Matrix ComplexOrder

namespace QProg

/-! ## Gate Combinators -/

/-- Apply an embedded single-qubit gate. -/
def applySingleGate {σ : Type} {n : ℕ} (q : Fin n)
    (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : Operator.IsUnitary U) : QProg σ n Unit :=
  QProg.applyUnitary (QMat.applySingle q U) (QMat.applySingle_unitary q U hU)

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

end QProg

end

end QLean
