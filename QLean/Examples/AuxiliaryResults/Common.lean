/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
import QLean.Foundation.Basis

/-!
# Shared Prerequisites for Canonical Algorithm Examples
-/

namespace QLean

noncomputable section

open scoped Matrix ComplexOrder

namespace QMat
namespace Canonical

open QIndex

@[simp] theorem firstBits_apply {m work : ℕ} (z : Q[m + work]) (i : Fin m) :
    firstBits z i = QIndex.bitBool (z (firstRegisterIndex m work i)) := rfl

@[simp] theorem bitBool_boolBit (b : Bool) :
    QIndex.bitBool (QIndex.boolBit b) = b := by
  cases b <;> simp [QIndex.bitBool, QIndex.boolBit]

@[simp] theorem boolBit_bitBool (b : Fin 2) :
    QIndex.boolBit (QIndex.bitBool b) = b := by
  rcases Fin.exists_fin_two.mp ⟨b, rfl⟩ with hb | hb <;>
    simp [hb, QIndex.bitBool, QIndex.boolBit]

@[simp] theorem appendTargetBit_apply_of_lt {m : ℕ} (x : QIndex.BitVec m) (y : Bool)
    (q : Fin (m + 1)) (h : q.val < m) :
    appendTargetBit x y q = QIndex.boolBit (x ⟨q.val, h⟩) := by
  simp [appendTargetBit, QIndex.appendTargetBit, h]

@[simp] theorem appendTargetBit_apply_of_not_lt {m : ℕ} (x : QIndex.BitVec m) (y : Bool)
    (q : Fin (m + 1)) (h : ¬q.val < m) :
    appendTargetBit x y q = QIndex.boolBit y := by
  simp [appendTargetBit, QIndex.appendTargetBit, h]

@[simp] theorem firstBits_appendTargetBit {m : ℕ} (x : QIndex.BitVec m) (y : Bool) :
    firstBits (work := 1) (appendTargetBit x y) = x := by
  ext i
  simp [firstBits, QIndex.firstBits, QIndex.firstRegisterIndex]

@[simp] theorem targetBit_appendTargetBit {m : ℕ} (x : QIndex.BitVec m) (y : Bool) :
    QIndex.bitBool (appendTargetBit x y (targetIndex m)) = y := by
  simp [targetIndex, QIndex.targetIndex]

@[simp] theorem appendTargetBit_targetIndex {m : ℕ} (x : QIndex.BitVec m) (y : Bool) :
    appendTargetBit x y (targetIndex m) = QIndex.boolBit y := by
  simp [targetIndex, QIndex.targetIndex]

def boolPhase : Bool → ℂ
  | false => 1
  | true => -1

def queryMinusAmp {m : ℕ} (x : QIndex.BitVec m) : Q[m + 1] → ℂ :=
  fun z =>
    if firstBits (work := 1) z = x ∧ QIndex.bitBool (z (targetIndex m)) = false then
      QMat.invSqrt2
    else if firstBits (work := 1) z = x ∧ QIndex.bitBool (z (targetIndex m)) = true then
      -QMat.invSqrt2
    else
      0

/-! ## Oracle specs -/

structure DeutschOracleSpec (Uf : QMat 2) (f : Bool → Bool) : Prop where
  unitary : Uf.Unitary
  maps_basis :
    ∀ x y : Bool,
      MapsBasis Uf
        (appendTargetBit (m := 1) (singletonBitVec x) y)
        (appendTargetBit (m := 1) (singletonBitVec x) (bitXor y (f x)))

structure BooleanOracleSpec {m : ℕ} (Uf : QMat (m + 1)) (f : QIndex.BitVec m → Bool) :
    Prop where
  unitary : Uf.Unitary
  maps_basis :
    ∀ x : QIndex.BitVec m, ∀ y : Bool,
      MapsBasis Uf
        (appendTargetBit x y)
        (appendTargetBit x (bitXor y (f x)))

structure SimonOracleSpec {m : ℕ}
    (Uf : QMat (m + m)) (f : QIndex.BitVec m → QIndex.BitVec m)
    (s : QIndex.BitVec m) : Prop where
  unitary : Uf.Unitary
  nonzero : s ≠ allZero
  simon_promise : ∀ x y : QIndex.BitVec m, f x = f y ↔ y = x ∨ y = bitVecXor x s
  maps_basis :
    ∀ x y : QIndex.BitVec m,
      MapsBasis Uf
        (pairBits x y)
        (pairBits x (bitVecXor y (f x)))

def orthogonalPost {m : ℕ} (s : QIndex.BitVec m) :
    QIndex.BitVec m → QMat (m + m)
  | y => if bitDot y s = false then 1 else 0

end Canonical
end QMat

end

end QLean
