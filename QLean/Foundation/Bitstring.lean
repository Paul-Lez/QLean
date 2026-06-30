/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Range
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.NormNum

/-!
# Computational-Basis Bitstrings
-/

namespace QLean

noncomputable section

/-- A computational-basis index over a finite collection of qubit labels. -/
abbrev QIndex (ι : Type*) := ι → Fin 2

@[inherit_doc QIndex]
notation "Q[" i "]" => QIndex (Fin i)

/-  Computational-basis bitstrings -/

namespace QIndex

/-- Finite Boolean strings, indexed little-endian by `Fin n`. -/
abbrev BitVec (n : ℕ) := Fin n → Bool

/-- Boolean exclusive-or. -/
def bitXor : Bool → Bool → Bool :=
  Bool.xor

/-- Pointwise exclusive-or of Boolean strings. -/
def bitVecXor {m : ℕ} (x y : BitVec m) : BitVec m :=
  fun i => bitXor (x i) (y i)

/-- The mod-2 Boolean dot product: xor over all `a i && x i`. -/
def bitDot {m : ℕ} (a x : BitVec m) : Bool :=
  (List.finRange m).foldl (fun acc i => bitXor acc (a i && x i)) false

/-- The all-zero Boolean string. -/
def allZero {m : ℕ} : BitVec m :=
  fun _ => false

/-- The one-bit Boolean string containing `b`. -/
def singletonBitVec (b : Bool) : BitVec 1 :=
  fun _ => b

/-- Convert a list of measurement results to a total Boolean string, defaulting to `false`. -/
def bitVecOfList {m : ℕ} (bits : List Bool) : BitVec m :=
  fun i => bits.getD i.val false

/-- Number of computational-basis states in an `n`-qubit register. -/
def qdim (n : ℕ) : ℕ := 2 ^ n

/-- There are `2^n` computational-basis states in an `n`-qubit register. -/
theorem card (n : ℕ) : Fintype.card Q[n] = 2 ^ n := by
  simp [QIndex]

/-- Read a `Fin 2` bit as a natural number. -/
def bitVal (b : Fin 2) : ℕ :=
  b.val

/-- Convert a basis bit to a Boolean. -/
def bitBool (b : Fin 2) : Bool :=
  decide (b = (1 : Fin 2))

/-- Convert a Boolean to the corresponding computational-basis bit. -/
def boolBit : Bool → Fin 2
  | false => 0
  | true => 1

/-- Decode a little-endian bitstring as a natural number. -/
def bitsToNat : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * bitsToNat bs

theorem bitsToNat_lt_two_pow_length (bits : List Bool) :
    bitsToNat bits < 2 ^ bits.length := by
  induction bits with
  | nil => norm_num [bitsToNat]
  | cons b bs ih =>
    cases b <;> simp [bitsToNat, pow_succ'] <;> omega

theorem bitsToNat_lt_of_length {bits : List Bool} {n : ℕ} (hbits : bits.length = n) :
    bitsToNat bits < qdim n := by
  simpa [qdim, hbits] using bitsToNat_lt_two_pow_length bits

/-- The measured bits of a computational-basis index, in little-endian order. -/
def basisBits {n : ℕ} (x : Q[n]) : List Bool :=
  (List.finRange n).map fun i => bitBool (x i)

theorem basisBits_length {n : ℕ} (x : Q[n]) :
    (basisBits x).length = n := by
  simp [basisBits]

/-- Decode a computational-basis index as a natural number. -/
def basisToNat {n : ℕ} (x : Q[n]) : ℕ :=
  bitsToNat (basisBits x)

theorem basisToNat_lt {n : ℕ} (x : Q[n]) :
    basisToNat x < qdim n :=
  bitsToNat_lt_of_length (basisBits_length x)

/-- Decode a computational-basis index as a bounded `Fin (2^n)`. -/
def basisToFin {n : ℕ} (x : Q[n]) : Fin (qdim n) :=
  ⟨basisToNat x, basisToNat_lt x⟩

/-- The low-level bit of a natural number, encoded as a `Fin 2` basis index. -/
def natBit (x i : ℕ) : Fin 2 :=
  if x.testBit i then 1 else 0

/-- Encode a natural number as an `n`-qubit computational-basis index. -/
def natToBasis (n x : ℕ) : Q[n] :=
  fun i => natBit x i.val

/-- Interpret a Boolean string as a computational-basis index. -/
def basisOfBits {n : ℕ} (bits : BitVec n) : Q[n] :=
  fun q => boolBit (bits q)

/-- Read a computational-basis index as a Boolean string. -/
def bitsOfBasis {n : ℕ} (x : Q[n]) : BitVec n :=
  fun q => bitBool (x q)

/-- Dot product of two bitstrings modulo 2. -/
def bitDotMod2 {n : ℕ} (x y : Q[n]) : ℕ :=
  ((List.finRange n).foldl (fun acc i => acc + bitVal (x i) * bitVal (y i)) 0) % 2

/-- The first-register index inside an `m + work` qubit register. -/
def firstRegisterIndex (m work : ℕ) (i : Fin m) : Fin (m + work) :=
  ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right m work)⟩

/-- The second-register index inside an `m + work` qubit register. -/
def secondRegisterIndex (m work : ℕ) (i : Fin work) : Fin (m + work) :=
  ⟨m + i.val, Nat.add_lt_add_left i.isLt m⟩

/-- The final target qubit of an `m + 1` register. -/
def targetIndex (m : ℕ) : Fin (m + 1) :=
  ⟨m, Nat.lt_succ_self m⟩

/-- The first `m` bits of an `m + work` computational-basis index. -/
def firstBits {m work : ℕ} (z : Q[m + work]) : BitVec m :=
  fun i => bitBool (z (firstRegisterIndex m work i))

/-- The second `work` bits of an `m + work` computational-basis index. -/
def secondBits {m work : ℕ} (z : Q[m + work]) : BitVec work :=
  fun i => bitBool (z (secondRegisterIndex m work i))

/-- Append one target bit to an `m`-bit query string. -/
def appendTargetBit {m : ℕ} (x : BitVec m) (y : Bool) : Q[m + 1] :=
  fun q =>
    if h : q.val < m then
      boolBit (x ⟨q.val, h⟩)
    else
      boolBit y

/-- Pair two `m`-bit strings as a two-register computational-basis index. -/
def pairBits {m : ℕ} (x y : BitVec m) : Q[m + m] :=
  fun q =>
    if h : q.val < m then
      boolBit (x ⟨q.val, h⟩)
    else
      boolBit (y ⟨q.val - m, by
        have hle : m ≤ q.val := Nat.le_of_not_gt h
        have hlt : q.val < m + m := q.isLt
        omega⟩)

/-- Project the first `t` qubits from a `t + m` basis index. -/
def firstRegisterBasis (t m : ℕ) (z : Q[t + m]) : Q[t] :=
  fun i => z (firstRegisterIndex t m i)

/-- Project the last `m` qubits from a `t + m` basis index. -/
def secondRegisterBasis (t m : ℕ) (z : Q[t + m]) : Q[m] :=
  fun i => z (secondRegisterIndex t m i)

/-- Decode the first register. -/
def firstRegisterNat (t m : ℕ) (z : Q[t + m]) : ℕ :=
  basisToNat (firstRegisterBasis t m z)

/-- Decode the second register. -/
def secondRegisterNat (t m : ℕ) (z : Q[t + m]) : ℕ :=
  basisToNat (secondRegisterBasis t m z)

/-- Replace the second register by the basis encoding of a natural number. -/
def replaceSecondRegister (t m : ℕ) (z : Q[t + m]) (y : ℕ) : Q[t + m] :=
  fun q =>
    if q.val < t then
      z q
    else
      natBit y (q.val - t)

end QIndex

end

end QLean
