/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/

import QLean.Foundation.QMat

/-! # Shared proof support for full-register gates -/

namespace QLean

noncomputable section

open scoped Matrix ComplexOrder
open Matrix Complex

namespace QMat

private theorem bitsToNat_cons_eq_cons {b₁ b₂ : Bool} {l₁ l₂ : List Bool}
    (h : QIndex.bitsToNat (b₁ :: l₁) = QIndex.bitsToNat (b₂ :: l₂)) :
    b₁ = b₂ ∧ QIndex.bitsToNat l₁ = QIndex.bitsToNat l₂ := by
  cases b₁ <;> cases b₂ <;> simp [QIndex.bitsToNat] at h ⊢ <;> omega

private theorem bitBool_injective :
    Function.Injective QIndex.bitBool := by
  intro b₁ b₂ hbits
  rcases Fin.exists_fin_two.mp ⟨b₁, rfl⟩ with rfl | rfl <;>
    rcases Fin.exists_fin_two.mp ⟨b₂, rfl⟩ with rfl | rfl <;>
    simp [QIndex.bitBool] at hbits ⊢

theorem bitsToNat_injective_of_length_eq :
    ∀ (l₁ l₂ : List Bool), l₁.length = l₂.length →
      QIndex.bitsToNat l₁ = QIndex.bitsToNat l₂ → l₁ = l₂ := by
  intro l₁
  induction l₁ with
  | nil =>
      intro l₂ hlen _hsum
      cases l₂ with
      | nil => rfl
      | cons _ _ => cases hlen
  | cons b₁ l₁ ih =>
      intro l₂ hlen hsum
      cases l₂ with
      | nil => cases hlen
      | cons b₂ l₂ =>
          have hlen_tail : l₁.length = l₂.length := Nat.succ.inj hlen
          have hcons := bitsToNat_cons_eq_cons (b₁ := b₁) (b₂ := b₂) (l₁ := l₁)
            (l₂ := l₂) hsum
          exact congrArg₂ List.cons hcons.1 (ih l₂ hlen_tail hcons.2)

theorem basisToNat_injective {n : ℕ} :
    Function.Injective (QIndex.basisToNat (n := n)) := by
  intro x y hxy
  have hbits : QIndex.basisBits x = QIndex.basisBits y := by
    apply bitsToNat_injective_of_length_eq
    · simp [QIndex.basisBits]
    · simpa [QIndex.basisToNat] using hxy
  ext i
  have hbitBool : QIndex.bitBool (x i) = QIndex.bitBool (y i) := by
    have hget := congrArg (fun bits => bits.getD i.val false) hbits
    simpa [QIndex.basisBits, List.getD_map, i.isLt] using hget
  exact congrArg Fin.val (bitBool_injective hbitBool)

private theorem natBit_succ_eq_natBit_div_two (x i : ℕ) :
    QIndex.natBit x i.succ = QIndex.natBit (x / 2) i := by
  unfold QIndex.natBit
  rw [Nat.testBit_succ]

private theorem basisBits_natToBasis_succ_tail (n x : ℕ) :
    ((List.finRange n).map fun i : Fin n =>
      QIndex.bitBool (QIndex.natBit x (Fin.succ i).val)) =
        QIndex.basisBits (QIndex.natToBasis n (x / 2)) := by
  apply List.ext_get
  · simp [QIndex.basisBits]
  · intro i hleft hright
    simp [QIndex.basisBits, QIndex.natToBasis, natBit_succ_eq_natBit_div_two]

private theorem lowBit_add_two_mul_div_two (x : ℕ) :
    (if QIndex.bitBool (QIndex.natBit x 0) then 1 else 0) + 2 * (x / 2) = x := by
  unfold QIndex.bitBool QIndex.natBit
  simp
  split_ifs <;> omega

private theorem div_two_lt_two_pow_of_lt_two_pow_succ {n x : ℕ}
    (hx : x < 2 ^ (n + 1)) :
    x / 2 < 2 ^ n :=
  Nat.div_lt_of_lt_mul (by simpa [pow_succ'] using hx)

theorem bitsToNat_basisBits_natToBasis (n : ℕ) (b : Fin (2 ^ n)) :
    QIndex.bitsToNat (QIndex.basisBits (QIndex.natToBasis n b.val)) = b.val := by
  induction n with
  | zero =>
      have hb : b.val = 0 := by omega
      change QIndex.bitsToNat [] = b.val
      rw [hb]
      rfl
  | succ n ih =>
      let tail : Fin (2 ^ n) :=
        ⟨b.val / 2, div_two_lt_two_pow_of_lt_two_pow_succ (by
          simp)⟩
      have htail :
          QIndex.bitsToNat (QIndex.basisBits (QIndex.natToBasis n (b.val / 2))) =
            b.val / 2 := by
        simpa [tail] using ih tail
      change
        QIndex.bitsToNat
            ((List.finRange (Nat.succ n)).map fun i : Fin (Nat.succ n) =>
              QIndex.bitBool (QIndex.natBit b.val i.val)) =
          b.val
      rw [List.finRange_succ]
      simp only [List.map_cons, List.map_map, QIndex.bitsToNat]
      change
        (if QIndex.bitBool (QIndex.natBit b.val 0) then 1 else 0) +
            2 * QIndex.bitsToNat
              ((List.finRange n).map fun i : Fin n =>
                QIndex.bitBool (QIndex.natBit b.val (Fin.succ i).val)) =
          b.val
      rw [basisBits_natToBasis_succ_tail, htail]
      exact lowBit_add_two_mul_div_two b.val

theorem basisToNat_natToBasis (n : ℕ) (b : Fin (2 ^ n)) :
    QIndex.basisToNat (QIndex.natToBasis n b.val) = b.val := by
  simpa [QIndex.basisToNat] using bitsToNat_basisBits_natToBasis n b

theorem natToBasis_eq_testBit (n b : ℕ) :
    QIndex.natToBasis n b = (fun i : Fin n => if b.testBit i.val then 1 else 0) := by
  ext i
  have hmod : b / 2 ^ i.val % 2 < 2 := Nat.mod_lt _ (by decide)
  by_cases h : b / 2 ^ i.val % 2 = 0
  · simp [QIndex.natToBasis, QIndex.natBit, Nat.testBit, Nat.shiftRight_eq_div_pow, h]
  · have h' : b / 2 ^ i.val % 2 = 1 := by omega
    simp [QIndex.natToBasis, QIndex.natBit, Nat.testBit, Nat.shiftRight_eq_div_pow, h']

theorem basisToNat_of_testBit (n b : ℕ) (hb : b < 2 ^ n) :
    QIndex.basisToNat (fun i : Fin n => if b.testBit i.val then 1 else 0) = b := by
  rw [← natToBasis_eq_testBit]
  exact basisToNat_natToBasis n ⟨b, hb⟩

theorem sum_qindex_eq_sum_range_basisToNat {n : ℕ} {α : Type*} [AddCommMonoid α]
    (f : ℕ → α) :
    (∑ k : Q[n], f k.basisToNat) = ∑ x ∈ Finset.range (2 ^ n), f x := by
  refine Finset.sum_bij (fun x _ => x.basisToNat) ?_ ?_ ?_ ?_
  · intro a _
    exact Finset.mem_range.mpr (QIndex.basisToNat_lt a)
  · intro a₁ _ a₂ _ h
    exact basisToNat_injective h
  · intro b hb
    exact
      ⟨fun i => if b.testBit i.val then 1 else 0, Finset.mem_univ _,
        basisToNat_of_testBit n b (Finset.mem_range.mp hb)⟩
  · intro a _
    rfl

theorem unitary_star {n : ℕ} {U : QMat n} (hU : U.Unitary) :
    (star U).Unitary := by
  rcases hU with ⟨h_left, h_right⟩
  constructor
  · simpa [star_star] using h_right
  · simpa [star_star] using h_left

end QMat

end

end QLean
