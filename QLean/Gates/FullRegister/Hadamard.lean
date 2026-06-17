/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/

import QLean.Gates.FullRegister.Support

/-! # Full-register Hadamard layer -/

namespace QLean

noncomputable section

open scoped Matrix ComplexOrder
open Matrix Complex

namespace QMat

/-- Amplitude of the full-register Walsh-Hadamard transform. -/
def hadamardAmplitude (n : ℕ) (out inn : Q[n]) : ℂ :=
  ((1 / Real.sqrt (2 ^ n : ℝ) : ℝ) : ℂ) *
    (if QIndex.bitDotMod2 out inn = 0 then 1 else -1)

/-- Full-register Hadamard layer. -/
def hadamardLayer (n : ℕ) : QMat n :=
  Matrix.of fun out inn => hadamardAmplitude n out inn

private theorem walsh_single_factor_eq {n : ℕ} (v z : Q[n]) (i : Fin n) :
    (-1 : ℂ) ^ (if v i = 1 then (z i).val else 0) =
      (-1 : ℂ) ^ (QIndex.bitVal (z i) * QIndex.bitVal (v i)) := by
  rcases Fin.exists_fin_two.mp ⟨z i, rfl⟩ with hzi | hzi <;>
    rcases Fin.exists_fin_two.mp ⟨v i, rfl⟩ with hvi | hvi <;>
    simp [hzi, hvi, QIndex.bitVal]

private theorem walsh_product_eq_bitDotMod2 {n : ℕ} (v z : Q[n]) :
    (∏ i : Fin n, (-1 : ℂ) ^ (if v i = 1 then (z i).val else 0)) =
      (-1 : ℂ) ^ (QIndex.bitDotMod2 z v) := by
  rw [Finset.prod_congr rfl fun i _ => walsh_single_factor_eq v z i]
  rw [Finset.prod_pow_eq_pow_sum]
  rw [← Nat.mod_add_div (∑ i, QIndex.bitVal (z i) * QIndex.bitVal (v i)) 2]
  norm_num [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
  rw [Finset.sum_eq_multiset_sum]
  erw [Multiset.map_coe]
  norm_num [List.sum_eq_foldl]
  rw [List.foldl_map]
  simp [QIndex.bitDotMod2]

private theorem walsh_character_sum_factor {n : ℕ} (v : Q[n]) :
    (∑ z : Q[n], (-1 : ℂ) ^ (QIndex.bitDotMod2 z v)) =
      ∏ i : Fin n, ∑ b : Fin 2, (-1 : ℂ) ^ (if v i = 1 then b.val else 0) := by
  rw [Finset.prod_sum]
  refine Finset.sum_bij (fun z _ => fun i _ => z i) ?_ ?_ ?_ ?_
  · intro z _
    simp
  · intro z₁ _ z₂ _ hz
    ext i
    exact congrArg Fin.val (congrFun (congrFun hz i) (Finset.mem_univ i))
  · intro b _
    exact ⟨fun i => b i (Finset.mem_univ i), Finset.mem_univ _, rfl⟩
  · intro z _
    simpa using (walsh_product_eq_bitDotMod2 v z).symm

private theorem walsh_character_sum_zero_vector (n : ℕ) :
    (∑ z : Q[n], (-1 : ℂ) ^ (QIndex.bitDotMod2 z 0)) = 2 ^ n := by
  simp [QIndex.bitDotMod2, QIndex.bitVal]

private theorem exists_one_of_ne_zero {n : ℕ} {v : Q[n]} (hv : v ≠ 0) :
    ∃ i, v i = 1 := by
  by_contra hnone
  exact hv (funext fun i =>
    match Fin.exists_fin_two.mp ⟨v i, rfl⟩ with
    | Or.inl hzero => hzero
    | Or.inr hone => False.elim (hnone ⟨i, hone⟩))

private theorem walsh_character_sum_nonzero {n : ℕ} {v : Q[n]} (hv : v ≠ 0) :
    (∑ z : Q[n], (-1 : ℂ) ^ (QIndex.bitDotMod2 z v)) = 0 := by
  rw [walsh_character_sum_factor v, Finset.prod_eq_zero_iff]
  obtain ⟨i, hi⟩ := exists_one_of_ne_zero hv
  exact ⟨i, Finset.mem_univ i, by simp [hi]⟩

private theorem walsh_character_sum_zero {n : ℕ} (v : Q[n]) :
    (∑ z : Q[n], (-1 : ℂ) ^ (QIndex.bitDotMod2 z v)) =
      if v = 0 then 2 ^ n else 0 := by
  by_cases hv : v = 0
  · subst v
    simpa using walsh_character_sum_zero_vector n
  · simpa [hv] using walsh_character_sum_nonzero (v := v) hv

private theorem bitVal_xor_add_modEq (z x y : Fin 2) :
    QIndex.bitVal z * QIndex.bitVal x + QIndex.bitVal z * QIndex.bitVal y ≡
      QIndex.bitVal z * QIndex.bitVal (if x = y then 0 else 1) [MOD 2] := by
  rcases Fin.exists_fin_two.mp ⟨z, rfl⟩ with hz | hz <;>
    rcases Fin.exists_fin_two.mp ⟨x, rfl⟩ with hx | hx <;>
    rcases Fin.exists_fin_two.mp ⟨y, rfl⟩ with hy | hy <;>
    simp [hz, hx, hy, QIndex.bitVal, Nat.ModEq]

private theorem bitVal_xor_add_zmod (z x y : Fin 2) :
    ((QIndex.bitVal z * QIndex.bitVal x + QIndex.bitVal z * QIndex.bitVal y : ℕ) :
        ZMod 2) =
      (QIndex.bitVal z * QIndex.bitVal (if x = y then 0 else 1) : ℕ) := by
  simpa [← ZMod.natCast_eq_natCast_iff] using bitVal_xor_add_modEq z x y

private theorem nat_foldl_cast_zmod {n : ℕ} (f : Fin n → ℕ) :
    ∀ (l : List (Fin n)) (a : ℕ),
      ((l.foldl (fun acc i => acc + f i) a : ℕ) : ZMod 2) =
        l.foldl (fun acc i => acc + (f i : ZMod 2)) (a : ZMod 2) := by
  intro l
  induction l with
  | nil =>
      intro a
      simp
  | cons i l ih =>
      intro a
      simp [ih]

private theorem bitDot_foldl_xor_zmod_aux {n : ℕ} (z x y : Q[n]) :
    ∀ (l : List (Fin n)) (ax ay axy : ZMod 2),
      ax + ay = axy →
        l.foldl
            (fun (acc : ZMod 2) i =>
              acc + (QIndex.bitVal (z i) * QIndex.bitVal (x i) : ℕ))
            ax +
          l.foldl
            (fun (acc : ZMod 2) i =>
              acc + (QIndex.bitVal (z i) * QIndex.bitVal (y i) : ℕ))
            ay =
          l.foldl
            (fun (acc : ZMod 2) i =>
              acc + (QIndex.bitVal (z i) *
                QIndex.bitVal (if x i = y i then 0 else 1) : ℕ))
            axy := by
  intro l
  induction l with
  | nil =>
      intro ax ay axy hacc
      simpa using hacc
  | cons i l ih =>
      intro ax ay axy hacc
      simp only [List.foldl_cons]
      apply ih
      have hterm := bitVal_xor_add_zmod (z i) (x i) (y i)
      calc
        (ax + (QIndex.bitVal (z i) * QIndex.bitVal (x i) : ℕ)) +
            (ay + (QIndex.bitVal (z i) * QIndex.bitVal (y i) : ℕ)) =
          (ax + ay) +
            ((QIndex.bitVal (z i) * QIndex.bitVal (x i) +
              QIndex.bitVal (z i) * QIndex.bitVal (y i) : ℕ) : ZMod 2) := by
            rw [Nat.cast_add]
            ring
        _ =
          axy +
            (QIndex.bitVal (z i) * QIndex.bitVal (if x i = y i then 0 else 1) : ℕ) := by
            rw [hacc, hterm]

private def qindexXor {n : ℕ} (x y : Q[n]) : Q[n] :=
  fun i => if x i = y i then 0 else 1

private theorem bitDotMod2_add_xor_mod {n : ℕ} (z x y : Q[n]) :
    QIndex.bitDotMod2 z x + QIndex.bitDotMod2 z y ≡
      QIndex.bitDotMod2 z (qindexXor x y) [MOD 2] := by
  unfold QIndex.bitDotMod2
  rw [← ZMod.natCast_eq_natCast_iff]
  rw [Nat.cast_add, ZMod.natCast_mod, ZMod.natCast_mod, ZMod.natCast_mod]
  simpa [qindexXor, nat_foldl_cast_zmod] using
    bitDot_foldl_xor_zmod_aux z x y (List.finRange n) 0 0 0 (by simp)

private theorem qindex_xor_eq_zero_iff {n : ℕ} (x y : Q[n]) :
    qindexXor x y = 0 ↔ x = y := by
  constructor
  · intro h
    funext i
    have hi := congrFun h i
    by_cases hxy : x i = y i
    · exact hxy
    · simp [qindexXor, hxy] at hi
  · intro h
    subst y
    funext i
    simp [qindexXor]

private theorem hadamard_character_sum {n : ℕ} (x y : Q[n]) :
    ∑ z : Q[n], (-1 : ℂ) ^ (QIndex.bitDotMod2 z x + QIndex.bitDotMod2 z y) =
      if x = y then 2 ^ n else 0 := by
  convert walsh_character_sum_zero (qindexXor x y) using 1
  · refine Finset.sum_congr rfl fun z _ => ?_
    rw [← Nat.mod_add_div (z.bitDotMod2 x + z.bitDotMod2 y) 2,
      bitDotMod2_add_xor_mod z x y]
    norm_num [pow_add, pow_mul]
    rw [← Nat.mod_add_div (z.bitDotMod2 (qindexXor x y)) 2]
    norm_num [pow_add, pow_mul]
  · simp [qindex_xor_eq_zero_iff]

private theorem hadamardAmplitude_eq_scale {n : ℕ} (z x : Q[n]) :
    hadamardAmplitude n z x =
      (1 / Real.sqrt (2 ^ n) : ℂ) * (-1 : ℂ) ^ QIndex.bitDotMod2 z x := by
  unfold hadamardAmplitude
  by_cases h : QIndex.bitDotMod2 z x = 0
  · simp [h]
  · have h_one : QIndex.bitDotMod2 z x = 1 := Nat.mod_two_ne_zero.mp h
    simp [h_one]

private theorem hadamardAmplitude_star_mul {n : ℕ} (z x y : Q[n]) :
    star (hadamardAmplitude n z x) * hadamardAmplitude n z y =
      (-1 : ℂ) ^ (QIndex.bitDotMod2 z x + QIndex.bitDotMod2 z y) *
        (1 / Real.sqrt (2 ^ n) : ℂ) ^ 2 := by
  rw [hadamardAmplitude_eq_scale z x, hadamardAmplitude_eq_scale z y]
  simp [pow_add, pow_two, mul_comm, mul_left_comm, mul_assoc]

private theorem hadamardLayer_conjTranspose_mul_self (n : ℕ) :
    (hadamardLayer n).conjTranspose * (hadamardLayer n) = 1 := by
  ext x y
  have h_sum := hadamard_character_sum x y
  convert congr_arg (fun z : ℂ => z * (1 / Real.sqrt (2 ^ n) : ℂ) ^ 2) h_sum using 1 <;>
    norm_num [hadamardLayer]
  · norm_num [Matrix.mul_apply]
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun z _ => by
      simpa [one_div, inv_pow] using hadamardAmplitude_star_mul z x y
  · norm_num [← Complex.ofReal_pow, Matrix.one_apply]
    norm_num [Nat.cast_pow]

theorem hadamardLayer_unitary (n : ℕ) :
    (hadamardLayer n).Unitary :=
  unitary_of_star_mul_eq_one (hadamardLayer_conjTranspose_mul_self n)

end QMat

end

end QLean
