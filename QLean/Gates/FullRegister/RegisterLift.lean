/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/

import QLean.Gates.FullRegister.Support

/-! # First-register lifting helpers -/

namespace QLean

noncomputable section

open scoped Matrix ComplexOrder
open Matrix Complex

namespace QMat

/-- Lift a matrix on the first register to a full `t + m` register, acting as identity on
the work register. -/
def liftFirstRegisterMatrix (t m : ℕ) (U : QMat t) : QMat (t + m) :=
  Matrix.of fun out inn =>
    if QIndex.secondRegisterBasis t m out = QIndex.secondRegisterBasis t m inn then
      U (QIndex.firstRegisterBasis t m out) (QIndex.firstRegisterBasis t m inn)
    else
      0

private def joinRegisters (t m : ℕ) (x : Q[t]) (y : Q[m]) : Q[t + m] :=
  fun i =>
    if h : i.val < t then
      x ⟨i.val, h⟩
    else
      y ⟨i.val - t, by
        rw [tsub_lt_iff_left]
        · exact i.isLt
        · exact Nat.le_of_not_gt h⟩

@[simp] private theorem firstRegisterBasis_joinRegisters (t m : ℕ) (x : Q[t]) (y : Q[m]) :
    QIndex.firstRegisterBasis t m (joinRegisters t m x y) = x := by
  ext i
  simp [joinRegisters, QIndex.firstRegisterBasis, QIndex.firstRegisterIndex]

@[simp] private theorem secondRegisterBasis_joinRegisters (t m : ℕ) (x : Q[t]) (y : Q[m]) :
    QIndex.secondRegisterBasis t m (joinRegisters t m x y) = y := by
  ext i
  have hi : ¬t + i.val < t := by omega
  simp [joinRegisters, QIndex.secondRegisterBasis, QIndex.secondRegisterIndex, hi,
    Nat.add_sub_cancel_left t i.val]

@[simp] private theorem joinRegisters_first_second (t m : ℕ) (z : Q[t + m]) :
    joinRegisters t m (QIndex.firstRegisterBasis t m z) (QIndex.secondRegisterBasis t m z) = z := by
  ext i
  by_cases hi : i.val < t
  · simp [joinRegisters, hi, QIndex.firstRegisterBasis, QIndex.firstRegisterIndex]
  · simp [joinRegisters, hi, QIndex.secondRegisterBasis, QIndex.secondRegisterIndex,
      Nat.add_sub_of_le (Nat.le_of_not_gt hi)]

private theorem register_eq_of_first_second_eq {t m : ℕ} {x y : Q[t + m]}
    (hfirst : QIndex.firstRegisterBasis t m x = QIndex.firstRegisterBasis t m y)
    (hsecond : QIndex.secondRegisterBasis t m x = QIndex.secondRegisterBasis t m y) :
    x = y := by
  rw [← joinRegisters_first_second t m x, ← joinRegisters_first_second t m y, hfirst, hsecond]

private theorem firstRegisterBasis_injective_on_secondRegisterBasis {t m : ℕ} {a b : Q[t + m]}
    {y : Q[m]} (ha : QIndex.secondRegisterBasis t m a = y)
    (hb : QIndex.secondRegisterBasis t m b = y)
    (hfirst : QIndex.firstRegisterBasis t m a = QIndex.firstRegisterBasis t m b) :
    a = b :=
  register_eq_of_first_second_eq hfirst (ha.trans hb.symm)

private theorem fixed_secondRegisterBasis_fiber_nonempty (t m : ℕ) (x : Q[t]) (y : Q[m]) :
    ∃ z : Q[t + m],
      QIndex.firstRegisterBasis t m z = x ∧ QIndex.secondRegisterBasis t m z = y :=
  ⟨joinRegisters t m x y, by simp⟩

private theorem sum_fixed_secondRegisterBasis_eq_sum_firstRegisterBasis {α : Type*}
    [AddCommMonoid α] (t m : ℕ) (y : Q[m]) (f : Q[t] → α) :
    (∑ z : Q[t + m],
      if QIndex.secondRegisterBasis t m z = y then f (QIndex.firstRegisterBasis t m z) else 0) =
      ∑ x : Q[t], f x := by
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun z _ => QIndex.firstRegisterBasis t m z) ?_ ?_ ?_ ?_
  · intro z _
    exact Finset.mem_univ _
  · intro a ha b hb hfirst
    exact firstRegisterBasis_injective_on_secondRegisterBasis
      (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2 hfirst
  · intro x _
    obtain ⟨z, hzfirst, hzsecond⟩ := fixed_secondRegisterBasis_fiber_nonempty t m x y
    exact ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzsecond⟩, hzfirst⟩
  · intro z _
    rfl

private theorem sum_fixed_secondRegisterBasis_mul_eq_zero_of_ne {t m : ℕ} {y₁ y₂ : Q[m]}
    (hne : y₁ ≠ y₂) (f g : Q[t] → ℂ) :
    (∑ z : Q[t + m],
      (if QIndex.secondRegisterBasis t m z = y₁ then f (QIndex.firstRegisterBasis t m z) else 0) *
        (if QIndex.secondRegisterBasis t m z = y₂ then
          g (QIndex.firstRegisterBasis t m z)
        else
          0)) = 0 := by
  refine Finset.sum_eq_zero ?_
  intro z _
  by_cases h₁ : QIndex.secondRegisterBasis t m z = y₁
  · simp [h₁, hne]
  · simp [h₁]

private theorem liftFirstRegisterMatrix_mul_star_apply_sum (t m : ℕ) (U : QMat t)
    (out inn : Q[t + m]) :
    (liftFirstRegisterMatrix t m U * star (liftFirstRegisterMatrix t m U)) out inn =
      ∑ x : Q[t + m],
        (if QIndex.secondRegisterBasis t m x = QIndex.secondRegisterBasis t m out then
          U (QIndex.firstRegisterBasis t m out) (QIndex.firstRegisterBasis t m x)
        else
          0) *
          (if QIndex.secondRegisterBasis t m x = QIndex.secondRegisterBasis t m inn then
            star (U (QIndex.firstRegisterBasis t m inn) (QIndex.firstRegisterBasis t m x))
          else
            0) := by
  simp only [Matrix.mul_apply, liftFirstRegisterMatrix, Matrix.of_apply, Matrix.star_apply]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hout : QIndex.secondRegisterBasis t m x = QIndex.secondRegisterBasis t m out
  · have hout' : QIndex.secondRegisterBasis t m out = QIndex.secondRegisterBasis t m x := hout.symm
    by_cases hinn : QIndex.secondRegisterBasis t m x = QIndex.secondRegisterBasis t m inn
    · have hinn' : QIndex.secondRegisterBasis t m inn = QIndex.secondRegisterBasis t m x :=
        hinn.symm
      rw [if_pos hout', if_pos hinn', if_pos hout, if_pos hinn]
    · have hinn' : QIndex.secondRegisterBasis t m inn ≠ QIndex.secondRegisterBasis t m x := by
        intro h
        exact hinn h.symm
      rw [if_pos hout', if_neg hinn', if_pos hout, if_neg hinn]
      simp
  · have hout' : QIndex.secondRegisterBasis t m out ≠ QIndex.secondRegisterBasis t m x := by
      intro h
      exact hout h.symm
    rw [if_neg hout', if_neg hout]
    simp

private theorem liftFirstRegisterMatrix_mul_star_apply_of_second_eq (t m : ℕ) (U : QMat t)
    {out inn : Q[t + m]}
    (hsecond : QIndex.secondRegisterBasis t m out = QIndex.secondRegisterBasis t m inn) :
    (liftFirstRegisterMatrix t m U * star (liftFirstRegisterMatrix t m U)) out inn =
      (U * star U)
        (QIndex.firstRegisterBasis t m out) (QIndex.firstRegisterBasis t m inn) := by
  rw [liftFirstRegisterMatrix_mul_star_apply_sum]
  calc
    (∑ x : Q[t + m],
      (if QIndex.secondRegisterBasis t m x = QIndex.secondRegisterBasis t m out then
        U (QIndex.firstRegisterBasis t m out) (QIndex.firstRegisterBasis t m x)
      else
        0) *
        (if QIndex.secondRegisterBasis t m x = QIndex.secondRegisterBasis t m inn then
          star (U (QIndex.firstRegisterBasis t m inn) (QIndex.firstRegisterBasis t m x))
        else
          0)) =
        ∑ x : Q[t + m],
          if QIndex.secondRegisterBasis t m x = QIndex.secondRegisterBasis t m out then
            U (QIndex.firstRegisterBasis t m out) (QIndex.firstRegisterBasis t m x) *
              star (U (QIndex.firstRegisterBasis t m inn) (QIndex.firstRegisterBasis t m x))
          else
            0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : QIndex.secondRegisterBasis t m x = QIndex.secondRegisterBasis t m out
      · have hxinn : QIndex.secondRegisterBasis t m x = QIndex.secondRegisterBasis t m inn :=
          hx.trans hsecond
        rw [if_pos hx, if_pos hxinn, if_pos hx]
      · rw [if_neg hx, if_neg hx]
        simp
    _ = ∑ x : Q[t],
          U (QIndex.firstRegisterBasis t m out) x *
            star (U (QIndex.firstRegisterBasis t m inn) x) :=
      sum_fixed_secondRegisterBasis_eq_sum_firstRegisterBasis t m
        (QIndex.secondRegisterBasis t m out) fun x =>
          U (QIndex.firstRegisterBasis t m out) x *
          star (U (QIndex.firstRegisterBasis t m inn) x)
    _ = (U * star U)
        (QIndex.firstRegisterBasis t m out) (QIndex.firstRegisterBasis t m inn) := by
      simp [Matrix.mul_apply, Matrix.star_apply]

private theorem liftFirstRegisterMatrix_mul_star_apply_of_second_ne (t m : ℕ) (U : QMat t)
    {out inn : Q[t + m]}
    (hsecond : QIndex.secondRegisterBasis t m out ≠ QIndex.secondRegisterBasis t m inn) :
    (liftFirstRegisterMatrix t m U * star (liftFirstRegisterMatrix t m U)) out inn = 0 := by
  rw [liftFirstRegisterMatrix_mul_star_apply_sum]
  exact sum_fixed_secondRegisterBasis_mul_eq_zero_of_ne hsecond
    (fun x => U (QIndex.firstRegisterBasis t m out) x)
    (fun x => star (U (QIndex.firstRegisterBasis t m inn) x))

private theorem liftFirstRegisterMatrix_mul_star (t m : ℕ) (U : QMat t) :
    liftFirstRegisterMatrix t m U * star (liftFirstRegisterMatrix t m U) =
      liftFirstRegisterMatrix t m (U * star U) := by
  ext out inn
  by_cases hsecond :
      QIndex.secondRegisterBasis t m out = QIndex.secondRegisterBasis t m inn
  · rw [liftFirstRegisterMatrix_mul_star_apply_of_second_eq t m U hsecond]
    simp [liftFirstRegisterMatrix, hsecond]
  · rw [liftFirstRegisterMatrix_mul_star_apply_of_second_ne t m U hsecond]
    simp [liftFirstRegisterMatrix, hsecond]

private theorem liftFirstRegisterMatrix_one (t m : ℕ) :
    liftFirstRegisterMatrix t m (1 : QMat t) = 1 := by
  ext out inn
  by_cases hsecond :
      QIndex.secondRegisterBasis t m out = QIndex.secondRegisterBasis t m inn
  · by_cases hfirst : QIndex.firstRegisterBasis t m out = QIndex.firstRegisterBasis t m inn
    · have hidx : out = inn := register_eq_of_first_second_eq hfirst hsecond
      simp [liftFirstRegisterMatrix, Matrix.one_apply, hidx]
    · have hidx : out ≠ inn := by
        intro hidx
        exact hfirst (by simp [hidx])
      simp [liftFirstRegisterMatrix, hsecond, hfirst, Matrix.one_apply, hidx]
  · have hidx : out ≠ inn := by
      intro hidx
      exact hsecond (by simp [hidx])
    simp [liftFirstRegisterMatrix, hsecond, Matrix.one_apply, hidx]

theorem liftFirstRegisterMatrix_unitary (t m : ℕ) (U : QMat t) (hU : U.Unitary) :
    (liftFirstRegisterMatrix t m U).Unitary := by
  rcases hU with ⟨h_left, h_right⟩
  have h_lift_right : liftFirstRegisterMatrix t m U * star (liftFirstRegisterMatrix t m U) = 1 := by
    rw [liftFirstRegisterMatrix_mul_star, h_right, liftFirstRegisterMatrix_one]
  exact unitary_of_mul_star_eq_one h_lift_right

end QMat

end

end QLean
