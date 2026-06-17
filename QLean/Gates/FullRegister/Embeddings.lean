/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/

import QLean.Foundation.QMat

/-! # Single-qubit full-register embeddings -/

namespace QLean

noncomputable section

open scoped Matrix ComplexOrder
open Matrix Complex

namespace QMat

/-- Embed a single-qubit matrix in a register indexed by arbitrary qubit labels. -/
def applySingle {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (QIndex ι) (QIndex ι) ℂ :=
  Matrix.piKronecker
    ((fun j => if i = j then M else (1 : Matrix (Fin 2) (Fin 2) ℂ)) :
      ι → Matrix (Fin 2) (Fin 2) ℂ)

private theorem qindex_exists_ne_of_ne {n : ℕ} {a c : Q[n]} (h : a ≠ c) :
    ∃ i, a i ≠ c i := by
  by_contra hforall
  exact h (funext fun i => not_not.mp fun hi => hforall ⟨i, hi⟩)

private theorem qindex_delta_prod_of_eq {n : ℕ} {a c : Q[n]} (h : a = c) :
    (∏ i : Fin n, if a i = c i then (1 : ℂ) else 0) = 1 := by
  subst c
  exact Finset.prod_eq_one fun i _ => if_pos rfl

private theorem qindex_delta_prod_of_ne {n : ℕ} {a c : Q[n]} (h : a ≠ c) :
    (∏ i : Fin n, if a i = c i then (1 : ℂ) else 0) = 0 := by
  obtain ⟨i, hi⟩ := qindex_exists_ne_of_ne h
  exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

private theorem qindex_delta_prod {n : ℕ} (a c : Q[n]) :
    (∏ i : Fin n, if a i = c i then (1 : ℂ) else 0) =
      if a = c then 1 else 0 := by
  by_cases h : a = c
  · rw [if_pos h, qindex_delta_prod_of_eq h]
  · rw [if_neg h, qindex_delta_prod_of_ne h]

private theorem sum_qindex_mul_prod_eq_prod_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f g : (i : ι) → Fin 2 → ℂ) :
    (∑ x : QIndex ι, (∏ i : ι, f i (x i)) * (∏ i : ι, g i (x i))) =
      ∏ i : ι, ∑ x_i : Fin 2, f i x_i * g i x_i := by
  simp only [← Finset.prod_mul_distrib]
  exact Eq.symm (Fintype.prod_sum fun i x_i => f i x_i * g i x_i)

private theorem singleQubit_star_mul_self_apply
    {M : Matrix (Fin 2) (Fin 2) ℂ} (hM : star M * M = 1) (a c : Fin 2) :
    (∑ x : Fin 2, star (M x a) * M x c) = if a = c then 1 else 0 := by
  have h_entry := congr_fun (congr_fun hM a) c
  simpa only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] using h_entry

private theorem piKronecker_star_mul_self_apply {n : ℕ}
    (M : Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (h_left : ∀ i, star (M i) * M i = 1) (a c : Q[n]) :
    (star (Matrix.piKronecker (fun {i} => M i) : QMat n) *
        (Matrix.piKronecker (fun {i} => M i) : QMat n)) a c =
      if a = c then 1 else 0 := by
  simp only [Matrix.mul_apply, Matrix.piKronecker, Matrix.of_apply, Matrix.star_apply, star_prod]
  rw [sum_qindex_mul_prod_eq_prod_sum
    (fun i x_i => star (M i x_i (a i)))
    (fun i x_i => M i x_i (c i))]
  rw [Finset.prod_congr rfl fun i _ =>
    singleQubit_star_mul_self_apply (h_left i) (a i) (c i)]
  exact qindex_delta_prod a c

private theorem piKronecker_star_mul_self {n : ℕ}
    (M : Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (h_left : ∀ i, star (M i) * M i = 1) :
    star (Matrix.piKronecker (fun {i} => M i) : QMat n) *
      (Matrix.piKronecker (fun {i} => M i) : QMat n) = 1 := by
  ext a c
  simpa only [Matrix.one_apply] using piKronecker_star_mul_self_apply M h_left a c

private theorem piKronecker_fin_two_unitary {n : ℕ}
    (M : Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (h_left : ∀ i, star (M i) * M i = 1) :
    QMat.Unitary (Matrix.piKronecker (fun {i} => M i) : QMat n) :=
  unitary_of_star_mul_eq_one (piKronecker_star_mul_self M h_left)

/-
If a single-qubit matrix is unitary, its full-register embedding is unitary.
-/
theorem applySingle_unitary {n : ℕ} (q : Fin n) (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : Operator.IsUnitary U) :
    QMat.Unitary (applySingle q U) := by
  unfold applySingle
  refine piKronecker_fin_two_unitary (fun i : Fin n => if q = i then U else 1) ?_
  intro i
  by_cases hqi : q = i
  · simpa [hqi, Operator.IsUnitary, Matrix.star_eq_conjTranspose] using hU
  · simp [hqi]

end QMat

end

end QLean
