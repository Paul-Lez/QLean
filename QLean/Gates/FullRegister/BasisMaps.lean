/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/

import QLean.Foundation.QMat

/-! # Basis-map full-register gates -/

namespace QLean

noncomputable section

open scoped Matrix ComplexOrder
open Matrix Complex

namespace QMat

/--
Matrix of a computational-basis map.

The entry convention is `out, inn`, so applying this matrix sends the basis vector `|inn>` to
`|f inn>`. The matrix is unitary when `f` is bijective.
-/
def basisMapMatrix {n : ℕ} (f : Q[n] → Q[n]) : QMat n :=
  Matrix.of fun out inn => if out = f inn then 1 else 0

private theorem basisMapMatrix_star_mul_self_of_injective {n : ℕ} {f : Q[n] → Q[n]}
    (hf : Function.Injective f) :
    star (basisMapMatrix f) * basisMapMatrix f = 1 := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    calc
      (star (basisMapMatrix f) * basisMapMatrix f) i i = 1 := by
        rw [Matrix.mul_apply, Fintype.sum_eq_single (f i)]
        · simp [basisMapMatrix]
        · intro k hk
          simp [basisMapMatrix, hk]
      _ = (1 : QMat n) i i := by simp
  · have hfij : f i ≠ f j := fun h => hij (hf h)
    calc
      (star (basisMapMatrix f) * basisMapMatrix f) i j = 0 := by
        rw [Matrix.mul_apply]
        apply Finset.sum_eq_zero
        intro k _
        by_cases hki : k = f i
        · simp [basisMapMatrix, hki, hfij]
        · simp [basisMapMatrix, hki]
      _ = (1 : QMat n) i j := by simp [hij]

private theorem basisMapMatrix_mul_star_self_of_bijective {n : ℕ} {f : Q[n] → Q[n]}
    (hf : Function.Bijective f) :
    basisMapMatrix f * star (basisMapMatrix f) = 1 := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    obtain ⟨x, hx⟩ := hf.2 i
    calc
      (basisMapMatrix f * star (basisMapMatrix f)) i i = 1 := by
        rw [Matrix.mul_apply, Fintype.sum_eq_single x]
        · simp [basisMapMatrix, hx]
        · intro y hyx
          have hiy : i ≠ f y := by
            intro hiy
            apply hyx
            apply hf.1
            calc
              f y = i := hiy.symm
              _ = f x := hx.symm
          simp [basisMapMatrix, hiy]
      _ = (1 : QMat n) i i := by simp
  · have hterm : ∀ k,
        (if i = f k then (1 : ℂ) else 0) * (if j = f k then (1 : ℂ) else 0) = 0 := by
      intro k
      by_cases hik : i = f k
      · have hjk : j ≠ f k := by
          intro hjk
          exact hij (hik.trans hjk.symm)
        simp [hik, hjk]
      · simp [hik]
    calc
      (basisMapMatrix f * star (basisMapMatrix f)) i j = 0 := by
        rw [Matrix.mul_apply]
        apply Finset.sum_eq_zero
        intro k _
        simpa [basisMapMatrix] using hterm k
      _ = (1 : QMat n) i j := by simp [hij]

theorem basisMapMatrix_unitary_of_bijective {n : ℕ} (f : Q[n] → Q[n])
    (hf : Function.Bijective f) :
    (basisMapMatrix f).Unitary :=
  ⟨basisMapMatrix_star_mul_self_of_injective hf.1,
    basisMapMatrix_mul_star_self_of_bijective hf⟩

/-- An involutive basis-state map gives a unitary permutation matrix. -/
theorem basisMapMatrix_unitary_of_involutive {n : ℕ} (f : Q[n] → Q[n])
    (hf : Function.Involutive f) :
    (basisMapMatrix f).Unitary :=
  basisMapMatrix_unitary_of_bijective f hf.bijective

/-- Replace one bit of a basis index. -/
def updateBit {n : ℕ} (x : Q[n]) (q : Fin n) (b : Fin 2) : Q[n] :=
  Function.update x q b

@[simp] private theorem updateBit_apply_self {n : ℕ} (x : Q[n]) (q : Fin n)
    (b : Fin 2) :
    updateBit x q b q = b := by
  simp [updateBit]

@[simp] private theorem updateBit_apply_ne {n : ℕ} (x : Q[n]) {i q : Fin n}
    (b : Fin 2) (hiq : i ≠ q) :
    updateBit x q b i = x i := by
  simp [updateBit, hiq]

/-- Flip a computational-basis bit. -/
def flipBit {n : ℕ} (x : Q[n]) (q : Fin n) : Q[n] :=
  updateBit x q (if x q = (0 : Fin 2) then 1 else 0)

@[simp] private theorem flipBit_apply_self {n : ℕ} (x : Q[n]) (q : Fin n) :
    flipBit x q q = if x q = (0 : Fin 2) then 1 else 0 := by
  simp [flipBit]

@[simp] private theorem flipBit_apply_ne {n : ℕ} (x : Q[n]) {i q : Fin n}
    (hiq : i ≠ q) :
    flipBit x q i = x i := by
  simp [flipBit, hiq]

private theorem flipBit_involutive {n : ℕ} (q : Fin n) :
    Function.Involutive (fun x : Q[n] => flipBit x q) := by
  intro x
  ext i
  by_cases hiq : i = q
  · subst i
    rcases Fin.exists_fin_two.mp ⟨x q, rfl⟩ with h | h <;> simp [h, flipBit]
  · simp [hiq]

/-- Swap two computational-basis bits. -/
def swapBits {n : ℕ} (x : Q[n]) (q r : Fin n) : Q[n] :=
  updateBit (updateBit x q (x r)) r (x q)

private theorem swapBits_apply {n : ℕ} (x : Q[n]) (q r i : Fin n) :
    swapBits x q r i = if i = r then x q else if i = q then x r else x i := by
  unfold swapBits
  by_cases hir : i = r
  · subst i
    simp
  · by_cases hiq : i = q
    · subst i
      simp [hir]
    · simp [hir, hiq]

private theorem swapBits_involutive {n : ℕ} (q r : Fin n) :
    Function.Involutive (fun x : Q[n] => swapBits x q r) := by
  intro x
  ext i
  by_cases hiq : i = q
  · subst i
    by_cases hqr : q = r <;> simp [swapBits_apply, hqr]
  · by_cases hir : i = r
    · subst i
      have hqr : q ≠ r := by
        intro hqr
        exact hiq hqr.symm
      simp [swapBits_apply, hqr]
    · simp [swapBits_apply, hiq, hir]

private theorem cnotBasisMap_involutive {n : ℕ} (control target : Fin n)
    (hct : control ≠ target) :
    Function.Involutive (fun x : Q[n] =>
      if x control = (1 : Fin 2) then flipBit x target else x) := by
  intro x
  by_cases hx : x control = (1 : Fin 2)
  · have hcontrol : (flipBit x target) control = (1 : Fin 2) := by
      simp [hct, hx]
    simp [hx, hcontrol, flipBit_involutive target x]
  · simp [hx]

private theorem toffoliBasisMap_involutive {n : ℕ}
    (control₁ control₂ target : Fin n)
    (h₁t : control₁ ≠ target) (h₂t : control₂ ≠ target) :
    Function.Involutive (fun x : Q[n] =>
      if x control₁ = (1 : Fin 2) ∧ x control₂ = (1 : Fin 2) then
        flipBit x target
      else
        x) := by
  intro x
  by_cases hx : x control₁ = (1 : Fin 2) ∧ x control₂ = (1 : Fin 2)
  · have hcontrol₁ : (flipBit x target) control₁ = (1 : Fin 2) := by
      simp [h₁t, hx.1]
    have hcontrol₂ : (flipBit x target) control₂ = (1 : Fin 2) := by
      simp [h₂t, hx.2]
    simp [hx, hcontrol₁, hcontrol₂, flipBit_involutive target x]
  · simp [hx]

/-- Permutation matrix for a bit flip. -/
def xMatrix {n : ℕ} (target : Fin n) : QMat n :=
  basisMapMatrix fun x => flipBit x target

/-- Permutation matrix for controlled-NOT. -/
def cnotMatrix {n : ℕ} (control target : Fin n) : QMat n :=
  basisMapMatrix fun x =>
    if x control = (1 : Fin 2) then flipBit x target else x


/-- Permutation matrix for a Toffoli / CCNOT gate. -/
def toffoliMatrix {n : ℕ} (control₁ control₂ target : Fin n) : QMat n :=
  basisMapMatrix fun x =>
    if x control₁ = (1 : Fin 2) ∧ x control₂ = (1 : Fin 2) then
      flipBit x target
    else
      x

/-- Permutation matrix for a SWAP gate. -/
def swapMatrix {n : ℕ} (q r : Fin n) : QMat n :=
  basisMapMatrix fun x => swapBits x q r

theorem xMatrix_unitary {n : ℕ} (target : Fin n) :
    (xMatrix target).Unitary := by
  simpa [xMatrix] using
    basisMapMatrix_unitary_of_involutive
      (fun x : Q[n] => flipBit x target) (flipBit_involutive target)

theorem cnotMatrix_unitary {n : ℕ} (control target : Fin n) (hct : control ≠ target) :
    (cnotMatrix control target).Unitary := by
  simpa [cnotMatrix] using
    basisMapMatrix_unitary_of_involutive
      (fun x : Q[n] => if x control = (1 : Fin 2) then flipBit x target else x)
      (cnotBasisMap_involutive control target hct)

theorem toffoliMatrix_unitary {n : ℕ}
    (control₁ control₂ target : Fin n)
    (h₁t : control₁ ≠ target) (h₂t : control₂ ≠ target) :
    (toffoliMatrix control₁ control₂ target).Unitary := by
  simpa [toffoliMatrix] using
    basisMapMatrix_unitary_of_involutive
      (fun x : Q[n] =>
        if x control₁ = (1 : Fin 2) ∧ x control₂ = (1 : Fin 2) then flipBit x target else x)
      (toffoliBasisMap_involutive control₁ control₂ target h₁t h₂t)

theorem swapMatrix_unitary {n : ℕ} (q r : Fin n) :
    (swapMatrix q r).Unitary := by
  simpa [swapMatrix] using
    basisMapMatrix_unitary_of_involutive
      (fun x : Q[n] => swapBits x q r) (swapBits_involutive q r)

end QMat

end

end QLean
