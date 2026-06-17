/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
import QLean.Foundation.Basis
import QLean.Gates.FullRegister.Hadamard
import QLean.Gates.FullRegister.Phase

/-!
# Shared Prerequisites for Canonical Algorithm Examples
-/

namespace QLean

noncomputable section

open scoped Matrix ComplexOrder

namespace QMat
namespace Canonical

def wpMeasQubitsCont {n : ℕ} : List (Fin n) → (List Bool → QMat n → ℝ) → QMat n → ℝ
  | [], post, ρ => post [] ρ
  | q :: qs, post, ρ =>
      wpMeasQubitsCont qs (fun bits => post (false :: bits)) (QMat.measured q false ρ) +
      wpMeasQubitsCont qs (fun bits => post (true :: bits)) (QMat.measured q true ρ)

def wpMeasBitVecCont {n m : ℕ} (idx : Fin m → Fin n)
    (post : QIndex.BitVec m → QMat n → ℝ) (ρ : QMat n) : ℝ :=
  wpMeasQubitsCont ((List.finRange m).map idx) (fun bits => post (QIndex.bitVecOfList bits)) ρ

/-- A two-qubit marked phase oracle for exact `N = 4` Grover search. -/
structure Grover4OracleSpec (Umark : QMat 2) (marked : QIndex.BitVec 2) : Prop where
  unitary : Umark.Unitary
  maps_basis_phase :
    ∀ x : QIndex.BitVec 2, ∀ z : Q[2],
      Umark z (QIndex.basisOfBits x) =
        if z = QIndex.basisOfBits x then
          (if x = marked then (-1 : ℂ) else 1)
        else
          0

end Canonical
end QMat

end

end QLean
