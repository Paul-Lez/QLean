/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
import QLean.Examples.Algorithms.GroverWP.LinearAlgebra

/-!
# Exact Four-Element Grover Search

This file contains the main ingredients and exact success theorem for the two-qubit GroverWP
instance.  The exact matrix calculation itself is imported through `GroverWP.LinearAlgebra`.
-/

namespace QLean

noncomputable section

open scoped Matrix ComplexOrder

namespace QProg
namespace GroverWP

/-! ## Program Ingredients -/

/-- Mark exactly one two-qubit computational-basis vector. -/
def markedBasisPredicate (marked : QIndex.BitVec 2) : Marked 2 :=
  fun x => x = QIndex.basisOfBits marked

/-- The two-qubit instance of the standard Grover lower bound. -/
def grover4LowerBound : ℝ :=
  1 - 1 / (2 ^ 2 : ℝ)

/-- Success probability of the prepared one-round two-qubit Grover program from `|00><00|`. -/
def grover4SuccessProbability (marked : QIndex.BitVec 2) : ℝ :=
  QMat.expect (QMat.successEffect (markedBasisPredicate marked))
    (programEvolve (markedBasisPredicate marked) 1 (QMat.zeroDensity 2))

theorem markedBasisPredicate_unique (marked : QIndex.BitVec 2) :
    ∀ x, markedBasisPredicate marked x = true ↔ x = QIndex.basisOfBits marked := by
  intro x
  simp [markedBasisPredicate]

theorem phaseOracle_markedBasisPredicate_spec (marked : QIndex.BitVec 2) :
    QMat.Canonical.Grover4OracleSpec
      (QMat.phaseOracle (markedBasisPredicate marked)) marked where
  unitary := QMat.phaseOracle_unitary (markedBasisPredicate marked)
  maps_basis_phase := by
    intro x z
    by_cases hz : z = QIndex.basisOfBits x
    · subst z
      have hbasis :
          QIndex.basisOfBits x = QIndex.basisOfBits marked ↔
            x = marked :=
        LinearAlgebra.basisOfBits_injective.eq_iff
      simp [QMat.phaseOracle, markedBasisPredicate, hbasis]
    · simp [QMat.phaseOracle, Matrix.diagonal, hz]

/-! ## Exact Two-Qubit Proof -/

/-- The current GroverWP one-round evolution agrees with the exact Grover-4 matrix result. -/
theorem programEvolve_grover4_eq_projBits (marked : QIndex.BitVec 2) :
    programEvolve (markedBasisPredicate marked) 1 (QMat.zeroDensity 2) =
      QMat.projBits marked := by
  rw [programEvolve, pow_one, QMat.groverIterate, LinearAlgebra.exec_evolve_mul]
  exact QMat.Canonical.grover4Final_eq_projBits marked
    (QMat.phaseOracle (markedBasisPredicate marked))
    (phaseOracle_markedBasisPredicate_spec marked)

theorem grover4_successProbability_eq_one (marked : QIndex.BitVec 2) :
    grover4SuccessProbability marked = 1 := by
  unfold grover4SuccessProbability
  rw [programEvolve_grover4_eq_projBits]
  exact QMat.Canonical.expect_successEffect_projBits marked

/--
Exact two-qubit amplitude-amplification bound for one Grover round.

For `N = 4`, one oracle-plus-diffusion round reaches the marked basis state exactly, so the
standard two-qubit lower bound `1 - 1/4` follows immediately.
-/
theorem grover4_success_bound (marked : QIndex.BitVec 2) :
    grover4LowerBound ≤ grover4SuccessProbability marked := by
  rw [grover4_successProbability_eq_one]
  norm_num [grover4LowerBound]

end GroverWP
end QProg

end

end QLean
