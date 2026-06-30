/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
import QLean.Syntax.WP
import QLean.Gates.FullRegister.Hadamard
import QLean.Gates.FullRegister.Phase

/-!
# Grover Search Verification Prerequisites
-/

namespace QLean

noncomputable section

open scoped Matrix ComplexOrder

namespace QProg
namespace GroverWP

/-! ## Bitstring-Level Operators -/

/-- A search predicate over the computational basis of an `n`-qubit register. -/
abbrev Marked (n : ℕ) := Q[n] → Bool

/-! ## Programs -/

/-- Prepare the usual Grover initial state by applying the full-register Hadamard layer. -/
def prepareUniform {σ : Type} (n : ℕ) : QProg σ n Unit :=
  QProg.applyUnitary (QMat.hadamardLayer n) (QMat.hadamardLayer_unitary n)

/-- One syntactic Grover round: phase oracle followed by diffusion. -/
def round {σ : Type} {n : ℕ} (marked : Marked n) : QProg σ n Unit :=
  do
    QProg.applyUnitary (σ := σ) (QMat.phaseOracle marked) (QMat.phaseOracle_unitary marked)
    QProg.applyUnitary (σ := σ) (QMat.diffusion n) (QMat.diffusion_unitary n)

/-- The compiled `k`-round Grover body as one powered unitary. -/
def iterations {σ : Type} {n : ℕ} (marked : Marked n) (k : ℕ) : QProg σ n Unit :=
  QProg.applyUnitary ((QMat.groverIterate marked) ^ k) (QMat.groverIterate_pow_unitary marked k)

/-- Grover search up to the final readout: prepare uniform state, then run `k` iterations. -/
def program {σ : Type} {n : ℕ} (marked : Marked n) (k : ℕ) : QProg σ n Unit := do
  prepareUniform (σ := σ) n
  iterations (σ := σ) marked k

/-! ## Matrix Summaries -/

/-- Matrix evolution induced by one syntactic Grover round. -/
def roundEvolve {n : ℕ} (marked : Marked n) (ρ : QMat n) : QMat n :=
  QMat.evolve (QMat.diffusion n) (QMat.evolve (QMat.phaseOracle marked) ρ)

/-- Matrix evolution induced by the compiled `k`-round Grover program after preparation. -/
def programEvolve {n : ℕ} (marked : Marked n) (k : ℕ) (ρ : QMat n) : QMat n :=
  QMat.evolve ((QMat.groverIterate marked) ^ k) (QMat.evolve (QMat.hadamardLayer n) ρ)

end GroverWP
end QProg

end

end QLean
