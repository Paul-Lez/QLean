/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
import QLean.Syntax.WP
import QLean.Syntax.Gates

/-!
# Reusable Execution Properties

This file contains generic semantic infrastructure for fixed-register `QProg` programs:
finite-support execution traces, branch-label predicates, branchwise positivity, a lightweight
classical-quantum state wrapper, and structural trace/positivity preservation lemmas.
-/

namespace QLean

noncomputable section

open scoped Matrix ComplexOrder

namespace QProg

/-! ## Finite-support execution predicates -/

/--
Total trace of a finite-support classical-quantum execution state.

For physical executions this is the total probability mass of all branches, because branch
matrices are subnormalised.
-/
def execTrace {n : ℕ} {α : Type} (μ : QProg.Exec n α) : ℂ :=
  μ.sum fun _ ρ => Matrix.trace ρ

@[simp] theorem execTrace_zero {n : ℕ} {α : Type} :
    execTrace (0 : QProg.Exec n α) = 0 := by
  simp [execTrace]

theorem execTrace_add {n : ℕ} {α : Type} (μ ν : QProg.Exec n α) :
    execTrace (μ + ν) = execTrace μ + execTrace ν := by
  classical
  unfold execTrace
  rw [Finsupp.sum_add_index]
  · intro a ha
    simp
  · intro a ha ρ₁ ρ₂
    simp [Matrix.trace_add]

@[simp] theorem execTrace_pureBranch {n : ℕ} {α : Type} (a : α) (ρ : QMat n) :
    execTrace (QProg.Exec.pureBranch a ρ) = Matrix.trace ρ := by
  unfold execTrace QProg.Exec.pureBranch
  rw [Finsupp.sum_single_index]
  simp

theorem execTrace_bind_pureBranch_map {n : ℕ} {α β : Type}
    (μ : QProg.Exec n α) (f : α → β) :
    execTrace (QProg.Exec.bind μ (fun a ρ => QProg.Exec.pureBranch (f a) ρ)) =
      execTrace μ := by
  classical
  induction μ using Finsupp.induction with
  | zero =>
      simp [QProg.Exec.bind]
  | single_add a ρ μ ha hρ ih =>
      have hzero : ∀ a, QProg.Exec.pureBranch (f a) (0 : QMat n) = 0 := by
        intro a
        simp
      have hadd :
          ∀ a (ρ₁ ρ₂ : QMat n),
            QProg.Exec.pureBranch (f a) (ρ₁ + ρ₂) =
              QProg.Exec.pureBranch (f a) ρ₁ + QProg.Exec.pureBranch (f a) ρ₂ := by
        intro a ρ₁ ρ₂
        simp
      change execTrace
          (QProg.Exec.bind (QProg.Exec.pureBranch a ρ + μ)
            (fun a ρ => QProg.Exec.pureBranch (f a) ρ)) =
        execTrace (QProg.Exec.pureBranch a ρ + μ)
      rw [QProg.Exec.bind_add (QProg.Exec.pureBranch a ρ) μ
        (fun a ρ => QProg.Exec.pureBranch (f a) ρ) hzero hadd]
      rw [execTrace_add, execTrace_add]
      rw [ih]
      simp [execTrace, QProg.Exec.bind, QProg.Exec.pureBranch]

/-- Trace preservation for a bind whose continuation preserves branch trace. -/
theorem execTrace_bind_of_trace {n : ℕ} {α β : Type}
    (μ : QProg.Exec n α) (K : α → QMat n → QProg.Exec n β)
    (hzero : ∀ a, K a 0 = 0)
    (hadd : ∀ a ρ₁ ρ₂, K a (ρ₁ + ρ₂) = K a ρ₁ + K a ρ₂)
    (htrace : ∀ a ρ, execTrace (K a ρ) = Matrix.trace ρ) :
    execTrace (QProg.Exec.bind μ K) = execTrace μ := by
  classical
  induction μ using Finsupp.induction with
  | zero =>
      simp [QProg.Exec.bind]
  | single_add a ρ μ ha hρ ih =>
      change execTrace (QProg.Exec.bind (QProg.Exec.pureBranch a ρ + μ) K) =
        execTrace (QProg.Exec.pureBranch a ρ + μ)
      rw [QProg.Exec.bind_add (QProg.Exec.pureBranch a ρ) μ K hzero hadd]
      rw [execTrace_add, execTrace_add]
      rw [ih]
      rw [QProg.Exec.bind_pureBranch_of_zero K hzero a ρ]
      simp [htrace]

/-- Branchwise positivity of a finite-support classical-quantum execution state. -/
def ExecPos {n : ℕ} {α : Type} (μ : QProg.Exec n α) : Prop :=
  ∀ a ∈ μ.support, (μ a).PosSemidef

/-- Branch-label predicate for every nonzero branch of an execution state. -/
def ExecLabelForall {n : ℕ} {α : Type} (μ : QProg.Exec n α) (P : α → Prop) : Prop :=
  ∀ a ∈ μ.support, P a

@[simp] theorem execLabelForall_zero {n : ℕ} {α : Type} {P : α → Prop} :
    ExecLabelForall (0 : QProg.Exec n α) P := by
  intro a ha
  simp at ha

theorem execLabelForall_add {n : ℕ} {α : Type} {μ ν : QProg.Exec n α}
    {P : α → Prop} (hμ : ExecLabelForall μ P) (hν : ExecLabelForall ν P) :
    ExecLabelForall (μ + ν) P := by
  intro a ha
  rw [Finsupp.mem_support_iff] at ha
  by_cases hμa : μ a = 0
  · have hνa : ν a ≠ 0 := by
      intro hνa
      exact ha (by simp [Pi.add_apply, hμa, hνa])
    exact hν a (by simpa [Finsupp.mem_support_iff] using hνa)
  · exact hμ a (by simpa [Finsupp.mem_support_iff] using hμa)

theorem execLabelForall_bind {n : ℕ} {α β : Type}
    (μ : QProg.Exec n α) (K : α → QMat n → QProg.Exec n β) {P : β → Prop}
    (hzero : ∀ a, K a 0 = 0)
    (hadd : ∀ a ρ₁ ρ₂, K a (ρ₁ + ρ₂) = K a ρ₁ + K a ρ₂)
    (hK : ∀ a ρ, ExecLabelForall (K a ρ) P) :
    ExecLabelForall (QProg.Exec.bind μ K) P := by
  classical
  induction μ using Finsupp.induction with
  | zero =>
      simp [ExecLabelForall, QProg.Exec.bind]
  | single_add a ρ μ ha hρ ih =>
      change ExecLabelForall (QProg.Exec.bind (QProg.Exec.pureBranch a ρ + μ) K) P
      rw [QProg.Exec.bind_add (QProg.Exec.pureBranch a ρ) μ K hzero hadd]
      apply execLabelForall_add
      · rw [QProg.Exec.bind_pureBranch_of_zero K hzero a ρ]
        exact hK a ρ
      · exact ih

theorem execLabelForall_bind_of_labels {n : ℕ} {α β : Type}
    (μ : QProg.Exec n α) (K : α → QMat n → QProg.Exec n β)
    {P : β → Prop} {Q : α → Prop}
    (hzero : ∀ a, K a 0 = 0)
    (hadd : ∀ a ρ₁ ρ₂, K a (ρ₁ + ρ₂) = K a ρ₁ + K a ρ₂)
    (hμ : ExecLabelForall μ Q)
    (hK : ∀ a ρ, Q a → ExecLabelForall (K a ρ) P) :
    ExecLabelForall (QProg.Exec.bind μ K) P := by
  classical
  revert hμ
  induction μ using Finsupp.induction with
  | zero =>
      intro hμ
      simp [QProg.Exec.bind]
  | single_add a ρ μ ha hρ ih =>
      intro hsum
      change ExecLabelForall (QProg.Exec.bind (QProg.Exec.pureBranch a ρ + μ) K) P
      rw [QProg.Exec.bind_add (QProg.Exec.pureBranch a ρ) μ K hzero hadd]
      apply execLabelForall_add
      · rw [QProg.Exec.bind_pureBranch_of_zero K hzero a ρ]
        have hμa_zero : μ a = 0 := by
          simpa [Finsupp.mem_support_iff] using ha
        have ha_support : a ∈ (QProg.Exec.pureBranch a ρ + μ).support := by
          rw [Finsupp.mem_support_iff]
          simp [QProg.Exec.pureBranch, hμa_zero, hρ]
        exact hK a ρ (hsum a ha_support)
      · apply ih
        intro b hb
        have hb_ne_a : b ≠ a := by
          intro hba
          subst b
          exact ha hb
        have hb_support : b ∈ (QProg.Exec.pureBranch a ρ + μ).support := by
          rw [Finsupp.mem_support_iff] at hb ⊢
          simp [QProg.Exec.pureBranch, Finsupp.single_eq_of_ne hb_ne_a, hb]
        exact hsum b hb_support

theorem execLabelForall_pureBranch {n : ℕ} {α : Type} (a : α) (ρ : QMat n)
    {P : α → Prop} (ha : P a) :
    ExecLabelForall (QProg.Exec.pureBranch a ρ) P := by
  intro b hb
  by_cases hρ : ρ = 0
  · simp [QProg.Exec.pureBranch, hρ] at hb
  · have hb' : b = a := by
      by_contra hne
      rw [Finsupp.mem_support_iff] at hb
      exact hb (by simp [QProg.Exec.pureBranch, Finsupp.single_eq_of_ne hne])
    simpa [hb'] using ha

theorem execLabelForall_bind_pureBranch_map {n : ℕ} {α β : Type}
    (μ : QProg.Exec n α) (f : α → β) {P : β → Prop}
    (hμ : ExecLabelForall μ (fun a => P (f a))) :
    ExecLabelForall
      (QProg.Exec.bind μ (fun a ρ => QProg.Exec.pureBranch (f a) ρ)) P := by
  apply execLabelForall_bind_of_labels μ
      (fun a ρ => QProg.Exec.pureBranch (f a) ρ)
      (P := P) (Q := fun a => P (f a))
  · intro a
    simp
  · intro a ρ₁ ρ₂
    simp
  · exact hμ
  · intro a ρ ha
    exact execLabelForall_pureBranch (f a) ρ ha

@[simp] theorem execPos_zero {n : ℕ} {α : Type} :
    ExecPos (0 : QProg.Exec n α) := by
  intro a ha
  simp at ha

theorem execPos_add {n : ℕ} {α : Type} {μ ν : QProg.Exec n α}
    (hμ : ExecPos μ) (hν : ExecPos ν) :
    ExecPos (μ + ν) := by
  intro a ha
  rw [Finsupp.mem_support_iff] at ha
  by_cases hμa : μ a = 0
  · have hνa : ν a ≠ 0 := by
      intro hνa
      exact ha (by simp [Pi.add_apply, hμa, hνa])
    have hνpos := hν a (by simpa [Finsupp.mem_support_iff] using hνa)
    simpa [Pi.add_apply, hμa] using hνpos
  · by_cases hνa : ν a = 0
    · have hμpos := hμ a (by simpa [Finsupp.mem_support_iff] using hμa)
      simpa [Pi.add_apply, hνa] using hμpos
    · have hμpos := hμ a (by simpa [Finsupp.mem_support_iff] using hμa)
      have hνpos := hν a (by simpa [Finsupp.mem_support_iff] using hνa)
      simpa [Pi.add_apply] using QMat.pos_add hμpos hνpos

theorem execPos_pureBranch {n : ℕ} {α : Type} (a : α) {ρ : QMat n}
    (hρ : ρ.PosSemidef) :
    ExecPos (QProg.Exec.pureBranch a ρ) := by
  intro b hb
  by_cases hzero : ρ = 0
  · simp [QProg.Exec.pureBranch, hzero] at hb
  · by_cases hba : b = a
    · subst b
      simpa [QProg.Exec.pureBranch] using hρ
    · rw [Finsupp.mem_support_iff] at hb
      exact (hb (by simp [QProg.Exec.pureBranch, Finsupp.single_eq_of_ne hba])).elim

theorem execPos_bind_of_pos {n : ℕ} {α β : Type}
    (μ : QProg.Exec n α) (K : α → QMat n → QProg.Exec n β)
    (hzero : ∀ a, K a 0 = 0)
    (hadd : ∀ a ρ₁ ρ₂, K a (ρ₁ + ρ₂) = K a ρ₁ + K a ρ₂)
    (hμ : ExecPos μ)
    (hK : ∀ a ρ, ρ.PosSemidef → ExecPos (K a ρ)) :
    ExecPos (QProg.Exec.bind μ K) := by
  classical
  revert hμ
  induction μ using Finsupp.induction with
  | zero =>
      intro hμ
      simp [QProg.Exec.bind]
  | single_add a ρ μ ha hρ ih =>
      intro hsum
      change ExecPos (QProg.Exec.bind (QProg.Exec.pureBranch a ρ + μ) K)
      rw [QProg.Exec.bind_add (QProg.Exec.pureBranch a ρ) μ K hzero hadd]
      apply execPos_add
      · rw [QProg.Exec.bind_pureBranch_of_zero K hzero a ρ]
        have hμa_zero : μ a = 0 := by
          simpa [Finsupp.mem_support_iff] using ha
        have ha_support : a ∈ (QProg.Exec.pureBranch a ρ + μ).support := by
          rw [Finsupp.mem_support_iff]
          simp [QProg.Exec.pureBranch, hμa_zero, hρ]
        have hρpos' := hsum a ha_support
        have hρpos : ρ.PosSemidef := by
          simpa [QProg.Exec.pureBranch, hμa_zero] using hρpos'
        exact hK a ρ hρpos
      · apply ih
        intro b hb
        have hb_ne_a : b ≠ a := by
          intro hba
          subst b
          exact ha hb
        have hb_support : b ∈ (QProg.Exec.pureBranch a ρ + μ).support := by
          rw [Finsupp.mem_support_iff] at hb ⊢
          simp [QProg.Exec.pureBranch, Finsupp.single_eq_of_ne hb_ne_a, hb]
        have hpos' := hsum b hb_support
        simpa [QProg.Exec.pureBranch, Finsupp.single_eq_of_ne hb_ne_a] using hpos'

theorem execPos_bind_pureBranch_map {n : ℕ} {α β : Type}
    (μ : QProg.Exec n α) (f : α → β) (hμ : ExecPos μ) :
    ExecPos (QProg.Exec.bind μ (fun a ρ => QProg.Exec.pureBranch (f a) ρ)) := by
  apply execPos_bind_of_pos μ
      (fun a ρ => QProg.Exec.pureBranch (f a) ρ)
  · intro a
    simp
  · intro a ρ₁ ρ₂
    simp
  · exact hμ
  · intro a ρ hρ
    exact execPos_pureBranch (f a) hρ

/-! ## Structural Trace and Positivity Preservation -/

/-- Trace preservation for a fixed-register program. -/
def TracePreserving {σ α : Type} {n : ℕ} (prog : QProg σ n α) : Prop :=
  ∀ (s : σ) (ρ : QMat n), execTrace (QProg.denote prog s ρ) = Matrix.trace ρ

/-- Positivity preservation for a fixed-register program. -/
def PositivityPreserving {σ α : Type} {n : ℕ} (prog : QProg σ n α) : Prop :=
  ∀ (s : σ) (ρ : QMat n), ρ.PosSemidef → ExecPos (QProg.denote prog s ρ)

theorem tracePreserving_bind_pure_map {σ α β : Type} {n : ℕ}
    (prog : QProg σ n α) (f : α → β) (hprog : TracePreserving prog) :
    TracePreserving (prog >>= fun a => pure (f a)) := by
  intro s ρ
  rw [QProg.denote_bind]
  change execTrace
      (QProg.Exec.bind (QProg.denote prog s ρ)
        (fun sa ρ' => QProg.denote (Pure.pure (f sa.2) : QProg σ n β) sa.1 ρ')) =
    Matrix.trace ρ
  change execTrace
      (QProg.Exec.bind (QProg.denote prog s ρ)
        (fun sa ρ' => QProg.Exec.pureBranch (sa.1, f sa.2) ρ')) =
    Matrix.trace ρ
  rw [execTrace_bind_pureBranch_map]
  exact hprog s ρ

theorem tracePreserving_bind {σ α β : Type} {n : ℕ}
    (prog : QProg σ n α) (cont : α → QProg σ n β)
    (hprog : TracePreserving prog) (hcont : ∀ a, TracePreserving (cont a)) :
    TracePreserving (prog >>= cont) := by
  intro s ρ
  rw [QProg.denote_bind]
  change execTrace
      (QProg.Exec.bind (QProg.denote prog s ρ)
        (fun sa ρ' => QProg.denote (cont sa.2) sa.1 ρ')) =
    Matrix.trace ρ
  rw [execTrace_bind_of_trace]
  · exact hprog s ρ
  · intro sa
    exact QProg.denote_zero (cont sa.2) sa.1
  · intro sa ρ₁ ρ₂
    exact QProg.denote_add (cont sa.2) sa.1 ρ₁ ρ₂
  · intro sa ρ'
    exact hcont sa.2 sa.1 ρ'

theorem tracePreserving_pure {σ α : Type} {n : ℕ} (a : α) :
    TracePreserving (Pure.pure a : QProg σ n α) := by
  intro s ρ
  change execTrace (QProg.Exec.pureBranch (s, a) ρ) = Matrix.trace ρ
  simp

theorem tracePreserving_applyUnitary {σ : Type} {n : ℕ}
    (U : QMat n) (hU : U.Unitary) :
    TracePreserving (QProg.applyUnitary (σ := σ) U hU) := by
  intro s ρ
  rw [QProg.denote_applyUnitary]
  simp [QProg.denotePrim, QProg.Exec.evolve, QMat.trace_evolve_of_unitary U hU]

theorem tracePreserving_meas {σ : Type} {n : ℕ} (q : Fin n) :
    TracePreserving (QProg.meas (σ := σ) q) := by
  intro s ρ
  rw [QProg.denote_meas]
  unfold QProg.denotePrim
  change execTrace (QProg.Exec.measBranch q s ρ) = Matrix.trace ρ
  unfold QProg.Exec.measBranch
  rw [execTrace_add]
  change execTrace
      (QProg.Exec.pureBranch (s, false)
        (QMat.measProjector q false * ρ * QMat.measProjector q false)) +
      execTrace
        (QProg.Exec.pureBranch (s, true)
          (QMat.measProjector q true * ρ * QMat.measProjector q true)) =
    Matrix.trace ρ
  simp only [execTrace_pureBranch]
  simpa [QMat.measProjector] using QMat.trace_measure_split q ρ

theorem tracePreserving_measQubits {σ : Type} {n : ℕ}
    (qs : List (Fin n)) :
    TracePreserving (QProg.measQubits (σ := σ) qs) := by
  induction qs with
  | nil =>
      simpa [QProg.measQubits] using
        (tracePreserving_pure (σ := σ) (n := n) ([] : List Bool))
  | cons q qs ih =>
      simpa [QProg.measQubits, Cslib.FreeM.bind_eq_bind] using
        tracePreserving_bind (QProg.meas (σ := σ) q)
          (fun b => QProg.measQubits (σ := σ) qs >>= fun bs => pure (b :: bs))
          (tracePreserving_meas q)
          (fun b => tracePreserving_bind_pure_map
            (QProg.measQubits (σ := σ) qs) (fun bs => b :: bs) ih)

theorem positivityPreserving_bind_pure_map {σ α β : Type} {n : ℕ}
    (prog : QProg σ n α) (f : α → β) (hprog : PositivityPreserving prog) :
    PositivityPreserving (prog >>= fun a => pure (f a)) := by
  intro s ρ hρ
  rw [QProg.denote_bind]
  change ExecPos
      (QProg.Exec.bind (QProg.denote prog s ρ)
        (fun sa ρ' => QProg.Exec.pureBranch (sa.1, f sa.2) ρ'))
  exact execPos_bind_pureBranch_map
    (QProg.denote prog s ρ) (fun sa => (sa.1, f sa.2)) (hprog s ρ hρ)

theorem positivityPreserving_bind {σ α β : Type} {n : ℕ}
    (prog : QProg σ n α) (cont : α → QProg σ n β)
    (hprog : PositivityPreserving prog) (hcont : ∀ a, PositivityPreserving (cont a)) :
    PositivityPreserving (prog >>= cont) := by
  intro s ρ hρ
  rw [QProg.denote_bind]
  change ExecPos
      (QProg.Exec.bind (QProg.denote prog s ρ)
        (fun sa ρ' => QProg.denote (cont sa.2) sa.1 ρ'))
  apply execPos_bind_of_pos
  · intro sa
    exact QProg.denote_zero (cont sa.2) sa.1
  · intro sa ρ₁ ρ₂
    exact QProg.denote_add (cont sa.2) sa.1 ρ₁ ρ₂
  · exact hprog s ρ hρ
  · intro sa ρ' hρ'
    exact hcont sa.2 sa.1 ρ' hρ'

theorem positivityPreserving_pure {σ α : Type} {n : ℕ} (a : α) :
    PositivityPreserving (Pure.pure a : QProg σ n α) := by
  intro s ρ hρ
  change ExecPos (QProg.Exec.pureBranch (s, a) ρ)
  exact execPos_pureBranch (s, a) hρ

theorem positivityPreserving_applyUnitary {σ : Type} {n : ℕ}
    (U : QMat n) (hU : U.Unitary) :
    PositivityPreserving (QProg.applyUnitary (σ := σ) U hU) := by
  intro s ρ hρ
  rw [QProg.denote_applyUnitary]
  change ExecPos (QProg.Exec.pureBranch (s, ()) (QProg.Exec.evolve U ρ))
  exact execPos_pureBranch (s, ()) (QMat.pos_evolve_of_unitary U hU hρ)

theorem positivityPreserving_meas {σ : Type} {n : ℕ} (q : Fin n) :
    PositivityPreserving (QProg.meas (σ := σ) q) := by
  intro s ρ hρ
  rw [QProg.denote_meas]
  unfold QProg.denotePrim QProg.Exec.measBranch
  exact execPos_add
    (execPos_pureBranch (s, false) (QMat.pos_measure q false hρ))
    (execPos_pureBranch (s, true) (QMat.pos_measure q true hρ))

theorem positivityPreserving_measQubits {σ : Type} {n : ℕ}
    (qs : List (Fin n)) :
    PositivityPreserving (QProg.measQubits (σ := σ) qs) := by
  induction qs with
  | nil =>
      simpa [QProg.measQubits] using
        (positivityPreserving_pure (σ := σ) (n := n) ([] : List Bool))
  | cons q qs ih =>
      simpa [QProg.measQubits, Cslib.FreeM.bind_eq_bind] using
        positivityPreserving_bind (QProg.meas (σ := σ) q)
          (fun b => QProg.measQubits (σ := σ) qs >>= fun bs => pure (b :: bs))
          (positivityPreserving_meas q)
          (fun b => positivityPreserving_bind_pure_map
            (QProg.measQubits (σ := σ) qs) (fun bs => b :: bs) ih)

theorem execTrace_denoteOn_of_tracePreserving {σ α : Type} {n : ℕ}
    (prog : QProg σ n α) (hprog : TracePreserving prog) (μ : QProg.Exec n σ) :
    execTrace (QProg.denoteOn prog μ) = execTrace μ := by
  unfold QProg.denoteOn QProg.ExecM.runOn
  exact execTrace_bind_of_trace μ
    (fun s ρ => QProg.denote prog s ρ)
    (fun s => QProg.denote_zero prog s)
    (fun s ρ₁ ρ₂ => QProg.denote_add prog s ρ₁ ρ₂)
    (fun s ρ => hprog s ρ)

theorem execPos_denoteOn_of_positivityPreserving {σ α : Type} {n : ℕ}
    (prog : QProg σ n α) (hprog : PositivityPreserving prog)
    {μ : QProg.Exec n σ} (hμ : ExecPos μ) :
    ExecPos (QProg.denoteOn prog μ) := by
  unfold QProg.denoteOn QProg.ExecM.runOn
  exact execPos_bind_of_pos μ
    (fun s ρ => QProg.denote prog s ρ)
    (fun s => QProg.denote_zero prog s)
    (fun s ρ₁ ρ₂ => QProg.denote_add prog s ρ₁ ρ₂)
    hμ
    (fun s ρ hρ => hprog s ρ hρ)

theorem measQubits_output_length {σ : Type} {n : ℕ}
    (qs : List (Fin n)) :
    ∀ (s : σ) (ρ : QMat n),
      ExecLabelForall (QProg.denote (QProg.measQubits (σ := σ) qs) s ρ)
        (fun out : σ × List Bool => out.2.length = qs.length) := by
  induction qs with
  | nil =>
      intro s ρ
      change ExecLabelForall (QProg.Exec.pureBranch (s, ([] : List Bool)) ρ)
        (fun out : σ × List Bool => out.2.length = ([] : List (Fin n)).length)
      exact execLabelForall_pureBranch (s, ([] : List Bool)) ρ rfl
  | cons q qs ih =>
      intro s ρ
      change ExecLabelForall
            (QProg.denote
              (QProg.meas (σ := σ) q >>= fun b =>
            QProg.measQubits (σ := σ) qs >>= fun bs =>
            pure (b :: bs)) s ρ)
        (fun out : σ × List Bool => out.2.length = (q :: qs).length)
      rw [QProg.denote_meas_bind]
      apply execLabelForall_add
      · rw [QProg.denote_bind]
        change ExecLabelForall
            (QProg.Exec.bind
            (QProg.denote (QProg.measQubits (σ := σ) qs) s
              (QMat.measProjector q false * ρ * QMat.measProjector q false))
            (fun sa ρ' => QProg.Exec.pureBranch (sa.1, false :: sa.2) ρ'))
          (fun out : σ × List Bool => out.2.length = (q :: qs).length)
        apply execLabelForall_bind_pureBranch_map
        intro out hout
        have hlen := ih s
          (QMat.measProjector q false * ρ * QMat.measProjector q false) out hout
        simpa using hlen
      · rw [QProg.denote_bind]
        change ExecLabelForall
            (QProg.Exec.bind
            (QProg.denote (QProg.measQubits (σ := σ) qs) s
              (QMat.measProjector q true * ρ * QMat.measProjector q true))
            (fun sa ρ' => QProg.Exec.pureBranch (sa.1, true :: sa.2) ρ'))
          (fun out : σ × List Bool => out.2.length = (q :: qs).length)
        apply execLabelForall_bind_pureBranch_map
        intro out hout
        have hlen := ih s
          (QMat.measProjector q true * ρ * QMat.measProjector q true) out hout
        simpa using hlen

end QProg

end

end QLean
