/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
import QLean.Syntax.Core
import Std.Tactic.Do

/-!
# Weakest Preconditions and Quantum Hoare Expectations for QProg

This file keeps the `Std.Do`/`mvcgen` integration and expectation-style Hoare layer separate
from the core QProg syntax and denotational semantics.

There are two semantics in this file.

* `ExecM` is the aggregated denotational semantics. It quotients execution paths by final
  classical label and adds their subnormalised density matrices. This is the semantics used by
  `QHoare`.

* `Path.M` is a path-preserving symbolic semantics used to satisfy Lean's `Std.Do.WPMonad`
  interface and to drive `mvcgen`.

The bridge theorem `denotePath_toAggregated_eq_denote` connects them.
-/

namespace QLean

noncomputable section

open scoped Matrix ComplexOrder
open Std.Do

namespace QProg

namespace Exec

/-! ## Branchwise support predicates -/

/-- Branchwise assertion over a finite-support execution. -/
def Forall {n : ℕ} {α : Type}
    (μ : Exec n α) (P : α → QMat n → Prop) : Prop :=
  ∀ a ∈ μ.support, P a (μ a)

@[simp] theorem forall_pureBranch {n : ℕ} {α : Type}
    (a : α) (ρ : QMat n) (P : α → QMat n → Prop) :
    Forall (pureBranch a ρ) P ↔ (ρ ≠ 0 → P a ρ) := by
  classical
  constructor
  · intro h hρ
    simpa [pureBranch] using h a (by simpa [Forall, pureBranch] using hρ)
  · intro h a' ha'
    by_cases heq : a' = a
    · subst a'
      simpa [pureBranch] using h (by simpa [Forall, pureBranch] using ha')
    · simp [pureBranch, Finsupp.single_eq_of_ne heq] at ha'

@[simp] theorem forall_bind {n : ℕ} {α β : Type}
    (μ : Exec n α) (K : α → QMat n → Exec n β) (P : β → QMat n → Prop) :
    Forall (bind μ K) P ↔
      ∀ b ∈ (bind μ K).support, P b ((bind μ K) b) :=
  Iff.rfl

@[simp] theorem forall_mapQuantum {n : ℕ} {α : Type}
    (φ : QMat n → QMat n) (hφ : φ 0 = 0)
    (μ : Exec n α) (P : α → QMat n → Prop) :
    Forall (mapQuantum φ hφ μ) P ↔
      ∀ a ∈ (mapQuantum φ hφ μ).support, P a (φ (μ a)) := by
  simp [Forall, mapQuantum]

@[simp] theorem forall_applyUnitary {n : ℕ} {α : Type}
    (U : QMat n) (μ : Exec n α) (P : α → QMat n → Prop) :
    Forall (applyUnitary U μ) P ↔
      ∀ a ∈ (applyUnitary U μ).support, P a (evolve U (μ a)) := by
  simp [applyUnitary]

@[simp] theorem forall_measBranch {n : ℕ} {α : Type}
    (target : Fin n) (label : α) (ρ : QMat n)
    (P : α × Bool → QMat n → Prop) :
    Forall (measBranch target label ρ) P ↔
      ((QMat.measProjector target false * ρ * QMat.measProjector target false) ≠ 0 →
        P (label, false)
          (QMat.measProjector target false * ρ * QMat.measProjector target false)) ∧
      ((QMat.measProjector target true * ρ * QMat.measProjector target true) ≠ 0 →
        P (label, true)
          (QMat.measProjector target true * ρ * QMat.measProjector target true)) := by
  classical
  let ρ0 := QMat.measProjector target false * ρ * QMat.measProjector target false
  let ρ1 := QMat.measProjector target true * ρ * QMat.measProjector target true
  have hfalse_true : (label, false) ≠ (label, true) := by
    intro h
    exact Bool.false_ne_true (congrArg Prod.snd h)
  unfold Forall measBranch
  change (∀ br ∈ (Finsupp.single (label, false) ρ0 + Finsupp.single (label, true) ρ1).support,
      P br ((Finsupp.single (label, false) ρ0 + Finsupp.single (label, true) ρ1) br)) ↔
      (ρ0 ≠ 0 → P (label, false) ρ0) ∧ (ρ1 ≠ 0 → P (label, true) ρ1)
  constructor
  · intro h
    constructor
    · intro h0
      have hsupp :
          (label, false) ∈
            (Finsupp.single (label, false) ρ0 + Finsupp.single (label, true) ρ1).support := by
        rw [Finsupp.mem_support_iff]
        simp [hfalse_true, h0]
      simpa [hfalse_true] using h (label, false) hsupp
    · intro h1
      have htrue_false : (label, true) ≠ (label, false) := fun h => hfalse_true h.symm
      have hsupp :
          (label, true) ∈
            (Finsupp.single (label, false) ρ0 + Finsupp.single (label, true) ρ1).support := by
        rw [Finsupp.mem_support_iff]
        simp [htrue_false, h1]
      simpa [htrue_false] using h (label, true) hsupp
  · intro h br hsupp
    rw [Finsupp.mem_support_iff] at hsupp
    rcases br with ⟨c, b⟩
    cases b
    · by_cases hc : c = label
      · subst c
        have h0 : ρ0 ≠ 0 := by simpa [hfalse_true] using hsupp
        simpa [hfalse_true] using h.1 h0
      · exfalso
        have hne0 : (c, false) ≠ (label, false) := by
          intro heq
          exact hc (congrArg Prod.fst heq)
        have hne1 : (c, false) ≠ (label, true) := by
          intro heq
          exact Bool.false_ne_true (congrArg Prod.snd heq)
        have hval :
            (Finsupp.single (label, false) ρ0 + Finsupp.single (label, true) ρ1)
              (c, false) = 0 := by
          simp [Finsupp.single_eq_of_ne hne0, Finsupp.single_eq_of_ne hne1]
        exact hsupp hval
    · by_cases hc : c = label
      · subst c
        have htrue_false : (label, true) ≠ (label, false) := fun h => hfalse_true h.symm
        have h1 : ρ1 ≠ 0 := by simpa [htrue_false] using hsupp
        simpa [htrue_false] using h.2 h1
      · exfalso
        have hne0 : (c, true) ≠ (label, false) := by
          intro heq
          exact Bool.false_ne_true (congrArg Prod.snd heq).symm
        have hne1 : (c, true) ≠ (label, true) := by
          intro heq
          exact hc (congrArg Prod.fst heq)
        have hval :
            (Finsupp.single (label, false) ρ0 + Finsupp.single (label, true) ρ1)
              (c, true) = 0 := by
          simp [Finsupp.single_eq_of_ne hne0, Finsupp.single_eq_of_ne hne1]
        exact hsupp hval

/-! ### Aggregated execution algebra -/

/-- Binding an aggregated execution with the singleton branch constructor is the identity. -/
@[simp] theorem bind_pureBranch {n : ℕ} {α : Type} (μ : Exec n α) :
    bind μ (fun a ρ => pureBranch a ρ) = μ := by
  ext a i j
  simp [bind, pureBranch]

@[simp] theorem bind_zero {n : ℕ} {α β : Type}
    (K : α → QMat n → Exec n β) :
    bind (0 : Exec n α) K = 0 := by
  simp [bind]

theorem bind_add {n : ℕ} {α β : Type}
    (μ ν : Exec n α) (K : α → QMat n → Exec n β)
    (hzero : ∀ a, K a 0 = 0)
    (hadd : ∀ a ρ₁ ρ₂, K a (ρ₁ + ρ₂) = K a ρ₁ + K a ρ₂) :
    bind (μ + ν) K = bind μ K + bind ν K := by
  simp [bind, Finsupp.sum_add_index' hzero hadd]

theorem bind_assoc {n : ℕ} {α β γ : Type}
    (μ : Exec n α) (K : α → QMat n → Exec n β)
    (L : β → QMat n → Exec n γ)
    (hLzero : ∀ b, L b 0 = 0)
    (hLadd : ∀ b ρ₁ ρ₂, L b (ρ₁ + ρ₂) = L b ρ₁ + L b ρ₂) :
    bind (bind μ K) L = bind μ fun a ρ => bind (K a ρ) L := by
  simp only [bind]
  rw [Finsupp.sum_sum_index]
  · exact hLzero
  · exact hLadd

theorem bind_pureBranch_of_zero {n : ℕ} {α β : Type}
    (K : α → QMat n → Exec n β)
    (hzero : ∀ a, K a 0 = 0)
    (a : α) (ρ : QMat n) :
    bind (pureBranch a ρ) K = K a ρ := by
  simp [bind, pureBranch, Finsupp.sum_single_index (hzero a)]

@[simp] theorem pureBranch_zero {n : ℕ} {α : Type} (a : α) :
    pureBranch (n := n) a 0 = 0 := by
  simp [pureBranch]

@[simp] theorem pureBranch_add {n : ℕ} {α : Type}
    (a : α) (ρ₁ ρ₂ : QMat n) :
    pureBranch a (ρ₁ + ρ₂) = pureBranch a ρ₁ + pureBranch a ρ₂ := by
  ext b i j
  simp [pureBranch]

@[simp] theorem measBranch_zero {n : ℕ} {α : Type}
    (target : Fin n) (a : α) :
    measBranch target a 0 = 0 := by
  ext b i j
  simp [measBranch]

@[simp] theorem measBranch_add {n : ℕ} {α : Type}
    (target : Fin n) (a : α) (ρ₁ ρ₂ : QMat n) :
    measBranch target a (ρ₁ + ρ₂) =
      measBranch target a ρ₁ + measBranch target a ρ₂ := by
  let Pfalse := QMat.measProjector target false
  let Ptrue := QMat.measProjector target true
  have hfalse : Pfalse * (ρ₁ + ρ₂) * Pfalse =
      Pfalse * ρ₁ * Pfalse + Pfalse * ρ₂ * Pfalse := by
    simp [mul_add, add_mul]
  have htrue : Ptrue * (ρ₁ + ρ₂) * Ptrue =
      Ptrue * ρ₁ * Ptrue + Ptrue * ρ₂ * Ptrue := by
    simp [mul_add, add_mul]
  simp [measBranch, Pfalse, Ptrue, hfalse, htrue, add_assoc, add_left_comm]

/-- Sum the expectation of a postcondition over all finite-support output branches. -/
def expectPost {n : ℕ} {σ α : Type}
    (post : α → σ → QMat n)
    (μ : Exec n (σ × α)) : ℝ :=
  μ.sum fun sa ρ => QMat.expect (post sa.2 sa.1) ρ

@[simp] theorem expectPost_zero {n : ℕ} {σ α : Type}
    (post : α → σ → QMat n) :
    expectPost post (0 : Exec n (σ × α)) = 0 := by
  simp [expectPost]

theorem expectPost_add {n : ℕ} {σ α : Type}
    (post : α → σ → QMat n)
    (μ ν : Exec n (σ × α)) :
    expectPost post (μ + ν) = expectPost post μ + expectPost post ν := by
  classical
  unfold expectPost
  rw [Finsupp.sum_add_index]
  · intro a ha
    simp [QMat.expect]
  · intro a ha ρ₁ ρ₂
    simp [QMat.expect, mul_add, Matrix.trace_add, Complex.add_re]

end Exec

/- Weakest-precondition interface -/

/-- Postcondition shape for fixed-register QProg execution. -/
abbrev qprogPostShape (n : ℕ) (σ : Type) : Std.Do.PostShape :=
  -- our pre and post conditions can depend on both the classical state and the
  -- quantum state.
  .arg σ (.arg (QMat n) .pure)

/--
Support-based WP for aggregated denotations.

This is useful for denotational lemmas, but it is not a lawful `WPMonad`: zero branches are
dropped by `Finsupp.support`, and equal final labels are aggregated by matrix addition.
-/
instance instWPExecM {n : ℕ} {σ : Type} :
    Std.Do.WP (ExecM n σ) (qprogPostShape n σ) where
  wp {α} x :=
    { trans := fun Q s ρ =>
        ⟨Exec.Forall (x s ρ) fun sa ρ' => (Q.1 sa.2 sa.1 ρ').down⟩
      conjunctiveRaw := by
        intro Q₁ Q₂
        apply SPred.bientails.of_eq
        funext s ρ
        simp only [Exec.Forall, Finsupp.mem_support_iff, ne_eq, SPred.and, Prod.forall,
          ULift.up.injEq, eq_iff_iff]
        constructor
        · intro h
          constructor
          · intro s' a hsa
            exact (h s' a hsa).1
          · intro s' a hsa
            exact (h s' a hsa).2
        · intro h s' a hsa
          exact ⟨h.1 s' a hsa, h.2 s' a hsa⟩ }

namespace ExecM

/-- Binding a denotational computation with `pure` is valid even for aggregated executions. -/
@[simp] theorem bind_pure {n : ℕ} {σ α : Type} (x : ExecM n σ α) :
    ExecM.bind x (fun a => ExecM.pure a) = x := by
  funext s ρ
  simp [ExecM.bind, ExecM.pure]

end ExecM

/-! ## Path-preserving symbolic semantics -/

namespace Path

abbrev Event (n : ℕ) := Fin n × Bool
abbrev Trace (n : ℕ) := List (Event n)

/-- A symbolic execution branch. Zero `qstate` branches are deliberately retained. -/
structure Branch (n : ℕ) (σ α : Type) where
  trace : Trace n
  state : σ
  val : α
  qstate : QMat n

/-- Path-preserving symbolic execution. This is a list, not a `Finsupp`, so zero branches remain. -/
abbrev Exec (n : ℕ) (σ α : Type) := List (Branch n σ α)


-- Note: this is close to a finite-support representation, but keeps explicit path
-- information. The path semantics is what makes the `Std.Do` WP instance convenient.

/-- Path-preserving execution monad used by `mvcgen`. -/
abbrev M (n : ℕ) (σ : Type) (α : Type) :=
  σ → QMat n → Exec n σ α

def pure {n : ℕ} {σ α : Type} (a : α) : M n σ α :=
  fun s ρ => [{ trace := [], state := s, val := a, qstate := ρ }]

def bind {n : ℕ} {σ α β : Type}
    (x : M n σ α) (K : α → M n σ β) : M n σ β :=
  fun s ρ =>
    List.flatMap (fun br =>
      (K br.val br.state br.qstate).map fun br' =>
        { trace := br.trace ++ br'.trace,
          state := br'.state,
          val := br'.val,
          qstate := br'.qstate }) (x s ρ)

instance instMonadPathM {n : ℕ} {σ : Type} : Monad (M n σ) where
  pure := pure
  bind := bind
  map f x := bind x fun a => pure (f a)
  seq f x := bind f fun g => bind (x ()) fun a => pure (g a)

instance instLawfulMonadPathM {n : ℕ} {σ : Type} : LawfulMonad (M n σ) := LawfulMonad.mk'
  (bind_pure_comp := by
    intros
    rfl)
  (id_map := by
    intros
    funext s ρ
    simp [Functor.map, bind, pure])
  (pure_bind := by
    intros
    funext s ρ
    simp [Bind.bind, Pure.pure, pure, bind])
  (bind_assoc := by
    intros
    funext s ρ
    simp [Bind.bind, bind, List.flatMap_assoc]
    simp [List.flatMap_map, List.map_map, Function.comp_def, List.append_assoc, List.map_flatMap])

/-- Pathwise assertion over every symbolic branch, including zero-probability branches. -/
def Forall {n : ℕ} {σ α : Type}
    (xs : Exec n σ α) (P : α → σ → QMat n → Prop) : Prop :=
  ∀ br ∈ xs, P br.val br.state br.qstate

@[simp] theorem forall_nil {n : ℕ} {σ α : Type}
    (P : α → σ → QMat n → Prop) :
    Forall ([] : Exec n σ α) P ↔ True := by
  simp [Forall]

@[simp] theorem forall_cons {n : ℕ} {σ α : Type}
    (br : Branch n σ α) (xs : Exec n σ α) (P : α → σ → QMat n → Prop) :
    Forall (br :: xs) P ↔ P br.val br.state br.qstate ∧ Forall xs P := by
  simp [Forall]

@[simp] theorem forall_singleton {n : ℕ} {σ α : Type}
    (br : Branch n σ α) (P : α → σ → QMat n → Prop) :
    Forall ([br] : Exec n σ α) P ↔ P br.val br.state br.qstate := by
  simp [Forall]

@[simp] theorem forall_append {n : ℕ} {σ α : Type}
    (xs ys : Exec n σ α) (P : α → σ → QMat n → Prop) :
    Forall (xs ++ ys) P ↔ Forall xs P ∧ Forall ys P := by
  simp [Forall, or_imp, forall_and]

@[simp] theorem forall_bind {n : ℕ} {σ α β : Type}
    (xs : Exec n σ α) (K : Branch n σ α → Exec n σ β)
    (P : β → σ → QMat n → Prop) :
    Forall (List.flatMap K xs) P ↔ ∀ br ∈ xs, Forall (K br) P := by
  constructor
  · intro h br hbr br' hbr'
    exact h br' (List.mem_flatMap.mpr ⟨br, hbr, hbr'⟩)
  · intro h br' hbr'
    rcases List.mem_flatMap.mp hbr' with ⟨br, hxs, hK⟩
    exact h br hxs br' hK

@[simp] theorem forall_map {n : ℕ} {σ α β : Type}
    (xs : Exec n σ α) (f : Branch n σ α → Branch n σ β)
    (P : β → σ → QMat n → Prop) :
    Forall (xs.map f) P ↔
      ∀ br ∈ xs, P (f br).val (f br).state (f br).qstate := by
  simp [Forall]

noncomputable def denotePrim {n : ℕ} {σ : Type} {α : Type} :
    QProg.Prim σ n α → M n σ α
  | QProg.Prim.applyUnitary U _hU =>
      fun s ρ =>
        [{ trace := [],
           state := s,
           val := (),
           qstate := QProg.Exec.evolve U ρ }]
  | QProg.Prim.applyClassical f =>
      fun s ρ =>
        [{ trace := [],
           state := f s,
           val := (),
           qstate := ρ }]
  | QProg.Prim.readClassical =>
      fun s ρ =>
        [{ trace := [],
           state := s,
           val := s,
           qstate := ρ }]
  | QProg.Prim.meas target =>
      fun s ρ =>
        let Pfalse := QMat.measProjector target false
        let Ptrue := QMat.measProjector target true
        ({ trace := [(target, false)],
           state := s,
           val := false,
           qstate := Pfalse * ρ * Pfalse } : Branch n σ Bool) ::
        [({ trace := [(target, true)],
            state := s,
            val := true,
            qstate := Ptrue * ρ * Ptrue } : Branch n σ Bool)]

noncomputable def denote {n : ℕ} {σ α : Type} :
    QProg σ n α → M n σ α :=
  Cslib.FreeM.liftM (fun {ι} (op : QProg.Prim σ n ι) => denotePrim op)


instance instWPPathM {n : ℕ} {σ : Type} :
    Std.Do.WP (M n σ) (qprogPostShape n σ) where
  wp {α} x :=
    { trans := fun Q s ρ =>
        ⟨Forall (x s ρ) fun a s' ρ' => (Q.1 a s' ρ').down⟩
      conjunctiveRaw := by
        intro Q₁ Q₂
        apply SPred.bientails.of_eq
        funext s ρ
        simp only [Forall, SPred.and, ULift.up.injEq, eq_iff_iff]
        constructor
        · intro h
          constructor
          · intro br hbr
            exact (h br hbr).1
          · intro br hbr
            exact (h br hbr).2
        · intro h br hbr
          exact ⟨h.1 br hbr, h.2 br hbr⟩ }

instance instWPMonadPathM {n : ℕ} {σ : Type} :
    Std.Do.WPMonad (M n σ) (qprogPostShape n σ) where
  wp_pure := by
    intros
    apply Std.Do.PredTrans.ext
    intro Q
    funext s ρ
    simp [Std.Do.WP.wp, Std.Do.PredTrans.apply, Pure.pure, pure, Forall,
      Std.Do.PredTrans.pure]
  wp_bind := by
    intros
    apply Std.Do.PredTrans.ext
    intro Q
    funext s ρ
    simp only [wp, PredTrans.apply, Forall, Bind.bind, bind, List.mem_flatMap,
      List.mem_map, forall_exists_index, and_imp, PredTrans.bind, ULift.up.injEq, eq_iff_iff]
    constructor
    · intro h br hbr br' hbr'
      simpa using h
        { trace := br.trace ++ br'.trace
          state := br'.state
          val := br'.val
          qstate := br'.qstate }
        br hbr br' hbr' rfl
    · intro h br br₀ hbr₀ br₁ hbr₁ hEq
      subst hEq
      exact h br₀ hbr₀ br₁ hbr₁

namespace Branch

def toExec {n : ℕ} {σ α : Type}
    (br : Branch n σ α) : QProg.Exec n (σ × α) :=
  Finsupp.single (br.state, br.val) br.qstate

end Branch

namespace Exec

def toAggregated {n : ℕ} {σ α : Type}
    (xs : Exec n σ α) : QProg.Exec n (σ × α) :=
  xs.foldr (fun br acc => br.toExec + acc) 0

@[simp] theorem toAggregated_nil {n : ℕ} {σ α : Type} :
    toAggregated ([] : Exec n σ α) = 0 :=
  rfl

@[simp] theorem toAggregated_cons {n : ℕ} {σ α : Type}
    (br : Branch n σ α) (xs : Exec n σ α) :
    toAggregated (br :: xs) = br.toExec + xs.toAggregated :=
  rfl

@[simp] theorem toAggregated_append {n : ℕ} {σ α : Type}
    (xs ys : Exec n σ α) :
    toAggregated (xs ++ ys) = xs.toAggregated + ys.toAggregated := by
  induction xs with
  | nil =>
      simp
  | cons br xs ih =>
      simp [ih, add_assoc]

/-- Aggregation forgets symbolic traces. -/
@[simp] theorem toAggregated_map_trace {n : ℕ} {σ α : Type}
    (xs : Exec n σ α) (pref : Trace n) :
    toAggregated
        (xs.map fun br =>
          { trace := pref ++ br.trace
            state := br.state
            val := br.val
            qstate := br.qstate }) =
      xs.toAggregated := by
  induction xs with
  | nil =>
      simp
  | cons br xs ih =>
      simp [ih, Branch.toExec]

theorem toAggregated_pathBind {n : ℕ} {σ α β : Type}
    (xs : Exec n σ α)
    (Kp : α → σ → QMat n → Exec n σ β)
    (Ke : α → σ → QMat n → QProg.Exec n (σ × β))
    (hK : ∀ a s ρ, (Kp a s ρ).toAggregated = Ke a s ρ)
    (hzero : ∀ a s, Ke a s 0 = 0)
    (hadd : ∀ a s ρ₁ ρ₂, Ke a s (ρ₁ + ρ₂) = Ke a s ρ₁ + Ke a s ρ₂) :
    toAggregated
        (List.flatMap
          (fun br =>
            (Kp br.val br.state br.qstate).map fun br' =>
              { trace := br.trace ++ br'.trace
                state := br'.state
                val := br'.val
                qstate := br'.qstate })
          xs) =
      QProg.Exec.bind xs.toAggregated fun sa ρ => Ke sa.2 sa.1 ρ := by
  classical
  induction xs with
  | nil =>
      simp [QProg.Exec.bind]
  | cons br xs ih =>
      simp only [List.flatMap_cons, toAggregated_append, toAggregated_cons]
      rw [toAggregated_map_trace, hK, ih]
      rw [QProg.Exec.bind_add]
      · have hsingle :
            QProg.Exec.bind br.toExec (fun sa ρ => Ke sa.2 sa.1 ρ) =
              Ke br.val br.state br.qstate := by
          simpa [Branch.toExec, QProg.Exec.pureBranch] using
            (QProg.Exec.bind_pureBranch_of_zero
              (K := fun sa ρ => Ke sa.2 sa.1 ρ)
              (fun sa => hzero sa.2 sa.1)
              (a := (br.state, br.val)) (ρ := br.qstate))
        rw [hsingle]
      · intro sa
        exact hzero sa.2 sa.1
      · intro sa ρ₁ ρ₂
        exact hadd sa.2 sa.1 ρ₁ ρ₂

end Exec

end Path

instance instWPQProg {n : ℕ} {σ : Type} :
    Std.Do.WP (QProg σ n) (qprogPostShape n σ) where
  wp prog := Std.Do.WP.wp (Path.denote prog)

instance instWPMonadQProg {n : ℕ} {σ : Type} :
    Std.Do.WPMonad (QProg σ n) (qprogPostShape n σ) where
  wp_pure := by
    intro α a
    simpa [Std.Do.WP.wp, Path.denote] using
      (Std.Do.WPMonad.wp_pure (m := Path.M n σ) (ps := qprogPostShape n σ) a)
  wp_bind := by
    intro α β x f
    simpa [Std.Do.WP.wp, Path.denote] using
      (Std.Do.WPMonad.wp_bind (m := Path.M n σ) (ps := qprogPostShape n σ)
        (Path.denote x) (fun a => Path.denote (f a)))

@[simp] theorem denote_pure {n : ℕ} {σ α : Type} (a : α) :
    denote (Pure.pure a : QProg σ n α) = ExecM.pure a :=
  rfl

/- ## Denotation lemmas for primitive smart constructors -/

@[simp] theorem denote_applyUnitary {σ : Type} {n : ℕ}
    (U : QMat n) (hU : U.Unitary) :
    denote (applyUnitary (σ := σ) U hU) =
      denotePrim (QProg.Prim.applyUnitary (σ := σ) (n := n) U hU) := by
  simp only [denote, applyUnitary, Cslib.FreeM.lift_def, Cslib.FreeM.liftM_liftBind,
    Cslib.FreeM.liftM_pure]
  exact ExecM.bind_pure
    (denotePrim (QProg.Prim.applyUnitary (σ := σ) (n := n) U hU))

@[simp] theorem denote_applyClassical {σ : Type} {n : ℕ}
    (f : σ → σ) :
    denote (applyClassical (σ := σ) (n := n) f) =
      denotePrim (QProg.Prim.applyClassical (σ := σ) (n := n) f) := by
  simp only [denote, applyClassical, Cslib.FreeM.lift_def, Cslib.FreeM.liftM_liftBind,
    Cslib.FreeM.liftM_pure]
  exact ExecM.bind_pure
    (denotePrim (QProg.Prim.applyClassical (σ := σ) (n := n) f))

@[simp] theorem denote_readClassical {σ : Type} {n : ℕ} :
    denote (readClassical (σ := σ) (n := n)) =
      denotePrim (QProg.Prim.readClassical (σ := σ) (n := n)) := by
  simp only [denote, readClassical, Cslib.FreeM.lift_def, Cslib.FreeM.liftM_liftBind,
    Cslib.FreeM.liftM_pure]
  exact ExecM.bind_pure
    (denotePrim (QProg.Prim.readClassical (σ := σ) (n := n)))

@[simp] theorem denote_meas {σ : Type} {n : ℕ}
    (target : Fin n) :
    denote (meas (σ := σ) target) =
      denotePrim (QProg.Prim.meas (σ := σ) (n := n) target) := by
  simp only [denote, meas, Cslib.FreeM.lift_def, Cslib.FreeM.liftM_liftBind,
    Cslib.FreeM.liftM_pure]
  exact ExecM.bind_pure
    (denotePrim (QProg.Prim.meas (σ := σ) (n := n) target))

/- Primitive `mvcgen` specifications -/

@[simp] theorem wp_applyUnitary {n : ℕ} {σ : Type}
    (U : QMat n) (hU : U.Unitary)
    (Q : Std.Do.PostCond Unit (qprogPostShape n σ)) :
    wp⟦QProg.applyUnitary (σ := σ) U hU⟧ Q =
      fun s ρ => Q.1 () s (Exec.evolve U ρ) := by
  funext s ρ
  simp [Std.Do.WP.wp, Std.Do.PredTrans.apply, Path.denote, applyUnitary,
    Path.denotePrim, Path.Forall]

@[simp] theorem wp_applyClassical {n : ℕ} {σ : Type}
    (f : σ → σ)
    (Q : Std.Do.PostCond Unit (qprogPostShape n σ)) :
    wp⟦QProg.applyClassical (σ := σ) (n := n) f⟧ Q =
      fun s ρ => Q.1 () (f s) ρ := by
  funext s ρ
  simp [Std.Do.WP.wp, Std.Do.PredTrans.apply, Path.denote, applyClassical,
    Path.denotePrim, Path.Forall]

@[simp] theorem wp_applyClassical_bind_pure {n : ℕ} {σ β : Type}
    (f : σ → σ) (b : β)
    (Q : Std.Do.PostCond β (qprogPostShape n σ)) :
    wp⟦(Cslib.FreeM.bind (QProg.applyClassical (σ := σ) (n := n) f)
        fun _ => Cslib.FreeM.pure b : QProg σ n β)⟧ Q =
      fun s ρ => Q.1 b (f s) ρ := by
  funext s ρ
  simp [Std.Do.WP.wp, Std.Do.PredTrans.apply, Path.denote, QProg.applyClassical,
    Path.denotePrim, Functor.map, Path.bind, Path.pure, Path.Forall]

@[simp] theorem wp_readClassical {n : ℕ} {σ : Type}
    (Q : Std.Do.PostCond σ (qprogPostShape n σ)) :
    wp⟦QProg.readClassical (σ := σ) (n := n)⟧ Q =
      fun s ρ => Q.1 s s ρ := by
  funext s ρ
  simp [Std.Do.WP.wp, Std.Do.PredTrans.apply, Path.denote, readClassical,
    Path.denotePrim, Path.Forall]

@[simp] theorem wp_meas {n : ℕ} {σ : Type}
    (target : Fin n)
    (Q : Std.Do.PostCond Bool (qprogPostShape n σ)) :
    wp⟦QProg.meas (σ := σ) target⟧ Q =
      fun s ρ =>
        SPred.and
          (Q.1 false s
            (QMat.measProjector target false * ρ * QMat.measProjector target false))
          (Q.1 true s
            (QMat.measProjector target true * ρ * QMat.measProjector target true)) := by
  funext s ρ
  simp [Std.Do.WP.wp, Std.Do.PredTrans.apply, Path.denote, meas, Path.denotePrim,
    Path.Forall, SPred.and]

@[spec] theorem applyUnitary_spec
    {n : ℕ} {σ : Type}
    (U : QMat n) (hU : U.Unitary)
    (Q : Std.Do.PostCond Unit (qprogPostShape n σ)) :
    ⦃ fun s ρ => Q.1 () s (Exec.evolve U ρ) ⦄
      QProg.applyUnitary (σ := σ) U hU
    ⦃ Q ⦄ := by
  simp [Std.Do.Triple]


@[spec] theorem applyClassical_spec
    {n : ℕ} {σ : Type}
    (f : σ → σ)
    (Q : Std.Do.PostCond Unit (qprogPostShape n σ)) :
    ⦃ fun s ρ => Q.1 () (f s) ρ ⦄
      QProg.applyClassical (σ := σ) (n := n) f
    ⦃ Q ⦄ := by
  simp [Std.Do.Triple]

@[spec] theorem readClassical_spec
    {n : ℕ} {σ : Type}
    (Q : Std.Do.PostCond σ (qprogPostShape n σ)) :
    ⦃ fun s ρ => Q.1 s s ρ ⦄
      QProg.readClassical (σ := σ) (n := n)
    ⦃ Q ⦄ := by
  simp [Std.Do.Triple]

@[spec] theorem meas_spec
    {n : ℕ} {σ : Type}
    (target : Fin n)
    (Q : Std.Do.PostCond Bool (qprogPostShape n σ)) :
    ⦃ fun s ρ =>
        SPred.and
          (Q.1 false s
            (QMat.measProjector target false * ρ * QMat.measProjector target false))
          (Q.1 true s
            (QMat.measProjector target true * ρ * QMat.measProjector target true)) ⦄
      QProg.meas (σ := σ) target
    ⦃ Q ⦄ := by
  simp [Std.Do.Triple]

/- Path aggregation bridge -/

namespace Path

/-- Aggregating the path semantics of one primitive recovers the denotational primitive. -/
@[simp] theorem denotePrim_toAggregated {n : ℕ} {σ α : Type}
    (op : QProg.Prim σ n α) (s : σ) (ρ : QMat n) :
    (denotePrim op s ρ).toAggregated = QProg.denotePrim op s ρ := by
  cases op with
  | applyUnitary U hU =>
      simp [denotePrim, QProg.denotePrim, Exec.toAggregated, Branch.toExec,
        QProg.Exec.pureBranch]
  | applyClassical f =>
      simp [denotePrim, QProg.denotePrim, Exec.toAggregated, Branch.toExec,
        QProg.Exec.pureBranch]
  | readClassical =>
      simp [denotePrim, QProg.denotePrim, Exec.toAggregated, Branch.toExec,
        QProg.Exec.pureBranch]
  | meas target =>
      simp [denotePrim, QProg.denotePrim, Exec.toAggregated, Branch.toExec,
        QProg.Exec.measBranch]

end Path

@[simp] theorem denotePrim_zero {n : ℕ} {σ α : Type}
    (op : QProg.Prim σ n α) (s : σ) :
    QProg.denotePrim op s 0 = 0 := by
  cases op with
  | applyUnitary U hU =>
      simp [QProg.denotePrim, Exec.pureBranch, Exec.evolve, QMat.evolve]
  | applyClassical f =>
      simp [QProg.denotePrim, Exec.pureBranch]
  | readClassical =>
      simp [QProg.denotePrim, Exec.pureBranch]
  | meas target =>
      simp [QProg.denotePrim]

@[simp] theorem denotePrim_add {n : ℕ} {σ α : Type}
    (op : QProg.Prim σ n α) (s : σ) (ρ₁ ρ₂ : QMat n) :
    QProg.denotePrim op s (ρ₁ + ρ₂) =
      QProg.denotePrim op s ρ₁ + QProg.denotePrim op s ρ₂ := by
  cases op with
  | applyUnitary U hU =>
      simp [QProg.denotePrim, Exec.pureBranch, Exec.evolve, QMat.evolve, mul_add, add_mul]
  | applyClassical f =>
      simp [QProg.denotePrim]
  | readClassical =>
      simp [QProg.denotePrim]
  | meas target =>
      simp [QProg.denotePrim]

@[simp] theorem denote_zero {n : ℕ} {σ α : Type}
    (prog : QProg σ n α) (s : σ) :
    QProg.denote prog s 0 = 0 := by
  induction prog generalizing s with
  | pure a =>
      change Exec.pureBranch (s, a) (0 : QMat n) = 0
      simp
  | liftBind op cont ih =>
      change ExecM.bind (QProg.denotePrim op) (fun a => QProg.denote (cont a)) s 0 = 0
      simp [ExecM.bind]

@[simp] theorem denote_add {n : ℕ} {σ α : Type}
    (prog : QProg σ n α) (s : σ) (ρ₁ ρ₂ : QMat n) :
    QProg.denote prog s (ρ₁ + ρ₂) =
      QProg.denote prog s ρ₁ + QProg.denote prog s ρ₂ := by
  induction prog generalizing s ρ₁ ρ₂ with
  | pure a =>
      change Exec.pureBranch (s, a) (ρ₁ + ρ₂) =
        Exec.pureBranch (s, a) ρ₁ + Exec.pureBranch (s, a) ρ₂
      simp
  | liftBind op cont ih =>
      simp only [QProg.denote, Cslib.FreeM.liftM_liftBind]
      change
        ExecM.bind (QProg.denotePrim op) (fun a => QProg.denote (cont a)) s (ρ₁ + ρ₂) =
          ExecM.bind (QProg.denotePrim op) (fun a => QProg.denote (cont a)) s ρ₁ +
          ExecM.bind (QProg.denotePrim op) (fun a => QProg.denote (cont a)) s ρ₂
      simp only [ExecM.bind]
      rw [denotePrim_add]
      rw [Exec.bind_add]
      · intro sa
        exact denote_zero (cont sa.2) sa.1
      · intro sa ρ₁ ρ₂
        exact ih sa.2 sa.1 ρ₁ ρ₂

@[simp] theorem denote_bind {n : ℕ} {σ α β : Type}
    (prog : QProg σ n α) (cont : α → QProg σ n β) :
    QProg.denote (prog >>= cont) =
      ExecM.bind (QProg.denote prog) fun a => QProg.denote (cont a) := by
  funext s ρ
  induction prog generalizing s ρ with
  | pure a =>
      change QProg.denote (cont a) s ρ =
        Exec.bind (Exec.pureBranch (s, a) ρ)
          (fun sa ρ' => QProg.denote (cont sa.2) sa.1 ρ')
      rw [Exec.bind_pureBranch_of_zero]
      intro sa
      exact denote_zero (cont sa.2) sa.1
  | liftBind op k ih =>
      change QProg.denote (Cslib.FreeM.liftBind op (fun a => k a >>= cont)) s ρ =
        ExecM.bind (QProg.denote (Cslib.FreeM.liftBind op k)) (fun a => QProg.denote (cont a)) s ρ
      simp only [QProg.denote, Cslib.FreeM.liftM_liftBind]
      change
        ExecM.bind (QProg.denotePrim op) (fun a => QProg.denote (k a >>= cont)) s ρ =
          ExecM.bind (ExecM.bind (QProg.denotePrim op) (fun a => QProg.denote (k a)))
            (fun a => QProg.denote (cont a)) s ρ
      have hcont :
          (fun a => QProg.denote (k a >>= cont)) =
            (fun a => ExecM.bind (QProg.denote (k a)) (fun b => QProg.denote (cont b))) := by
        funext a
        funext s ρ
        exact ih a s ρ
      rw [hcont]
      change
        ExecM.bind (QProg.denotePrim op)
            (fun a => ExecM.bind (QProg.denote (k a)) (fun b => QProg.denote (cont b))) s ρ =
          ExecM.bind (ExecM.bind (QProg.denotePrim op) (fun a => QProg.denote (k a)))
            (fun a => QProg.denote (cont a)) s ρ
      simp only [ExecM.bind]
      rw [← Exec.bind_assoc]
      · intro sa
        exact denote_zero (cont sa.2) sa.1
      · intro sa ρ₁ ρ₂
        exact denote_add (cont sa.2) sa.1 ρ₁ ρ₂

@[simp] theorem denote_applyUnitary_bind {n : ℕ} {σ α : Type}
    (U : QMat n) (hU : U.Unitary) (cont : Unit → QProg σ n α)
    (s : σ) (ρ : QMat n) :
    QProg.denote (QProg.applyUnitary (σ := σ) U hU >>= cont) s ρ =
      QProg.denote (cont ()) s (Exec.evolve U ρ) := by
  rw [denote_bind]
  change
    Exec.bind (QProg.denote (QProg.applyUnitary (σ := σ) U hU) s ρ)
        (fun sa ρ' => QProg.denote (cont sa.2) sa.1 ρ') =
      QProg.denote (cont ()) s (Exec.evolve U ρ)
  simp only [denote_applyUnitary, denotePrim, Exec.pureBranch]
  unfold Exec.bind
  rw [Finsupp.sum_single_index]
  · exact denote_zero (cont ()) s

@[simp] theorem denote_meas_bind {n : ℕ} {σ α : Type}
    (target : Fin n) (cont : Bool → QProg σ n α)
    (s : σ) (ρ : QMat n) :
    QProg.denote (QProg.meas target >>= cont) s ρ =
      QProg.denote (cont false) s
        (QMat.measProjector target false * ρ * QMat.measProjector target false) +
      QProg.denote (cont true) s
        (QMat.measProjector target true * ρ * QMat.measProjector target true) := by
  classical
  let ρ0 := QMat.measProjector target false * ρ * QMat.measProjector target false
  let ρ1 := QMat.measProjector target true * ρ * QMat.measProjector target true
  rw [denote_bind]
  change
    Exec.bind (QProg.denote (QProg.meas target) s ρ)
        (fun sa ρ' => QProg.denote (cont sa.2) sa.1 ρ') =
      QProg.denote (cont false) s ρ0 + QProg.denote (cont true) s ρ1
  simp only [denote_meas, denotePrim, Exec.measBranch]
  unfold Exec.bind
  change
    (Finsupp.single (s, false) ρ0 + Finsupp.single (s, true) ρ1).sum
        (fun sa ρ' => QProg.denote (cont sa.2) sa.1 ρ') =
      QProg.denote (cont false) s ρ0 + QProg.denote (cont true) s ρ1
  rw [Finsupp.sum_add_index]
  · rw [Finsupp.sum_single_index]
    · rw [Finsupp.sum_single_index]
      · exact denote_zero (cont true) s
    · exact denote_zero (cont false) s
  · intro a ha
    exact denote_zero (cont a.2) a.1
  · intro a ha ρ₁ ρ₂
    exact denote_add (cont a.2) a.1 ρ₁ ρ₂

/-- Aggregating path-preserving program semantics recovers the denotational semantics. -/
theorem denotePath_toAggregated_eq_denote
    {n : ℕ} {σ α : Type}
    (prog : QProg σ n α) (s : σ) (ρ : QMat n) :
    (Path.denote prog s ρ).toAggregated = QProg.denote prog s ρ := by
  induction prog generalizing s ρ with
  | pure a =>
      change Path.Exec.toAggregated
          ([{ trace := [], state := s, val := a, qstate := ρ }] : Path.Exec n σ α) =
        Exec.pureBranch (s, a) ρ
      simp [Path.Exec.toAggregated, Path.Branch.toExec, Exec.pureBranch]
  | liftBind op cont ih =>
      simp only [Path.denote, QProg.denote, Cslib.FreeM.liftM_liftBind]
      change
        (Path.bind (Path.denotePrim op) (fun a => Path.denote (cont a)) s ρ).toAggregated =
          ExecM.bind (QProg.denotePrim op) (fun a => QProg.denote (cont a)) s ρ
      simp only [Path.bind, ExecM.bind]
      rw [Path.Exec.toAggregated_pathBind
        (Kp := fun a s ρ => Path.denote (cont a) s ρ)
        (Ke := fun a s ρ => QProg.denote (cont a) s ρ)]
      · simp
      · intro a s ρ
        exact ih a s ρ
      · intro a s
        exact denote_zero (cont a) s
      · intro a s ρ₁ ρ₂
        exact denote_add (cont a) s ρ₁ ρ₂


namespace Path

/-- A postcondition accepts zero-probability aggregated branches. -/
def ZeroClosed {n : ℕ} {σ α : Type}
    (P : α → σ → QMat n → Prop) : Prop :=
  ∀ a s, P a s 0

/-- A postcondition is closed under adding subnormalised matrices for the same final label. -/
def AddClosed {n : ℕ} {σ α : Type}
    (P : α → σ → QMat n → Prop) : Prop :=
  ∀ a s ρ₁ ρ₂,
    P a s ρ₁ → P a s ρ₂ → P a s (ρ₁ + ρ₂)

theorem forall_toAggregated
    {n : ℕ} {σ α : Type}
    {P : α → σ → QMat n → Prop}
    (hzero : ZeroClosed P)
    (hadd : AddClosed P)
    {xs : Path.Exec n σ α}
    (h : Path.Forall xs P) :
    QProg.Exec.Forall xs.toAggregated
      (fun sa ρ => P sa.2 sa.1 ρ) := by
  classical
  induction xs with
  | nil =>
      simp [Path.Exec.toAggregated, QProg.Exec.Forall]
  | cons br xs ih =>
      rw [Path.forall_cons] at h
      have hbr : P br.val br.state br.qstate := h.1
      have hxs : Path.Forall xs P := h.2
      have ihxs := ih hxs
      intro sa hsa
      let acc := Path.Exec.toAggregated xs
      have hhead : P sa.2 sa.1 (br.toExec sa) := by
        by_cases hsame : sa = (br.state, br.val)
        · subst sa
          simpa [Path.Branch.toExec]
        · have hzeroHead : br.toExec sa = 0 := by
            simp [Path.Branch.toExec, hsame]
          simpa [hzeroHead] using hzero sa.2 sa.1
      have htail : P sa.2 sa.1 (acc sa) := by
        by_cases hacc : acc sa = 0
        · simpa [hacc] using hzero sa.2 sa.1
        · exact ihxs sa (by
            rw [Finsupp.mem_support_iff]
            exact hacc)
      simpa [Path.Exec.toAggregated, acc, Pi.add_apply] using
        hadd sa.2 sa.1 (br.toExec sa) (acc sa) hhead htail

end Path

/- Expectation-style quantum Hoare logic -/

namespace QHoare

/-- Denotational expectation transformer for total fixed-register QProg programs. -/
def wpTotal {n : ℕ} {σ α : Type}
    (prog : QProg σ n α)
    (post : α → σ → QMat n)
    (s : σ) (ρ : QMat n) : ℝ :=
  Exec.expectPost post (denote prog s ρ)

/--
A physical subnormalised fixed-register quantum state: positive semidefinite with trace at most
one.  Subnormalisation is intentional because measurement branches store their probability in the
density matrix itself.
-/
def Substate {n : ℕ} (ρ : QMat n) : Prop :=
  ρ.PosSemidef ∧ (QMat.trace ρ).re ≤ 1

/-- Physical total correctness over positive semidefinite subnormalised quantum states. -/
def PhysicalTotal {n : ℕ} {σ α : Type}
    (pre : σ → QMat n)
    (prog : QProg σ n α)
    (post : α → σ → QMat n) : Prop :=
  ∀ s ρ, Substate ρ → QMat.expect (pre s) ρ ≤ wpTotal prog post s ρ

/-- Saturated physical total correctness over subnormalised quantum states. -/
def SaturatedPhysicalTotal {n : ℕ} {σ α : Type}
    (pre : σ → QMat n)
    (prog : QProg σ n α)
    (post : α → σ → QMat n) : Prop :=
  ∀ s ρ, Substate ρ → QMat.expect (pre s) ρ = wpTotal prog post s ρ

notation "⦃ᵩ " P " ⦄ " prog " ⦃ᵩ " Q " ⦄" =>
  QProg.QHoare.PhysicalTotal P prog Q

@[simp] theorem wpTotal_pure {n : ℕ} {σ α : Type}
    (a : α) (post : α → σ → QMat n) (s : σ) (ρ : QMat n) :
    wpTotal (Pure.pure a : QProg σ n α) post s ρ =
      QMat.expect (post a s) ρ := by
  change ((Finsupp.single (s, a) ρ).sum fun sa ρ => QMat.expect (post sa.2 sa.1) ρ) =
    QMat.expect (post a s) ρ
  rw [Finsupp.sum_single_index]
  simp [QMat.expect]

@[simp] theorem wpTotal_applyUnitary {n : ℕ} {σ : Type}
    (U : QMat n) (hU : U.Unitary)
    (post : Unit → σ → QMat n) (s : σ) (ρ : QMat n) :
    wpTotal (QProg.applyUnitary (σ := σ) U hU) post s ρ =
      QMat.expect (post () s) (Exec.evolve U ρ) := by
  simp [wpTotal, Exec.expectPost, denotePrim, Exec.pureBranch, QMat.expect]

@[simp] theorem wpTotal_applyClassical {n : ℕ} {σ : Type}
    (f : σ → σ)
    (post : Unit → σ → QMat n) (s : σ) (ρ : QMat n) :
    wpTotal (QProg.applyClassical (σ := σ) (n := n) f) post s ρ =
      QMat.expect (post () (f s)) ρ := by
  simp [wpTotal, Exec.expectPost, denotePrim, Exec.pureBranch, QMat.expect]

@[simp] theorem wpTotal_readClassical {n : ℕ} {σ : Type}
    (post : σ → σ → QMat n) (s : σ) (ρ : QMat n) :
    wpTotal (QProg.readClassical (σ := σ) (n := n)) post s ρ =
      QMat.expect (post s s) ρ := by
  simp [wpTotal, Exec.expectPost, denotePrim, Exec.pureBranch, QMat.expect]

@[simp] theorem wpTotal_meas
    {n : ℕ} {σ : Type} (target : Fin n)
    (post : Bool → σ → QMat n) (s : σ) (ρ : QMat n) :
    wpTotal (QProg.meas (σ := σ) target) post s ρ
      =
    QMat.expect (post false s)
      (QMat.measProjector target false * ρ * QMat.measProjector target false)
    +
    QMat.expect (post true s)
      (QMat.measProjector target true * ρ * QMat.measProjector target true) := by
  classical
  let ρ0 := QMat.measProjector target false * ρ * QMat.measProjector target false
  let ρ1 := QMat.measProjector target true * ρ * QMat.measProjector target true
  simp only [wpTotal, Exec.expectPost, denote_meas, denotePrim]
  unfold Exec.measBranch
  change ((Finsupp.single (s, false) ρ0 + Finsupp.single (s, true) ρ1).sum
      fun sa ρ => QMat.expect (post sa.2 sa.1) ρ) =
    QMat.expect (post false s) ρ0 + QMat.expect (post true s) ρ1
  rw [Finsupp.sum_add_index]
  · rw [Finsupp.sum_single_index, Finsupp.sum_single_index]
    all_goals simp [QMat.expect]
  · intro a ha
    simp [QMat.expect]
  · intro a ha b1 b2
    simp [QMat.expect, mul_add]

@[simp] theorem wpTotal_applyUnitary_bind {n : ℕ} {σ α : Type}
    (U : QMat n) (hU : U.Unitary) (cont : Unit → QProg σ n α)
    (post : α → σ → QMat n) (s : σ) (ρ : QMat n) :
    wpTotal (QProg.applyUnitary (σ := σ) U hU >>= cont) post s ρ =
      wpTotal (cont ()) post s (Exec.evolve U ρ) := by
  unfold wpTotal
  rw [denote_applyUnitary_bind]

@[simp] theorem wpTotal_meas_bind {n : ℕ} {σ α : Type}
    (target : Fin n) (cont : Bool → QProg σ n α)
    (post : α → σ → QMat n) (s : σ) (ρ : QMat n) :
    wpTotal (QProg.meas (σ := σ) target >>= cont) post s ρ =
      wpTotal (cont false) post s
        (QMat.measProjector target false * ρ * QMat.measProjector target false) +
      wpTotal (cont true) post s
        (QMat.measProjector target true * ρ * QMat.measProjector target true) := by
  unfold wpTotal
  rw [denote_meas_bind, Exec.expectPost_add]

theorem physicalTotal_of_wp_le {n : ℕ} {σ α : Type}
    {pre : σ → QMat n} {prog : QProg σ n α} {post : α → σ → QMat n}
    (h : ∀ s ρ, Substate ρ → QMat.expect (pre s) ρ ≤ wpTotal prog post s ρ) :
    PhysicalTotal pre prog post := h

theorem saturatedPhysicalTotal_of_wp_eq {n : ℕ} {σ α : Type}
    {pre : σ → QMat n} {prog : QProg σ n α} {post : α → σ → QMat n}
    (h : ∀ s ρ, Substate ρ → QMat.expect (pre s) ρ = wpTotal prog post s ρ) :
    SaturatedPhysicalTotal pre prog post := h

theorem physicalTotal_applyUnitary {n : ℕ} {σ : Type}
    {pre : σ → QMat n} {post : Unit → σ → QMat n}
    (U : QMat n) (hU : U.Unitary)
    (h : ∀ s ρ, Substate ρ →
      QMat.expect (pre s) ρ ≤
      QMat.expect (post () s) (Exec.evolve U ρ)) :
    PhysicalTotal pre (QProg.applyUnitary (σ := σ) U hU) post := by
  simpa [PhysicalTotal] using h

theorem physicalTotal_applyClassical {n : ℕ} {σ : Type}
    {pre : σ → QMat n} {post : Unit → σ → QMat n}
    (f : σ → σ)
    (h : ∀ s ρ, Substate ρ →
      QMat.expect (pre s) ρ ≤
      QMat.expect (post () (f s)) ρ) :
    PhysicalTotal pre (QProg.applyClassical (σ := σ) (n := n) f) post := by
  simpa [PhysicalTotal] using h

theorem physicalTotal_readClassical {n : ℕ} {σ : Type}
    {pre : σ → QMat n} {post : σ → σ → QMat n}
    (h : ∀ s ρ, Substate ρ →
      QMat.expect (pre s) ρ ≤
      QMat.expect (post s s) ρ) :
    PhysicalTotal pre (QProg.readClassical (σ := σ) (n := n)) post := by
  simpa [PhysicalTotal] using h

theorem physicalTotal_meas {n : ℕ} {σ : Type}
    {pre : σ → QMat n} {post : Bool → σ → QMat n}
    (target : Fin n)
    (h : ∀ s ρ, Substate ρ →
      QMat.expect (pre s) ρ ≤
        QMat.expect (post false s)
          (QMat.measProjector target false * ρ * QMat.measProjector target false)
        +
        QMat.expect (post true s)
          (QMat.measProjector target true * ρ * QMat.measProjector target true)) :
    PhysicalTotal pre (QProg.meas (σ := σ) target) post := by
  simpa [PhysicalTotal] using h

end QHoare

end QProg

end

end QLean
