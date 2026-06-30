/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
import Mathlib.Data.Matrix.Reflection
import Mathlib.Tactic

/-!
# Matrix Computation Simprocs

This file contains a few simprocs. These are experimental and probably should be improved.
The goal is to PR them at some point.
-/

namespace QLean

open scoped Matrix ComplexOrder BigOperators
open Lean Meta Qq

namespace MatrixCompute

private def mkFinQ (i n : Q(ℕ)) : MetaM Q(Fin $n) := do
  return q(⟨$i, $(← mkDecideProofQ q($i < $n))⟩)

private def whnfDQ {u} {α : Q(Type u)} (e : Q($α)) : MetaM Q($α) := do
  let e' ← Meta.whnfD e
  let some eQ ← checkTypeQ e' q($α) | throwError "bad reduced expression"
  return eQ

private partial def reduceMatrixEntry {u} {α : Q(Type u)} (e : Q($α)) : MetaM Q($α) := do
  match_expr e with
  | Matrix.conjTranspose _ _ _ instStar A i j =>
      let some instStarQ ← checkTypeQ instStar q(Star $α) | throwError "bad Star instance"
      let entryExpr := mkAppN A #[j, i]
      let some entry ← checkTypeQ entryExpr q($α) | throwError "bad conjugate-transpose entry"
      let entry ← reduceMatrixEntry entry
      whnfDQ q(letI : Star $α := $instStarQ; star $entry)
  | _ => whnfDQ e

private def withMatrixType {ρ : Type} (type : Expr)
    (k : {uRows uCols uElem : Level} →
      Q(Type uRows) → Q(Type uCols) → Q(Type uElem) → MetaM ρ) :
    MetaM (Option ρ) := do
  let type ← instantiateMVars type
  let (fn, args) := type.getAppFnArgs
  if fn == ``Matrix && args.size == 3 then
    let ⟨_uRows, rows⟩ ← getLevelQ' args[0]!
    let ⟨_uCols, cols⟩ ← getLevelQ' args[1]!
    let ⟨_uElem, elem⟩ ← getLevelQ' args[2]!
    return some (← k rows cols elem)
  forallTelescopeReducing type fun xs body => do
    unless xs.size == 2 do return none
    let rowsType ← inferType xs[0]!
    let colsType ← inferType xs[1]!
    let ⟨_uRows, rows⟩ ← getLevelQ' rowsType
    let ⟨_uCols, cols⟩ ← getLevelQ' colsType
    let ⟨_uElem, elem⟩ ← getLevelQ' body
    return some (← k rows cols elem)

/--
Compute a concrete `Fin`-indexed matrix-vector product.

This rewrites `A *ᵥ v` to the eta-expanded literal produced by `Matrix.mulVecᵣ`.
Use it with `simp only [matrixVecMul, matrixVecMulReflect]`, often followed by scalar
simplification if the entries contain reducible numeric arithmetic.
-/
simproc_decl matrixVecMul (Matrix.mulVec _ _) := fun e => do
  match_expr e with
  | Matrix.mulVec _ _ _ _ _ A v =>
      let ⟨_, ~q(Fin $l → $α), _⟩ ← inferTypeQ' e | return Simp.Step.continue
      let some lVal := l.nat? | return Simp.Step.continue
      let ref ← mkAppM ``Matrix.mulVecᵣ #[A, v]
      let some refQ ← checkTypeQ ref q(Fin $l → $α) |
        throwError "bad reflected matrix-vector product"
      let mut elems : Array Q($α) := #[]
      for i in List.range lVal do
        let iQ ← mkFinQ (mkNatLitQ i) l
        let entry : Q($α) := q($refQ $iQ)
        elems := elems.push entry
      have _ : $l =Q $lVal := ⟨⟩
      let out : Q(Fin $l → $α) := PiFin.mkLiteralQ (n := lVal) (elems[·]!)
      let pf1 ← mkAppM ``Eq.symm #[← mkAppM ``Matrix.mulVecᵣ_eq #[A, v]]
      let pf2 ← mkAppM ``Eq.symm #[← mkAppM ``FinVec.etaExpand_eq #[ref]]
      let pf ← mkEqTrans pf1 pf2
      return .visit { expr := out, proof? := pf }
  | _ => return .continue

/--
Simplify an entry of a reflected concrete matrix-vector product.

This is the companion cleanup simproc for `matrixVecMul`: after `matrixVecMul` rewrites a
matrix-vector product to a vector literal with entries of the form `(Matrix.mulVecᵣ A v) i`,
this simproc weak-head reduces those reflected entries to scalar expressions.
-/
simproc matrixVecMulReflect ((Matrix.mulVecᵣ _ _) _) := fun e => do
  match_expr e with
  | Matrix.mulVecᵣ _ _ _ instMul instAdd instZero A v i =>
      let ⟨_, ~q(Matrix (Fin $l) (Fin $m) $α), _⟩ ← inferTypeQ' A |
        return Simp.Step.continue
      let some mVal := m.nat? | return Simp.Step.continue
      let some instMulQ ← checkTypeQ instMul q(Mul $α) | throwError "bad Mul instance"
      let some instAddQ ← checkTypeQ instAdd q(Add $α) | throwError "bad Add instance"
      let some instZeroQ ← checkTypeQ instZero q(Zero $α) | throwError "bad Zero instance"
      let some AQ ← checkTypeQ A q(Matrix (Fin $l) (Fin $m) $α) | throwError "bad matrix"
      let some vQ ← checkTypeQ v q(Fin $m → $α) | throwError "bad vector"
      let some iQ ← checkTypeQ i q(Fin $l) | throwError "bad row index"
      let mut acc : Option Q($α) := none
      for j in List.range mVal do
        let jQ ← mkFinQ (mkNatLitQ j) m
        let aijExpr ← withTransparency .all <| Meta.whnf q($AQ $iQ $jQ)
        let vjExpr ← withTransparency .all <| Meta.whnf q($vQ $jQ)
        let some aij ← checkTypeQ aijExpr q($α) | throwError "bad matrix entry"
        let some vj ← checkTypeQ vjExpr q($α) | throwError "bad vector entry"
        let term : Q($α) := q(letI : Mul $α := $instMulQ; $aij * $vj)
        acc :=
          match acc with
          | none => some term
          | some acc =>
              some q(letI : Add $α := $instAddQ; $acc + $term)
      let out : Q($α) :=
        match acc with
        | none => q(letI : Zero $α := $instZeroQ; 0)
        | some acc => acc
      return .continue <| some { expr := out }
  | _ => return .continue

/--
Compute a concrete `Fin`-indexed matrix product.
-/
simproc_decl matrixMul
    ((_ : Matrix (Fin _) (Fin _) _) * (_ : Matrix (Fin _) (Fin _) _)) := fun e => do
  match_expr e with
  | HMul.hMul _ _ _ _ A B =>
      let ⟨_, ~q(Matrix (Fin $l) (Fin $n) $α), _⟩ ← inferTypeQ' e |
        return Simp.Step.continue
      let some lVal := l.nat? | return Simp.Step.continue
      let some nVal := n.nat? | return Simp.Step.continue
      let ref ← mkAppM ``Matrix.mulᵣ #[A, B]
      let some refQ ← checkTypeQ ref q(Matrix (Fin $l) (Fin $n) $α) |
        throwError "bad reflected matrix product"
      let mut rows : Array Q(Fin $n → $α) := #[]
      for i in List.range lVal do
        let iQ ← mkFinQ (mkNatLitQ i) l
        let mut row : Array Q($α) := #[]
        for j in List.range nVal do
          let jQ ← mkFinQ (mkNatLitQ j) n
          let entry : Q($α) := q($refQ $iQ $jQ)
          row := row.push entry
        have _ : $n =Q $nVal := ⟨⟩
        rows := rows.push (PiFin.mkLiteralQ (n := nVal) (row[·]!))
      have _ : $l =Q $lVal := ⟨⟩
      let rowVec : Q(Fin $l → Fin $n → $α) :=
        PiFin.mkLiteralQ (α := q(Fin $n → $α)) (n := lVal) (rows[·]!)
      let out : Q(Matrix (Fin $l) (Fin $n) $α) := q(Matrix.of $rowVec)
      let pf1 ← mkAppM ``Eq.symm #[← mkAppM ``Matrix.mulᵣ_eq #[A, B]]
      let pf2 ← mkAppM ``Eq.symm #[← mkAppM ``Matrix.etaExpand_eq #[ref]]
      let pf ← mkEqTrans pf1 pf2
      return .continue <| some { expr := out, proof? := pf }
  | _ => return .continue

/--
Expand a matrix product over any finite middle index type.
-/
simproc_decl matrixMulApply (HMul.hMul _ _) := fun e => do
  match_expr e with
  | HMul.hMul leftTy rightTy _ hMulInst A B =>
      let some result ← withMatrixType leftTy fun l m α => do
        let some result ← withMatrixType rightTy fun m' n β => do
          unless ← isDefEq m m' do return Simp.Step.continue
          unless ← isDefEq α β do return Simp.Step.continue
          let some hMulInstQ ←
            checkTypeQ hMulInst
              q(HMul (Matrix $l $m $α) (Matrix $m $n $α) (Matrix $l $n $α)) |
            return Simp.Step.continue
          let canonicalHMul ←
            synthInstanceQ q(HMul (Matrix $l $m $α) (Matrix $m $n $α) (Matrix $l $n $α))
          unless ← isDefEq hMulInstQ canonicalHMul do return Simp.Step.continue
          let instFintypeQ ← synthInstanceQ q(Fintype $m)
          let instMulQ ← synthInstanceQ q(Mul $α)
          let instAddCommMonoidQ ← synthInstanceQ q(AddCommMonoid $α)
          let some AQ ← checkTypeQ A q(Matrix $l $m $α) | return Simp.Step.continue
          let some BQ ← checkTypeQ B q(Matrix $m $n $α) | return Simp.Step.continue
          let out : Q(Matrix $l $n $α) := q(fun i j =>
            letI : Fintype $m := $instFintypeQ
            letI : Mul $α := $instMulQ
            letI : AddCommMonoid $α := $instAddCommMonoidQ
            ∑ k : $m, $AQ i k * $BQ k j)
          return .continue <| some { expr := out }
        | return Simp.Step.continue
        return result
      | return Simp.Step.continue
      return result
  | _ => return .continue

/--
Simplify an entry of a reflected concrete matrix product.

This is the companion cleanup simproc for `matrixMul`: after `matrixMul` rewrites a matrix
product to a matrix literal with entries of the form `(Matrix.mulᵣ A B) i j`, this simproc
expands each reflected entry to the corresponding scalar sum. It keeps the reducer conservative,
but knows how to look through `conjTranspose` of concrete matrix entries.
-/
simproc matrixMulReflect ((Matrix.mulᵣ _ _) _ _) := fun e => do
  match_expr e with
  | Matrix.mulᵣ _ _ n _ instMul instAdd instZero A B i j =>
      let ⟨_, ~q(Matrix (Fin $l) (Fin $m) $α), _⟩ ← inferTypeQ' A |
        return Simp.Step.continue
      let some mVal := m.nat? | return Simp.Step.continue
      let some instMulQ ← checkTypeQ instMul q(Mul $α) | throwError "bad Mul instance"
      let some instAddQ ← checkTypeQ instAdd q(Add $α) | throwError "bad Add instance"
      let some instZeroQ ← checkTypeQ instZero q(Zero $α) | throwError "bad Zero instance"
      let some AQ ← checkTypeQ A q(Matrix (Fin $l) (Fin $m) $α) | throwError "bad matrix"
      let some nQ ← checkTypeQ n q(ℕ) | throwError "bad column dimension"
      let some BQ ← checkTypeQ B q(Matrix (Fin $m) (Fin $nQ) $α) | throwError "bad matrix"
      let some iQ ← checkTypeQ i q(Fin $l) | throwError "bad row index"
      let some jQ ← checkTypeQ j q(Fin $nQ) | throwError "bad column index"
      let mut acc : Option Q($α) := none
      for k in List.range mVal do
        let kQ ← mkFinQ (mkNatLitQ k) m
        let left ← reduceMatrixEntry q($AQ $iQ $kQ)
        let right ← reduceMatrixEntry q($BQ $kQ $jQ)
        let term : Q($α) := q(letI : Mul $α := $instMulQ; $left * $right)
        acc :=
          match acc with
          | none => some term
          | some acc => some q(letI : Add $α := $instAddQ; $acc + $term)
      let out : Q($α) :=
        match acc with
        | none => q(letI : Zero $α := $instZeroQ; 0)
        | some acc => acc
      return .continue <| some { expr := out }
  | _ => return .continue

/-! ## Documentation examples

These examples intentionally live with the experimental simprocs as executable documentation for
the supported concrete matrix shapes.
-/

example :
    Matrix.mulVec !![(1 : ℤ), 2; 3, 4] ![5, 6] =
      ![1 * 5 + 2 * 6, 3 * 5 + 4 * 6] := by
  simp only [matrixVecMul, matrixVecMulReflect]
  norm_num

example :
    Matrix.mulVec !![(1 : ℤ), 2; 3, 4] ![5, 6] = ![17, 39] := by
  simp only [matrixVecMul, matrixVecMulReflect]
  norm_num

example (x y : ℤ) :
    Matrix.mulVec !![(1 : ℤ), 2; 3, 4] ![x, y] =
      ![1 * x + 2 * y, 3 * x + 4 * y] := by
  simp only [matrixVecMul, matrixVecMulReflect]
  norm_num

example :
    Matrix.mulVec !![(1 : ℤ), 2, 3; 4, 5, 6] ![7, 8, 9] =
      ![1 * 7 + 2 * 8 + 3 * 9, 4 * 7 + 5 * 8 + 6 * 9] := by
  simp only [matrixVecMul, matrixVecMulReflect]
  norm_num

example :
    !![(1 : ℤ), 2; 3, 4] * !![5, 6; 7, 8] =
      !![1 * 5 + 2 * 7, 1 * 6 + 2 * 8; 3 * 5 + 4 * 7, 3 * 6 + 4 * 8] := by
  simp only [matrixMul, matrixMulReflect]
  rfl

example :
    !![(1 : ℤ), 2, 3; 4, 5, 6] * !![(7 : ℤ), 8; 9, 10; 11, 12] =
      !![1 * 7 + 2 * 9 + 3 * 11, 1 * 8 + 2 * 10 + 3 * 12;
         4 * 7 + 5 * 9 + 6 * 11, 4 * 8 + 5 * 10 + 6 * 12] := by
  simp only [matrixMul, matrixMulReflect]
  rfl

example (A : Matrix Unit Bool ℤ) (B : Matrix Bool (Fin 3) ℤ) (i : Unit) (j : Fin 3) :
    (A * B) i j = ∑ k : Bool, A i k * B k j := by
  simp only [matrixMulApply]

example (A B : Matrix Bool Bool ℤ) (i j : Bool) :
    (A * B) i j = A i true * B true j + A i false * B false j := by
  simp only [matrixMulApply]
  simp

example :
    (!![(1 : ℂ), 0; 0, 1].conjTranspose * !![(1 : ℂ), 0; 0, 1]) =
      !![1, 0; 0, 1] := by
  simp only [matrixMul, matrixMulReflect]
  norm_num [Complex.ext_iff]

end MatrixCompute

end QLean
