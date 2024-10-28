
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,3,2,2,4],[5,1,2,3,3,0],[3,0,4,0,0,1],[2,3,0,1,1,5],[0,4,5,4,4,2],[4,5,1,5,5,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,2,3,2,2,4],[5,1,2,3,3,0],[3,0,4,0,0,1],[2,3,0,1,1,5],[0,4,5,4,4,2],[4,5,1,5,5,3]]» : Magma (Fin 6) where
  op := memoFinOp fun x y => [[1,2,3,2,2,4],[5,1,2,3,3,0],[3,0,4,0,0,1],[2,3,0,1,1,5],[0,4,5,4,4,2],[4,5,1,5,5,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,2,3,2,2,4],[5,1,2,3,3,0],[3,0,4,0,0,1],[2,3,0,1,1,5],[0,4,5,4,4,2],[4,5,1,5,5,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2447] [2470, 3253] :=
    ⟨Fin 6, «FinitePoly [[1,2,3,2,2,4],[5,1,2,3,3,0],[3,0,4,0,0,1],[2,3,0,1,1,5],[0,4,5,4,4,2],[4,5,1,5,5,3]]», Finite.of_fintype _, by decideFin!⟩