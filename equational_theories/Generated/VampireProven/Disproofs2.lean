import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.MemoFinOp
import equational_theories.DecideBang

@[equational_result]
theorem Equation168_not_implies_Equation3523 : ∃ (G: Type) (_: Magma G) (_: Finite G), Equation168 G ∧ ¬ Equation3523 G :=
  ⟨Fin 9, ⟨memoFinOp fun x y => [[2, 2, 4, 5, 4, 5, 2, 4, 5], [3, 3, 3, 7, 8, 7, 8, 8, 7], [6, 6, 0, 1, 0, 0, 6, 1, 1], [2, 2, 0, 1, 0, 0, 2, 1, 1], [2, 2, 4, 7, 4, 7, 2, 4, 7], [3, 3, 3, 5, 8, 5, 8, 8, 5], [6, 6, 0, 1, 0, 0, 6, 1, 1], [3, 3, 3, 5, 8, 5, 8, 8, 5], [6, 6, 4, 7, 4, 7, 6, 4, 7]][x.val]![y.val]!⟩, Finite.of_fintype _, by decideFin!⟩

@[equational_result]
theorem Equation168_not_implies_Equation3463 : ∃ (G: Type) (_: Magma G) (_: Finite G), Equation168 G ∧ ¬ Equation3463 G :=
  ⟨Fin 9, ⟨memoFinOp fun x y => [[3, 4, 3, 6, 6, 4, 4, 6, 3], [1, 1, 1, 0, 0, 2, 0, 2, 2], [8, 8, 8, 7, 7, 5, 5, 7, 5], [8, 8, 8, 0, 0, 2, 0, 2, 2], [1, 1, 1, 6, 6, 5, 5, 6, 5], [8, 8, 8, 6, 6, 5, 5, 6, 5], [3, 4, 3, 7, 7, 4, 4, 7, 3], [3, 4, 3, 7, 7, 4, 4, 7, 3], [1, 1, 1, 0, 0, 2, 0, 2, 2]][x.val]![y.val]!⟩, Finite.of_fintype _, by decideFin!⟩

@[equational_result]
theorem Equation168_not_implies_Equation3532 : ∃ (G: Type) (_: Magma G) (_: Finite G), Equation168 G ∧ ¬ Equation3532 G :=
  ⟨Fin 9, ⟨memoFinOp fun x y => [[2, 3, 3, 3, 2, 2, 5, 5, 5], [8, 8, 7, 7, 8, 7, 6, 6, 6], [4, 4, 0, 0, 4, 0, 5, 5, 5], [2, 3, 3, 3, 2, 2, 1, 1, 1], [4, 4, 0, 0, 4, 0, 1, 1, 1], [8, 8, 7, 7, 8, 7, 6, 6, 6], [8, 8, 7, 7, 8, 7, 6, 6, 6], [2, 3, 3, 3, 2, 2, 5, 5, 5], [4, 4, 0, 0, 4, 0, 1, 1, 1]][x.val]![y.val]!⟩, Finite.of_fintype _, by decideFin!⟩

@[equational_result]
theorem Equation2450_not_implies_Equation3319 : ∃ (G: Type) (_: Magma G) (_: Finite G), Equation2450 G ∧ ¬ Equation3319 G :=
  ⟨Fin 7, ⟨memoFinOp fun x y => [[0, 2, 5, 0, 6, 2, 4], [3, 3, 3, 3, 3, 3, 3], [4, 6, 2, 2, 0, 6, 5], [1, 1, 1, 1, 1, 1, 1], [5, 0, 6, 4, 4, 0, 2], [6, 5, 4, 5, 2, 5, 0], [2, 4, 0, 6, 5, 4, 6]][x.val]![y.val]!⟩, Finite.of_fintype _, by decideFin!⟩

@[equational_result]
theorem Equation2450_not_implies_Equation326 : ∃ (G: Type) (_: Magma G) (_: Finite G), Equation2450 G ∧ ¬ Equation326 G :=
  ⟨Fin 7, ⟨memoFinOp fun x y => [[0, 0, 3, 4, 3, 6, 5], [2, 2, 2, 2, 2, 2, 2], [1, 1, 1, 1, 1, 1, 1], [6, 3, 5, 3, 5, 4, 0], [5, 4, 4, 6, 4, 0, 3], [3, 5, 6, 0, 6, 5, 4], [4, 6, 0, 5, 0, 3, 6]][x.val]![y.val]!⟩, Finite.of_fintype _, by decideFin!⟩

@[equational_result]
theorem Equation2712_not_implies_Equation4584 : ∃ (G: Type) (_: Magma G) (_: Finite G), Equation2712 G ∧ ¬ Equation4584 G :=
  ⟨Fin 11, ⟨memoFinOp fun x y => [[2, 1, 2, 7, 7, 5, 2, 7, 7, 2, 10], [3, 6, 6, 3, 8, 6, 6, 8, 8, 6, 6], [0, 5, 5, 3, 4, 5, 6, 7, 8, 6, 5], [2, 1, 2, 2, 1, 5, 5, 1, 10, 2, 10], [9, 10, 2, 9, 10, 10, 6, 10, 10, 9, 10], [0, 10, 2, 3, 8, 8, 6, 8, 8, 9, 10], [4, 1, 2, 8, 4, 5, 8, 7, 8, 2, 10], [0, 10, 2, 0, 0, 10, 6, 10, 0, 9, 10], [9, 1, 2, 9, 1, 5, 6, 1, 10, 9, 10], [4, 5, 5, 8, 4, 5, 5, 7, 8, 5, 5], [0, 5, 6, 3, 4, 5, 6, 7, 8, 6, 6]][x.val]![y.val]!⟩, Finite.of_fintype _, by decideFin!⟩

@[equational_result]
theorem Equation2712_not_implies_Equation4070 : ∃ (G: Type) (_: Magma G) (_: Finite G), Equation2712 G ∧ ¬ Equation4070 G :=
  ⟨Fin 11, ⟨memoFinOp fun x y => [[2, 1, 2, 2, 4, 5, 4, 4, 2, 2, 10], [3, 7, 7, 3, 7, 7, 7, 7, 9, 9, 9], [0, 5, 5, 3, 4, 5, 6, 7, 9, 9, 5], [4, 1, 2, 4, 4, 5, 4, 4, 2, 4, 10], [0, 10, 2, 3, 10, 10, 7, 7, 8, 9, 10], [0, 10, 2, 3, 7, 7, 7, 7, 8, 9, 10], [9, 10, 2, 9, 10, 10, 10, 10, 8, 9, 10], [8, 1, 2, 9, 4, 5, 4, 9, 8, 9, 10], [6, 5, 5, 6, 4, 5, 6, 7, 5, 4, 5], [6, 1, 2, 6, 4, 5, 6, 7, 2, 4, 10], [0, 5, 9, 3, 4, 5, 6, 7, 9, 9, 9]][x.val]![y.val]!⟩, Finite.of_fintype _, by decideFin!⟩

@[equational_result]
theorem Equation2712_not_implies_Equation3458 : ∃ (G: Type) (_: Magma G) (_: Finite G), Equation2712 G ∧ ¬ Equation3458 G :=
  ⟨Fin 11, ⟨memoFinOp fun x y => [[2, 1, 2, 4, 4, 2, 4, 2, 8, 4, 10], [3, 7, 7, 3, 3, 7, 9, 7, 7, 9, 7], [0, 8, 8, 3, 4, 7, 6, 7, 8, 9, 8], [2, 1, 2, 2, 1, 2, 1, 2, 8, 2, 10], [0, 10, 2, 0, 10, 5, 0, 7, 10, 0, 10], [6, 8, 8, 9, 6, 8, 6, 8, 8, 9, 8], [5, 10, 2, 5, 10, 5, 10, 7, 10, 2, 10], [6, 1, 2, 9, 4, 2, 6, 9, 8, 9, 10], [0, 10, 2, 3, 3, 5, 9, 7, 9, 9, 10], [5, 1, 2, 5, 1, 5, 1, 7, 8, 2, 10], [0, 8, 7, 3, 4, 7, 6, 7, 8, 9, 7]][x.val]![y.val]!⟩, Finite.of_fintype _, by decideFin!⟩

@[equational_result]
theorem Equation2712_not_implies_Equation3052 : ∃ (G: Type) (_: Magma G) (_: Finite G), Equation2712 G ∧ ¬ Equation3052 G :=
  ⟨Fin 11, ⟨memoFinOp fun x y => [[2, 1, 2, 5, 2, 5, 6, 5, 8, 2, 2], [3, 4, 3, 3, 4, 10, 4, 10, 10, 4, 10], [0, 8, 8, 3, 4, 5, 8, 7, 8, 4, 10], [5, 1, 2, 5, 5, 5, 6, 5, 8, 2, 5], [7, 1, 2, 10, 10, 5, 6, 7, 8, 2, 10], [0, 6, 2, 3, 4, 6, 6, 10, 6, 9, 10], [0, 8, 4, 3, 4, 5, 4, 7, 8, 4, 10], [9, 6, 2, 9, 4, 6, 6, 6, 6, 9, 2], [0, 6, 2, 3, 4, 10, 6, 10, 10, 9, 10], [7, 8, 8, 7, 5, 5, 8, 7, 8, 8, 10], [9, 1, 2, 9, 4, 5, 6, 5, 8, 9, 2]][x.val]![y.val]!⟩, Finite.of_fintype _, by decideFin!⟩

@[equational_result]
theorem Equation2712_not_implies_Equation3105 : ∃ (G: Type) (_: Magma G) (_: Finite G), Equation2712 G ∧ ¬ Equation3105 G :=
  ⟨Fin 11, ⟨memoFinOp fun x y => [[2, 6, 2, 7, 2, 2, 6, 7, 2, 2, 2], [0, 5, 8, 5, 4, 5, 5, 5, 8, 8, 10], [0, 3, 7, 3, 4, 5, 7, 7, 8, 8, 10], [4, 9, 2, 4, 4, 4, 9, 4, 8, 9, 4], [10, 1, 2, 3, 2, 5, 6, 7, 2, 2, 10], [4, 1, 2, 7, 4, 4, 6, 7, 8, 9, 4], [0, 5, 8, 5, 4, 5, 5, 5, 8, 8, 10], [0, 9, 2, 0, 4, 5, 9, 8, 8, 9, 10], [10, 1, 2, 3, 10, 5, 6, 7, 10, 2, 10], [10, 3, 10, 3, 10, 5, 7, 7, 10, 10, 10], [4, 1, 2, 7, 4, 7, 6, 7, 8, 9, 7]][x.val]![y.val]!⟩, Finite.of_fintype _, by decideFin!⟩

@[equational_result]
theorem Equation2712_not_implies_Equation2469 : ∃ (G: Type) (_: Magma G) (_: Finite G), Equation2712 G ∧ ¬ Equation2469 G :=
  ⟨Fin 11, ⟨memoFinOp fun x y => [[5, 1, 5, 9, 9, 5, 9, 7, 5, 9, 10], [3, 2, 2, 3, 4, 2, 4, 2, 2, 4, 2], [6, 1, 4, 4, 4, 5, 6, 7, 5, 9, 10], [5, 1, 5, 5, 10, 5, 1, 7, 5, 1, 10], [8, 1, 2, 8, 10, 5, 1, 7, 8, 1, 10], [0, 7, 2, 3, 4, 7, 6, 7, 2, 9, 7], [8, 10, 2, 8, 10, 5, 10, 10, 8, 10, 10], [0, 10, 2, 3, 4, 5, 4, 4, 8, 4, 10], [6, 7, 7, 4, 4, 7, 6, 7, 7, 9, 7], [0, 10, 2, 0, 0, 5, 0, 10, 8, 10, 10], [0, 7, 2, 3, 4, 2, 6, 7, 2, 9, 2]][x.val]![y.val]!⟩, Finite.of_fintype _, by decideFin!⟩

@[equational_result]
theorem Equation2712_not_implies_Equation2256 : ∃ (G: Type) (_: Magma G) (_: Finite G), Equation2712 G ∧ ¬ Equation2256 G :=
  ⟨Fin 11, ⟨memoFinOp fun x y => [[2, 2, 2, 3, 9, 5, 6, 5, 9, 9, 2], [8, 6, 3, 3, 8, 5, 6, 7, 8, 9, 3], [0, 4, 6, 6, 4, 6, 6, 7, 8, 9, 4], [4, 1, 1, 7, 4, 7, 7, 7, 7, 7, 1], [9, 2, 2, 3, 9, 5, 6, 9, 9, 9, 2], [0, 1, 1, 6, 4, 1, 6, 7, 8, 9, 1], [0, 1, 2, 5, 4, 5, 7, 7, 7, 7, 10], [10, 1, 2, 3, 1, 5, 6, 1, 9, 9, 10], [10, 1, 2, 5, 1, 5, 5, 5, 5, 5, 10], [0, 1, 2, 5, 4, 5, 5, 7, 7, 5, 10], [8, 6, 6, 6, 8, 6, 6, 7, 8, 9, 6]][x.val]![y.val]!⟩, Finite.of_fintype _, by decideFin!⟩

@[equational_result]
theorem Equation2712_not_implies_Equation1644 : ∃ (G: Type) (_: Magma G) (_: Finite G), Equation2712 G ∧ ¬ Equation1644 G :=
  ⟨Fin 11, ⟨memoFinOp fun x y => [[2, 1, 2, 8, 2, 5, 8, 7, 8, 8, 2], [3, 4, 4, 3, 4, 4, 9, 4, 9, 9, 4], [0, 5, 5, 3, 4, 5, 6, 5, 8, 9, 4], [2, 1, 2, 2, 2, 5, 1, 7, 1, 2, 2], [6, 1, 2, 9, 9, 5, 6, 7, 8, 9, 2], [0, 7, 2, 3, 4, 9, 9, 7, 9, 9, 10], [10, 7, 2, 10, 4, 7, 7, 7, 7, 2, 10], [0, 5, 4, 3, 4, 5, 6, 4, 8, 9, 4], [0, 7, 2, 0, 4, 7, 0, 7, 7, 0, 10], [10, 1, 2, 10, 4, 5, 1, 7, 1, 7, 10], [6, 5, 5, 9, 5, 5, 6, 5, 8, 9, 5]][x.val]![y.val]!⟩, Finite.of_fintype _, by decideFin!⟩

@[equational_result]
theorem Equation2712_not_implies_Equation1631 : ∃ (G: Type) (_: Magma G) (_: Finite G), Equation2712 G ∧ ¬ Equation1631 G :=
  ⟨Fin 11, ⟨memoFinOp fun x y => [[2, 1, 2, 2, 4, 6, 6, 2, 10, 2, 10], [3, 7, 7, 3, 7, 8, 7, 7, 8, 7, 7], [0, 4, 4, 3, 4, 5, 6, 7, 8, 7, 4], [2, 1, 2, 2, 4, 6, 6, 2, 10, 2, 10], [0, 10, 2, 3, 8, 8, 8, 7, 8, 9, 10], [9, 10, 2, 9, 10, 10, 10, 7, 10, 9, 10], [0, 10, 2, 3, 10, 8, 10, 7, 8, 9, 10], [5, 1, 2, 8, 4, 5, 6, 8, 8, 2, 10], [9, 1, 2, 9, 4, 6, 6, 7, 10, 9, 10], [8, 4, 4, 8, 4, 5, 6, 6, 8, 4, 4], [0, 4, 7, 3, 4, 5, 6, 7, 8, 7, 7]][x.val]![y.val]!⟩, Finite.of_fintype _, by decideFin!⟩

@[equational_result]
theorem Equation2712_not_implies_Equation2253 : ∃ (G: Type) (_: Magma G) (_: Finite G), Equation2712 G ∧ ¬ Equation2253 G :=
  ⟨Fin 11, ⟨memoFinOp fun x y => [[2, 2, 2, 3, 5, 5, 8, 7, 8, 5, 2], [9, 7, 3, 3, 9, 5, 6, 7, 8, 9, 3], [0, 4, 7, 7, 4, 5, 6, 7, 7, 9, 4], [4, 1, 1, 6, 4, 6, 6, 6, 6, 6, 1], [5, 2, 2, 3, 5, 5, 5, 7, 8, 5, 2], [0, 1, 2, 8, 4, 8, 6, 8, 8, 6, 10], [10, 1, 2, 3, 1, 5, 1, 7, 8, 5, 10], [0, 1, 2, 8, 4, 6, 6, 6, 8, 6, 10], [0, 1, 1, 7, 4, 5, 6, 7, 1, 9, 1], [10, 1, 2, 8, 1, 8, 8, 8, 8, 8, 10], [9, 7, 7, 7, 9, 5, 6, 7, 7, 9, 7]][x.val]![y.val]!⟩, Finite.of_fintype _, by decideFin!⟩

@[equational_result]
theorem Equation2712_not_implies_Equation25 : ∃ (G: Type) (_: Magma G) (_: Finite G), Equation2712 G ∧ ¬ Equation25 G :=
  ⟨Fin 11, ⟨memoFinOp fun x y => [[3, 1, 4, 3, 4, 3, 4, 7, 8, 4, 3], [2, 5, 2, 5, 2, 5, 6, 5, 5, 2, 5], [3, 1, 3, 3, 1, 3, 8, 7, 8, 1, 3], [0, 7, 2, 7, 4, 5, 6, 7, 7, 9, 5], [0, 8, 0, 3, 8, 5, 0, 8, 8, 0, 10], [9, 1, 6, 3, 4, 6, 6, 7, 8, 9, 3], [10, 1, 10, 3, 1, 5, 8, 7, 8, 1, 10], [0, 8, 2, 3, 2, 5, 6, 6, 8, 6, 10], [0, 7, 2, 5, 4, 5, 6, 7, 5, 9, 5], [10, 8, 10, 3, 8, 5, 3, 8, 8, 8, 10], [9, 7, 9, 7, 9, 7, 6, 7, 7, 9, 7]][x.val]![y.val]!⟩, Finite.of_fintype _, by decideFin!⟩

@[equational_result]
theorem Equation3113_not_implies_Equation1832 : ∃ (G: Type) (_: Magma G) (_: Finite G), Equation3113 G ∧ ¬ Equation1832 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 2, 3, 5, 2, 4], [0, 1, 2, 3, 4, 5], [5, 3, 1, 4, 0, 3], [4, 4, 0, 1, 5, 2], [3, 5, 5, 2, 1, 0], [2, 0, 4, 0, 3, 1]][x.val]![y.val]!⟩, Finite.of_fintype _, by decideFin!⟩

@[equational_result]
theorem Equation474_not_implies_Equation1629 : ∃ (G: Type) (_: Magma G) (_: Finite G), Equation474 G ∧ ¬ Equation1629 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 0, 5, 4, 3, 2], [2, 1, 3, 4, 5, 0], [3, 2, 1, 0, 5, 4], [5, 3, 4, 1, 2, 0], [2, 4, 0, 5, 1, 3], [4, 5, 3, 2, 0, 1]][x.val]![y.val]!⟩, Finite.of_fintype _, by decideFin!⟩

@[equational_result]
theorem Equation854_not_implies_Equation1225 : ∃ (G: Type) (_: Magma G) (_: Finite G), Equation854 G ∧ ¬ Equation1225 G :=
  ⟨Fin 11, ⟨memoFinOp fun x y => [[2, 7, 0, 4, 6, 0, 0, 8, 7, 8, 0], [2, 5, 4, 1, 2, 1, 1, 1, 5, 1, 1], [2, 3, 5, 1, 2, 2, 2, 2, 5, 2, 1], [3, 3, 5, 9, 3, 10, 10, 10, 5, 3, 5], [6, 7, 4, 4, 6, 4, 4, 1, 7, 1, 4], [5, 5, 5, 9, 5, 9, 10, 10, 5, 5, 5], [6, 6, 6, 9, 6, 9, 10, 10, 6, 6, 6], [6, 7, 7, 9, 6, 9, 9, 10, 7, 6, 7], [2, 3, 4, 1, 2, 8, 8, 8, 5, 8, 1], [10, 9, 9, 9, 6, 9, 9, 10, 9, 1, 9], [10, 10, 5, 9, 10, 10, 10, 10, 5, 10, 1]][x.val]![y.val]!⟩, Finite.of_fintype _, by decideFin!⟩

@[equational_result]
theorem Equation3964_not_implies_Equation3456 : ∃ (G: Type) (_: Magma G) (_: Finite G), Equation3964 G ∧ ¬ Equation3456 G :=
  ⟨Fin 17, ⟨memoFinOp fun x y => [[1, 13, 0, 14, 16, 3, 9, 13, 1, 1, 2, 2, 8, 0, 3, 8, 4], [2, 5, 9, 11, 7, 6, 4, 5, 13, 2, 5, 5, 4, 8, 6, 4, 12], [0, 8, 1, 3, 4, 14, 2, 8, 0, 0, 9, 9, 13, 1, 14, 13, 16], [16, 7, 4, 0, 0, 15, 6, 7, 14, 16, 11, 11, 12, 3, 15, 12, 15], [3, 6, 14, 15, 0, 0, 12, 6, 16, 3, 7, 7, 11, 4, 0, 11, 15], [4, 12, 16, 15, 15, 0, 11, 12, 3, 4, 6, 6, 7, 14, 0, 7, 0], [13, 5, 8, 7, 6, 12, 5, 5, 9, 13, 4, 4, 4, 2, 12, 4, 11], [2, 5, 9, 11, 7, 6, 4, 5, 13, 2, 5, 5, 4, 8, 6, 4, 12], [0, 9, 1, 4, 14, 16, 8, 9, 1, 0, 13, 13, 2, 0, 16, 2, 3], [1, 13, 0, 14, 16, 3, 9, 13, 1, 1, 2, 2, 8, 0, 3, 8, 4], [8, 4, 13, 12, 11, 7, 4, 4, 2, 8, 5, 5, 5, 9, 7, 5, 6], [8, 4, 13, 12, 11, 7, 4, 4, 2, 8, 5, 5, 5, 9, 7, 5, 6], [9, 4, 2, 6, 12, 11, 5, 4, 8, 9, 4, 4, 5, 13, 11, 5, 7], [1, 2, 0, 16, 3, 4, 13, 2, 0, 1, 8, 8, 9, 1, 4, 9, 14], [4, 12, 16, 15, 15, 0, 11, 12, 3, 4, 6, 6, 7, 14, 0, 7, 0], [9, 4, 2, 6, 12, 11, 5, 4, 8, 9, 4, 4, 5, 13, 11, 5, 7], [14, 11, 3, 0, 15, 15, 7, 11, 4, 14, 12, 12, 6, 16, 15, 6, 0]][x.val]![y.val]!⟩, Finite.of_fintype _, by decideFin!⟩

@[equational_result]
theorem Equation2126_not_implies_Equation166 : ∃ (G: Type) (_: Magma G) (_: Finite G), Equation2126 G ∧ ¬ Equation166 G :=
  ⟨Fin 21, ⟨memoFinOp fun x y => [[1, 1, 19, 1, 19, 1, 1, 19, 16, 19, 16, 1, 19, 16, 19, 1, 1, 16, 19, 16, 19], [15, 1, 5, 5, 5, 1, 11, 11, 16, 5, 16, 1, 15, 11, 15, 1, 1, 11, 5, 16, 11], [15, 1, 5, 5, 5, 1, 11, 11, 16, 5, 16, 1, 15, 11, 15, 1, 1, 11, 5, 16, 11], [17, 20, 7, 7, 7, 20, 17, 7, 17, 17, 20, 20, 17, 7, 17, 20, 20, 20, 20, 20, 7], [14, 0, 12, 9, 9, 8, 9, 12, 14, 14, 9, 8, 14, 12, 14, 8, 0, 12, 9, 0, 12], [4, 2, 18, 9, 9, 2, 9, 3, 4, 4, 9, 2, 4, 18, 4, 2, 2, 3, 9, 18, 3], [15, 1, 5, 5, 5, 1, 11, 11, 16, 5, 16, 1, 15, 11, 15, 1, 1, 11, 5, 16, 11], [4, 2, 7, 13, 7, 2, 13, 7, 4, 4, 20, 2, 4, 7, 4, 2, 2, 20, 20, 13, 7], [15, 15, 5, 5, 5, 11, 11, 11, 5, 5, 5, 5, 15, 11, 15, 15, 5, 11, 5, 11, 11], [4, 6, 18, 10, 10, 6, 10, 3, 4, 4, 10, 6, 4, 18, 4, 6, 6, 3, 10, 18, 3], [4, 6, 18, 10, 10, 6, 10, 3, 4, 4, 10, 6, 4, 18, 4, 6, 6, 3, 10, 18, 3], [17, 6, 7, 13, 7, 6, 13, 7, 17, 17, 20, 6, 17, 7, 17, 6, 6, 20, 20, 13, 7], [17, 2, 7, 13, 7, 2, 13, 7, 17, 17, 20, 2, 17, 7, 17, 2, 2, 20, 20, 13, 7], [19, 6, 19, 6, 19, 6, 6, 3, 6, 19, 6, 6, 19, 6, 19, 6, 6, 3, 19, 19, 3], [14, 0, 12, 9, 9, 8, 9, 12, 14, 14, 9, 8, 14, 12, 14, 8, 0, 12, 9, 0, 12], [14, 0, 12, 0, 14, 12, 0, 12, 14, 14, 0, 0, 14, 12, 14, 14, 0, 12, 0, 0, 12], [10, 19, 19, 10, 10, 8, 10, 10, 8, 19, 10, 8, 19, 10, 19, 8, 10, 19, 10, 19, 10], [14, 0, 12, 9, 9, 8, 9, 12, 14, 14, 9, 8, 14, 12, 14, 8, 0, 12, 9, 0, 12], [13, 2, 19, 13, 19, 2, 13, 13, 2, 19, 13, 2, 19, 2, 19, 2, 2, 13, 2, 13, 19], [14, 2, 12, 9, 9, 2, 9, 12, 14, 14, 9, 2, 14, 12, 14, 2, 2, 12, 9, 12, 12], [17, 10, 18, 10, 10, 17, 10, 18, 17, 17, 10, 18, 17, 18, 17, 17, 10, 17, 10, 18, 17]][x.val]![y.val]!⟩, Finite.of_fintype _, by decideFin!⟩

@[equational_result]
theorem Equation1486_not_implies_Equation2052 : ∃ (G: Type) (_: Magma G) (_: Finite G), Equation1486 G ∧ ¬ Equation2052 G :=
  ⟨Fin 21, ⟨memoFinOp fun x y => [[1, 12, 12, 7, 7, 6, 14, 12, 18, 7, 18, 12, 0, 6, 19, 11, 18, 7, 6, 6, 18], [2, 8, 8, 10, 10, 19, 0, 0, 20, 10, 20, 8, 0, 19, 19, 8, 10, 20, 0, 19, 20], [1, 2, 2, 13, 13, 11, 0, 0, 1, 13, 1, 2, 0, 2, 11, 11, 11, 13, 0, 1, 1], [1, 2, 2, 10, 15, 11, 14, 12, 1, 15, 1, 2, 15, 2, 11, 11, 11, 15, 6, 1, 1], [2, 12, 12, 7, 4, 6, 4, 12, 9, 4, 9, 12, 4, 6, 19, 3, 11, 9, 6, 6, 9], [1, 2, 2, 7, 7, 11, 14, 5, 1, 7, 1, 2, 0, 2, 11, 11, 11, 7, 17, 1, 1], [2, 5, 5, 13, 13, 19, 4, 5, 18, 13, 18, 5, 4, 19, 19, 3, 18, 13, 6, 19, 18], [2, 3, 3, 7, 4, 17, 4, 5, 9, 4, 9, 3, 4, 17, 16, 3, 18, 9, 17, 17, 9], [1, 2, 2, 7, 15, 11, 0, 12, 1, 15, 1, 2, 15, 2, 11, 11, 11, 15, 0, 1, 1], [1, 8, 8, 10, 10, 17, 4, 0, 20, 10, 20, 8, 4, 17, 19, 8, 10, 20, 17, 17, 20], [2, 3, 3, 10, 4, 16, 4, 5, 9, 4, 9, 3, 4, 16, 16, 3, 10, 9, 6, 16, 9], [1, 5, 5, 13, 15, 16, 14, 5, 14, 15, 14, 5, 15, 16, 16, 8, 11, 15, 17, 16, 14], [1, 2, 2, 7, 7, 11, 0, 0, 1, 7, 1, 2, 4, 2, 11, 11, 11, 7, 0, 1, 1], [1, 3, 3, 7, 4, 17, 4, 12, 9, 4, 9, 3, 4, 17, 11, 3, 18, 9, 17, 17, 9], [1, 8, 8, 10, 10, 6, 0, 0, 20, 10, 20, 8, 4, 6, 19, 8, 10, 20, 6, 6, 20], [2, 12, 12, 13, 4, 17, 4, 12, 9, 4, 9, 12, 4, 17, 11, 11, 18, 9, 17, 17, 9], [1, 5, 5, 13, 13, 19, 14, 5, 14, 13, 14, 5, 4, 19, 19, 3, 10, 13, 6, 19, 14], [1, 5, 5, 13, 13, 19, 14, 5, 18, 13, 18, 5, 4, 19, 19, 11, 18, 13, 0, 19, 18], [1, 8, 8, 10, 10, 16, 0, 0, 20, 10, 20, 8, 4, 16, 16, 8, 10, 20, 17, 16, 20], [1, 5, 5, 13, 13, 19, 14, 5, 14, 13, 14, 5, 4, 19, 19, 3, 11, 13, 0, 19, 14], [1, 8, 8, 10, 10, 17, 0, 5, 20, 10, 20, 8, 4, 17, 19, 8, 10, 20, 17, 17, 20]][x.val]![y.val]!⟩, Finite.of_fintype _, by decideFin!⟩