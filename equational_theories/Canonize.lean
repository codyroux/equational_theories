import equational_theories.FreeMagma
import equational_theories.MagmaLaw

open FreeMagma
open Law

#print FreeMagma

def Canon {X} (R : FreeMagma X → FreeMagma X) :
  FreeMagma X → FreeMagma X
| .Leaf x => x
| .Fork t u => R <| .Fork (Canon R t) (Canon R u)

#check Canon

-- let's try a recursive def instead of an inductive
@[simp]
def Subterm {X} : FreeMagma X → FreeMagma X → Prop :=
λ t' t ↦
  match t with
  | .Leaf _ => False
  | .Fork t₁ t₂ =>
    t' = t₁ ∨ t' = t₂ ∨ Subterm t' t₁ ∨ Subterm t' t₂

def Collapsing {X} (E : MagmaLaw X) := Subterm E.rhs E.lhs

def WeakCanon {X}
  (R : FreeMagma X → FreeMagma X)
  (E : MagmaLaw X) :=
  ∀ θ : X → FreeMagma X, R (E.lhs ⬝ θ) = E.rhs ⬝ θ

def NonLeaf {X} : FreeMagma X → Bool
| .Leaf _ => false
| .Fork _ _ => true

-- Sheesh
def NonOverlapping {X}
  (R : FreeMagma X → FreeMagma X)
  (E : MagmaLaw X) :=
  ∀ t θ, Subterm t E.lhs →
  NonLeaf t →
  R (t ⬝ θ) = t ⬝ θ

def StrongCanon {X}
  (C : FreeMagma X → FreeMagma X)
  (E : MagmaLaw X) :=
  ∀ t u, {E} ⊢' t ≃ u → C t = C u

lemma SubtermMulTrans₁ {X}
  (t₁₁ t₁₂ t₂ : FreeMagma X) :
  Subterm (t₁₁⋆t₁₂) t₂ →
  Subterm t₁₁ t₂ :=
by
  cases t₂
  case Leaf => simp
  case Fork a b =>
    simp; intro
    | .inl h =>
      grind [Subterm]
    | .inr (.inl h) =>
      grind [Subterm]
    | .inr (.inr (.inl h)) =>
      right; right; left
      apply SubtermMulTrans₁; trivial
    | .inr (.inr (.inr h)) =>
      right; right; right
      apply SubtermMulTrans₁; trivial

lemma SubtermMulTrans₂ {X}
  (t₁₁ t₁₂ t₂ : FreeMagma X) :
  Subterm (t₁₁⋆t₁₂) t₂ →
  Subterm t₁₂ t₂ :=
by
  cases t₂
  case Leaf => simp
  case Fork a b =>
    simp; intro
    | .inl h =>
      grind [Subterm]
    | .inr (.inl h) =>
      grind [Subterm]
    | .inr (.inr (.inl h)) =>
      right; right; left
      apply SubtermMulTrans₂; trivial
    | .inr (.inr (.inr h)) =>
      right; right; right
      apply SubtermMulTrans₂; trivial

lemma SubtermTrans {X} (t₁ t₂ t₃ : FreeMagma X) :
  Subterm t₁ t₂ → Subterm t₂ t₃ → Subterm t₁ t₃ :=
by
  cases t₂
  case Leaf => simp
  case Fork t₂₁ t₂₂ =>
    simp [Subterm]
    intro
    | .inl h =>
      grind [SubtermMulTrans₁]
    | .inr (.inl h) =>
      grind [SubtermMulTrans₂]
    | .inr (.inr (.inl h)) =>
      intro h'; apply SubtermTrans
      . exact h
      . exact SubtermMulTrans₁ t₂₁ t₂₂ t₃ h'
    | .inr (.inr (.inr h)) =>
      intro h'; apply SubtermTrans
      . exact h
      . exact SubtermMulTrans₂ t₂₁ t₂₂ t₃ h'

-- The crucial, CRUCIAL lemma:
lemma NonOverlapSubst {X}
  (R : FreeMagma X → FreeMagma X)
  (t : FreeMagma X) :
  (∀ t' θ, Subterm t' t ∨ t' = t → NonLeaf t' → R (t'⬝θ) = t'⬝θ) →
  ∀ θ, Canon R (t⬝θ) = t ⬝ (Canon R ∘ θ) :=
by
  cases t
  case _ => simp [evalInMagma]
  case Fork t₁ t₂ =>
    simp [Canon, evalInMagma]
    intros subOrtho θ
    repeat rw [NonOverlapSubst]
    show (R (t₁ ⋆ t₂ ⬝ Canon R∘θ) = _)
    rw [subOrtho]; simp [evalInMagma]
    . simp
    . simp [NonLeaf]
    . grind
    . grind

lemma NonOverlapSubst' {X}
  (R : FreeMagma X → FreeMagma X)
  (t : FreeMagma X) :
  (∀ t' θ, Subterm t' t → NonLeaf t' → R (t'⬝θ) = t'⬝θ) →
  NonLeaf t →
  ∀ θ, Canon R (t⬝θ) = R (t ⬝ (Canon R ∘ θ)) := by
  cases t
  case Leaf => simp [NonLeaf]
  case Fork t₁ t₂ =>
    simp [evalInMagma, Canon]; intros
    congr 2 <;> apply NonOverlapSubst <;> grind

lemma CollapsingNonLeaf {X}
  (E : MagmaLaw X) :
  Collapsing E → NonLeaf E.lhs :=
by
  simp [Collapsing]; cases E.lhs <;> simp [NonLeaf]

-- Fixme: a hassle to fix this termination proof;
-- basically we need to replace StrongCannon by a much
-- weirder statement, and then annyoningly the cases need to
-- be refactored a bit to apply the IH.
theorem WeakToStrong {X}
  (R : FreeMagma X → FreeMagma X)
  (E : MagmaLaw X) :
  WeakCanon R E →
  Collapsing E →
  NonOverlapping R E →
  StrongCanon (Canon R) E :=
by
  intros wc coll nov t u eq
  cases eq
  case SubstAx E' mem θ =>
    cases mem
    calc
      Canon R (E.lhs ⬝ θ) = R (E.lhs ⬝ Canon R ∘ θ) := by
        apply NonOverlapSubst'; intros; apply nov <;> grind
        apply CollapsingNonLeaf; trivial
      _                   = E.rhs ⬝ Canon R ∘ θ := wc _
      _                   = Canon R (E.rhs ⬝ θ) := by
        symm; apply NonOverlapSubst
        intros t _ h _; apply nov <;> try grind
        cases h <;> simp [Collapsing] at coll <;> grind [SubtermTrans]
  case Ref => trivial
  case Sym =>
    symm; apply WeakToStrong <;> trivial
  case Trans =>
    trans <;> apply WeakToStrong <;> trivial
  case Cong =>
    simp [Canon]; congr 2 <;> apply WeakToStrong <;> trivial
