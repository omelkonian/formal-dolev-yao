{-# OPTIONS --rewriting #-}
module DolevYao where

open import Agda.Builtin.Equality.Rewrite
open import Data.List.Relation.Unary.Linked using (Linked; _∷_; [-])

open import Prelude.Init; open SetAsType
open L.Mem
open import Prelude.Nary
open import Prelude.InferenceRules
open import Prelude.DecEq
open import Prelude.Semigroup
open import Prelude.Monoid
open import Prelude.Functor
open import Prelude.Bifunctor
open import Prelude.Sets hiding (_∪_)
open import Prelude.FromList
open import Prelude.Setoid

-- ** shorthands

infixr 5 _∪_; _∪_ = _◇_
pattern 𝟘 = here refl
pattern 𝟙 = there 𝟘
pattern 𝟚 = there 𝟙

-- ** Basics

postulate
  Part : Type
  instance DecEq-Part : DecEq Part

data Op : Type where
  E D : Part → Op
unquoteDecl DecEq-Op = DERIVE DecEq [ quote Op , DecEq-Op ]

Ops = List Op
private variable ops : Ops

_∗ : Ops → Type
ops ∗ = List (∃ (L.Mem._∈ ops))

forget : ops ∗ → Ops
forget = map proj₁

cancelOut : Rel₀ Op
cancelOut = λ where
  (E x) (D y) → x ≡ y
  (D x) (E y) → x ≡ y
  (E _) (E _) → ⊥
  (D _) (D _) → ⊥

cancelOut? : Decidable² cancelOut
cancelOut? = λ where
  (E x) (D y) → x ≟ y
  (D x) (E y) → x ≟ y
  (E _) (E _) → no λ ()
  (D _) (D _) → no λ ()

cancelOutᵇ : Op → Op → Bool
cancelOutᵇ = isYes ∘₂ cancelOut?

Reduced : Pred₀ Ops
Reduced = Linked (¬_ ∘₂ cancelOut)

{-# TERMINATING #-}
reduce : Op₁ Ops
reduce = λ where
  [] → []
  (x ∷ []) → [ x ]
  (x ∷ y ∷ xs) →
    if cancelOutᵇ x y then reduce xs
    else reduce (x ∷ reduce (y ∷ xs))

postulate reduce-correct : ∀ γ → Reduced (reduce γ)

module _ where private
  postulate A B C : Part; A≢B : A ≢ B

  ∙≡∙ : ∀ (A : Part) → (A ≟ A) ≡ yes refl
  ∙≡∙ = ≟-refl
  {-# REWRITE ∙≡∙ #-}
  ∙≢∘ : isYes (A ≟ B) ≡ false
  ∙≢∘ rewrite dec-no (A ≟ B) A≢B .proj₂ = refl
  {-# REWRITE ∙≢∘ #-}
  ∘≢∙ : isYes (B ≟ A) ≡ false
  ∘≢∙ rewrite dec-no (B ≟ A) (≢-sym A≢B) .proj₂ = refl
  {-# REWRITE ∘≢∙ #-}

  _ = reduce ⟦ E C , E A , D B , E B , D A ⟧ ≡ [ E C ]
    ∋ refl

-- ** Two-party cascade protocol

module _ (A B : Type) where
  infixr 4 _⟨∷_ _∷⟩_
  mutual
    data AlterList : Type where
      [] : AlterList
      _⟨∷_ : A → AlterListᴮ → AlterList

    data AlterListᴮ : Type where
      [] : AlterListᴮ
      _∷⟩_ : B → AlterList → AlterListᴮ

private
  variable A A′ B B′ : Type
  module _ (f : A → A′) (g : B → B′) where mutual
    bi : AlterList _ _ → AlterList _ _
    bi = λ where [] → []
                 (a ⟨∷ bs) → f a ⟨∷ biᴮ bs

    biᴮ : AlterListᴮ _ _ → AlterListᴮ _ _
    biᴮ = λ where [] → []
                  (b ∷⟩ as) → g b ∷⟩ bi as

instance
  Bifunctor-AL : Bifunctor AlterList
  Bifunctor-AL .bimap = bi

  Bifunctor-AL′ : Bifunctor AlterListᴮ
  Bifunctor-AL′ .bimap = biᴮ

lefts : AlterList A B → List A
lefts = go where mutual
  go : AlterList _ _ → List _
  go = λ where [] → []
               (a ⟨∷ bs) → a ∷ goᴮ bs

  goᴮ : AlterListᴮ _ _ → List _
  goᴮ = λ where [] → []
                (_ ∷⟩ as) → go as

rights : AlterList A B → List B
rights = go where mutual
  go : AlterList _ _ → List _
  go = λ where [] → []
               (_ ⟨∷ bs) → goᴮ bs

  goᴮ : AlterListᴮ _ _ → List _
  goᴮ = λ where [] → []
                (b ∷⟩ as) → b ∷ go as

merge : AlterList A A → List A
merge = go where mutual
  go : AlterList _ _ → List _
  go = λ where [] → []
               (a ⟨∷ bs) → a ∷ goᴮ bs

  goᴮ : AlterListᴮ _ _ → List _
  goᴮ = λ where [] → []
                (b ∷⟩ as) → b ∷ go as

private
  _ = AlterList ℕ String
    ∋ 0 ⟨∷ "zero" ∷⟩ []
  _ = AlterList ℕ String
    ∋ 0 ⟨∷ "zero" ∷⟩ 1 ⟨∷ []
  _ = AlterList ℕ String
    ∋ 0 ⟨∷ "zero" ∷⟩ 1 ⟨∷ "one" ∷⟩ []

module _ (X Y : Part) {X≢Y : X ≢ Y} where
  record 𝟚-cascade : Type where
    field series : AlterList (⟦ E X , E Y , D X ⟧ ∗) (⟦ E X , E Y , D Y ⟧ ∗)

    run : AlterList Ops Ops
    run = bimap forget forget series
    αβs = merge run
    αs  = lefts run
    βs  = rights run

    field reduced : All Reduced αβs

    Secure : Type
    Secure =
      ∀ (Z : Part) →
        let
          Σ₁ = (E <$> ⟦ X , Y , Z ⟧) ∪ [ D Z ]
          Σ₂ = concat (drop 1 αs)
          Σ₃ = concat βs
        in
          ∀ (γ : (Σ₁ ∪ Σ₂ ∪ Σ₃) ∗) →
            ∀ Nᵢ → Nᵢ ∈ αβs →
              reduce (forget γ ◇ Nᵢ) ≢ ε

    -- ** a characterization of secure protocols
    Symbol = Op; Word = Ops

    lt : Word → Set⟨ Symbol ⟩
    lt = fromList

    _-balanced-wrt-_ : Word → Part → Type
    π -balanced-wrt- A = D A ∈ˢ lt π → E A ∈ˢ lt π

    postulate
      Lemma1 :
        ∀ (Z : Part) →
        let Σ₁ = (E <$> ⟦ X , Y , Z ⟧) ∪ [ D Z ]
            Σ₂ = concat (drop 1 αs)
            Σ₃ = concat βs
        in ∀ (η : (Σ₁ ∪ Σ₂ ∪ Σ₃) ∗) →
                (_≢ Z) ⊆¹ (reduce (forget η) -balanced-wrt-_)

    Balanced : Type
    Balanced = All (_-balanced-wrt- X) (drop 1 $ lefts run)
             × All (_-balanced-wrt- Y) (rights run)

    postulate -- ** Theorem 1
      Balanced⇔Secure :
        ∙ lt (concat $ take 1 αs) ∩ lt ⟦ E X , E Y ⟧ ≉ ∅
        ∙ Balanced
          ════════════════════════════════════════════════════
          Secure

  open 𝟚-cascade public

  private
    𝟚-example : 𝟚-cascade
    𝟚-example = λ where
      .series → (E Y , 𝟙) ∷ (D X , 𝟚) ∷ []
             ⟨∷ (E X , 𝟘) ∷ (D Y , 𝟚) ∷ (E X , 𝟘) ∷ (E X , 𝟘) ∷ (D Y , 𝟚) ∷ []
             ∷⟩ []
      .reduced → ( (λ where refl → ⊥-elim $ X≢Y refl)
                 ∷ [-])
               ∷ ( (λ where refl → ⊥-elim $ X≢Y refl)
                 ∷ (λ where refl → ⊥-elim $ X≢Y refl)
                 ∷ (λ ())
                 ∷ (λ where refl → ⊥-elim $ X≢Y refl)
                 ∷ [-])
               ∷ []

    _ = run 𝟚-example
      ≡ (  ⟦ E Y , D X ⟧
        ⟨∷ ⟦ E X , D Y , E X , E X , D Y ⟧
        ∷⟩ [])
      ∋ refl

-- ** TODO: Name-stamp protocols

-- ** TODO: Decision procedure for checking protocal security
