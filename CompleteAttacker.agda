module CompleteAttacker where

open import Prelude.Init; open SetAsType
open L.Mem
open import Prelude.Nary
open import Prelude.Monoid

-- ** shorthands
pattern 𝟘 = here refl

-- ** pure syntax

data Sort : Type where
  bool message : Sort

Sorts = List Sort

𝑆 : Sorts
𝑆 = ⟦ bool , message ⟧

Symbol = String
Symbols = List Symbol

record SymbolTy : Type where
  field args : Sorts
        ret  : Sort
open SymbolTy public

private variable f : Symbol

record 𝐹 : Type where
  field symbols : Symbols
        type    : f ∈ symbols → SymbolTy

  arity : f ∈ symbols → ℕ
  arity = length ∘ args ∘ type

open 𝐹 public

instance
  Semigroup-𝐹 : Semigroup 𝐹
  Semigroup-𝐹 ._◇_ sig sig′ = λ where
    .symbols → sig .symbols ◇ sig′ .symbols
    .type    f∈ → case ∈-++⁻ _ f∈ of λ where
      (inj₁ f∈) → sig  .type f∈
      (inj₂ f∈) → sig′ .type f∈

  Monoid-𝐹 : Monoid 𝐹
  Monoid-𝐹 .ε = λ where
    .symbols → []
    .type ()

_∶_↦_ : String → Sorts → Sort → 𝐹
f ∶ as ↦ r = record
  { symbols = [ f ]
  ; type = λ where 𝟘 → record {args = as; ret = r}
  }

_∶↦_ : String → Sort → 𝐹
f ∶↦ r = f ∶ [] ↦ r

Base𝐹 : 𝐹
Base𝐹
  = "true"  ∶↦ message
  ◇ "false" ∶↦ message
  ◇ "if_then_else_" ∶ ⟦ bool , message , message ⟧
                    ↦ message
  ◇ "∅" ∶↦ message
  ◇ "EQ(_)" ∶ ⟦ message , message ⟧ ↦ bool
  ◇ "EQL(_)" ∶ ⟦ message , message ⟧ ↦ bool

-- ** Example 4

PrivateAuth : 𝐹
PrivateAuth
  = Base𝐹
  ◇ "{_}⁻_＿_" ∶ ⟦ message , message , message ⟧
              ↦ message
  ◇ "dec(_,_)" ∶ ⟦ message , message ⟧ ↦ message
  ◇ "k(_)" ∶ ⟦ message ⟧ ↦ message
  ◇ "pk(_)" ∶ ⟦ message ⟧ ↦ message
  ◇ "sk(_)" ∶ ⟦ message ⟧ ↦ message
  ◇ "⟨_,_⟩" ∶ ⟦ message , message ⟧ ↦ message
  ◇ "π₁(_)" ∶ ⟦ message ⟧ ↦ message
  ◇ "π₂(_)" ∶ ⟦ message ⟧ ↦ message


-- ** Example 5
