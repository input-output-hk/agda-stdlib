------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of unique lists (setoid equality) using K
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Data.List.Relation.Unary.Unique.Propositional.Properties.WithK where

open import Data.Empty
open import Data.List.Membership.Propositional
open import Data.List.Relation.Binary.BagAndSetEquality
open import Data.List.Relation.Unary.All.Properties
open import Data.List.Relation.Unary.AllPairs
open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Unary.Unique.Propositional
open import Function.Equality
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- membership

module _ {a} {A : Set a} where

  unique⇒∈-prop : ∀ {l} → Unique l → (x : A) → isPropositional (x ∈ l)
  unique⇒∈-prop (hx ∷ h) x (here refl) (here refl) = refl
  unique⇒∈-prop (hx ∷ h) x (here refl) (there b)   = ⊥-elim (All¬⇒¬Any hx b)
  unique⇒∈-prop (hx ∷ h) x (there a)   (here refl) = ⊥-elim (All¬⇒¬Any hx a)
  unique⇒∈-prop (hx ∷ h) x (there a)   (there b) rewrite unique⇒∈-prop h x a b = refl

  unique∧set⇒bag : ∀ {l l'} → Unique l → Unique l' → l ∼[ set ] l' → l ∼[ bag ] l'
  unique∧set⇒bag h h' eq {a} with eq {a}
  ... | record { to = to ; from = from } = record
    { to         = to
    ; from       = from
    ; inverse-of = record
      { left-inverse-of  = λ x → unique⇒∈-prop h a (from ⟨$⟩ (to ⟨$⟩ x)) x
      ; right-inverse-of = λ x → unique⇒∈-prop h' a (to ⟨$⟩ (from ⟨$⟩ x)) x } }
