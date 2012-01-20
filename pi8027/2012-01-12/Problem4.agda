
-- 離散構造 第二章「集合」 演習問題4

module Problem4 where

open import Level
open import Function
open import Data.Sum
open import Data.Product
open import Relation.Binary
open import Relation.Unary
open import Relation.Nullary

complement : ∀ {ℓ} {U : Set ℓ} → Pred U ℓ → Pred U ℓ
complement A a = ¬ A a

_-_ : ∀ {ℓ} {U : Set ℓ} → (A B : Pred U ℓ) → Pred U ℓ
A - B = A ∩ complement B

_▵_ : ∀ {ℓ} {U : Set ℓ} → (A B : Pred U ℓ) → Pred U ℓ
A ▵ B = (A - B) ∪ (B - A)

_▵′_ : ∀ {ℓ} {U : Set ℓ} → (A B : Pred U ℓ) → Pred U ℓ
A ▵′ B = (A ∩ complement B) ∪ (complement A ∩ B)

_≡P_ : ∀ {ℓ} {U : Set ℓ} → (A B : Pred U ℓ) → Set _
A ≡P B = A ⊆ B × B ⊆ A

≡Prefl : ∀ {c} {U : Set c} → Reflexive (_≡P_ {c} {U})
≡Prefl = id , id

≡Psym : ∀ {c} {U : Set c} → Symmetric (_≡P_ {c} {U})
≡Psym (p1 , p2) = p2 , p1

≡Ptrans : ∀ {c} {U : Set c} → Transitive (_≡P_ {c} {U})
≡Ptrans (p1 , p2) (p3 , p4) = (p3 ∘ p1) , (p2 ∘ p4)

≡PisEquivalence : ∀ {c} {U : Set c} → IsEquivalence (_≡P_ {c} {U})
≡PisEquivalence {c} {U} = record
  { refl = id , id
  ; sym = ≡Psym
  ; trans = ≡Ptrans
  }

PredSetoid : ∀ {c} → Set c → Setoid (suc c) c
PredSetoid {c} U = record
  { Carrier = Pred U c
  ; _≈_ = _≡P_
  ; isEquivalence = ≡PisEquivalence
  }

Lemma1 : ∀ {ℓ} {U : Set ℓ} → (A B : Pred U ℓ) → (A ▵ B) ≡P (A ▵′ B)
Lemma1 A B = f1 , f2 where
  f1 : A ▵ B ⊆ A ▵′ B
  f1 (inj₁ p) = inj₁ p
  f1 (inj₂ p) = inj₂ (proj₂ p , proj₁ p)
  f2 : A ▵′ B ⊆ A ▵ B
  f2 (inj₁ p) = inj₁ p
  f2 (inj₂ p) = inj₂ (proj₂ p , proj₁ p)

Lemma2 : ∀ {ℓ} {U : Set ℓ} → (A B : Pred U ℓ) → (A ▵ B) ≡P ((A ∪ B) - (A ∩ B))
Lemma2 A B = f1 , f2 where
  f1 : A ▵ B ⊆ (A ∪ B) - (A ∩ B)
  f1 (inj₁ (p1 , p2)) = inj₁ p1 , p2 ∘ proj₂
  f1 (inj₂ (p1 , p2)) = inj₂ p1 , p2 ∘ proj₁
  f2 : (A ∪ B) - (A ∩ B) ⊆ A ▵ B
  f2 (inj₁ p1 , p2) = inj₁ (p1 , p2 ∘ _,_ p1)
  f2 (inj₂ p1 , p2) = inj₂ (p1 , p2 ∘ flip _,_ p1)

Lemma3 : ∀ {ℓ} {U : Set ℓ} → (A B C : Pred U ℓ) → (A ∩ (B ▵ C)) ≡P ((A ∩ B) ▵ (A ∩ C))
Lemma3 A B C = f1 , f2 where
  f1 : A ∩ (B ▵ C) ⊆ (A ∩ B) ▵ (A ∩ C)
  f1 (p1 , inj₁ (p2 , p3)) = inj₁ ((p1 , p2) , p3 ∘ proj₂)
  f1 (p1 , inj₂ (p2 , p3)) = inj₂ ((p1 , p2) , p3 ∘ proj₂)
  f2 : (A ∩ B) ▵ (A ∩ C) ⊆ A ∩ (B ▵ C)
  f2 (inj₁ ((p1 , p2) , p3)) = p1 , inj₁ (p2 , p3 ∘ _,_ p1)
  f2 (inj₂ ((p1 , p2) , p3)) = p1 , inj₂ (p2 , p3 ∘ _,_ p1)

