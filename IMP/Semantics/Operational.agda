open import Relation.Nullary using (yes; no)

open import Relation.Binary using (Decidable; Rel)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂)
  
open import Function using (_$_)

open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_; [_,_])
open import Data.Product using (_×_; _,_)

open import Data.Integer as Int using (ℤ)
open import Data.Bool using (Bool; true; false)

module IMP.Semantics.Operational {Loc : Set} (_loc≟_ : Decidable {A = Loc} _≡_) where

open import IMP.Syntax Loc

_≰_ : Rel ℤ _
x ≰ y = Relation.Nullary.¬ x Int.≤ y

data a⟨_,_⟩⟶_ : Aexp → Ctx → ℤ → Set where
  num : ∀ {σ}
      → (n : ℤ)
      → a⟨ lit n , σ ⟩⟶ n
      
  loc : ∀ {σ}
      → (X : Loc)
      → a⟨ loc X , σ ⟩⟶ σ X
      
  sum : ∀ {a₀ a₁ n₀ n₁ σ}
      → (⟶₀ : a⟨ a₀ , σ ⟩⟶ n₀)
      → (⟶₁ : a⟨ a₁ , σ ⟩⟶ n₁)
      → a⟨ a₀ + a₁ , σ ⟩⟶ (n₀ Int.+ n₁)
      
  dif : ∀ {a₀ a₁ n₀ n₁ σ}
      → (⟶₀ : a⟨ a₀ , σ ⟩⟶ n₀)
      → (⟶₁ : a⟨ a₁ , σ ⟩⟶ n₁)
      → a⟨ a₀ - a₁ , σ ⟩⟶ (n₀ Int.- n₁)
      
  mul : ∀ {a₀ a₁ n₀ n₁ σ}
      → (⟶₀ : a⟨ a₀ , σ ⟩⟶ n₀)
      → (⟶₁ : a⟨ a₁ , σ ⟩⟶ n₁)
      → a⟨ a₀ * a₁ , σ ⟩⟶ (n₀ Int.* n₁)

data b⟨_,_⟩⟶_ : Bexp → Ctx → Bool → Set where
  lit : ∀ {σ} b → b⟨ lit b , σ ⟩⟶ b
  
  ∧-t : ∀ {b₀ b₁ σ}
      → b⟨ b₀ , σ ⟩⟶ true × b⟨ b₁ , σ ⟩⟶ true
      → b⟨ b₀ ∧ b₁ , σ ⟩⟶ true
  ∧-f : ∀ {b₀ b₁ σ}
      → b⟨ b₀ , σ ⟩⟶ false ⊎ b⟨ b₁ , σ ⟩⟶ false
      → b⟨ b₀ ∧ b₁ , σ ⟩⟶ false
         
  ∨-t : ∀ {b₀ b₁ σ}
      → b⟨ b₀ , σ ⟩⟶ true ⊎ b⟨ b₁ , σ ⟩⟶ true
      → b⟨ b₀ ∨ b₁ , σ ⟩⟶ true
  ∨-f : ∀ {b₀ b₁ σ}
      → b⟨ b₀ , σ ⟩⟶ false × b⟨ b₁ , σ ⟩⟶ false
      → b⟨ b₀ ∨ b₁ , σ ⟩⟶ false
       
  ==-t : ∀ {a₀ a₁ n₀ n₁ σ}
       → (⟶₀ : a⟨ a₀ , σ ⟩⟶ n₀)
       → (⟶₁ : a⟨ a₁ , σ ⟩⟶ n₁)
       → (n₀≡n₁ : n₀ ≡ n₁)
       → b⟨ a₀ == a₁ , σ ⟩⟶ true
  ==-f : ∀ {a₀ a₁ n₀ n₁ σ}
       → (⟶₀ : a⟨ a₀ , σ ⟩⟶ n₀)
       → (⟶₁ : a⟨ a₁ , σ ⟩⟶ n₁)
       → (n₀≢n₁ : n₀ ≢ n₁)
       → b⟨ a₀ == a₁ , σ ⟩⟶ false
     
  ≤-t : ∀ {a₀ a₁ n₀ n₁ σ}
      → (a⟶n₀ : a⟨ a₀ , σ ⟩⟶ n₀)
      → (a⟶n₁ : a⟨ a₁ , σ ⟩⟶ n₁)
      → (n₀≤n₁ : n₀ Int.≤ n₁)
      → b⟨ a₀ ≤ a₁ , σ ⟩⟶ true
  ≤-f : ∀ {a₀ a₁ n₀ n₁ σ}
      → (a⟶n₀ : a⟨ a₀ , σ ⟩⟶ n₀)
      → (a⟶n₁ : a⟨ a₁ , σ ⟩⟶ n₁)
      → (n₀≰n₁ : n₀ ≰ n₁)
      → b⟨ a₀ ≤ a₁ , σ ⟩⟶ false
       
  ¬-t : ∀ {σ b}
      → b⟨   b , σ ⟩⟶ false
      → b⟨ ¬ b , σ ⟩⟶ true
  ¬-f : ∀ {σ b}
      → b⟨   b , σ ⟩⟶ true
      → b⟨ ¬ b , σ ⟩⟶ false
      
extend : ∀ {n} → Loc → (a : Aexp) → (σ : Ctx) → a⟨ a , σ ⟩⟶ n → Ctx
extend {n} l a σ p x with x loc≟ l
... | yes x≡l = n
... | no  x≢l = σ x

data c⟨_,_⟩⟶_ : Com → Ctx → Ctx → Set where
  skip : (σ : Ctx) → c⟨ skip , σ ⟩⟶ σ

  assign : ∀ {a n σ}
         → (l : Loc)
         → (a⟶n : a⟨ a , σ ⟩⟶ n)
         → c⟨ l := a , σ ⟩⟶ extend l a σ a⟶n
  
  then : ∀ {c₀ c₁ σ σ′ σ″}
       → (⟶₀ : c⟨ c₀ , σ ⟩⟶ σ′)
       → (⟶₁ : c⟨ c₁ , σ′ ⟩⟶ σ″)
       → c⟨ c₀ >> c₁ , σ ⟩⟶ σ″

  if-t : ∀ {b tt ff σ σ′ }
       → (b⟶true : b⟨ b , σ ⟩⟶ true)
       → (tt⟶σ′ : c⟨ tt , σ ⟩⟶ σ′)
       → c⟨ if b then tt else ff , σ ⟩⟶ σ′
  if-f : ∀ {b tt ff σ σ′}
       → (b⟶false : b⟨ b , σ ⟩⟶ false)
       → (ff⟶σ′ : c⟨ ff , σ ⟩⟶ σ′)
       → c⟨ if b then tt else ff , σ ⟩⟶ σ′       

  while-t : ∀ {b c σ σ′ σ″}
          → (b⟶true : b⟨ b , σ ⟩⟶ true)
          → (c⟶σ : c⟨ c , σ ⟩⟶ σ′)
          → (loop : c⟨ while b do c , σ′ ⟩⟶ σ″)
          → c⟨ while b do c , σ  ⟩⟶ σ″
  while-f : ∀ {b c σ}
          → (b⟶false : b⟨ b , σ ⟩⟶ false)
          → c⟨ while b do c , σ  ⟩⟶ σ

data ⟨_,_⟩⟶_ : Term → Ctx → Value → Set where
  aexp : ∀ {a σ n}  → (a⟶n  : a⟨ a , σ ⟩⟶ n ) → ⟨ aexp a , σ ⟩⟶ aval n
  bexp : ∀ {b σ t}  → (b⟶t  : b⟨ b , σ ⟩⟶ t ) → ⟨ bexp b , σ ⟩⟶ bval t
  com  : ∀ {c σ σ′} → (c⟶σ′ : c⟨ c , σ ⟩⟶ σ′) → ⟨ com  c , σ ⟩⟶ ctx  σ′

Aexp-confluence : ∀ {σ r r′}
                → (a : Aexp) → a⟨ a , σ ⟩⟶ r → a⟨ a , σ ⟩⟶ r′ → r ≡ r′
Aexp-confluence (lit n) (num .n) (num .n) = refl
Aexp-confluence (loc X) (loc .X) (loc .X) = refl
Aexp-confluence (a₀ + a₁) (sum ⟶₀ ⟶₁) (sum ⟶₀′ ⟶₁′)
  = cong₂ Int._+_ (Aexp-confluence a₀ ⟶₀ ⟶₀′) (Aexp-confluence a₁ ⟶₁ ⟶₁′)
Aexp-confluence (a₀ - a₁) (dif ⟶₀ ⟶₁) (dif ⟶₀′ ⟶₁′)
  = cong₂ Int._-_ (Aexp-confluence a₀ ⟶₀ ⟶₀′) (Aexp-confluence a₁ ⟶₁ ⟶₁′)
Aexp-confluence (a₀ * a₁) (mul ⟶₀ ⟶₁) (mul ⟶₀′ ⟶₁′)
  = cong₂ Int._*_ (Aexp-confluence a₀ ⟶₀ ⟶₀′) (Aexp-confluence a₁ ⟶₁ ⟶₁′)

Bexp-confluence : ∀ {σ r r′}
                → (b : Bexp) → b⟨ b , σ ⟩⟶ r → b⟨ b , σ ⟩⟶ r′ → r ≡ r′
Bexp-confluence (lit t) (lit .t) (lit .t) = refl
Bexp-confluence (_ ∧ _) (∧-t _) (∧-t _) = refl
Bexp-confluence (b₀ ∧ b₁) (∧-t (⟶₀ , ⟶₁)) (∧-f x)
  = [ Bexp-confluence b₀ ⟶₀ , Bexp-confluence b₁ ⟶₁ ] x
Bexp-confluence (b₀ ∧ b₁) (∧-f x) (∧-t (⟶₀′ , ⟶₁′))
  = sym $ [ Bexp-confluence b₀ ⟶₀′ , Bexp-confluence b₁ ⟶₁′ ] x
Bexp-confluence (_ ∧ _) (∧-f _) (∧-f _) = refl
Bexp-confluence (_ ∨ _) (∨-t _) (∨-t _) = refl
Bexp-confluence (b₀ ∨ b₁) (∨-t x) (∨-f (⟶₀′ , ⟶₁′))
  = sym $ [ Bexp-confluence b₀ ⟶₀′ , Bexp-confluence b₁ ⟶₁′ ] x
Bexp-confluence (b₀ ∨ b₁) (∨-f (⟶₀ , ⟶₁)) (∨-t x)
  = [ Bexp-confluence b₀ ⟶₀ , Bexp-confluence b₁ ⟶₁ ] x
Bexp-confluence (_ ∨ _) (∨-f _) (∨-f _) = refl
Bexp-confluence (_ == _) (==-t _ _ _) (==-t _ _ _) = refl
Bexp-confluence (a₀ == a₁) (==-t ⟶₀ ⟶₁ n₀≡n₁) (==-f ⟶₀′ ⟶₁′ n₀′≢n₁′)
  rewrite Aexp-confluence a₀ ⟶₀ ⟶₀′ | Aexp-confluence a₁ ⟶₁ ⟶₁′
    = ⊥-elim (n₀′≢n₁′ n₀≡n₁)
Bexp-confluence (a₀ == a₁) (==-f ⟶₀ ⟶₁ n₀≢n₁) (==-t ⟶₀′ ⟶₁′ n₀′≡n₁′)
  rewrite Aexp-confluence a₀ ⟶₀ ⟶₀′ | Aexp-confluence a₁ ⟶₁ ⟶₁′
    = ⊥-elim (n₀≢n₁ n₀′≡n₁′)
Bexp-confluence (_ == _) (==-f _ _ _) (==-f _ _ _) = refl
Bexp-confluence (_ ≤ _) (≤-t _ _ _) (≤-t _ _ _) = refl
Bexp-confluence (a₀ ≤ a₁) (≤-t ⟶₀ ⟶₁ n₀≤n₁) (≤-f ⟶₀′ ⟶₁′ n₀′≰n₁′)
  rewrite Aexp-confluence a₀ ⟶₀ ⟶₀′ | Aexp-confluence a₁ ⟶₁ ⟶₁′
    = ⊥-elim (n₀′≰n₁′ n₀≤n₁)
Bexp-confluence (a₀ ≤ a₁) (≤-f ⟶₀ ⟶₁ n₀≰n₁) (≤-t ⟶₀′ ⟶₁′ n₀′≤n₁′)
  rewrite Aexp-confluence a₀ ⟶₀ ⟶₀′ | Aexp-confluence a₁ ⟶₁ ⟶₁′
    = ⊥-elim(n₀≰n₁ n₀′≤n₁′)
Bexp-confluence (_ ≤ _) (≤-f _ _ _) (≤-f _ _ _) = refl
Bexp-confluence (¬ _) (¬-t _) (¬-t _) = refl
Bexp-confluence (¬ b) (¬-t ⟶) (¬-f ⟶′) = Bexp-confluence b ⟶′ ⟶
Bexp-confluence (¬ b) (¬-f ⟶) (¬-t ⟶′) = Bexp-confluence b ⟶′ ⟶
Bexp-confluence (¬ _) (¬-f _) (¬-f _) = refl

Com-confluence : ∀ {σ r r′}
               → (c : Com) → c⟨ c , σ ⟩⟶ r → c⟨ c , σ ⟩⟶ r′ → r ≡ r′
Com-confluence skip (skip r) (skip .r) = refl
Com-confluence (X := a) (assign .X a⟶n) (assign .X a⟶n′)
  with Aexp-confluence a a⟶n a⟶n′
... | refl = refl
Com-confluence (c₀ >> c₁) (then ⟶₀ ⟶₁) (then ⟶₀′ ⟶₁′)
  rewrite Com-confluence c₀ ⟶₀ ⟶₀′ = Com-confluence c₁ ⟶₁ ⟶₁′
Com-confluence (if _ then tt else _) (if-t _ ⟶) (if-t _ ⟶′)
  = Com-confluence tt ⟶ ⟶′ 
Com-confluence (if b then _ else _) (if-t b⟶true _) (if-f b⟶false _)
  with Bexp-confluence b b⟶true b⟶false
... | ()
Com-confluence (if b then _ else _) (if-f b⟶false _) (if-t b⟶true _)
  with Bexp-confluence b b⟶true b⟶false
... | ()
Com-confluence (if _ then _ else ff) (if-f _ ⟶) (if-f _ ⟶′)
  = Com-confluence ff ⟶ ⟶′
Com-confluence (while b do c) (while-t b⟶true ⟶ loop) (while-t b⟶true′ ⟶′ loop′)
  rewrite Com-confluence c ⟶ ⟶′ = Com-confluence (while b do c) loop loop′
Com-confluence (while b do _) (while-t b⟶true _ _) (while-f b⟶false)
  with Bexp-confluence b b⟶true b⟶false
... | ()
Com-confluence (while b do c) (while-f b⟶false) (while-t b⟶true ⟶′ loop′)
  with Bexp-confluence b b⟶true b⟶false
... | ()
Com-confluence (while _ do _) (while-f _) (while-f _) = refl

confluence : ∀ {σ r r′} (e : Term) → ⟨ e , σ ⟩⟶ r → ⟨ e , σ ⟩⟶ r′ → r ≡ r′
confluence (aexp a) (aexp a⟶n) (aexp a⟶n′)
  = cong aval (Aexp-confluence a a⟶n a⟶n′)
confluence (bexp b) (bexp b⟶t) (bexp b⟶t′)
  = cong bval (Bexp-confluence b b⟶t b⟶t′)
confluence (com c) (com c⟶σ′) (com c⟶σ″)
  = cong ctx (Com-confluence c c⟶σ′ c⟶σ″)
