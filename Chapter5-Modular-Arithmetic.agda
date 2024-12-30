module Chapter5-Modular-Arithmetic where 

open import Data.Bool 
  using (Bool; false)

open import Data.Nat 
  using (ℕ; suc; _+_; _*_; _≤_; z≤n; s≤s)

open import Data.Nat.Properties 
  using (+-assoc; *-distribʳ-+; *-comm; +-comm; +-identityʳ; +-suc; suc-injective)


open import Agda.Primitive
  using (Level)

open import Relation.Binary 
  using (Rel; IsEquivalence; Reflexive; Symmetric; Transitive; IsPreorder)

-- open import Relation.Binary.Structures using (IsPreorder)


open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; isPreorder; sym; cong)

import Relation.Binary.PropositionalEquality.Properties as PropEqProp 

import Relation.Binary.Reasoning.Setoid as RelReasoning


-- 5.1 Instance Arguments
module Playground-Instances where
  open PropEq

  default : {ℓ : Level} {A : Set ℓ} → ⦃ a : A ⦄ → A 
  default ⦃ val ⦄ = val 

  private instance 
    default-ℕ : ℕ 
    default-ℕ = 0

    default-Bool : Bool 
    default-Bool = false 

  _ : default ≡ 0
  _ = PropEq.refl

  _ : default ≡ false 
  _ = PropEq.refl

  private instance
    find-z≤n : {n : ℕ} → 0 ≤ n
    find-z≤n = z≤n

    find-s≤n : {m n : ℕ} → ⦃ m ≤ n ⦄ → suc m ≤ suc n
    find-s≤n ⦃ m≤n ⦄ = s≤s m≤n

  _ : 10 ≤ 20
  _ = default

module Playground-Instances₂ where

  record HasDefault {ℓ : Level} (A : Set ℓ) : Set ℓ where
    constructor default-of
    field
      the-default : A

  default : {ℓ : Level} {A : Set ℓ} → ⦃ HasDefault A ⦄ → A
  default ⦃ default-of val ⦄ = val

  private instance 
    _ = default-of 0 
    _ = default-of false 

  data Color : Set where
    red green blue : Color

  private instance
    _ = green

  -- _ : Color 
  -- _ = default 

  open HasDefault ⦃ ... ⦄

  -- the-default : {ℓ : Level} {A : Set ℓ} → ⦃ HasDefault A ⦄ → A
  -- the-default ⦃ x ⦄ = x .HasDefault.the-default

-- instance
--   equiv-to-preorder
--     : {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} {_~_ : Rel A ℓ₂}
--     → ⦃ IsEquivalence _~_ ⦄
--     → IsPreorder _~_
--   equiv-to-preorder = isPreorder

--   ≡-is-equivalence = ≡-equiv


-- 5.2 The Ring of Natural Numbers Modulo N 

module ℕ/nℕ (n : ℕ) where 

  record _≈_ (a b : ℕ) : Set where
    constructor ≈-mod
    field
      x y : ℕ
      is-mod : a + x * n ≡ b + y * n

  infix 4 _≈_

  ≈-refl : Reflexive _≈_
  ≈-refl = ≈-mod 0 0 PropEq.refl

  ≈-sym : Symmetric _≈_
  ≈-sym (≈-mod x y p) = ≈-mod y x (PropEq.sym p)

-- 5.3 Deriving Transitivity 

  lemma₁ : (a x z : ℕ) → a + (x + z) * n ≡ (a + x * n) + z * n
  lemma₁ a x z = begin
    a + (x + z) * n ≡⟨ cong (a +_) (*-distribʳ-+ n x z) ⟩
    a + (x * n + z * n) ≡⟨ sym (+-assoc a _ _) ⟩
    (a + x * n) + z * n ∎
    where open PropEqProp.≡-Reasoning
    
  lemma₂ : (i j k : ℕ) → (i + j) + k ≡ (i + k) + j
  lemma₂ i j k = begin
    (i + j) + k ≡⟨ +-assoc i j k ⟩
    i + (j + k) ≡⟨ cong (i +_) (+-comm j k) ⟩
    i + (k + j) ≡⟨ sym (+-assoc i k j) ⟩
    (i + k) + j ∎
    where open PropEqProp.≡-Reasoning

  ≈-trans : Transitive _≈_
  ≈-trans {a} {b} {c} (≈-mod x y pxy) (≈-mod z w pzw) =
    ≈-mod (x + z) (w + y)
    ( begin
      a + (x + z) * n ≡⟨ lemma₁ a x z ⟩
      (a + x * n) + z * n ≡⟨ cong (_+ z * n) pxy ⟩
      (b + y * n) + z * n ≡⟨ lemma₂ b (y * n) (z * n) ⟩
      (b + z * n) + y * n ≡⟨ cong (_+ y * n) pzw ⟩
      c + w * n + y * n ≡⟨ sym (lemma₁ c w y) ⟩
      c + (w + y) * n ∎
    )
    where open PropEqProp.≡-Reasoning

  ≈-equiv : IsEquivalence _≈_
  IsEquivalence.refl ≈-equiv = ≈-refl
  IsEquivalence.sym ≈-equiv = ≈-sym
  IsEquivalence.trans ≈-equiv = ≈-trans

  
-- 5.4 Congruence of Addition 

  0≈n : 0 ≈ n
  0≈n = ≈-mod 1 0 _≡_.refl

  suc-cong-mod : {a b : ℕ} → a ≈ b → suc a ≈ suc b
  suc-cong-mod (≈-mod x y p) = ≈-mod x y (cong suc p)

  +-zero-mod : (a b : ℕ) → a ≈ 0 → a + b ≈ b
  +-zero-mod a zero a≈0 = begin
    a + zero ≡⟨ +-identityʳ a ⟩
    a ≈⟨ a≈0 ⟩
    zero ∎
    where open RelReasoning
  +-zero-mod a (suc b) a≈0 = begin
    a + suc b ≡⟨ +-suc a b ⟩
    suc a + b ≡⟨⟩
    suc (a + b) ≈⟨ suc-cong-mod (+-zero-mod a b a≈0) ⟩
    suc b ∎
    where open RelReasoning

  suc-injective-mod : {a b : ℕ} → suc a ≈ suc b → a ≈ b
  suc-injective-mod (≈-mod x y p) = ≈-mod x y (suc-injective p)

  +-cong₂-mod : {a b c d : ℕ}
    → a ≈ b → c ≈ d
    → a + c ≈ b + d
  +-cong₂-mod {zero} {b} {c} {d} pab pcd = begin
    c ≈⟨ pcd ⟩
    d ≈⟨ sym (+-zero-mod b d (sym pab)) ⟩
    b + d ∎
    where open RelReasoning
  +-cong₂-mod {suc a} {zero} {c} {d} pab pcd = begin
    suc a + c ≈⟨ +-zero-mod (suc a) c pab ⟩
    c ≈⟨ pcd ⟩
    d ∎
    where open RelReasoning
  +-cong₂-mod {suc _} {suc _} pab pcd =
    suc-cong-mod (+-cong₂-mod (suc-injective-mod pab) pcd)

-- 5.5 Congruence of Multiplication 
  *-zero-mod : (a b : ℕ) → b ≈ 0 → a * b ≈ 0
  *-zero-mod zero b x = _≡_.refl
  *-zero-mod (suc a) b x = begin
    suc a * b ≡⟨⟩
    b + a * b ≈⟨ +-cong₂-mod x (*-zero-mod a b x) ⟩
    0 ∎
    where open RelReasoning

  *-cong₂-mod : {a b c d : ℕ} → a ≈ b → c ≈ d → a * c ≈ b * d
  *-cong₂-mod {zero} {b} {c} {d} a=b c=d = begin
    zero * c ≡⟨⟩
    zero ≈⟨ sym (*-zero-mod d b (sym a=b)) ⟩
    d * b ≡⟨ *-comm d b ⟩
    b * d ∎
    where open RelReasoning
  *-cong₂-mod {suc a} {zero} {c} {d} a=b c=d = begin
    suc a * c ≡⟨ *-comm (suc a) c ⟩
    c * suc a ≈⟨ *-zero-mod c (suc a) a=b ⟩
    zero ≡⟨⟩
    zero * d ∎
    where open RelReasoning
  *-cong₂-mod {suc a} {suc b} {c} {d} a=b c=d = begin
    suc a * c ≡⟨⟩
    c + a * c ≈⟨ +-cong₂-mod c=d
    (*-cong₂-mod (suc-injective-mod a=b) c=d)⟩
    d + b * d ≡⟨⟩
    suc b * d ∎
    where open RelReasoning

