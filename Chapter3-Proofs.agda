module Chapter3-Proofs where 
  
open import Agda.Builtin.Bool
  using (Bool; true; false)
  
_∨_ : Bool → Bool → Bool 
false ∨ y = y
true ∨ y = true

_∧_ : Bool → Bool → Bool 
false ∧ y = false 
true ∧ y = y

not : Bool → Bool 
not true = false 
not false = true 

open import Agda.Builtin.Nat as Nat 
  using (Nat; zero; suc; _+_; _*_)

one : Nat 
one = suc zero 

two : Nat 
two = suc one 

_^_ : Nat → Nat → Nat 
x ^ zero = suc zero 
x ^ (suc y) = x * (x ^ y)

module Example-ProofsAsPrograms where 

  data IsEven : Nat → Set where 
    zero-even : IsEven zero 
    suc-suc-even : {n : Nat} → IsEven n → IsEven (suc (suc n))
  
  zero-is-even : IsEven zero 
  zero-is-even = zero-even

  one-is-even : IsEven (suc zero)
  one-is-even = {!   !}

module Definition where 
  
  data _≡_ {A : Set} : A → A → Set where  
    refl :  {x : A} → x ≡ x

  infix 4 _≡_

module Playground where 
  open import Agda.Builtin.Equality 
    using (_≡_; refl)

  _ : suc (suc (suc zero)) ≡ suc (suc (suc zero))
  _ = refl


  0+x≡x : (x : Nat) → zero + x ≡ x 
  0+x≡x _ = refl

  -- x+0≡x : (x : Nat) → x + zero ≡ x
  -- x+0≡x zero = refl 
  -- x+0≡x (suc x) = {!   !}


  -- 3.5 Congruence
  cong : {A B : Set} → {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y 
  cong f refl = refl

  x+0≡x : (x : Nat) → x + zero ≡ x
  x+0≡x zero = refl 
  x+0≡x (suc x) = cong suc (x+0≡x x)

  -- 3.6 Identity and Zero Elements
  +-identityˡ : (x : Nat) → zero + x ≡ x 
  +-identityˡ = 0+x≡x
  
  +-identityʳ : (x : Nat) → x + zero ≡ x 
  +-identityʳ = x+0≡x

  --Exercise 
  *-identityˡ : (x : Nat) → (suc zero) * x ≡ x
  *-identityˡ zero = refl
  *-identityˡ (suc x) = cong suc (*-identityˡ x)

  *-identityʳ : (x : Nat) → x * (suc zero) ≡ x
  *-identityʳ zero = refl
  *-identityʳ (suc x) = cong suc (*-identityʳ x)

  ^-identityʳ : (x : Nat) → x ^ (suc zero) ≡ x
  ^-identityʳ x = *-identityʳ x

  -- Bool identities
  ∨-identityˡ : (x : Bool) → false ∨ x ≡ x
  ∨-identityˡ _ = refl
  
  ∨-identityʳ : (x : Bool) → x ∨ false ≡ x
  ∨-identityʳ false = refl
  ∨-identityʳ true = refl

  -- annihilator 
  *-zeroˡ : (x : Nat) → zero * x ≡ zero
  *-zeroˡ _ = refl
  
  *-zeroʳ : (x : Nat) → x * zero ≡ zero
  *-zeroʳ zero = refl
  *-zeroʳ (suc x) = *-zeroʳ x

  -- Boolean annihilator 
  ∨-zeroˡ : (x : Bool) → true ∨ x ≡ true
  ∨-zeroˡ _ = refl
  
  ∨-zeroʳ : (x : Bool) → x ∨ true ≡ true
  ∨-zeroʳ false = refl
  ∨-zeroʳ true = refl 

  -- 3.7 Symmetry and Involutivity 
  sym : {A : Set} → {x y : A} → x ≡ y → y ≡ x
  sym refl = refl

  *-identityˡ′ : (x : Nat) → x ≡ 1 * x
  *-identityˡ′ x = sym (*-identityˡ x)

  sym-involutive : {A : Set} → {x y : A} → (p : x ≡ y) → sym (sym p) ≡ p
  sym-involutive refl = refl

  -- not-involutive : (x : Bool) → not (not x) ≡ x
  -- not-involutive false = refl
  -- not-involutive true = refl

  -- 3.8 Transitivity 
  trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  trans refl refl = refl

  a^1≡a+b*0 : (a b : Nat) → a ^ 1 ≡ a + (b * zero)
  a^1≡a+b*0 a b 
    = trans (^-identityʳ a) 
    (trans (sym (+-identityʳ a)) 
           (cong (a +_) (sym (*-zeroʳ b)))
    )

  -- 3.9 Mixfix Parsing 
  _! : Nat → Nat
  zero ! = 1
  (suc n) ! = (suc n) * (n !)

  ∣_ : Nat → Nat
  ∣_ = suc
  infixr 20 ∣_

  □ : Nat
  □ = zero
  
  five : Nat
  five = ∣ ∣ ∣ ∣ ∣ □

  postulate
    ℝ : Set
    π : ℝ
    ⌊_⌋ : ℝ → Nat
  
  three′ : Nat
  three′ = ⌊ π ⌋

  -- ternary operator 
  _‽_⦂_ : {A : Set} → Bool → A → A → A
  false ‽ t ⦂ f = f
  true ‽ t ⦂ f = t

  infixr 20 _‽_⦂_

  _ : Nat
  _ = not true ‽ 4 ⦂ 1

  -- if then else 
  if_then_else_ : {A : Set} → Bool → A → A → A
  if_then_else_ = _‽_⦂_
  infixr 20 if_then_else_

  _ : Nat
  _ = if not true then 4 else 1

  _ : Nat 
  _ = if not true then 4
    else if true then 1
    else 0

  -- case of 
  case_of_ : {A B : Set} → A → (A → B) → B
  case e of f = f e

  _ : Nat 
  _ = case not true of λ
    { false → 1
    ; true → 4
    }

  _is-equal-to_ : {A : Set} → A → A → Set
  x is-equal-to y = x ≡ y
  
  -- 3.10 Equational Reasoning
  module ≡-Reasoning where 
    _∎ : {A : Set} → (x : A) → x ≡ x
    _∎ x = refl
    infix 3 _∎

    _≡⟨⟩_ : {A : Set} {y : A}
        → (x : A)
        → x ≡ y
        → x ≡ y
    x ≡⟨⟩ p = p

    infixr 2 _≡⟨⟩_ 

    _ : 4 ≡ suc (one + two)
    _ =
      4 ≡⟨⟩
      (two + two ≡⟨⟩
      (suc one + two ≡⟨⟩
      (suc (one + two) ∎)))

    _≡⟨_⟩_
      : {A : Set}
      → (x : A)
      → {y z : A}
      → x ≡ y
      → y ≡ z
      → x ≡ z
    x ≡⟨ j ⟩ p = trans j p

    infixr 2 _≡⟨_⟩_

    begin_ : {A : Set} → {x y : A} → x ≡ y → x ≡ y
    begin_ x=y = x=y
    
    infix 1 begin_

  a^1≡a+b*0′ : (a b : Nat) → a ^ 1 ≡ a + b * 0
  a^1≡a+b*0′ a b =
    begin
      a ^ 1 ≡⟨ ^-identityʳ a ⟩
      a ≡⟨ sym (+-identityʳ a) ⟩
      a + 0 ≡⟨ cong (a +_) (sym (*-zeroʳ b)) ⟩
      a + b * 0 ∎
    where open ≡-Reasoning

  -- 3.11 Ergonomics, Associativity and Commutativity 
  ∨-assoc : (a b c : Bool) → (a ∨ b) ∨ c ≡ a ∨ (b ∨ c)
  ∨-assoc false b c = refl
  ∨-assoc true b c = refl

  ∧-assoc : (a b c : Bool) → (a ∧ b) ∧ c ≡ a ∧ (b ∧ c)
  ∧-assoc false b c = refl
  ∧-assoc true b c = refl 

  +-sucʳ : (x y : Nat) → x + suc y ≡ suc (x + y)
  +-sucʳ zero y = refl
  +-sucʳ (suc x) y = cong suc (+-sucʳ x y)

  +-sucˡ : (x y : Nat) → (suc x) + y ≡ suc (x + y)
  +-sucˡ x y = refl 

  +-comm : (x y : Nat) → x + y ≡ y + x
  +-comm zero y = sym (+-identityʳ y)
  +-comm (suc x) y = begin 
    suc (x + y) ≡⟨ cong suc (+-comm x y) ⟩  
    suc (y + x) ≡⟨ sym (+-sucʳ y x) ⟩
    y + suc x ∎ 
    where open ≡-Reasoning

  +-assoc : (x y z : Nat) → (x + y) + z ≡ x + (y + z)
  +-assoc zero y z = refl 
  +-assoc (suc x) y z = begin 
    (suc x + y) + z ≡⟨ cong (λ φ → φ + z) (+-sucˡ x y) ⟩
    suc (x + y) + z ≡⟨ +-sucˡ (x + y) z ⟩
    suc (x + y + z) ≡⟨ cong suc (+-assoc x y z) ⟩
    suc (x + (y + z)) ≡⟨ +-sucˡ x (y + z) ⟩ 
    suc x + (y + z) ∎  
    where open ≡-Reasoning 

  -- 3.12 Exercises in Proof 
  suc-injective : {x y : Nat} → suc x ≡ suc y → x ≡ y
  suc-injective refl = refl

  *-suc : (x y : Nat) → x * suc y ≡ x + x * y
  *-suc zero y = refl 
  *-suc (suc x) y = begin 
    suc (y + x * suc y) ≡⟨ cong (λ φ → suc (y + φ)) (*-suc x y) ⟩
    suc (y + (x + x * y)) ≡⟨ cong suc (sym (+-assoc y x (x * y))) ⟩ 
    suc ((y + x) + x * y) ≡⟨ cong (λ φ → suc (φ + x * y)) (+-comm y x) ⟩ 
    suc ((x + y) + x * y) ≡⟨ cong suc (+-assoc x y (x * y)) ⟩ 
    suc (x + (y + x * y)) ∎ 
    where open ≡-Reasoning

  *-comm : (x y : Nat) → x * y ≡ y * x
  *-comm zero y = sym (*-zeroʳ y) 
  *-comm (suc x) y = begin 
    y + x * y ≡⟨ cong (y +_) (*-comm x y) ⟩
    y + y * x ≡⟨ sym (*-suc y x) ⟩ 
    y * suc x ∎ 
    where open ≡-Reasoning

  -- *-distribʳ-+ : (x y z : Nat) → (y + z) * x ≡ y * x + z * x 
  -- *-distribʳ-+ zero y z = begin 
  --   (y + z) * zero ≡⟨ *-zeroʳ (y + z) ⟩ 
  --   zero ≡⟨ +-identityʳ zero ⟩
  --   zero + zero ≡⟨ cong (λ m → m + zero) (sym (*-zeroʳ y)) ⟩
  --   y * zero + zero ≡⟨ cong (y * zero +_) (sym (*-zeroʳ z)) ⟩   
  --   y * zero + z * zero ∎ 
  --   where open ≡-Reasoning
  -- *-distribʳ-+ (suc x) y z = begin 
  --   (y + z) * suc x ≡⟨ *-suc (y + z) x ⟩ 
  --   (y + z) + (y + z) * x ≡⟨ cong ((y + z) +_) (*-distribʳ-+ x y z) ⟩
  --   (y + z) + (y * x + z * x) ≡⟨ {!   !} ⟩ 
  --   y * suc x + z * suc x ∎ 
  --   where open ≡-Reasoning

  *-distribʳ-+ : (x y z : Nat) → (y + z) * x ≡ y * x + z * x 
  *-distribʳ-+ x zero z = refl 
  *-distribʳ-+ x (suc y) z = begin 
    x + (y + z) * x ≡⟨ cong (x +_) (*-distribʳ-+ x y z) ⟩
    x + (y * x + z * x) ≡⟨ sym (+-assoc x (y * x) (z * x)) ⟩  
    x + y * x + z * x ∎ 
    where open ≡-Reasoning

  *-distribˡ-+ : ( x y z : Nat ) → x * (y + z) ≡ x * y + x * z
  *-distribˡ-+ x y z = begin 
    x * (y + z) ≡⟨ *-comm x (y + z) ⟩
    (y + z) * x ≡⟨ *-distribʳ-+ x y z ⟩
    y * x + z * x ≡⟨ cong (λ φ → φ + z * x) (*-comm y x) ⟩
    x * y + z * x ≡⟨ cong (x * y +_) (*-comm z x) ⟩
    x * y + x * z ∎ 
    where open ≡-Reasoning

  *-assoc : (x y z : Nat) → (x * y) * z ≡ x * (y * z)
  *-assoc x y zero = 
    trans (*-zeroʳ (x * y)) 
          (trans (sym (*-zeroʳ x)) 
                 (cong (x *_) (sym (*-zeroʳ y))))
  *-assoc x y (suc z) = begin 
    x * y * suc z ≡⟨ *-suc (x * y) z ⟩
    x * y + (x * y) * z ≡⟨ cong (x * y +_) (*-assoc x y z) ⟩
    x * y + x * (y * z) ≡⟨ sym (*-distribˡ-+ x y (y * z)) ⟩
    x * (y + y * z) ≡⟨ cong (x *_) (sym (*-suc y z)) ⟩ 
    x * (y * suc z) ∎ 
    where open ≡-Reasoning
  
  
  