module Chapter2-Numbers where 

import Chapter1-Agda


-- 2.1 Natural Numbers 

module Definition-Naturals where
  
  data ℕ : Set where
    zero : ℕ
    suc  : ℕ → ℕ


-- 2.3 Playing with Naturals 

module Sandbox-Naturals where 
  open import Agda.Builtin.Nat 
    using (Nat; zero; suc)

  one : Nat 
  one = suc zero 

  two : Nat
  two = suc one

  three : Nat
  three = suc two
  
  four : Nat
  four = suc three


  open import Agda.Builtin.Bool
    using (Bool; true; false)

  n=0? : Nat → Bool 
  n=0? zero = true 
  n=0? (suc n) = false

  n=2? : Nat → Bool 
  n=2? (suc (suc zero)) = true 
  n=2? _ = false


  -- 2.4 Induction

  even? : Nat → Bool 
  even? zero = true 
  even? (suc zero) = false 
  even? (suc (suc n)) = even? n

  
  -- 2.5 Two Notions of Evenness 

  data EvenNat : Set where 
    zero : EvenNat
    suc-suc : EvenNat → EvenNat 

  toNat : EvenNat → Nat 
  toNat zero = zero 
  toNat (suc-suc x) = suc (suc (toNat x))

  module Sandbox-Usable where 
    postulate 
      Usable : Set 
      Unusable : Set 

    IsEven : Nat → Set 
    IsEven zero = Usable 
    IsEven (suc zero) = Unusable 
    IsEven (suc (suc x)) = IsEven x

  data IsEven : Nat → Set where 
    zero-even : IsEven zero 
    suc-suc-even : {n : Nat} → IsEven n → IsEven (suc (suc n))

  four-is-even : IsEven four 
  four-is-even = suc-suc-even (suc-suc-even zero-even)

  three-is-even : IsEven three 
  three-is-even = suc-suc-even {!   !} 

  data IsOdd : Nat → Set where 
    one-odd : IsOdd one 
    suc-suc-odd : {n : Nat} → IsOdd n → IsOdd (suc (suc n))

  three-is-odd : IsOdd three 
  three-is-odd = suc-suc-odd one-odd

  four-is-odd : IsOdd four 
  four-is-odd = suc-suc-odd (suc-suc-odd {!   !})

  zero-is-odd : IsOdd zero 
  zero-is-odd = {!   !}

  -- Exercise
  data IsOdd' : Nat → Set where 
    is-odd : {n : Nat} → IsEven n → IsOdd' (suc n)

  three-is-odd' : IsOdd' three
  three-is-odd' = is-odd (suc-suc-even zero-even)

  -- Exercise 
  even-followed-by-odd : {n : Nat} → IsEven n → IsOdd (suc n)
  even-followed-by-odd zero-even = one-odd
  even-followed-by-odd (suc-suc-even x) = suc-suc-odd (even-followed-by-odd x)

  even-followed-by-odd' : {n : Nat} → IsEven n → IsOdd' (suc n)
  even-followed-by-odd' = is-odd


  -- 2.6 Constructing Evidence 
  data Maybe (A : Set) : Set where 
    just : A → Maybe A 
    nothing : Maybe A 
 
  evenEv : (n : Nat) → Maybe (IsEven n)
  evenEv zero = just zero-even
  evenEv (suc zero) = nothing
  evenEv (suc (suc n)) with evenEv n 
  ... | just x = just (suc-suc-even x)
  ... | nothing = nothing


  -- 2.7 Addition 
  _+_ : Nat → Nat → Nat 
  zero + y = y 
  suc x + y = suc (x + y)

  infixl 6 _+_

  -- 2.8 Termination Checking
  module Example-Silly where
      
    not : Bool → Bool 
    not false = true 
    not true = false

    data Nat’ : Set where
      zero : Nat’
      suc : Nat’ → Nat’
      2suc : Nat’ → Nat’

    even?’ : Nat’ → Bool
    even?’ zero = true
    even?’ (suc n) = not (even?’ n)
    even?’ (2suc zero) = true
    even?’ (2suc (suc n)) = not (even?’ n)
    even?’ (2suc (2suc n)) = even?’ n

  -- 2.9 Multiplication and Exponentiation 
  _*_ : Nat → Nat → Nat 
  zero * b = zero 
  suc a * b = b + (a * b) 
  
  infixl 7 _*_

  _^_ : Nat → Nat → Nat 
  a ^ zero = one 
  a ^ suc b = a * (a ^ b)

  -- 2.10 Semi-subtraction 
  _∸_ : Nat → Nat → Nat 
  a ∸ zero = a
  zero ∸ suc b = zero
  suc a ∸ suc b = a ∸ b

  module Natural-Tests where 
    open import Agda.Builtin.Equality 

    _ : one + two ≡ three
    _ = refl
    
    _ : three ∸ one ≡ two
    _ = refl
    
    _ : one ∸ three ≡ zero
    _ = refl
    
    _ : two * two ≡ four
    _ = refl

-- 2.11 Inconvenient Integers 
module Misstep-Integers₁ where 
  data ℤ : Set where 
    zero : ℤ 
    suc : ℤ → ℤ
    pred : ℤ → ℤ 

  normalize : ℤ → ℤ
  normalize zero = zero
  normalize (suc zero) = suc zero
  normalize (suc (suc x)) = suc (normalize (suc x))
  normalize (suc (pred x)) = normalize x
  normalize (pred zero) = pred zero
  normalize (pred (suc x)) = normalize x
  normalize (pred (pred x)) = pred (normalize (pred x))

  module Counterexample where
    open import Agda.Builtin.Equality
    _ : normalize (suc (suc (pred (pred zero)))) ≡ suc (pred zero)
    _ = refl
  
-- 2.12 Difference Integers 
module Misstep-Integers₂ where 
  import Agda.Builtin.Nat as Nat 
  open Nat using (Nat; zero; suc) 

  record ℤ : Set where
    constructor mkℤ
    field
      pos : Nat 
      neg : Nat

  normalize : ℤ → ℤ
  normalize (mkℤ zero neg) = mkℤ zero neg
  normalize (mkℤ (suc pos) zero) = mkℤ (suc pos) zero
  normalize (mkℤ (suc pos) (suc neg)) = normalize (mkℤ pos neg)

  _+_ : ℤ → ℤ → ℤ
  mkℤ p₁ n₁ + mkℤ p₂ n₂
    = normalize (mkℤ (p₁ Nat.+ p₂) (n₁ Nat.+ n₂))
  
  infixl 5 _+_

  _-_ : ℤ → ℤ → ℤ
  mkℤ p₁ n₁ - mkℤ p₂ n₂
    = normalize (mkℤ (p₁ Nat.+ n₂) (n₁ Nat.+ p₂))
  
  infixl 5 _-_

  _*_ : ℤ → ℤ → ℤ
  mkℤ p₁ n₁ * mkℤ p₂ n₂
    = normalize
    (mkℤ (p₁ Nat.* p₂ Nat.+ n₁ Nat.* n₂)
    (p₁ Nat.* n₂ Nat.+ p₂ Nat.* n₁))

  infixl 6 _*_

  
-- 2.13 Unique Integer Representations
module Misstep-Integers₃ where 
  open import Agda.Builtin.Nat 
  
  data ℤ : Set where 
    +_ : Nat → ℤ
    -_ : Nat → ℤ 

  _ : ℤ 
  _ = - 2

  _ : ℤ 
  _ = + 6 

  _ : ℤ
  _ = + 0
  
  _ : ℤ
  _ = - 0


module Sandbox-Integers where 
  import Agda.Builtin.Nat 
  open Agda.Builtin.Nat using (Nat) 

  data ℤ : Set where
    +_ : Nat → ℤ 
    -[1+_] : Nat → ℤ

  0ℤ : ℤ 
  0ℤ = + 0 

  1ℤ : ℤ 
  1ℤ = + 1 

  -1ℤ : ℤ 
  -1ℤ = -[1+ 0 ]


  suc : ℤ → ℤ 
  suc (+ x) = + (Nat.suc x)
  suc -[1+ Nat.zero ] = + Nat.zero
  suc -[1+ Nat.suc x ] = -[1+ x ]  

  pred : ℤ → ℤ 
  pred (+ Nat.zero) = -[1+ Nat.zero ]
  pred (+ Nat.suc x) = + x
  pred -[1+ x ] = -[1+ (Nat.suc x) ]


-- 2.14 Pattern Synonyms 
  -_ : ℤ → ℤ 
  - (+ Nat.zero) = 0ℤ
  - (+ Nat.suc x) = -[1+ x ]
  - -[1+ x ] = + Nat.suc x

  pattern +[1+_] n = + Nat.suc n 
  pattern +0 = + Nat.zero 

  -'_ : ℤ → ℤ 
  -' +0 = +0 
  -' +[1+ n ] = -[1+ n ]
  -' -[1+ n ] = +[1+ n ]


-- 2.15 Integer Addition 
  module Naive-Addition where 
    _+_ : ℤ → ℤ → ℤ
    +0 + y = y
    +[1+ x ] + +0 = +[1+ x ]
    +[1+ x ] + +[1+ y ] = +[1+ 1 Agda.Builtin.Nat.+ x Agda.Builtin.Nat.+ y ]
    +[1+ x ] + -[1+ y ] = {! !}
    -[1+ x ] + +0 = -[1+ x ]
    -[1+ x ] + +[1+ y ] = {! !}
    -[1+ x ] + -[1+ y ] = -[1+ 1 Agda.Builtin.Nat.+ x Agda.Builtin.Nat.+ y ]

  _⊖_ : Nat → Nat → ℤ
  Nat.zero ⊖ Nat.zero = +0
  Nat.zero ⊖ Nat.suc n = -[1+ n ]
  Nat.suc m ⊖ Nat.zero = +[1+ m ]
  Nat.suc m ⊖ Nat.suc n = m ⊖ n

  infixl 5 _+_ 

  _+_ : ℤ → ℤ → ℤ 
  (+ x) + (+ y) = + (x Agda.Builtin.Nat.+ y)
  (+ x) + -[1+ y ] = x ⊖ (Nat.suc y) 
  -[1+ x ] + (+ y) = y ⊖ (Nat.suc x) 
  -[1+ x ] + -[1+ y ] = -[1+ (Nat.suc (x Agda.Builtin.Nat.+ y))]

  infixl 5 _-_
  _-_ : ℤ → ℤ → ℤ
  x - y = x + (- y)

  infixl 6 _*_
  _*_ : ℤ → ℤ → ℤ
  x * +0 = +0
  x * +[1+ Nat.zero ] = x
  x * -[1+ Nat.zero ] = - x
  x * +[1+ Nat.suc y ] = (+[1+ y ] * x) + x
  x * -[1+ Nat.suc y ] = (-[1+ y ] * x) - x
  
  module Tests where
    open import Agda.Builtin.Equality
    _ : - (+ 2) * - (+ 6) ≡ + 12
    _ = refl
    _ : (+ 3) - (+ 10) ≡ - (+ 7)
    _ = refl
