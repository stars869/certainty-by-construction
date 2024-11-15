{-# OPTIONS --allow-unsolved-metas #-}

module Chapter1-Agda where 


-- 1.4 Importing Code

module Example-Imports where 
  import Agda.Builtin.Bool 

  _ : Agda.Builtin.Bool.Bool 
  _ = Agda.Builtin.Bool.false


module Example-Emports-2 where 
  import Agda.Builtin.Bool 
  open Agda.Builtin.Bool

  _ : Bool 
  _ = false 


-- 1.6 Importing Code 

module Example-TypingJudgments where 
  postulate 
    Bool  : Set
    false : Bool 
    true  : Bool 


module Booleans where 
  
  data Bool : Set where 
    false : Bool 
    true : Bool 

-- 1.7 Your First Function 

  not : Bool → Bool 
  not false = true 
  not true = false


  -- 1.9 unit test

  open import Agda.Builtin.Equality

  _ : not (not false) ≡ false 
  _ = refl 


  -- 1.13 Agda's Computational Model 
  
  _∨_ : Bool → Bool → Bool 
  false ∨ false = false
  false ∨ true = true
  true ∨ false = true
  true ∨ true = true

  _∨'_ : Bool → Bool → Bool 
  false ∨' other = other
  true ∨' other = true


-- 1.15 Records and Tuples 

module Example-Employees where 
  open Booleans
  open import Agda.Builtin.String 
    using (String)

  data Department : Set where 
    administrative : Department
    engineering : Department
    finance : Department
    marketing : Department
    sales : Department
    
  record Employee : Set where 
    field 
      name : String 
      department : Department
      is-new-hire : Bool 

  tillman : Employee 
  tillman = record
    { 
      name = "Tillman";
      department = engineering;
      is-new-hire = false 
    }


module Sandbox-Tuples where 
  record _×_ (A : Set) (B : Set) : Set where 
    field 
      proj₁ : A 
      proj₂ : B 

  open Booleans 
  
  my-tuple : Bool × Bool 
  my-tuple = record { proj₁ = true ; proj₂ = false }

  first : Bool × Bool → Bool 
  first record { proj₁ = x ; proj₂ = y } = x

  my-tuple-first : Bool 
  my-tuple-first = _×_.proj₁ my-tuple

  open _×_ 

  my-tuple-second : Bool 
  my-tuple-second = proj₂ my-tuple

-- 1.16 Copatterns and Constructors 

  my-copattern : Bool × Bool 
  proj₁ my-copattern = false
  proj₂ my-copattern = true

  nested-copattern : Bool × (Bool × Bool)
  proj₁ nested-copattern = {!   !} 
  proj₁ (proj₂ nested-copattern) = {!   !}
  proj₂ (proj₂ nested-copattern) = {!   !}

  _,_ : {A B : Set} → A → B → A × B 
  x , y = record { proj₁ = x ; proj₂ = y}
  
  my-tuple' : Bool × Bool 
  my-tuple' = true , false


module Sandbox-Tuples₂  where 
  open Booleans 

  record _×_ (A : Set) (B : Set) : Set where 
    constructor _,_ 
    field
      proj₁ : A 
      proj₂ : B 

  open _×_ 

  -- 1.17 Fixities
  -- precedence & associativity
  infixr 4 _,_ 

  infixr 2 _×_ 


  -- 1.18 Coproduct Types 

  data _⊎_ (A : Set) (B : Set) : Set where 
    inj₁ : A → A ⊎ B 
    inj₂ : B → A ⊎ B

  infixr 1 _⊎_


  -- 1.19 Function Types 
  module Example-Pets where 
    open import Agda.Builtin.String 
      using (String)

    data Species : Set where 
      bird cat dog reptile : Species 

    data Temperament : Set where 
      anxious : Temperament
      chill : Temperament
      excitable : Temperament
      grumpy : Temperament

    record Pet : Set where 
      constructor makePet
      field 
        species : Species
        temperament : Temperament
        name : String 
        
    makeGrumpyCat : String → Pet 
    makeGrumpyCat = makePet cat grumpy


  -- 1.20 The Curry/Uncurry Isomorphism 
  or : Bool × Bool → Bool 
  or (false , y) = y 
  or (true , y) = true 

  _ : Bool 
  _ = or (true , false)

  curry : {A B C : Set} → (A × B → C) → (A → B → C)
  curry f a b = f (a , b)

  uncurry : {A B C : Set} → (A → B → C) → (A × B → C)
  uncurry f (a , b) = f a b 


  -- 1.21 Implicit Arguments

  -- C-c C-s to solve
  _ : {!   !}
  _ = uncurry _∨_


module Sandbox-Implicits where 
  open Booleans 
    using (Bool; false; true; not; _∨_)
  open Sandbox-Tuples₂
  
  mk-tuple : (A : Set) → (B : Set) → A → B → A × B
  mk-tuple A B x y = x , y 

  _ : Bool × Bool 
  _ = mk-tuple Bool Bool {!   !} {!   !}


  data PrimaryColor : Set where 
    red green blue : PrimaryColor 

  -- bad-tuple : Bool × Bool 
  -- bad-tuple = mk-tuple PrimaryColor Bool ? ?

  color-bool-tuple : PrimaryColor × Bool 
  color-bool-tuple = mk-tuple _ _ red false 

  mk-color-bool-tuple : PrimaryColor → Bool → PrimaryColor × Bool 
  mk-color-bool-tuple = _,_


-- 1.22 Wrapping up

-- open import Agda.Builtin.Bool
--   using (Bool; false; true; not; _∨_; _∧_)
--   public

-- open import Data.Product
--   using (_×_; _,_; proj₁; proj₂; curry; uncurry)
--   public


-- open import Data.Sum
--   using (_⊎_; inj₁; inj₂)
--   public 

