data Nat : Set where
  zero : Nat
  suc : Nat → Nat

plus : Nat → Nat → Nat
plus zero zero = zero
plus zero (suc m) = suc m 
plus (suc n) zero = suc n
plus (suc n) (suc m) = suc (suc (plus n m) )

plus2 : Nat → Nat → Nat
plus2 zero n = n
plus2 (suc m) n = suc (plus2 m n)

data Bool : Set where
  true : Bool
  false : Bool
  
not : Bool → Bool
not true = false
not false = true

or : Bool → Bool → Bool
or true _ = true
or false true = true
or false false = false

and : Bool → Bool → Bool
and true true = true
and true false = false
and false true = false
and false false = false   -- and _ _ = falseともかける

data _≡_ {A : Set} (x : A) : A → Set where
     refl : x ≡ x
     
cong : {A B : Set} {x y : A} →(f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

plus3 : Nat → Nat → Nat
plus3 zero y = y
plus3 (suc x) y = suc (plus3 x y)

unitPlus : (n : Nat) → (plus3 zero n) ≡ n
unitPlus zero = refl
unitPlus (suc n) = cong suc (unitPlus n)

data ⊥ : Set where

record ⊤ : Set where

record _∧_ (P Q : Set) : Set where
  field
    Elim1 : P
    Elim2 : Q
    
test1 : (P Q : Set) → Set
test1 p q = p ∧ q

test2 : (P : Set) → Set
test2 p = p ∧ ⊥

lemma1 : (P Q : Set) → P ∧ Q → P
lemma1 p q = _∧_.Elim1
--導入規則の定義
∧Intro : {P Q : Set} → P → Q → P ∧ Q
∧Intro p q = record {Elim1 = p ; Elim2 = q}

data _∨_ (P Q : Set) : Set where
  ∨Intro1 : P → P ∨ Q
  ∨Intro2 : Q → P ∨ Q

∨Elim : {P Q R : Set} → P ∨ Q → (P → R) → (Q → R) → R
∨Elim (∨Intro1 a) prfP _ = prfP a
∨Elim (∨Intro2 b) _ prfQ = prfQ b

test3 : (P Q : Set) → Set
test3 p q = p ∨ q

lemma2 : (P Q : Set) → P → P ∨ Q
lemma2 p q = ∨Intro1
