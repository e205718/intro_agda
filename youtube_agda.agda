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

⊥Elim : {P : Set} → ⊥ → P
⊥Elim ()

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


data _⊃_ (P Q : Set) : Set where
  ⊃Intro : (P → Q) → P ⊃ Q

⊃Elim : (P Q : Set) → P ⊃ Q → P → Q
⊃Elim P Q (⊃Intro x)  = x

⊃Elim2 : {P Q : Set} → P ⊃ Q → P → Q
⊃Elim2 (⊃Intro x) q  = x q

⊃Elim3 : {P Q : Set} → P ⊃ Q → P → Q
⊃Elim3 (⊃Intro x)  = x

prop1 : (A B : Set) → (A ∧ B) ⊃ (A ∨ B)
--prop1 A B = ⊃Intro (λ x → ∨Intro1 (_∧_.Elim1 x)) where
prop1 A B = ⊃Intro (proof2 A B)  where
  p1 : (A B : Set) → A ∧ B
  p1 A B = {!!}
  
  p2 : (A B : Set)  → A ∨ B
  p2 A B = {!!} 
  p2' : (A B : Set) → A → A ∨ B
  p2' A B = ∨Intro1

  p3 : (A B : Set) → A → A
  p3 A a = λ a → a
  
  p3' : (A B : Set) → A ∧ B → A
  p3' A B = _∧_.Elim1
  
  p3'' : {A B : Set} → A ∧ B → A
  p3'' = λ x → _∧_.Elim1 x
  
  p3''' : (A B : Set) → A ∧ B → A
  p3''' = λ a b x → _∧_.Elim1 x --- C-c,C-e

  proof2 : (A B : Set) → A ∧ B → A ∨ B 
  proof2 A B = λ x → ∨Intro1 (_∧_.Elim1 x)

data all (P : Set) (Q : P → Set) : Set where
  ∀Intro : ((a : P) → Q a) → all P Q 

∀Elim : {P : Set } → {Q : P → Set} → all P Q → (a : P) → Q a 
∀Elim (∀Intro f) a = f a  --C-c,C-n  e

record exist (P : Set)(Q : P → Set) : Set where
  field
    evidence : P
    Elim : Q evidence

∃Intro : {P : Set} {Q : P → Set} → (a : P) → Q a → exist P Q
--∃Intro a = λ x → record {evidence = a ; Elim = x}
∃Intro a p = record {evidence = a ; Elim = p}

-- prop3 : ∃x (∀y (P x y)) → (∀y (∃x P (x y)))
--まずはx y の２値だから使用する変数は２
--P はA Bに作用して、Setを返す関数。Pを定義する
--prop3 :  (A B : Set) → (P : A → (B → Set)) → exist A (all B (P A B)) →
--         all B (exist A P (A B))
--命題の通りに、記号を並べると以上のようになるが、これだとErrorが出て通らない。
--おそらく、Pを定義したが、Pは関数定義なので、引数を値で受け取る必要がある？？
--値の定義にラムダ式を使用している。
  --なぜラムダ式を使わないといけないのかについて考える。x
  
