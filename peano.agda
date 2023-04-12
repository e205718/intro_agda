module peano where

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

_+_ : Nat → Nat → Nat
zero + y = y
suc x + y = suc (x + y)

one = (suc zero)
two = (suc one)

_*_ : Nat → Nat → Nat
x * zero = zero
x * suc y = x + (x * y)

_-_ : Nat → Nat → Nat
zero - y = zero
suc x - zero = suc x
suc x - suc y = x - y

-- _/_ : Nat → Nat → Nat
--zero / suc x = zero
--suc x / zero = zero

data _≡_{A : Set } : A → A →  Set where
     refl : {x : A} → x ≡ x

cong : {A B : Set} → {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

add-suc : (x y : Nat) → suc (x + y) ≡ (x + (suc y))
add-suc zero y = refl
add-suc (suc x) y = cong suc (add-suc x y)

add-comm : (x y : Nat) → (x + y) ≡ (y + x)
add-comm zero zero = refl
add-comm zero (suc y) = cong suc (add-comm zero y )
add-comm (suc x) y = trans (cong suc (add-comm x y )) (add-suc y x)

