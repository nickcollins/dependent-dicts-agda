open import Prelude
open import Nat
open import Bij

module Int where

  data Int : Set where
    +_     : Nat → Int
    -[1+_] : Nat → Int

  int→nat : Int → Nat
  int→nat (+ n) = 1+ (n + n)
  int→nat -[1+ n ] = n + n

  int→nat:inj : ∀{m n} →
                   int→nat m == int→nat n →
                   m == n
  int→nat:inj {+ m} {+ n} eq rewrite even-inj {m} {n} (1+inj eq) = refl
  int→nat:inj {+ m} { -[1+ n ]} eq = abort (even-not-odd {m} {n} eq)
  int→nat:inj { -[1+ m ]} {+ n} eq = abort (even-not-odd {n} {m} (! eq))
  int→nat:inj { -[1+ m ]} { -[1+ n ]} eq rewrite even-inj {m} {n} eq = refl

  int→nat:surj : (n : Nat) → Σ[ m ∈ Int ] (int→nat m == n)
  int→nat:surj Z = -[1+ Z ] , refl
  int→nat:surj (1+ Z) = (+ Z) , refl
  int→nat:surj (1+ (1+ n)) with int→nat:surj n
  int→nat:surj (1+ (1+ .(1+ (n + n)))) | (+ n) , refl = (+ 1+ n) , 1+ap (1+ap n+1+m==1+n+m)
  int→nat:surj (1+ (1+ .(n + n))) | -[1+ n ] , refl = -[1+ 1+ n ] , 1+ap n+1+m==1+n+m

  instance
    IntBij : bij Int Nat
    IntBij = record {
      convert = int→nat;
      inj     = int→nat:inj;
      surj    = int→nat:surj}
