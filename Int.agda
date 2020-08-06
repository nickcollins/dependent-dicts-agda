open import Prelude
open import Nat
open import List -- TODO delete

module Int where

  data Int : Set where
    +_     : Nat → Int
    -[1+_] : Nat → Int

  nat→int' : Nat → Nat → Int
  nat→int' acc Z = -[1+ acc ]
  nat→int' acc (1+ Z) = + acc
  nat→int' acc (1+ (1+ n)) = nat→int' (1+ acc) n

  nat→int : Nat → Int
  nat→int = nat→int' Z

  int→nat : Int → Nat
  int→nat (+ n) = 1+ (n + n)
  int→nat -[1+ n ] = n + n

  -- TODO delete
  x = map nat→int (0 :: (1 :: (2 :: (3 :: (4 :: [])))))
  y = map int→nat ((+ 0) :: ((+ 1) :: ((+ 2) :: ((+ 3) :: ((+ 4) :: [])))))
  z = map int→nat (-[1+ 0 ] :: (-[1+ 1 ] :: (-[1+ 2 ] :: (-[1+ 3 ] :: (-[1+ 4 ] :: [])))))

  nat→int:math : ∀{acc m n} →
                    nat→int' acc m == nat→int n →
                    n == acc + acc + m
  nat→int:math {m = Z} {Z} eq = {!!}
  nat→int:math {m = Z} {1+ n} eq = {!!}
  nat→int:math {m = 1+ m} {Z} eq = {!!}
  nat→int:math {m = 1+ m} {1+ n} eq = {!!}

  {- TODO use it or lose it
  nat→pos:acc : ∀{acc m n} →
                   nat→int m == + n →
                   nat→int acc m == + n →
  nat→pos:acc eq = ?
  -}

  int→nat:inj : ∀{m n} →
                   int→nat m == int→nat n →
                   m == n
  int→nat:inj {+ m} {+ n} eq rewrite even-inj {m} {n} (1+inj eq) = refl
  int→nat:inj {+ m} { -[1+ n ]} eq = abort (even-not-odd {m} {n} eq)
  int→nat:inj { -[1+ m ]} {+ n} eq = abort (even-not-odd {n} {m} (! eq))
  int→nat:inj { -[1+ m ]} { -[1+ n ]} eq rewrite even-inj {m} {n} eq = refl

  int→nat:surj : ∀{n} → Σ[ m ∈ Int ] (int→nat m == n)
  int→nat:surj {Z} = -[1+ Z ] , refl
  int→nat:surj {1+ Z} = (+ Z) , refl
  int→nat:surj {1+ (1+ n)} with int→nat:surj {n}
  int→nat:surj {1+ (1+ .(1+ (n + n)))} | (+ n) , refl = (+ 1+ n) , 1+ap (1+ap n+1+m==1+n+m)
  int→nat:surj {1+ (1+ .(n + n))} | -[1+ n ] , refl = -[1+ 1+ n ] , 1+ap n+1+m==1+n+m

  nat→int:inj : ∀{n m} →
                   nat→int n == nat→int m →
                   n == m
  nat→int:inj {Z} {Z} eq = refl
  nat→int:inj {Z} {1+ m} eq = {!!}
  nat→int:inj {1+ n} {Z} eq = {!!}
  nat→int:inj {1+ Z} {1+ Z} eq = refl
  nat→int:inj {1+ Z} {1+ (1+ m)} eq = {!!}
  nat→int:inj {1+ (1+ n)} {1+ Z} eq = {!!}
  nat→int:inj {1+ (1+ n)} {1+ (1+ m)} eq = {!!}

  nat→int':+ : ∀{acc1 acc2 n1 n2} →
                  nat→int' acc1 n1 == nat→int' acc2 n2 →
                  nat→int' (1+ acc1) n1 == nat→int' (1+ acc2) n2
  nat→int':+ eq = {!!}

  {- TODO use it or lose it}
  nat→int':+ : ∀{acc acc+ m n} →
                  nat→int' acc m == nat→int n →
                  nat→int' (acc+ + acc) m == nat→int' acc+ n
  nat→int':+ {acc+ = Z} eq = eq
  nat→int':+ {acc+ = 1+ acc+} {n = Z} eq = {!!}
  nat→int':+ {acc+ = 1+ acc+} {n = 1+ Z} eq = {!!}
  nat→int':+ {acc+ = 1+ acc+} {n = 1+ (1+ n)} eq = {!!}
  nat→int':+ {Z} {1+ acc+} eq = {!!}
  nat→int':+ {1+ acc} {1+ acc+} eq = {!!}
  -}

  nat→int':1+ : ∀{acc m n} →
                  nat→int' acc m == nat→int n →
                  nat→int' (1+ acc) m == nat→int' 1 n
  nat→int':1+ {n = Z} eq = {!!}
  nat→int':1+ {n = 1+ Z} eq = {!!}
  nat→int':1+ {n = 1+ (1+ n)} eq = {!!}
  nat→int':1+ {Z} eq = {!eq!}
  nat→int':1+ {1+ acc} {m} {n} eq = {!n!} -- nat→int':1+ {1+ acc} {m} {n} {!eq!}

  nat→int':2x : ∀{acc n} → nat→int' acc n == nat→int (acc + acc + n)
  nat→int':2x {Z} = refl
  nat→int':2x {1+ acc} {n} rewrite n+1+m==1+n+m {acc} {acc}
    = nat→int':1+ {acc} {n} {acc + acc + n} (nat→int':2x {acc} {n})

  nat-int-bij : ∀{n} → nat→int (int→nat n) == n
  nat-int-bij {+ Z} = refl
  nat-int-bij { -[1+ Z ]} = refl
  nat-int-bij {+ 1+ n} = {!!}
  nat-int-bij { -[1+ 1+ n ]} = {!!}

  -- TODO prove this in terms of previous stuff
  int-nat-bij : ∀{n} → int→nat (nat→int n) == n
  int-nat-bij {Z} = refl
  int-nat-bij {1+ Z} = refl
  int-nat-bij {1+ (1+ n)} = {!!}
