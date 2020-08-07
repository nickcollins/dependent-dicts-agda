open import Prelude
open import Nat
open import List

-- The contents of this file were originally written in a different codebase,
-- which was itself a descendant of a prior codebase that had been using non-standard
-- definitions of naturals and other basic definitions. As such this code has
-- inherited these non-standard idioms, as seen in Prelude, Nat, and List. Ideally,
-- this file would be refactored to use the Agda standard library instead, but beyond
-- the significant effort of refactoring, the Agda standard library appears not to be
-- packaged with Agda, and must be installed separately. The difficulties inherent in
-- attempting to use a "standard library" that is not sufficiently standard as to be
-- included with Agda itself, added to the difficulties of refactoring, have led us
-- to continue with the the non-standard forms and definitions. We hope that they are
-- fairly self-explanatory and intuitive. Below we note some of our idioms that may
-- not be obvious:
-- * abort used to prove any goal given ⊥
-- * == is used for reflexive equality
-- * Z is zero, 1+ is suc
-- * ≤ is defined as data, < is defined as n < m = n ≤ m ∧ n ≠ m
-- * TODO if we don't switch to truncation, we need to talk about subtraction
-- * l⟦i⟧ is used to (maybe) get the ith element of list l
--
-- Agda's encapsulation facilities seem insufficient to properly encapsulate the
-- raw data of a delta dictionary. Thus, we do not use encapsulation, but leave
-- comments explaining that list functionality must not be used on a dlt
module Delta where
  -- helper function
  diff-1 : ∀{n m} → n < m → Nat
  diff-1 n<m = difference (n<m→1+n≤m n<m)

  ---- the core declarations ----
  -- TODO move definitions

  _dlt : Set → Set
  A dlt = List (Nat ∧ A)

  -- nil dlt
  ∅ : {A : Set} → A dlt
  ∅ = []

  -- singleton dlt
  ■_ : {A : Set} → (Nat ∧ A) → A dlt
  ■_ (x , a) = (x , a) :: []

  -- dlt extension/insertion - never use _::_
  _,,_ : ∀{A} → A dlt → (Nat ∧ A) → A dlt
  [] ,, (x , a) = ■ (x , a)
  ((hx , ha) :: t) ,, (x , a) with <dec x hx
  ... | Inl x<hx       = (x , a) :: ((diff-1 x<hx , ha) :: t)
  ... | Inr (Inl refl) = (x , a) :: t
  ... | Inr (Inr hx<x) = (hx , ha) :: (t ,, (diff-1 hx<x , a))

  infixl 10 _,,_

  -- membership, or presence, in a dlt
  data _∈_ : {A : Set} (p : Nat ∧ A) → (Γ : A dlt) → Set where
    InH : {A : Set} {Γ : A dlt} {x : Nat} {a : A} →
           (x , a) ∈ ((x , a) :: Γ)
    InT : {A : Set} {Γ : A dlt} {x s : Nat} {a a' : A} →
           (x , a) ∈ Γ →
           ((x + 1+ s , a)) ∈ ((s , a') :: Γ)

  -- the domain of a dlt
  dom : {A : Set} → A dlt → Nat → Set
  dom {A} Γ x = Σ[ a ∈ A ] ((x , a) ∈ Γ)

  -- apartness for dlts
  _#_ : {A : Set} (n : Nat) → (Γ : A dlt) → Set
  x # Γ = dom Γ x → ⊥

  _##_ : {A : Set} → A dlt → A dlt → Set
  Γ1 ## Γ2 = (x : Nat) → dom Γ1 x → x # Γ2

  _~_ : {A : Set} → A dlt → A dlt → Set
  _~_ {A} Γ1 Γ2 = (x : Nat) (a1 a2 : A) →
                   (x , a1) ∈ Γ1 ∧ (x , a2) ∈ Γ2 →
                   a1 == a2

  -- TODO theorems
  -- maps f across the values of the dlt
  dltmap : {A B : Set} → (A → B) → A dlt → B dlt
  dltmap f Γ = map (λ {(hx , ha) → (hx , f ha)}) Γ

  -- TODO theorems
  -- returns a list of the values stored in the dlt
  dlt⇒values : {A : Set} → A dlt → List A

  -- converts a list of key-value pairs into a dlt, with later pairs in the list
  -- overriding bindings definend by previous pairs
  list⇒dlt : {A : Set} → List (Nat ∧ A) → A dlt

  -- converts a dlt into a list of key-value pairs; the inverse of list⇒dlt
  dlt⇒list : {A : Set} → A dlt → List (Nat ∧ A)

  -- TODO theorems
  -- converts a list of key-value pairs into a multi-dlt, where each value of
  -- the result is the sublist of values from the former that were mapped to by the
  -- corresponding key
  list⇒list-dlt : {A : Set} → List (Nat ∧ A) → (List A) dlt

  -- union merge A B is the union of A and B,
  -- with (merge a b) being invoked to handle the mappings they have in common
  union : {A : Set} → (A → A → A) → A dlt → A dlt → A dlt

  -- The primary way to test membership is to use _∈_,
  -- but this can be used in cases where using _∈_
  -- would be too verbose or awkward.
  -- The lookup theorems prove that they are compatible
  _⦃⦃_⦄⦄ : {A : Set} → A dlt → Nat → Maybe A
  [] ⦃⦃ x ⦄⦄ = None
  ((hx , ha) :: t) ⦃⦃ x ⦄⦄ with <dec x hx
  ... | Inl x<hx       = None
  ... | Inr (Inl refl) = Some ha
  ... | Inr (Inr hx<x) = t ⦃⦃ diff-1 hx<x ⦄⦄

  ---- lemmas ----

  undiff-1 : (x s : Nat) → (x<s+1+x : x < s + 1+ x) → s == diff-1 x<s+1+x
  undiff-1 x s x<s+1+x
    rewrite n+1+m==1+n+m {s} {x} | ! (m-n==1+m-1+n n≤m+n (n<m→1+n≤m x<s+1+x)) | +comm {s} {x}
      = ! (n+m-n==m n≤n+m)

  too-small : {A : Set} {Γ : A dlt} {xl xb : Nat} {a : A} →
               xl < xb →
               dom ((xb , a) :: Γ) xl →
               ⊥
  too-small (_ , ne) (_ , InH) = ne refl
  too-small (x+1+xb≤xb , x+1+xb==xb) (_ , InT _) =
    x+1+xb==xb (≤antisym x+1+xb≤xb (≤trans (≤1+ ≤refl) n≤m+n))

  all-not-none : {A : Set} {Γ : A dlt} {x : Nat} {a : A} →
                  None ≠ (((x , a) :: Γ) ⦃⦃ x ⦄⦄)
  all-not-none {x = x} rewrite <dec-refl x = λ ()

  all-bindings-==-rec-eq : {A : Set} {Γ1 Γ2 : A dlt} {x : Nat} {a : A} →
                            ((x' : Nat) → ((x , a) :: Γ1) ⦃⦃ x' ⦄⦄ == ((x , a) :: Γ2) ⦃⦃ x' ⦄⦄) →
                            ((x' : Nat) → Γ1 ⦃⦃ x' ⦄⦄ == Γ2 ⦃⦃ x' ⦄⦄)
  all-bindings-==-rec-eq {x = x} h x'
    with h (x' + 1+ x)
  ... | eq
    with <dec (x' + 1+ x) x
  ... | Inl x'+1+x<x
          = abort (<antisym x'+1+x<x (n<m→n<s+m n<1+n))
  ... | Inr (Inl x'+1+x==x)
          = abort ((flip n≠n+1+m) (n+1+m==1+n+m · (+comm {1+ x} · x'+1+x==x)))
  ... | Inr (Inr x<x'+1+x)
          rewrite ! (undiff-1 x x' x<x'+1+x) = eq

  all-bindings-==-rec : {A : Set} {Γ1 Γ2 : A dlt} {x1 x2 : Nat} {a1 a2 : A} →
                         ((x : Nat) → ((x1 , a1) :: Γ1) ⦃⦃ x ⦄⦄ == ((x2 , a2) :: Γ2) ⦃⦃ x ⦄⦄) →
                         ((x : Nat) → Γ1 ⦃⦃ x ⦄⦄ == Γ2 ⦃⦃ x ⦄⦄)
  all-bindings-==-rec {x1 = x1} {x2} h x
    with h x1 | h x2
  ... | eq1 | eq2
    rewrite <dec-refl x1 | <dec-refl x2
    with <dec x1 x2 | <dec x2 x1
  ... | Inl _ | _
          = abort (somenotnone eq1)
  ... | Inr _ | Inl _
          = abort (somenotnone (! eq2))
  ... | Inr (Inl refl) | Inr (Inl refl)
          rewrite someinj eq1 | someinj eq2
            = all-bindings-==-rec-eq h x
  ... | Inr (Inl refl) | Inr (Inr x2<x2)
          = abort (<antirefl x2<x2)
  ... | Inr (Inr x2<x2) | Inr (Inl refl)
          = abort (<antirefl x2<x2)
  ... | Inr (Inr x2<x1) | Inr (Inr x1<x2)
          = abort (<antisym x1<x2 x2<x1)

  sad-lemma : {A : Set} {Γ : A dlt} {x n : Nat} {a a' : A} →
               (x + 1+ n , a') ∈ ((n , a) :: Γ) →
               Σ[ x' ∈ Nat ] Σ[ Γ' ∈ A dlt ] (
                  Γ' == (n , a) :: Γ ∧
                  x' == x + 1+ n ∧
                  (x' , a') ∈ Γ')
  sad-lemma h = _ , _ , refl , refl , h

  lemma-math' : ∀{x x1 n} → x ≠ x1 + (n + 1+ x)
  lemma-math' {x} {x1} {n}
    rewrite ! (+assc {x1} {n} {1+ x})
          | n+1+m==1+n+m {x1 + n} {x}
          | +comm {1+ x1 + n} {x}
      = n≠n+1+m

  ---- core theorems ----

  -- lookup is decidable
  lookup-dec : {A : Set} (Γ : A dlt) (x : Nat) →
                Σ[ a ∈ A ] (Γ ⦃⦃ x ⦄⦄ == Some a) ∨ Γ ⦃⦃ x ⦄⦄ == None
  lookup-dec Γ x
    with Γ ⦃⦃ x ⦄⦄
  ... | Some a = Inl (a , refl)
  ... | None   = Inr refl

  -- The next two theorems show that lookup (_⦃⦃_⦄⦄) is consistent with membership (_∈_)
  lookup-cons-1 : {A : Set} {Γ : A dlt} {x : Nat} {a : A} →
                   Γ ⦃⦃ x ⦄⦄ == Some a →
                   (x , a) ∈ Γ
  lookup-cons-1 {Γ = []} ()
  lookup-cons-1 {Γ = (hx , ha) :: t} {x} h
    with <dec x hx
  lookup-cons-1 {_} {(hx , ha) :: t} {x} ()        | Inl _
  lookup-cons-1 {_} {(hx , ha) :: t} {.hx} refl    | Inr (Inl refl) = InH
  lookup-cons-1 {_} {(hx , ha) :: t} {x} {a = a} h | Inr (Inr hx<x)
    = tr
        (λ y → (y , a) ∈ ((hx , ha) :: t))
        (m-n+n==m (n<m→1+n≤m hx<x))
        (InT (lookup-cons-1 {Γ = t} h))

  lookup-cons-2 : {A : Set} {Γ : A dlt} {x : Nat} {a : A} →
                   (x , a) ∈ Γ →
                   Γ ⦃⦃ x ⦄⦄ == Some a
  lookup-cons-2 {x = x} InH rewrite <dec-refl x = refl
  lookup-cons-2 (InT {Γ = Γ} {x = x} {s} {a} x∈Γ)
    with <dec (x + 1+ s) s
  ... | Inl x+1+s<s        = abort (<antisym x+1+s<s (n<m→n<s+m n<1+n))
  ... | Inr (Inl x+1+s==s) = abort ((flip n≠n+1+m) (n+1+m==1+n+m · (+comm {1+ s} · x+1+s==s)))
  ... | Inr (Inr s<x+1+s)
    with lookup-cons-2 x∈Γ
  ... | h rewrite ! (undiff-1 s x s<x+1+s) = h

  -- membership (_∈_) respects insertion (_,,_)
  x,a∈Γ,,x,a : {A : Set} {Γ : A dlt} {x : Nat} {a : A} →
                (x , a) ∈ (Γ ,, (x , a))
  x,a∈Γ,,x,a {Γ = []} {x} {a} = InH
  x,a∈Γ,,x,a {_} {(hx , ha) :: t} {x} {a}
    with <dec x hx
  ... | Inl _          = InH
  ... | Inr (Inl refl) = InH
  ... | Inr (Inr hx<x) =
          tr
            (λ y → (y , a) ∈ ((hx , ha) :: (t ,, (diff-1 hx<x , a))))
            (m-n+n==m (n<m→1+n≤m hx<x))
            (InT (x,a∈Γ,,x,a {Γ = t} {diff-1 hx<x} {a}))

  -- insertion can't generate spurious membership
  x∈Γ+→x∈Γ : {A : Set} {Γ : A dlt} {x x' : Nat} {a a' : A} →
                x ≠ x' →
                (x , a) ∈ (Γ ,, (x' , a')) →
                (x , a) ∈ Γ
  x∈Γ+→x∈Γ {Γ = []} x≠x' InH = abort (x≠x' refl)
  x∈Γ+→x∈Γ {Γ = []} x≠x' (InT ())
  x∈Γ+→x∈Γ {Γ = (hx , ha) :: t} {x' = x'} x≠x' x∈Γ+
    with <dec x' hx
  x∈Γ+→x∈Γ {_} {(hx , ha) :: t} {x' = x'} x≠x' InH | Inl x'<hx = abort (x≠x' refl)
  x∈Γ+→x∈Γ {_} {(hx , ha) :: t} {x' = x'} x≠x' (InT InH) | Inl x'<hx
    rewrite m-n+n==m (n<m→1+n≤m x'<hx) = InH
  x∈Γ+→x∈Γ {_} {(hx , ha) :: t} {x' = x'} x≠x' (InT (InT {x = x} x∈Γ+)) | Inl x'<hx
    rewrite +assc {x} {1+ (diff-1 x'<hx)} {1+ x'} | m-n+n==m (n<m→1+n≤m x'<hx)
      = InT x∈Γ+
  x∈Γ+→x∈Γ {_} {(hx , ha) :: t} {x' = .hx} x≠x' InH | Inr (Inl refl) = abort (x≠x' refl)
  x∈Γ+→x∈Γ {_} {(hx , ha) :: t} {x' = .hx} x≠x' (InT x∈Γ+) | Inr (Inl refl) = InT x∈Γ+
  x∈Γ+→x∈Γ {_} {(hx , ha) :: t} {x' = x'} x≠x' InH | Inr (Inr hx<x') = InH
  x∈Γ+→x∈Γ {_} {(hx , ha) :: t} {x' = x'} x≠x' (InT x∈Γ+) | Inr (Inr hx<x')
    = InT (x∈Γ+→x∈Γ (λ where refl → x≠x' (m-n+n==m (n<m→1+n≤m hx<x'))) x∈Γ+)

  -- insertion respects membership
  x∈Γ→x∈Γ+ : {A : Set} {Γ : A dlt} {x x' : Nat} {a a' : A} →
                x ≠ x' →
                (x , a) ∈ Γ →
                (x , a) ∈ (Γ ,, (x' , a'))
  x∈Γ→x∈Γ+ {x = x} {x'} {a} {a'} x≠x' (InH {Γ = Γ'})
    with <dec x' x
  ... | Inl x'<x
          = tr
              (λ y → (y , a) ∈ ((x' , a') :: ((diff-1 x'<x , a) :: Γ')))
              (m-n+n==m (n<m→1+n≤m x'<x))
              (InT InH)
  ... | Inr (Inl refl) = abort (x≠x' refl)
  ... | Inr (Inr x<x') = InH
  x∈Γ→x∈Γ+ {x = .(_ + 1+ _)} {x'} {a} {a'} x≠x' (InT {Γ = Γ} {x} {s} {a' = a''} x∈Γ)
    with <dec x' s
  ... | Inl x'<s
          = tr
              (λ y → (y , a) ∈ ((x' , a') :: ((diff-1 x'<s , a'') :: Γ)))
              ((+assc {b = 1+ (diff-1 x'<s)}) · (ap1 (_+_ x) (1+ap (m-n+n==m (n<m→1+n≤m x'<s)))))
              (InT (InT x∈Γ))
  ... | Inr (Inl refl) = InT x∈Γ
  ... | Inr (Inr s<x') =
          InT (x∈Γ→x∈Γ+ (λ where refl → x≠x' (m-n+n==m (n<m→1+n≤m s<x'))) x∈Γ)

  -- Decidability of membership
  -- This also packages up an appeal to dlt membership into a form that
  -- lets us retain more information
  dltindirect : {A : Set} (Γ : A dlt) (x : Nat) → dom Γ x ∨ x # Γ
  dltindirect [] x = Inr (λ ())
  dltindirect ((hx , ha) :: t) x
    with <dec x hx
  ... | Inl x<hx       = Inr (too-small x<hx)
  ... | Inr (Inl refl) = Inl (ha , InH)
  ... | Inr (Inr hx<x)
    with dltindirect t (diff-1 hx<x)
  dltindirect ((hx , ha) :: t) x | Inr (Inr hx<x) | Inl (a , rec) =
    Inl (a , tr
               (λ y → (y , a) ∈ ((hx , ha) :: t))
               (m-n+n==m (n<m→1+n≤m hx<x))
               (InT rec))
  dltindirect {A} ((hx , ha) :: t) x | Inr (Inr hx<x) | Inr dne =
    Inr x∉Γ
    where
      x∉Γ : Σ[ a ∈ A ] ((x , a) ∈ ((hx , ha) :: t)) → ⊥
      x∉Γ (_ , x∈Γ) with x∈Γ
      ... | InH = (π2 hx<x) refl
      ... | InT {x = s} x-hx-1∈t
        rewrite ! (undiff-1 hx s hx<x) = dne (_ , x-hx-1∈t)

  -- dlts give at most one binding for each variable
  dltunicity : {A : Set} {Γ : A dlt} {x : Nat} {a a' : A} →
                 (x , a) ∈ Γ →
                 (x , a') ∈ Γ →
                 a == a'
  dltunicity ah a'h
    with lookup-cons-2 ah | lookup-cons-2 a'h
  ... | ah' | a'h' = someinj (! ah' · a'h')

  -- everything is apart from the nil dlt
  x#∅ : {A : Set} {x : Nat} → _#_ {A} x ∅
  x#∅ (_ , ())

  -- if an index is in the domain of a singleton dlt, it's the only
  -- index in the dlt
  lem-dom-eq : {A : Set} {a : A} {n m : Nat} →
                 dom (■ (m , a)) n →
                 n == m
  lem-dom-eq (_ , InH) = refl
  lem-dom-eq (_ , InT ())

  -- If two dlts are semantically equivalent
  -- (i.e. they represent the same mapping from ids to values),
  -- then they are physically equal as judged by _==_
  dlt-==-eqv : {A : Set} {Γ1 Γ2 : A dlt} →
                ((x : Nat) → Γ1 ⦃⦃ x ⦄⦄ == Γ2 ⦃⦃ x ⦄⦄) →
                Γ1 == Γ2
  dlt-==-eqv {Γ1 = []} {[]} all-bindings-== = refl
  dlt-==-eqv {Γ1 = []} {(hx2 , ha2) :: t2} all-bindings-==
    = abort (all-not-none {Γ = t2} {x = hx2} (all-bindings-== hx2))
  dlt-==-eqv {Γ1 = (hx1 , ha1) :: t1} {[]} all-bindings-==
    = abort (all-not-none {Γ = t1} {x = hx1} (! (all-bindings-== hx1)))
  dlt-==-eqv {Γ1 = (hx1 , ha1) :: t1} {(hx2 , ha2) :: t2} all-bindings-==
    rewrite dlt-==-eqv {Γ1 = t1} {t2} (all-bindings-==-rec all-bindings-==)
    with all-bindings-== hx1 | all-bindings-== hx2
  ... | ha1== | ha2== rewrite <dec-refl hx1 | <dec-refl hx2
    with <dec hx1 hx2 | <dec hx2 hx1
  ... | Inl hx1<hx2 | _
          = abort (somenotnone ha1==)
  ... | Inr (Inl refl) | Inl hx2<hx1
          = abort (somenotnone (! ha2==))
  ... | Inr (Inr hx2<hx1) | Inl hx2<'hx1
          = abort (somenotnone (! ha2==))
  ... | Inr (Inl refl) | Inr _
          rewrite someinj ha1== = refl
  ... | Inr (Inr hx2<hx1) | Inr (Inl refl)
          rewrite someinj ha2== = refl
  ... | Inr (Inr hx2<hx1) | Inr (Inr hx1<hx2)
          = abort (<antisym hx1<hx2 hx2<hx1)

  -- equality of dlts is decidable
  dlt-==-dec : {A : Set}
                (Γ1 Γ2 : A dlt) →
                ((a1 a2 : A) → a1 == a2 ∨ a1 ≠ a2) →
                Γ1 == Γ2 ∨ Γ1 ≠ Γ2
  dlt-==-dec [] [] _ = Inl refl
  dlt-==-dec [] (_ :: _) _ = Inr (λ ())
  dlt-==-dec (_ :: _) [] _ = Inr (λ ())
  dlt-==-dec ((hx1 , ha1) :: t1) ((hx2 , ha2) :: t2) A==dec
    with natEQ hx1 hx2 | A==dec ha1 ha2 | dlt-==-dec t1 t2 A==dec
  ... | Inl refl | Inl refl | Inl refl = Inl refl
  ... | Inl refl | Inl refl | Inr ne   = Inr λ where refl → ne refl
  ... | Inl refl | Inr ne   | _        = Inr λ where refl → ne refl
  ... | Inr ne   | _        | _        = Inr λ where refl → ne refl

  -- A useful way to destruct dlt membership. Never destruct a dlt via _::_
  dlt-split : {A : Set} {Γ : A dlt} {n m : Nat} {an am : A} →
                (n , an) ∈ (Γ ,, (m , am)) →
                (n ≠ m ∧ (n , an) ∈ Γ) ∨ (n == m ∧ an == am)
  dlt-split {Γ = Γ} {n} {m} {an} {am} n∈Γ+
    with natEQ n m
  ... | Inl refl = Inr (refl , dltunicity n∈Γ+ (x,a∈Γ,,x,a {Γ = Γ}))
  ... | Inr n≠m  = Inl (n≠m , x∈Γ+→x∈Γ n≠m n∈Γ+)

  dlt-delete : {A : Set} {Γ : A dlt} {n : Nat} {a : A} →
                (n , a) ∈ Γ →
                Σ[ Γ⁻ ∈ A dlt ] (
                   Γ == Γ⁻ ,, (n , a) ∧
                   n # Γ⁻)
  dlt-delete {Γ = (n' , a') :: Γ} {n} n∈Γ
    with <dec n n'
  ... | Inl n<n'       = abort (too-small n<n' (_ , n∈Γ))
  dlt-delete {_} {(n' , a') :: []} {.n'} InH                 | Inr (Inl _) = ∅ , refl , λ ()
  dlt-delete {_} {(n' , a') :: ((n'' , a'') :: Γ)} {.n'} InH | Inr (Inl _)
    = ((n'' + 1+ n' , a'') :: Γ) , lem , λ {(_ , n'∈Γ+) → abort (too-small (n<m→n<s+m n<1+n) (_ , n'∈Γ+))}
      where
        lem : (n' , a') :: ((n'' , a'') :: Γ) == ((n'' + 1+ n' , a'') :: Γ) ,, (n' , a')
        lem
          with <dec n' (n'' + 1+ n')
        lem | Inl n'<n''+1+n' rewrite ! (undiff-1 n' n'' n'<n''+1+n') = refl
        lem | Inr (Inl false) = abort (lemma-math' {x1 = Z} false)
        lem | Inr (Inr false) = abort (<antisym false (n<m→n<s+m n<1+n))
  dlt-delete {Γ = (n' , a') :: Γ} InH       | Inr (Inr n'<n') = abort (<antirefl n'<n')
  dlt-delete {Γ = (n' , a') :: Γ} (InT n∈Γ) | Inr _
    with dlt-delete {Γ = Γ} n∈Γ
  dlt-delete {Γ = (n' , a') :: Γ} {.(_ + 1+ n')} {a} (InT {x = x} n∈Γ) | Inr _ | Γ⁻ , refl , x#Γ⁻
    = _ , lem' , lem
      where
        lem : (x + 1+ n') # ((n' , a') :: Γ⁻)
        lem (_ , x+1+n'∈Γ?)
          with sad-lemma x+1+n'∈Γ?
        ... | _ , _ , refl , x'==x+1+n' , InH = abort (lemma-math' {x1 = Z} x'==x+1+n')
        ... | _ , _ , refl , x'==x+1+n' , InT {x = x'} x+1+n'∈Γ'
          rewrite +inj {b = 1+ n'} x'==x+1+n'
            = x#Γ⁻ (_ , x+1+n'∈Γ')
        lem' : ((n' , a') :: (Γ⁻ ,, (x , a))) == ((n' , a') :: Γ⁻) ,, (x + 1+ n' , a)
        lem'
          with <dec (x + 1+ n') n'
        lem' | Inl x+1+n'<n'       = abort (<antisym x+1+n'<n' (n<m→n<s+m n<1+n))
        lem' | Inr (Inl false)     = abort (lemma-math' {x1 = Z} (! false))
        lem' | Inr (Inr n'<x+1+n') rewrite ! (undiff-1 n' x n'<x+1+n') = refl

  -- Allows the elimination of dlts. Never destruct a dlt via _::_
  dlt-elim : {A : Set} {Γ : A dlt} →
              Γ == ∅
                ∨
              Σ[ n ∈ Nat ] Σ[ a ∈ A ] Σ[ Γ' ∈ A dlt ]
                 (Γ == Γ' ,, (n , a) ∧ n # Γ')
  dlt-elim {Γ = []}            = Inl refl
  dlt-elim {Γ = (n , a) :: []} = Inr (_ , _ , _ , refl , x#∅)
  dlt-elim {Γ = (n , a) :: ((m , a2) :: Γ'')}
    with expr-eq (λ _ → (m + 1+ n , a2) :: Γ'')
  ... | Γ' , eq
    = Inr (n , a , Γ' , eqP , not-dom)
      where
        eqP : (n , a) :: ((m , a2) :: Γ'') == Γ' ,, (n , a)
        eqP rewrite eq with <dec n (m + 1+ n)
        ... | Inl n<m+1+n
          rewrite ! (undiff-1 n m n<m+1+n) = refl
        ... | Inr (Inl n==m+1+n)
          = abort (n≠n+1+m (n==m+1+n · (n+1+m==1+n+m · +comm {1+ m})))
        ... | Inr (Inr m+1+n<n)
          = abort (<antisym m+1+n<n (n<m→n<s+m n<1+n))
        not-dom : dom Γ' n → ⊥
        not-dom rewrite eq = λ n∈Γ' →
          too-small (n<m→n<s+m n<1+n) n∈Γ'

  -- When using dlt-elim or dlt-delete, this theorem is useful for establishing termination
  dlt-decreasing : {A : Set} {Γ : A dlt} {n : Nat} {a : A} →
                    n # Γ →
                    ∥ Γ ,, (n , a) ∥ == 1+ ∥ Γ ∥
  dlt-decreasing {Γ = []} n#Γ = refl
  dlt-decreasing {Γ = (n' , a') :: Γ} {n} n#Γ
    with <dec n n'
  ... | Inl n<n'       = refl
  ... | Inr (Inl refl) = abort (n#Γ (_ , InH))
  ... | Inr (Inr n'<n)
    = 1+ap (dlt-decreasing λ {(a , diff∈Γ) →
        n#Γ (a , tr
                   (λ y → (y , a) ∈ ((n' , a') :: Γ))
                   (m-n+n==m (n<m→1+n≤m n'<n))
                   (InT diff∈Γ))})

  ---- contrapositives of some previous theorems ----

  lem-neq-apart : {A : Set} {a : A} {n m : Nat} →
                    n ≠ m →
                    n # (■ (m , a))
  lem-neq-apart n≠m h = n≠m (lem-dom-eq h)

  x#Γ→x#Γ+ : {A : Set} {Γ : A dlt} {x x' : Nat} {a' : A} →
               x ≠ x' →
               x # Γ →
               x # (Γ ,, (x' , a'))
  x#Γ→x#Γ+ {Γ = Γ} {x} {x'} {a'} x≠x' x#Γ
    with dltindirect (Γ ,, (x' , a')) x
  ... | Inl (_ , x∈Γ+) = abort (x#Γ (_ , x∈Γ+→x∈Γ x≠x' x∈Γ+))
  ... | Inr x#Γ+       = x#Γ+

  x#Γ+→x#Γ : {A : Set} {Γ : A dlt} {x x' : Nat} {a' : A} →
               x # (Γ ,, (x' , a')) →
               x # Γ
  x#Γ+→x#Γ {Γ = Γ} {x} {x'} {a'} x#Γ+
    with dltindirect Γ x
  ... | Inr x#Γ       = x#Γ
  ... | Inl (_ , x∈Γ)
    with natEQ x x'
  ... | Inl refl = abort (x#Γ+ (_ , x,a∈Γ,,x,a {Γ = Γ}))
  ... | Inr x≠x' = abort (x#Γ+ (_ , x∈Γ→x∈Γ+ x≠x' x∈Γ))

  lookup-cp-1 : {A : Set} {Γ : A dlt} {x : Nat} →
                 x # Γ →
                 Γ ⦃⦃ x ⦄⦄ == None
  lookup-cp-1 {Γ = Γ} {x} x#Γ
    with lookup-dec Γ x
  ... | Inl (_ , x∈Γ) = abort (x#Γ (_ , (lookup-cons-1 x∈Γ)))
  ... | Inr x#'Γ      = x#'Γ

  lookup-cp-2 : {A : Set} {Γ : A dlt} {x : Nat} →
                 Γ ⦃⦃ x ⦄⦄ == None →
                 x # Γ
  lookup-cp-2 {Γ = Γ} {x} x#Γ
    with dltindirect Γ x
  ... | Inl (_ , x∈Γ) = abort (somenotnone ((! (lookup-cons-2 x∈Γ)) · x#Γ))
  ... | Inr x#'Γ      = x#'Γ

  ---- remaining definitions ----

  merge' : {A : Set} → (A → A → A) → Maybe A → A → A
  merge' merge ma1 a2
    with ma1
  ... | None    = a2
  ... | Some a1 = merge a1 a2

  union' : {A : Set} → (A → A → A) → A dlt → A dlt → Nat → A dlt
  union' merge Γ1 [] _ = Γ1
  union' merge Γ1 ((hx , ha) :: Γ2) offset
    = union' merge (Γ1 ,, (hx + offset , merge' merge (Γ1 ⦃⦃ hx + offset ⦄⦄) ha)) Γ2 (1+ hx + offset)

  union merge Γ1 Γ2 = union' merge Γ1 Γ2 0

  list⇒dlt = foldl _,,_ ∅

  dlt⇒list [] = []
  dlt⇒list ((x , a) :: Γ) = (x , a) :: map (λ {(x' , a') → x' + 1+ x , a'}) (dlt⇒list Γ)

  dlt⇒values = map π2

  list⇒list-dlt {A} l
    = foldl f ∅ (reverse l)
      where
        f : (List A) dlt → Nat ∧ A → (List A) dlt
        f Γ (n , a)
          with dltindirect Γ n
        ... | Inl (as , n∈Γ)
          = Γ ,, (n , a :: as)
        ... | Inr n#Γ
          = Γ ,, (n , a :: [])

  ---- union and dlt <=> list lemmas ----

  lemma-union'-0 : {A : Set} {m : A → A → A} {Γ1 Γ2 : A dlt} {x n : Nat} {a : A} →
                    (x , a) ∈ Γ1 →
                    (x , a) ∈ union' m Γ1 Γ2 (n + 1+ x)
  lemma-union'-0 {Γ2 = []} x∈Γ1 = x∈Γ1
  lemma-union'-0 {Γ2 = (x1 , a1) :: Γ2} {x} {n} x∈Γ1
    rewrite ! (+assc {1+ x1} {n} {1+ x})
      = lemma-union'-0 {Γ2 = Γ2} {n = 1+ x1 + n} (x∈Γ→x∈Γ+ (lemma-math' {x1 = x1} {n}) x∈Γ1)

  lemma-union'-1 : {A : Set} {m : A → A → A} {Γ1 Γ2 : A dlt} {x n : Nat} {a : A} →
                    (x , a) ∈ Γ1 →
                    (n≤x : n ≤ x) →
                    (difference n≤x) # Γ2 →
                    (x , a) ∈ union' m Γ1 Γ2 n
  lemma-union'-1 {Γ2 = []} {x} x∈Γ1 n≤x x-n#Γ2 = x∈Γ1
  lemma-union'-1 {m = m} {Γ1} {(x1 , a1) :: Γ2} {x} {n} {a} x∈Γ1 n≤x x-n#Γ2
    with <dec x (x1 + n)
  lemma-union'-1 {m = m} {Γ1} {(x1 , a1) :: Γ2} {x} {n} {a} x∈Γ1 n≤x x-n#Γ2 | Inl x<x1+n
    with Γ1 ⦃⦃ x1 + n ⦄⦄
  lemma-union'-1 {m = m} {Γ1} {(x1 , a1) :: Γ2} {x} {n} {a} x∈Γ1 n≤x x-n#Γ2 | Inl x<x1+n | Some a'
    = tr
         (λ y → (x , a) ∈ union' m (Γ1 ,, (x1 + n , m a' a1)) Γ2 y)
         (n+1+m==1+n+m {difference (π1 x<x1+n)} · 1+ap (m-n+n==m (π1 x<x1+n)))
         (lemma-union'-0 {Γ2 = Γ2} (x∈Γ→x∈Γ+ (π2 x<x1+n) x∈Γ1))
  lemma-union'-1 {m = m} {Γ1} {(x1 , a1) :: Γ2} {x} {n} {a} x∈Γ1 n≤x x-n#Γ2 | Inl x<x1+n | None
    = tr
         (λ y → (x , a) ∈ union' m (Γ1 ,, (x1 + n , a1)) Γ2 y)
         (n+1+m==1+n+m {difference (π1 x<x1+n)} · 1+ap (m-n+n==m (π1 x<x1+n)))
         (lemma-union'-0 {Γ2 = Γ2} (x∈Γ→x∈Γ+ (π2 x<x1+n) x∈Γ1))
  lemma-union'-1 {m = m} {Γ1} {(x1 , a1) :: Γ2} {x} {n} {a} x∈Γ1 n≤x x-n#Γ2 | Inr (Inl refl)
    rewrite +comm {x1} {n} | n+m-n==m n≤x
      = abort (x-n#Γ2 (_ , InH))
  lemma-union'-1 {m = m} {Γ1} {(x1 , a1) :: Γ2} {x} {n} {a} x∈Γ1 n≤x x-n#Γ2 | Inr (Inr x1+n<x)
    rewrite (! (a+b==c→a==c-b (+assc {diff-1 x1+n<x} · m-n+n==m (n<m→1+n≤m x1+n<x)) n≤x))
      = lemma-union'-1
          (x∈Γ→x∈Γ+ (flip (π2 x1+n<x)) x∈Γ1)
          (n<m→1+n≤m x1+n<x)
          λ {(_ , x-x1-n∈Γ2) → x-n#Γ2 (_ , InT x-x1-n∈Γ2)}

  lemma-union'-2 : {A : Set} {m : A → A → A} {Γ1 Γ2 : A dlt} {x n : Nat} {a : A} →
                    (x + n) # Γ1 →
                    (x , a) ∈ Γ2 →
                    (x + n , a) ∈ union' m Γ1 Γ2 n
  lemma-union'-2 {Γ1 = Γ1} x+n#Γ1 (InH {Γ = Γ2})
    rewrite lookup-cp-1 x+n#Γ1
      = lemma-union'-0 {Γ2 = Γ2} {n = Z} (x,a∈Γ,,x,a {Γ = Γ1})
  lemma-union'-2 {Γ1 = Γ1} {n = n} x+n#Γ1 (InT {Γ = Γ2} {x = x} {s} x∈Γ2)
    rewrite +assc {x} {1+ s} {n}
    with Γ1 ⦃⦃ s + n ⦄⦄
  ... | Some a'
    = lemma-union'-2
        (λ {(_ , x∈Γ1+) →
             x+n#Γ1 (_ , x∈Γ+→x∈Γ (flip (lemma-math' {x1 = Z})) x∈Γ1+)})
        x∈Γ2
  ... | None
    = lemma-union'-2
        (λ {(_ , x∈Γ1+) →
             x+n#Γ1 (_ , x∈Γ+→x∈Γ (flip (lemma-math' {x1 = Z})) x∈Γ1+)})
        x∈Γ2

  lemma-union'-3 : {A : Set} {m : A → A → A} {Γ1 Γ2 : A dlt} {x n : Nat} {a1 a2 : A} →
                    (x + n , a1) ∈ Γ1 →
                    (x , a2) ∈ Γ2 →
                    (x + n , m a1 a2) ∈ union' m Γ1 Γ2 n
  lemma-union'-3 {Γ1 = Γ1} x+n∈Γ1 (InH {Γ = Γ2})
    rewrite lookup-cons-2 x+n∈Γ1
      = lemma-union'-0 {Γ2 = Γ2} {n = Z} (x,a∈Γ,,x,a {Γ = Γ1})
  lemma-union'-3 {Γ1 = Γ1} {n = n} x+n∈Γ1 (InT {Γ = Γ2} {x = x} {s} x∈Γ2)
    rewrite +assc {x} {1+ s} {n}
    with Γ1 ⦃⦃ s + n ⦄⦄
  ... | Some a'
    = lemma-union'-3 (x∈Γ→x∈Γ+ (flip (lemma-math' {x1 = Z})) x+n∈Γ1) x∈Γ2
  ... | None
    = lemma-union'-3 (x∈Γ→x∈Γ+ (flip (lemma-math' {x1 = Z})) x+n∈Γ1) x∈Γ2

  lemma-union'-4 : {A : Set} {m : A → A → A} {Γ1 Γ2 : A dlt} {x n : Nat} →
                    dom (union' m Γ1 Γ2 n) x →
                    dom Γ1 x ∨ (Σ[ s ∈ Nat ] (x == n + s ∧ dom Γ2 s))
  lemma-union'-4 {Γ2 = []} x∈un = Inl x∈un
  lemma-union'-4 {Γ1 = Γ1} {(x1 , a1) :: Γ2} {x} {n} x∈un
    with lemma-union'-4 {Γ2 = Γ2} x∈un
  ... | Inr (s , refl , _ , s∈Γ2)
    rewrite +comm {x1} {n}
          | ! (n+1+m==1+n+m {n + x1} {s})
          | +assc {n} {x1} {1+ s}
          | +comm {x1} {1+ s}
          | ! (n+1+m==1+n+m {s} {x1})
      = Inr (_ , refl , _ , InT s∈Γ2)
  ... | Inl (_ , x∈Γ1+)
    with natEQ x (n + x1)
  ... | Inl refl   = Inr (_ , refl , _ , InH)
  ... | Inr x≠n+x1
    rewrite +comm {x1} {n}
      = Inl (_ , x∈Γ+→x∈Γ x≠n+x1 x∈Γ1+)

  lemma-dlt⇒list' : {A : Set} {Γ Γ' : A dlt} {x : Nat} {a : A} →
                        foldl
                          (λ {b (x' , a') → b ,, (x' + 1+ x , a')})
                          ((x , a) :: Γ')
                          Γ
                        == (x , a) :: foldl _,,_ Γ' Γ
  lemma-dlt⇒list' {Γ = []} = refl
  lemma-dlt⇒list' {Γ = (x2 , a2) :: Γ} {x = x}
    with <dec (x2 + 1+ x) x
  ... | Inl x2+1+x<x
    = abort (<antisym x2+1+x<x (n<m→n<s+m n<1+n))
  ... | Inr (Inl x2+1+x=x)
    = abort ((flip n≠n+1+m) (n+1+m==1+n+m · (+comm {1+ x} · x2+1+x=x)))
  ... | Inr (Inr x<x2+1+x)
    rewrite ! (undiff-1 x x2 x<x2+1+x)
      = lemma-dlt⇒list' {Γ = Γ}

  ---- union theorems ----

  x,a∈Γ1→x∉Γ2→x,a∈Γ1∪Γ2 : {A : Set} {m : A → A → A} {Γ1 Γ2 : A dlt} {x : Nat} {a : A} →
                              (x , a) ∈ Γ1 →
                              x # Γ2 →
                              (x , a) ∈ union m Γ1 Γ2
  x,a∈Γ1→x∉Γ2→x,a∈Γ1∪Γ2 {Γ2 = Γ2} x∈Γ1 x#Γ2
    = lemma-union'-1 x∈Γ1 0≤n (tr (λ y → y # Γ2) (! (n+m-n==m 0≤n)) x#Γ2)

  x∉Γ1→x,a∈Γ2→x,a∈Γ1∪Γ2 : {A : Set} {m : A → A → A} {Γ1 Γ2 : A dlt} {x : Nat} {a : A} →
                              x # Γ1 →
                              (x , a) ∈ Γ2 →
                              (x , a) ∈ union m Γ1 Γ2
  x∉Γ1→x,a∈Γ2→x,a∈Γ1∪Γ2 {Γ1 = Γ1} {x = x} x#Γ1 x∈Γ2
    with lemma-union'-2 {n = Z} (tr (λ y → y # Γ1) (! n+Z==n) x#Γ1) x∈Γ2
  ... | rslt
    rewrite n+Z==n {x}
      = rslt

  x∈Γ1→x∈Γ2→x∈Γ1∪Γ2 : {A : Set} {m : A → A → A} {Γ1 Γ2 : A dlt} {x : Nat} {a1 a2 : A} →
                              (x , a1) ∈ Γ1 →
                              (x , a2) ∈ Γ2 →
                              (x , m a1 a2) ∈ union m Γ1 Γ2
  x∈Γ1→x∈Γ2→x∈Γ1∪Γ2 {Γ1 = Γ1} {Γ2} {x} {a1} x∈Γ1 x∈Γ2
    with lemma-union'-3 (tr (λ y → (y , a1) ∈ Γ1) (! n+Z==n) x∈Γ1) x∈Γ2
  ... | rslt
    rewrite n+Z==n {x}
      = rslt

  x∈Γ1∪Γ2→x∈Γ1∨x∈Γ2 : {A : Set} {m : A → A → A} {Γ1 Γ2 : A dlt} {x : Nat} →
                          dom (union m Γ1 Γ2) x →
                          dom Γ1 x ∨ dom Γ2 x
  x∈Γ1∪Γ2→x∈Γ1∨x∈Γ2 x∈Γ1∪Γ2
    with lemma-union'-4 {n = Z} x∈Γ1∪Γ2
  x∈Γ1∪Γ2→x∈Γ1∨x∈Γ2 x∈Γ1∪Γ2 | Inl x'∈Γ1 = Inl x'∈Γ1
  x∈Γ1∪Γ2→x∈Γ1∨x∈Γ2 x∈Γ1∪Γ2 | Inr (_ , refl , x'∈Γ2) = Inr x'∈Γ2

  ---- dlt <=> list theorems ----
  dlt⇒list-inversion : {A : Set} {Γ : A dlt} → list⇒dlt (dlt⇒list Γ) == Γ
  dlt⇒list-inversion {Γ = []} = refl
  dlt⇒list-inversion {Γ = (x , a) :: Γ}
    with dlt⇒list-inversion {Γ = Γ}
  ... | rec
    = foldl-map {l = dlt⇒list Γ} {_,,_} {λ {(x' , a') → x' + 1+ x , a'}} {(x , a) :: []}
      · (lemma-dlt⇒list' {Γ = dlt⇒list Γ} · ap1 (λ y → (x , a) :: y) rec)

  ---- contraction and exchange ----

  -- TODO these proofs could use refactoring -
  -- contraction should probably make use of dlt-==-dec and
  -- exchange is way too long and repetitive

  contraction : {A : Set} {Γ : A dlt} {x : Nat} {a a' : A} →
                 Γ ,, (x , a') ,, (x , a) == Γ ,, (x , a)
  contraction {Γ = []} {x} rewrite <dec-refl x = refl
  contraction {Γ = (hx , ha) :: t} {x} {a} {a'}
    with <dec x hx
  ... | Inl _          rewrite <dec-refl x  = refl
  ... | Inr (Inl refl) rewrite <dec-refl hx = refl
  ... | Inr (Inr hx<x)
    with <dec x hx
  ... | Inl x<hx        = abort (<antisym x<hx hx<x)
  ... | Inr (Inl refl)  = abort (<antirefl hx<x)
  ... | Inr (Inr hx<'x)
    rewrite diff-proof-irrelevance (n<m→1+n≤m hx<x) (n<m→1+n≤m hx<'x)
          | contraction {Γ = t} {diff-1 hx<'x} {a} {a'}
    = refl

  exchange : {A : Set} {Γ : A dlt} {x1 x2 : Nat} {a1 a2 : A} →
              x1 ≠ x2 →
              Γ ,, (x1 , a1) ,, (x2 , a2) == Γ ,, (x2 , a2) ,, (x1 , a1)
  exchange {A} {Γ} {x1} {x2} {a1} {a2} x1≠x2
    = dlt-==-eqv fun
      where
        fun : (x : Nat) →
               (Γ ,, (x1 , a1) ,, (x2 , a2)) ⦃⦃ x ⦄⦄ ==
               (Γ ,, (x2 , a2) ,, (x1 , a1)) ⦃⦃ x ⦄⦄
        fun x
          with natEQ x x1 | natEQ x x2 | dltindirect Γ x
        fun x  | Inl refl | Inl refl | _
          = abort (x1≠x2 refl)
        fun x1 | Inl refl | Inr x≠x2 | Inl (_ , x1∈Γ)
          with x,a∈Γ,,x,a {Γ = Γ} {x1} {a1}
        ... | x∈Γ+1
          with x∈Γ→x∈Γ+ {a' = a2} x≠x2 x∈Γ+1 | x,a∈Γ,,x,a {Γ = Γ ,, (x2 , a2)} {x1} {a1}
        ... | x∈Γ++1 | x∈Γ++2
          rewrite lookup-cons-2 x∈Γ++1 | lookup-cons-2 x∈Γ++2 = refl
        fun x1 | Inl refl | Inr x≠x2 | Inr x1#Γ
          with x,a∈Γ,,x,a {Γ = Γ} {x1} {a1}
        ... | x∈Γ+1
          with x∈Γ→x∈Γ+ {a' = a2} x≠x2 x∈Γ+1 | x,a∈Γ,,x,a {Γ = Γ ,, (x2 , a2)} {x1} {a1}
        ... | x∈Γ++1 | x∈Γ++2
          rewrite lookup-cons-2 x∈Γ++1 | lookup-cons-2 x∈Γ++2 = refl
        fun x2 | Inr x≠x1 | Inl refl | Inl (_ , x2∈Γ)
          with x,a∈Γ,,x,a {Γ = Γ} {x2} {a2}
        ... | x∈Γ+2
          with x∈Γ→x∈Γ+ {a' = a1} x≠x1 x∈Γ+2 | x,a∈Γ,,x,a {Γ = Γ ,, (x1 , a1)} {x2} {a2}
        ... | x∈Γ++1 | x∈Γ++2
          rewrite lookup-cons-2 x∈Γ++1 | lookup-cons-2 x∈Γ++2 = refl
        fun x2 | Inr x≠x1 | Inl refl | Inr x2#Γ
          with x,a∈Γ,,x,a {Γ = Γ} {x2} {a2}
        ... | x∈Γ+2
          with x∈Γ→x∈Γ+ {a' = a1} x≠x1 x∈Γ+2 | x,a∈Γ,,x,a {Γ = Γ ,, (x1 , a1)} {x2} {a2}
        ... | x∈Γ++1 | x∈Γ++2
          rewrite lookup-cons-2 x∈Γ++1 | lookup-cons-2 x∈Γ++2 = refl
        fun x  | Inr x≠x1 | Inr x≠x2 | Inl (_ , x∈Γ)
          with x∈Γ→x∈Γ+ {a' = a1} x≠x1 x∈Γ   | x∈Γ→x∈Γ+ {a' = a2} x≠x2 x∈Γ
        ... | x∈Γ+1  | x∈Γ+2
          with x∈Γ→x∈Γ+ {a' = a2} x≠x2 x∈Γ+1 | x∈Γ→x∈Γ+ {a' = a1} x≠x1 x∈Γ+2
        ... | x∈Γ++1 | x∈Γ++2
          rewrite lookup-cons-2 x∈Γ++1 | lookup-cons-2 x∈Γ++2 = refl
        fun x  | Inr x≠x1 | Inr x≠x2 | Inr x#Γ
          with x#Γ→x#Γ+ {a' = a1} x≠x1 x#Γ   | x#Γ→x#Γ+ {a' = a2} x≠x2 x#Γ
        ... | x#Γ+1  | x#Γ+2
          with x#Γ→x#Γ+ {a' = a2} x≠x2 x#Γ+1 | x#Γ→x#Γ+ {a' = a1} x≠x1 x#Γ+2
        ... | x#Γ++1 | x#Γ++2
          rewrite lookup-cp-1 x#Γ++1 | lookup-cp-1 x#Γ++2 = refl
