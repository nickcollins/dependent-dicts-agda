open import Prelude
open import Nat
open import Agda.Primitive using (Level; lzero; lsuc) renaming (_⊔_ to lmax)

module List where

  -- definitions

  data List (A : Set) : Set where
    [] : List A
    _::_ : A → List A → List A

  _++_ : {A : Set} → List A → List A → List A
  [] ++ l₂ = l₂
  (h :: l₁) ++ l₂ = h :: (l₁ ++ l₂)

  infixl 50 _++_

  ∥_∥ : {A : Set} → List A → Nat
  ∥ [] ∥ = Z
  ∥ a :: as ∥ = 1+ ∥ as ∥

  _⟦_⟧ : {A : Set} → List A → Nat → Maybe A
  [] ⟦ i ⟧ = None
  (a :: as) ⟦ Z ⟧ = Some a
  (a :: as) ⟦ 1+ i ⟧ = as ⟦ i ⟧

  data _In_ : {A : Set} → A → List A → Set where
    LInH : ∀{A} {a : A} {l : List A} → a In (a :: l)
    LInT : ∀{A} {a a' : A} {l : List A} → a In l → a In (a' :: l)

  _⫇_ : {A : Set} → List A → List A → Set
  _⫇_ {A} l1 l2 = (i1 : Nat) (a : A) →
                  l1 ⟦ i1 ⟧ == Some a →
                  Σ[ i2 ∈ Nat ] (l2 ⟦ i2 ⟧ == Some a)

  _≈_ : {A : Set} → List A → List A → Set
  _≈_ {A} l1 l2 = l1 ⫇ l2 ∧ l2 ⫇ l1

  reverse : {A : Set} → List A → List A
  reverse [] = []
  reverse (a :: as) = reverse as ++ (a :: [])

  map : {A B : Set} → (A → B) → List A → List B
  map f [] = []
  map f (a :: as) = f a :: map f as

  foldl : {A B : Set} → (B → A → B) → B → List A → B
  foldl f b [] = b
  foldl f b (a :: as) = foldl f (f b a) as

  foldr : {A B : Set} → (B → A → B) → B → List A → B
  foldr f b = foldl f b ⊙ reverse

  concat : {A : Set} → List (List A) → List A
  concat [] = []
  concat (l1 :: rest) = l1 ++ (concat rest)

  -- if the lists aren't the same length,
  -- the extra elements of the longer list are ignored
  zip : {A B : Set} → List A → List B → List (A ∧ B)
  zip []        _         = []
  zip (a :: as) []        = []
  zip (a :: as) (b :: bs) = (a , b) :: zip as bs

  unzip : {A B : Set} → List (A ∧ B) → (List A ∧ List B)
  unzip [] = ([] , [])
  unzip ((a , b) :: rest)
    with unzip rest
  ... | (as , bs) = (a :: as , b :: bs)

  -- theorems

  list-==-dec :  {A : Set} →
                 (l1 l2 : List A) →
                 ((a1 a2 : A) → a1 == a2 ∨ a1 ≠ a2) →
                 l1 == l2 ∨ l1 ≠ l2
  list-==-dec [] [] A-==-dec       = Inl refl
  list-==-dec [] (_ :: _) A-==-dec = Inr (λ ())
  list-==-dec (_ :: _) [] A-==-dec = Inr (λ ())
  list-==-dec (h1 :: t1) (h2 :: t2) A-==-dec
    with A-==-dec h1 h2
  ... | Inr ne = Inr (λ where refl → ne refl)
  ... | Inl refl
    with list-==-dec t1 t2 A-==-dec
  ... | Inr ne = Inr (λ where refl → ne refl)
  ... | Inl refl = Inl refl

  -- if the items of two lists are equal, then the lists are equal
  ==-per-elem : {A : Set} → {l1 l2 : List A} →
                 ((i : Nat) → l1 ⟦ i ⟧ == l2 ⟦ i ⟧) →
                 l1 == l2
  ==-per-elem {l1 = []} {[]} items== = refl
  ==-per-elem {l1 = []} {h2 :: t2} items== = abort (somenotnone (! (items== Z)))
  ==-per-elem {l1 = h1 :: t1} {[]} items== = abort (somenotnone (items== Z))
  ==-per-elem {l1 = h1 :: t1} {h2 :: t2} items==
    rewrite someinj (items== Z) | ==-per-elem {l1 = t1} {t2} (λ i → items== (1+ i))
      = refl

  -- _++_ theorems
  ++assc : ∀{A a1 a2 a3} → (_++_ {A} a1 a2) ++ a3 == a1 ++ (a2 ++ a3)
  ++assc {A} {[]} {a2} {a3} = refl
  ++assc {A} {x :: a1} {a2} {a3} with a1 ++ a2 ++ a3 | ++assc {A} {a1} {a2} {a3}
  ++assc {A} {x :: a1} {a2} {a3} | _ | refl = refl

  l++[]==l : {A : Set} (l : List A) →
              l ++ [] == l
  l++[]==l [] = refl
  l++[]==l (a :: as)
    rewrite l++[]==l as
      = refl

  -- ∥_∥ theorem
  ∥-++-comm : ∀{A a1 a2} → ∥ a1 ∥ + (∥_∥ {A} a2) == ∥ a1 ++ a2 ∥
  ∥-++-comm {A} {[]} {a2} = refl
  ∥-++-comm {A} {a :: a1} {a2} = 1+ap (∥-++-comm {A} {a1})

  -- _⟦_⟧ and ++ theorem
  ⦇l1++[a]++l2⦈⟦∥l1∥⟧==a : {A : Set} {l1 l2 : List A} {a : A} →
                             (l1 ++ (a :: []) ++ l2) ⟦ ∥ l1 ∥ ⟧ == Some a
  ⦇l1++[a]++l2⦈⟦∥l1∥⟧==a {l1 = []} = refl
  ⦇l1++[a]++l2⦈⟦∥l1∥⟧==a {l1 = a1 :: l1rest} {l2} {a} = ⦇l1++[a]++l2⦈⟦∥l1∥⟧==a {l1 = l1rest} {l2}

  -- packaging of list indexing results
  list-index-dec : {A : Set} (l : List A) (i : Nat) →
                    l ⟦ i ⟧ == None ∨ Σ[ a ∈ A ] (l ⟦ i ⟧ == Some a)
  list-index-dec l i
    with l ⟦ i ⟧
  ... | None   = Inl refl
  ... | Some a = Inr (a , refl)

  -- theorems characterizing the partiality of list indexing
  list-index-some : {A : Set} {l : List A} {i : Nat} →
                     i < ∥ l ∥ →
                     Σ[ a ∈ A ] (l ⟦ i ⟧ == Some a)
  list-index-some {l = []}      {Z}    i<∥l∥ = abort (n≮0 i<∥l∥)
  list-index-some {l = a :: as} {Z}    i<∥l∥ = _ , refl
  list-index-some {l = a :: as} {1+ i} i<∥l∥ = list-index-some (1+n<1+m→n<m i<∥l∥)

  list-index-none : {A : Set} {l : List A} {i : Nat} →
                     ∥ l ∥ ≤ i →
                     l ⟦ i ⟧ == None
  list-index-none {l = []}             i≥∥l∥ = refl
  list-index-none {l = a :: as} {1+ i} i≥∥l∥ = list-index-none (1+n≤1+m→n≤m i≥∥l∥)

  list-index-some-conv : {A : Set} {l : List A} {i : Nat} {a : A} →
                          l ⟦ i ⟧ == Some a →
                          i < ∥ l ∥
  list-index-some-conv {l = l} {i} i≥∥l∥
    with <dec ∥ l ∥ i
  ... | Inr (Inr i<∥l∥) = i<∥l∥
  ... | Inr (Inl refl)
    rewrite list-index-none {l = l} {∥ l ∥} ≤refl
      = abort (somenotnone (! i≥∥l∥))
  ... | Inl ∥l∥<i
    rewrite list-index-none (n<m→n≤m ∥l∥<i)
      = abort (somenotnone (! i≥∥l∥))

  list-index-none-conv : {A : Set} {l : List A} {i : Nat} →
                          l ⟦ i ⟧ == None →
                          ∥ l ∥ ≤ i
  list-index-none-conv {l = l} {i} i≥∥l∥
    with <dec ∥ l ∥ i
  ... | Inl ∥l∥<i       = n<m→n≤m ∥l∥<i
  ... | Inr (Inl refl) = ≤refl
  ... | Inr (Inr i<∥l∥)
    with list-index-some i<∥l∥
  ... | _ , i≱∥l∥ rewrite i≥∥l∥ = abort (somenotnone (! i≱∥l∥))

  ∥l1∥==∥l2∥→l1[i]→l2[i] : {A B : Set} {la : List A} {lb : List B} {i : Nat} {a : A} →
                             ∥ la ∥ == ∥ lb ∥ →
                             la ⟦ i ⟧ == Some a →
                             Σ[ b ∈ B ] (lb ⟦ i ⟧ == Some b)
  ∥l1∥==∥l2∥→l1[i]→l2[i] {i = i} ∥la∥==∥lb∥ la[i]==a
    = list-index-some (tr (λ y → i < y) ∥la∥==∥lb∥ (list-index-some-conv la[i]==a))

  ∥l1∥==∥l2∥→¬l1[i]→¬l2[i] : {A B : Set} {la : List A} {lb : List B} {i : Nat} →
                                ∥ la ∥ == ∥ lb ∥ →
                                la ⟦ i ⟧ == None →
                                lb ⟦ i ⟧ == None
  ∥l1∥==∥l2∥→¬l1[i]→¬l2[i] {i = i} ∥la∥==∥lb∥ la[i]==None
    = list-index-none (tr (λ y → y ≤ i) ∥la∥==∥lb∥ (list-index-none-conv la[i]==None))

  -- more list indexing theorems
  i∈l2→|l1|+i∈l1++l2 : {A : Set} {l1 l2 : List A} {i : Nat} {a : A} →
                          l2 ⟦ i ⟧ == Some a →
                          (l1 ++ l2) ⟦ ∥ l1 ∥ + i ⟧ == Some a
  i∈l2→|l1|+i∈l1++l2 {l1 = []} i∈l2 = i∈l2
  i∈l2→|l1|+i∈l1++l2 {l1 = a1 :: l1} i∈l2 = i∈l2→|l1|+i∈l1++l2 {l1 = l1} i∈l2

  i∈l1→i∈l1++l2 : {A : Set} {l1 l2 : List A} {i : Nat} {a : A} →
                      l1 ⟦ i ⟧ == Some a →
                      (l1 ++ l2) ⟦ i ⟧ == Some a
  i∈l1→i∈l1++l2 {l1 = a1 :: l1} {i = Z} i∈l1 = i∈l1
  i∈l1→i∈l1++l2 {l1 = a1 :: l1} {i = 1+ i} i∈l1 = i∈l1→i∈l1++l2 {l1 = l1} i∈l1

  append-index-split : {A : Set} {l1 l2 : List A} {i : Nat} {a : A} →
                         (l1 ++ l2) ⟦ i ⟧ == Some a →
                         l1 ⟦ i ⟧ == Some a ∨ (Σ[ j ∈ Nat ] (∥ l1 ∥ + j == i ∧ l2 ⟦ j ⟧ == Some a))
  append-index-split {l1 = []} i∈l1==l2 = Inr (_ , refl , i∈l1==l2)
  append-index-split {l1 = a1 :: l1} {i = Z} i∈l1==l2 = Inl i∈l1==l2
  append-index-split {l1 = a1 :: l1} {i = 1+ i} i∈l1==l2
    with append-index-split {l1 = l1} i∈l1==l2
  ... | Inl i∈l1 = Inl i∈l1
  ... | Inr (j , |l1|+j=i , j∈l2) = Inr (_ , 1+ap |l1|+j=i , j∈l2)

  -- reverse theorems
  reverse-single : {A : Set} {a : A} → reverse (a :: []) == a :: []
  reverse-single = refl

  reverse-++ : {A : Set} {l1 l2 : List A} →
                reverse (l1 ++ l2) == reverse l2 ++ reverse l1
  reverse-++ {l1 = []} {l2}
    rewrite l++[]==l (reverse l2)
      = refl
  reverse-++ {l1 = a1 :: as1} {l2}
    rewrite reverse-++ {l1 = as1} {l2}
      = ++assc {a1 = reverse l2}

  reverse-inv : {A : Set} {l : List A} → reverse (reverse l) == l
  reverse-inv {l = []} = refl
  reverse-inv {l = a :: as}
    rewrite reverse-++ {l1 = reverse as} {a :: []} | reverse-inv {l = as}
      = refl

  -- map theorems
  map-ext : ∀{A B : Set} {f g : A → B} {l : List A} →
              ((a : A) → f a == g a) →
              map f l == map g l
  map-ext {l = []} ext = refl
  map-ext {l = a :: l} ext rewrite ext a | map-ext {l = l} ext = refl

  map-id : ∀{A : Set} {l : List A} → map (λ a → a) l == l
  map-id {l = []} = refl
  map-id {l = a :: l} rewrite map-id {l = l} = refl

  map-len : ∀{A B : Set} {f : A → B} {l : List A} → ∥ map f l ∥ == ∥ l ∥
  map-len {l = []} = refl
  map-len {l = _ :: l} = 1+ap map-len

  map-In : ∀{A B : Set} {f : A → B} {l : List A} {a : A} →
             a In l →
             f a In map f l
  map-In LInH = LInH
  map-In (LInT aInL) = LInT (map-In aInL)

  map-++-comm : ∀{A B f a b} → map f a ++ map f b == map {A} {B} f (a ++ b)
  map-++-comm {a = []} = refl
  map-++-comm {A} {B} {f} {h :: t} {b} with map f (t ++ b) | map-++-comm {A} {B} {f} {t} {b}
  map-++-comm {A} {B} {f} {h :: t} {b} | _ | refl = refl

  map^2 : ∀{A B C f g l} → map {B} {C} f (map {A} {B} g l) == map (f ⊙ g) l
  map^2 {l = []} = refl
  map^2 {f = f} {g} {h :: t} rewrite map^2 {f = f} {g} {t} = refl

  reverse-map : {A B : Set} {f : A → B} {l : List A} → reverse (map f l) == map f (reverse l)
  reverse-map {l = []} = refl
  reverse-map {f = f} {a' :: l}
    rewrite reverse-map {f = f} {l}
      = map-++-comm {a = reverse l}

  -- foldl theorem
  foldl-++ : {A B : Set} {l1 l2 : List A} {f : B → A → B} {b0 : B} →
              foldl f b0 (l1 ++ l2) == foldl f (foldl f b0 l1) l2
  foldl-++ {l1 = []} = refl
  foldl-++ {l1 = a1 :: l1rest} = foldl-++ {l1 = l1rest}

  -- fold+map theorem
  foldl-map : {A' A B : Set} {l : List A'} {f-fold : B → A → B} {f-map : A' → A} {b0 : B} →
               foldl f-fold b0 (map f-map l) == foldl (λ b a' → f-fold b (f-map a')) b0 l
  foldl-map {l = []} = refl
  foldl-map {l = a' :: l} {f-fold} {f-map} {b0} = foldl-map {l = l}

  foldr-map : {A' A B : Set} {l : List A'} {f-fold : B → A → B} {f-map : A' → A} {b0 : B} →
               foldr f-fold b0 (map f-map l) == foldr (λ b a' → f-fold b (f-map a')) b0 l
  foldr-map {l = l} {_} {f}
    rewrite reverse-map {f = f} {l}
      = foldl-map {l = reverse l}

  -- zip/unzip theorems
  unzip-inv : {A B : Set} {l : List (A ∧ B)} {la : List A} {lb : List B} →
               unzip l == (la , lb) →
               l == zip la lb
  unzip-inv {l = []} form
    with form
  ... | refl = refl
  unzip-inv {l = (a' , b') :: rest} {a :: as} {b :: bs} form
    with unzip rest  | unzip-inv {l = rest} refl | form
  ...  | (as' , bs') | refl                      | refl = refl

  zip-inv : {A B : Set} {la : List A} {lb : List B} →
             ∥ la ∥ == ∥ lb ∥ →
             unzip (zip la lb) == (la , lb)
  zip-inv {la = []}      {[]}      len-eq = refl
  zip-inv {la = a :: as} {b :: bs} len-eq
    with unzip (zip as bs) | zip-inv (1+inj len-eq)
  ...  | (as' , bs')       | refl                   = refl

  -- _≈_ theorems
  ≈-++-comm-lem' : (A : Set) (l1 l2 : List A) (i : Nat) (a : A) →
                   (l1 ++ l2) ⟦ i ⟧ == Some a →
                   Σ[ i' ∈ Nat ] ((l2 ++ l1) ⟦ i' ⟧ == Some a)
  ≈-++-comm-lem' A l1 l2 i a i∈l1++l2
    with append-index-split {l1 = l1} i∈l1++l2
  ... | Inl i∈l1 = _ , i∈l2→|l1|+i∈l1++l2 {l1 = l2} i∈l1
  ... | Inr (j , |l1|+j=i , j∈l2) = _ , i∈l1→i∈l1++l2 {l1 = l2} j∈l2

  ≈-++-comm : {A : Set} {l1 l2 : List A} → l1 ++ l2 ≈ l2 ++ l1
  ≈-++-comm {A} {l1} {l2} = ≈-++-comm-lem' A l1 l2 , ≈-++-comm-lem' A l2 l1

  ≈-++-dup : {A : Set} {l : List A} → l ++ l ≈ l
  ≈-++-dup {l = []} = (λ i a ()) , (λ i a ())
  ≈-++-dup {A} {a :: l}
    = ≈-++-dup'1 , ≈-++-dup'2
      where
      ≈-++-dup'1 : (i : Nat) (a' : A) →
                   (a :: (l ++ (a :: l))) ⟦ i ⟧ == Some a' →
                   Σ[ i' ∈ Nat ] ((a :: l) ⟦ i' ⟧ == Some a')
      ≈-++-dup'1 Z a' i∈alal = Z , i∈alal
      ≈-++-dup'1 (1+ i) a' i∈alal
        with append-index-split {l1 = l} i∈alal
      ... | Inl i∈l = (1+ i) , i∈l
      ... | Inr (j , |l1|+j=i , j∈al) = j , j∈al

      ≈-++-dup'2 : (i : Nat) (a' : A) →
                   (a :: l) ⟦ i ⟧ == Some a' →
                   Σ[ i' ∈ Nat ] ((a :: (l ++ (a :: l))) ⟦ i' ⟧ == Some a')
      ≈-++-dup'2 i a' i∈al = (1 + ∥ l ∥ + i) , i∈l2→|l1|+i∈l1++l2 {l1 = l} i∈al
