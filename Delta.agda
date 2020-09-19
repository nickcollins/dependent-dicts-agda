open import Prelude
open import Nat
open import List
open import Bij

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
-- * We use "Some" and "None" instead of "Just" and "Nothing"
-- * abort is used to prove any goal given ⊥
-- * == is used for reflexive equality
-- * Z is zero, 1+ is suc
-- * ≤ is defined as data, < is defined as n < m = n ≤ m ∧ n ≠ m
-- * TODO if we don't switch to truncation, we need to talk about subtraction
-- * l⟦ i ⟧ is used to (maybe) get the ith element of list l
-- * ∥ l ∥ is the length of a list
--
-- Many of the definitions and theorems are documented to indicate their equivalents
-- in the Coq standard libraries Coq.FSets.FMapInterface and Coq.FSets.FMapFacts
module Delta (K : Set) {{bij : bij K Nat}} where
  abstract -- almost everything in the module is abstract

    open import delta-lemmas K {{bij}}

    ---- core definitions ----

    data dd (V : Set) : Set where
      DD : dl V → dd V

    -- nil/empty
    ∅ : {V : Set} → dd V
    ∅ = DD []

    -- singleton
    ■_ : {V : Set} → (K ∧ V) → dd V
    ■_ (k , v) = DD <| (nat k , v) :: []

    -- extension/insertion
    -- Corresponds to FMapInterface.add
    _,,_ : ∀{V} → dd V → (K ∧ V) → dd V
    (DD d) ,, (k , v) = DD <| d ,,' (nat k , v)

    infixl 10 _,,_

    -- lookup function
    -- Corresponds to FMapInterface.find
    _⟨_⟩ : {V : Set} → dd V → K → Maybe V
    (DD d) ⟨ k ⟩ = d lkup (nat k)

    -- There doesn't appear to be a corresponding function in FMapInterface
    destruct : ∀{V} → dd V → Maybe ((K ∧ V) ∧ dd V)
    destruct (DD [])
      = None
    destruct (DD ((n , v) :: []))
      = Some ((key n , v) , DD [])
    destruct (DD ((n , v) :: ((m , v') :: dd)))
      = Some ((key n , v) , DD ((m + 1+ n , v') :: dd))

    -- size
    -- Corresponds to FMapInterface.cardinal
    ||_|| : {V : Set} → dd V → Nat
    || DD d || = ∥ d ∥

    -- membership
    -- Corresponds to FMapInterface.MapsTo
    _∈_ : {V : Set} (p : K ∧ V) → (d : dd V) → Set
    _∈_ {V} (k , v) (DD d) = _∈'_ {V} (nat k , v) d

  -- domain (not abstract)
  -- Corresponds to FMapInterface.In
  dom : {V : Set} → dd V → K → Set
  dom {V} d k = Σ[ v ∈ V ] ((k , v) ∈ d)

  -- apartness, i.e. the opposite of dom (not abstract)
  _#_ : {V : Set} → K → dd V → Set
  k # d = dom d k → ⊥

  abstract

    -- maps f across the values of the delta dict
    -- Corresponds to FMapInterface.map
    dltmap : {A B : Set} → (A → B) → dd A → dd B
    dltmap f (DD d) = DD <| map (λ {(hn , hv) → (hn , f hv)}) d

    -- FMapInterface doesn't appear to have a corresponding function
    list⇒dlt : {V : Set} → List (K ∧ V) → dd V
    list⇒dlt d = d |> map (λ where (k , v) → (nat k , v)) |> list⇒dlt' |> DD

    -- converts a delta dict into a list of key-value pairs; the inverse of list⇒dlt
    -- Corresponds to FMapInterface.elements
    dlt⇒list : {V : Set} → dd V → List (K ∧ V)
    dlt⇒list (DD d) = dlt⇒list' d |> map (λ where (n , v) → (key n , v))

    -- union merge A B is the union of A and B,
    -- with (merge a b) being invoked to handle the mappings they have in common
    union : {V : Set} → (V → V → V) → dd V → dd V → dd V
    union merge (DD d1) (DD d2) = DD <| union' merge d1 d2 0

    ---- core theorems ----

    -- The next two theorems show that lookup (_⟨_⟩) is consistent with membership (_∈_)
    -- As such, future theorems which relate to membership can be taken to appropriately
    -- comment on lookup as well.
    -- Corresponds to FMapInterface.find_1
    lookup-cons-1 : {V : Set} {d : dd V} {k : K} {v : V} →
                     (k , v) ∈ d →
                     d ⟨ k ⟩ == Some v
    lookup-cons-1 {V} {DD d} {k} {v} = lookup-cons-1' {V} {d} {nat k} {v}

    -- Corresponds to FMapInterface.find_2
    lookup-cons-2 : {V : Set} {d : dd V} {k : K} {v : V} →
                     d ⟨ k ⟩ == Some v →
                     (k , v) ∈ d
    lookup-cons-2 {V} {DD d} {k} {v} h = lookup-cons-2' {d = d} {nat k} h

    -- membership (_∈_) respects insertion (_,,_)
    -- Corresponds to FMapInterface.add_1
    k,v∈d,,k,v : {V : Set} {d : dd V} {k : K} {v : V} →
                  (k , v) ∈ (d ,, (k , v))
    k,v∈d,,k,v {V} {d = DD d} {k} = n,v∈'d,,n,v {d = d} {nat k}

    -- insertion respects membership
    -- Corresponds to FMapInterface.add_2
    k∈d→k∈d+ : {V : Set} {d : dd V} {k k' : K} {v v' : V} →
                  k ≠ k' →
                  (k , v) ∈ d →
                  (k , v) ∈ (d ,, (k' , v'))
    k∈d→k∈d+ {V} {DD d} {k} {k'} {v} {v'} ne h
      = n∈d→'n∈d+ {V} {d} {nat k} {nat k'} {v} {v'} (inj-cp ne) h

    -- insertion can't generate spurious membership
    -- Corresponds to FMapInterface.add_3
    k∈d+→k∈d : {V : Set} {d : dd V} {k k' : K} {v v' : V} →
                k ≠ k' →
                (k , v) ∈ (d ,, (k' , v')) →
                (k , v) ∈ d
    k∈d+→k∈d {V} {d = DD d} {k} {k'} {v} {v'} ne h
      = n∈d+→'n∈d {V} {d} {nat k} {nat k'} {v} {v'} (inj-cp ne) h

    -- Decidability of membership
    -- This also packages up an appeal to delta dict membership into a form that
    -- lets us retain more information
    -- Corresponds to FMapFacts.In_dec
    mem-dec : {V : Set} (d : dd V) (k : K) → dom d k ∨ k # d
    mem-dec {V} (DD d) k = mem-dec' {V} d (nat k)

    -- delta dicts contain at most one binding for each variable
    -- Corresponds to FMapFacts.MapsTo_fun
    mem-unicity : {V : Set} {d : dd V} {k : K} {v v' : V} →
                   (k , v) ∈ d →
                   (k , v') ∈ d →
                   v == v'
    mem-unicity vh v'h
      with lookup-cons-1 vh | lookup-cons-1 v'h
    ... | vh' | v'h' = someinj (! vh' · v'h')

    -- meaning of nil, i.e. nothing is in nil
    -- Corresponds to FMapFacts.empty_in_iff
    k#∅ : {V : Set} {k : K} → _#_ {V} k ∅
    k#∅ (_ , ())

    -- meaning of the singleton
    ■-def : {V : Set} {k : K} {v : V} → (■ (k , v)) == ∅ ,, (k , v)
    ■-def = refl

    -- Theorem 2: Extensionality
    -- (i.e. if two dicts represent the same mapping from ids to values,
    -- then they are reflexively equal as judged by _==_)
    -- Corresponds to FMapFacts.Equal_Equiv
    extensional : {V : Set} {d1 d2 : dd V} →
                   ((k : K) → d1 ⟨ k ⟩ == d2 ⟨ k ⟩) →
                   d1 == d2
    extensional {V} {DD d1} {DD d2} all-bindings-==
      = ap1 DD <| extensional' {V} {d1} {d2} eqv-nat
        where
        eqv-nat : (n : Nat) → (d1 lkup n) == (d2 lkup n)
        eqv-nat n
          with bij.surj bij n
        ... | k , surj
          with all-bindings-== k
        ... | eq rewrite surj = eq

    -- Theorem 3: Decidable Equality
    -- This doesn't seem to directly correspond to any of the Coq theorems
    ==-dec : {V : Set}
              (d1 d2 : dd V) →
              ((v1 v2 : V) → v1 == v2 ∨ v1 ≠ v2) →
              d1 == d2 ∨ d1 ≠ d2
    ==-dec {V} (DD d1) (DD d2) h
      with ==-dec' {V} d1 d2 h
    ... | Inl refl = Inl refl
    ... | Inr ne   = Inr (λ where refl → ne refl)

    -- The next two theorems specify the behavior of destruct and prove that
    -- it behaves as intended. The third one combines them to match the paper.
    destruct-thm-1 : ∀{V} {d : dd V} →
                       destruct d == None →
                       d == ∅
    destruct-thm-1 {d = DD []} eq = refl
    destruct-thm-1 {d = DD (_ :: [])} ()
    destruct-thm-1 {d = DD (_ :: (_ :: _))} ()

    destruct-thm-2 : ∀{V} {d d' : dd V} {k : K} {v : V} →
                       destruct d == Some ((k , v) , d') →
                       k # d' ∧ d == d' ,, (k , v)
    destruct-thm-2 {d = DD ((n , v) :: [])} refl
      rewrite convert-bij2 {{bij}} {t = n}
        = n#'[] , refl
    destruct-thm-2 {d = DD ((n , v) :: ((m , v') :: t))} refl
      rewrite convert-bij2 {{bij}} {t = n}
      with too-small (n<m→n<s+m n<1+n)
    ... | not-in
      with <dec n (m + 1+ n)
    ... | Inl lt rewrite ! (undelta n m lt) = not-in , refl
    ... | Inr (Inl eq) = abort (n≠n+1+m (eq · (n+1+m==1+n+m · +comm {1+ m})))
    ... | Inr (Inr gt) = abort (<antisym gt (n<m→n<s+m n<1+n))

    -- Theorem 4: Not-So-Easy Destructibility
    destruct-thm : ∀{V} {d d' : dd V} {k : K} {v : V} →
                     (destruct d == None → d == ∅)
                       ∧
                     (destruct d == Some ((k , v) , d') →
                        k # d' ∧ d == d' ,, (k , v))
    destruct-thm = destruct-thm-1 , destruct-thm-2

    -- When using destruct or delete, this theorem is useful for establishing termination
    -- Roughly corresponds to FMapFacts.cardinal_2
    extend-size : {V : Set} {d : dd V} {k : K} {v : V} →
                   k # d →
                   || d ,, (k , v) || == 1+ || d ||
    extend-size {V} {DD d} {k} {v} n#d = extend-size' {V} {d} {nat k} {v} n#d

    -- remove a specific mapping from a delta dict
    -- Roughly corresponds to FMapInterface.remove, and associated theorems
    delete : {V : Set} {d : dd V} {k : K} {v : V} →
              (k , v) ∈ d →
              Σ[ d⁻ ∈ dd V ] (
                 d == d⁻ ,, (k , v) ∧
                 k # d⁻)
    delete {V} {DD d} {k} {v} h
      with delete' {V} {d} {nat k} {v} h
    ... | _ , refl , # = _ , refl , #

    ---- contraction and exchange ----

    -- Theorem 5
    contraction : {V : Set} {d : dd V} {k : K} {v v' : V} →
                   d ,, (k , v') ,, (k , v) == d ,, (k , v)
    contraction {V} {DD d} {k} {v} {v'}
      = ap1 DD <| contraction' {d = d} {nat k} {v} {v'}

    -- Theorem 6
    exchange : {V : Set} {d : dd V} {k1 k2 : K} {v1 v2 : V} →
                k1 ≠ k2 →
                d ,, (k1 , v1) ,, (k2 , v2) == d ,, (k2 , v2) ,, (k1 , v1)
    exchange {V} {DD d} {k1} {k2} {v1} {v2} k1≠k2
      = ap1 DD <| exchange' {d = d} <| inj-cp k1≠k2

    ---- union theorems ----

    k,v∈d1→k∉d2→k,v∈d1∪d2 : {V : Set} {m : V → V → V} {d1 d2 : dd V} {k : K} {v : V} →
                             (k , v) ∈ d1 →
                             k # d2 →
                             (k , v) ∈ union m d1 d2
    k,v∈d1→k∉d2→k,v∈d1∪d2 {d1 = DD d1} {DD d2} k∈d1 k#d2
      = lemma-union'-1 k∈d1 0≤n (tr (λ y → y #' d2) (! (n+m-n==m 0≤n)) k#d2)

    k∉d1→k,v∈d2→k,v∈d1∪d2 : {V : Set} {m : V → V → V} {d1 d2 : dd V} {k : K} {v : V} →
                             k # d1 →
                             (k , v) ∈ d2 →
                             (k , v) ∈ union m d1 d2
    k∉d1→k,v∈d2→k,v∈d1∪d2 {d1 = DD d1} {DD d2} {k} k#d1 k∈d2
      with lemma-union'-2 {n = Z} (tr (λ y → y #' d1) (! n+Z==n) k#d1) k∈d2
    ... | rslt
      rewrite n+Z==n {nat k}
        = rslt

    k∈d1→k∈d2→k∈d1∪d2 : {V : Set} {m : V → V → V} {d1 d2 : dd V} {k : K} {v1 v2 : V} →
                         (k , v1) ∈ d1 →
                         (k , v2) ∈ d2 →
                         (k , m v1 v2) ∈ union m d1 d2
    k∈d1→k∈d2→k∈d1∪d2 {d1 = DD d1} {DD d2} {k} {v1} k∈d1 k∈d2
      with lemma-union'-3 (tr (λ y → (y , v1) ∈' d1) (! n+Z==n) k∈d1) k∈d2
    ... | rslt
      rewrite n+Z==n {nat k}
        = rslt

    k∈d1∪d2→k∈d1∨k∈d2 : {V : Set} {m : V → V → V} {d1 d2 : dd V} {k : K} →
                         dom (union m d1 d2) k →
                         dom d1 k ∨ dom d2 k
    k∈d1∪d2→k∈d1∨k∈d2 {d1 = DD d1} {DD d2} k∈d1∪d2
      with lemma-union'-4 {n = Z} k∈d1∪d2
    k∈d1∪d2→k∈d1∨k∈d2 k∈d1∪d2 | Inl k'∈d1 = Inl k'∈d1
    k∈d1∪d2→k∈d1∨k∈d2 k∈d1∪d2 | Inr (_ , refl , k'∈d2) = Inr k'∈d2

    ---- dltmap theorem ----

    -- The Coq.FSets library uses different theorems to establish to specify map
    dltmap-func : {V1 V2 : Set} {d : dd V1} {f : V1 → V2} {k : K} {v : V1} →
                   dltmap f (d ,, (k , v)) == dltmap f d ,, (k , f v)
    dltmap-func {d = DD d} {f} {k} {v} = ap1 DD (dltmap-func' {d = d})

    ---- dlt <=> list theorems ----

    -- Corresponds to FMapInterface.cardinal_1
    dlt⇒list-size : {V : Set} {d : dd V} → ∥ dlt⇒list d ∥ == || d ||
    dlt⇒list-size {d = DD d} = map-len · dlt⇒list-size'

    -- Corresponds to FMapInterface.elements_1
    dlt⇒list-In-1 : {V : Set} {d : dd V} {k : K} {v : V} →
                      (k , v) ∈ d →
                      (k , v) In dlt⇒list d
    dlt⇒list-In-1 {d = DD d} {k} in'
      rewrite ! <| convert-bij1 {f = k}
      with dlt⇒list-In-1' in'
    ... | in'' rewrite convert-bij2 {{bij}} {t = bij.convert bij k}
      = map-In in''

    -- Corresponds to FMapInterface.elements_2
    dlt⇒list-In-2 : {V : Set} {d : dd V} {k : K} {v : V} →
                      (k , v) In dlt⇒list d →
                      (k , v) ∈ d
    dlt⇒list-In-2 {V} {d = DD d} {k} {v} in'
      with map-In {f = λ where (k' , v') → (nat k' , v')} in'
    ... | in'' rewrite map^2 {f = λ where (k' , v') → (nat k' , v')} {g = λ where (n' , v') → (key n' , v')} {l = dlt⇒list' d}
      = dlt⇒list-In-2' (tr
          (λ y → (nat k , v) In y)
          (map^2 · (map-ext bij-pair-1 · map-id))
          (map-In {f = λ where (k , v) → (nat k , v)} in'))

    list⇒dlt-In : {V : Set} {l : List (K ∧ V)} {k : K} {v : V} →
                    (k , v) ∈ list⇒dlt l →
                    (k , v) In l
    list⇒dlt-In {l = l} {k} {v} in'
      with list⇒dlt-In' {l = map (λ { (k , v) → nat k , v }) l} in' |> map-In {f = λ where (n , v) → key n , v}
    ... | in'' rewrite convert-bij1 {f = k}
      = tr
           (λ y → (k , v) In y)
           (map^2 · (map-ext bij-pair-2 · map-id))
           in''

    list⇒dlt-key-In : {V : Set} {l : List (K ∧ V)} {k : K} {v : V} →
                        (k , v) In l →
                        dom (list⇒dlt l) k
    list⇒dlt-key-In {_} {(k , v) :: l} {k} {v} LInH
      rewrite foldl-++ {l1 = reverse <| map (λ where (k , v) → nat k , v) l} {(nat k , v) :: []} {_,,'_} {[]}
        = _ , tr
           (λ y → (nat k , v) ∈' y)
           (! <| foldl-++ {l1 = reverse <| map (λ where (k , v) → nat k , v) l})
           (n,v∈'d,,n,v {d = list⇒dlt' <| map (λ where (k , v) → nat k , v) l})
    list⇒dlt-key-In {V} {(k' , v') :: l} {k} {v} (LInT in')
      with list⇒dlt-key-In in'
    ... | (_ , in'')
      = _ , tr
         (λ y → (nat k , vv) ∈' y)
         (! <| foldl-++ {l1 = reverse <| map (λ where (k , v) → nat k , v) l})
         lem'
      where
      nat-inj : ∀{k1 k2} → nat k1 == nat k2 → k1 == k2
      nat-inj eq = ! (convert-bij1 {{bij}}) · (ap1 key eq · convert-bij1 {{bij}})
      lem : Σ[ vv ∈ V ] ((nat k , vv) ∈' (list⇒dlt' (map (λ { (k , v) → nat k , v }) l) ,,' (nat k' , v')))
      lem
        with natEQ (nat k) (nat k')
      ... | Inl eq rewrite ! <| nat-inj eq
        = _ , n,v∈'d,,n,v {d = list⇒dlt' (map (λ { (k , v) → nat k , v }) l)}
      ... | Inr ne = _ , n∈d→'n∈d+ ne in''
      vv = π1 lem
      lem' = π2 lem

    -- contrapositives of some previous theorems
    dlt⇒list-In-1-cp : {V : Set} {d : dd V} {k : K} → (Σ[ v ∈ V ] ((k , v) In dlt⇒list d) → ⊥) → k # d
    dlt⇒list-In-1-cp {d = DD d} not-in = λ where (_ , in') → not-in (_ , (dlt⇒list-In-1 in'))
    list⇒dlt-key-In-cp : {V : Set} {l : List (K ∧ V)} {k : K} → k # list⇒dlt l → Σ[ v ∈ V ] ((k , v) In l) → ⊥
    list⇒dlt-key-In-cp k#d' (_ , k∈l) = k#d' (list⇒dlt-key-In k∈l)

    list⇒dlt-order : {V : Set} {l1 l2 : List (K ∧ V)} {k : K} {v1 v2 : V} →
                       (k , v1) ∈ (list⇒dlt ((k , v1) :: l1 ++ ((k , v2) :: l2)))
    list⇒dlt-order {_} {l1} {l2} {k} {v1} {v2}
      = tr
           (λ y → (nat k , v1) ∈' foldl _,,'_ [] (reverse y ++ ((nat k , v1) :: [])))
           (map-++-comm {a = l1})
           (list⇒dlt-order' {l1 = map (λ where (k , v) → nat k , v) l1})

    dlt⇒list-inversion : {V : Set} {d : dd V} → list⇒dlt (dlt⇒list d) == d
    dlt⇒list-inversion {d = DD d} = extensional lem
      where
      lem : (k : K) → (list⇒dlt (dlt⇒list <| DD d) ⟨ k ⟩ == DD d ⟨ k ⟩)
      lem k
        with mem-dec (list⇒dlt (dlt⇒list <| DD d)) k
      ... | Inl (_ , k∈d')
        = lookup-cons-1 k∈d' · (k∈d' |> list⇒dlt-In |> dlt⇒list-In-2 |> lookup-cons-1 {d = DD d} |> !)
      ... | Inr k#d'
        = lookup-cp-2' k#d' · (k#d' |> list⇒dlt-key-In-cp |> dlt⇒list-In-1-cp |> lookup-cp-2' {d = d} |> !)
