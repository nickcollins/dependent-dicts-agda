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
module Delta (K : Set) {{bij : bij K Nat}} where
  -- Agda 2.6.1 has some bugs involving the 'abstract' keyword, so we can't use it, but ideally,
  -- the following line would be uncommented to ensure proper encapsulation
  -- abstract -- everything in the module is abstract

    ---- gory details - skip to "core definitions" ----
    private
      -- abbreviations for conversion between K and Nat
      key : Nat → K
      key = convert-inv {{bij}}

      nat : K → Nat
      nat = bij.convert bij

      -- another bij-related convenience functions
      inj-cp : ∀{k1 k2} → k1 ≠ k2 → nat k1 ≠ nat k2
      inj-cp ne eq = abort (ne (bij.inj bij eq))

      -- helper function
      delta : ∀{n m} → n < m → Nat
      delta n<m = difference (n<m→1+n≤m n<m)

      -- raw underlying list-of-pairs type
      dl : (V : Set) → Set
      dl V = List (Nat ∧ V)

      ---- helper definitions ----

      _lkup_ : {V : Set} → dl V → Nat → Maybe V
      [] lkup x = None
      ((hn , hv) :: t) lkup n with <dec n hn
      ... | Inl n<hn       = None
      ... | Inr (Inl refl) = Some hv
      ... | Inr (Inr hn<n) = t lkup (delta hn<n)

      _,,'_ : ∀{V} → dl V → (Nat ∧ V) → dl V
      [] ,,' (n , v) = (n , v) :: []
      ((hn , hv) :: t) ,,' (n , v) with <dec n hn
      ... | Inl n<hn       = (n , v) :: ((delta n<hn , hv) :: t)
      ... | Inr (Inl refl) = (n , v) :: t
      ... | Inr (Inr hn<n) = (hn , hv) :: (t ,,' (delta hn<n , v))

      data _∈'_ : {V : Set} (p : Nat ∧ V) → (d : dl V) → Set where
        InH : {V : Set} {d : dl V} {n : Nat} {v : V} →
          (n , v) ∈' ((n , v) :: d)
        InT : {V : Set} {d : dl V} {n s : Nat} {v v' : V} →
          (n , v) ∈' d →
          (n + 1+ s , v) ∈' ((s , v') :: d)

      dom' : {V : Set} → dl V → Nat → Set
      dom' {V} d n = Σ[ v ∈ V ] ((n , v) ∈' d)

      _#'_ : {V : Set} (n : Nat) → (d : dl V) → Set
      n #' d = dom' d n → ⊥

      ---- lemmas ----

      undelta : (x s : Nat) → (x<s+1+x : x < s + 1+ x) → s == delta x<s+1+x
      undelta x s x<s+1+x
        rewrite n+1+m==1+n+m {s} {x} | ! (m-n==1+m-1+n n≤m+n (n<m→1+n≤m x<s+1+x)) | +comm {s} {x}
          = ! (n+m-n==m n≤n+m)

      n#'[] : {V : Set} {n : Nat} → _#'_ {V} n []
      n#'[] (_ , ())

      too-small : {V : Set} {d : dl V} {xl xb : Nat} {v : V} →
                   xl < xb →
                   dom' ((xb , v) :: d) xl →
                   ⊥
      too-small (_ , ne) (_ , InH) = ne refl
      too-small (x+1+xb≤xb , x+1+xb==xb) (_ , InT _) =
        x+1+xb==xb (≤antisym x+1+xb≤xb (≤trans (≤1+ ≤refl) n≤m+n))

      all-not-none : {V : Set} {d : dl V} {x : Nat} {v : V} →
                      None ≠ (((x , v) :: d) lkup x)
      all-not-none {x = x} rewrite <dec-refl x = λ ()

      all-bindings-==-rec-eq : {V : Set} {d1 d2 : dl V} {x : Nat} {v : V} →
                                ((x' : Nat) → ((x , v) :: d1) lkup x' == ((x , v) :: d2) lkup x') →
                                ((x' : Nat) → d1 lkup x' == d2 lkup x')
      all-bindings-==-rec-eq {x = x} h x'
        with h (x' + 1+ x)
      ... | eq
        with <dec (x' + 1+ x) x
      ... | Inl x'+1+x<x
              = abort (<antisym x'+1+x<x (n<m→n<s+m n<1+n))
      ... | Inr (Inl x'+1+x==x)
              = abort ((flip n≠n+1+m) (n+1+m==1+n+m · (+comm {1+ x} · x'+1+x==x)))
      ... | Inr (Inr x<x'+1+x)
              rewrite ! (undelta x x' x<x'+1+x) = eq

      all-bindings-==-rec : {V : Set} {d1 d2 : dl V} {x1 x2 : Nat} {v1 v2 : V} →
                             ((x : Nat) → ((x1 , v1) :: d1) lkup x == ((x2 , v2) :: d2) lkup x) →
                             ((x : Nat) → d1 lkup x == d2 lkup x)
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

      sad-lemma : {V : Set} {d : dl V} {x n : Nat} {v v' : V} →
                   (x + 1+ n , v') ∈' ((n , v) :: d) →
                   Σ[ x' ∈ Nat ] Σ[ d' ∈ dl V ] (
                      d' == ((n , v) :: d) ∧
                      x' == x + 1+ n ∧
                      (x' , v') ∈' d')
      sad-lemma h = _ , _ , refl , refl , h

      lemma-math' : ∀{x x1 n} → x ≠ x1 + (n + 1+ x)
      lemma-math' {x} {x1} {n}
        rewrite ! (+assc {x1} {n} {1+ x})
              | n+1+m==1+n+m {x1 + n} {x}
              | +comm {1+ x1 + n} {x}
          = n≠n+1+m

      lookup-cons-1' : {V : Set} {d : dl V} {n : Nat} {v : V} → d lkup n == Some v → (n , v) ∈' d
      lookup-cons-1' {d = []} ()
      lookup-cons-1' {d = ((hn , hv) :: t)} {n} h
        with <dec n hn
      lookup-cons-1' {d = ((hn , hv) :: t)} {n} ()     | Inl _
      lookup-cons-1' {d = ((hn , hv) :: t)} {.hn} refl | Inr (Inl refl) = InH
      lookup-cons-1' {d = ((hn , hv) :: t)} {n} {v} h  | Inr (Inr hn<n)
        = tr
            (λ y → (y , v) ∈' ((hn , hv) :: t))
            (m-n+n==m (n<m→1+n≤m hn<n))
            (InT (lookup-cons-1' {d = t} h))

      lookup-cons-2' : {V : Set} {d : dl V} {n : Nat} {v : V} →
                        (n , v) ∈' d →
                        d lkup n == Some v
      lookup-cons-2' {n = x} InH rewrite <dec-refl x = refl
      lookup-cons-2' (InT {d = d} {n = x} {s} {v} x∈d)
        with <dec (x + 1+ s) s
      ... | Inl x+1+s<s        = abort (<antisym x+1+s<s (n<m→n<s+m n<1+n))
      ... | Inr (Inl x+1+s==s) = abort ((flip n≠n+1+m) (n+1+m==1+n+m · (+comm {1+ s} · x+1+s==s)))
      ... | Inr (Inr s<x+1+s)
        with lookup-cons-2' x∈d
      ... | h rewrite ! (undelta s x s<x+1+s) = h

      n,v∈'d,,n,v : {V : Set} {d : dl V} {n : Nat} {v : V} → (n , v) ∈' (d ,,' (n , v))
      n,v∈'d,,n,v {d = []} {n} {v} = InH
      n,v∈'d,,n,v {d = ((hn , hv) :: t)} {n} {v}
        with <dec n hn
      ... | Inl _          = InH
      ... | Inr (Inl refl) = InH
      ... | Inr (Inr hn<n) =
              tr
                (λ y → (y , v) ∈' ((hn , hv) :: (t ,,' (delta hn<n , v))))
                (m-n+n==m (n<m→1+n≤m hn<n))
                (InT (n,v∈'d,,n,v {d = t} {delta hn<n}))

      n∈d+→'n∈d : {V : Set} {d : dl V} {n n' : Nat} {v v' : V} →
                   n ≠ n' →
                   (n , v) ∈' (d ,,' (n' , v')) →
                   (n , v) ∈' d
      n∈d+→'n∈d {d = []} n≠n' InH = abort (n≠n' refl)
      n∈d+→'n∈d {d = []} n≠n' (InT ())
      n∈d+→'n∈d {d = (hn , hv) :: t} {n' = n'} n≠n' n∈d+
        with <dec n' hn
      n∈d+→'n∈d {_} {(hn , hv) :: t} {n' = n'} n≠n' InH | Inl n'<hn = abort (n≠n' refl)
      n∈d+→'n∈d {_} {(hn , hv) :: t} {n' = n'} n≠n' (InT InH) | Inl n'<hn
        rewrite m-n+n==m (n<m→1+n≤m n'<hn) = InH
      n∈d+→'n∈d {_} {(hn , hv) :: t} {n' = n'} n≠n' (InT (InT {n = n} n∈d+)) | Inl n'<hn
        rewrite +assc {n} {1+ (delta n'<hn)} {1+ n'} | m-n+n==m (n<m→1+n≤m n'<hn)
          = InT n∈d+
      n∈d+→'n∈d {_} {(hn , hv) :: t} {n' = .hn} n≠n' InH | Inr (Inl refl) = abort (n≠n' refl)
      n∈d+→'n∈d {_} {(hn , hv) :: t} {n' = .hn} n≠n' (InT n∈d+) | Inr (Inl refl) = InT n∈d+
      n∈d+→'n∈d {_} {(hn , hv) :: t} {n' = n'} n≠n' InH | Inr (Inr hn<n') = InH
      n∈d+→'n∈d {_} {(hn , hv) :: t} {n' = n'} n≠n' (InT n∈d+) | Inr (Inr hn<n')
        = InT (n∈d+→'n∈d (λ where refl → n≠n' (m-n+n==m (n<m→1+n≤m hn<n'))) n∈d+)

      n∈d→'n∈d+ : {V : Set} {d : dl V} {n n' : Nat} {v v' : V} →
                   n ≠ n' →
                   (n , v) ∈' d →
                   (n , v) ∈' (d ,,' (n' , v'))
      n∈d→'n∈d+ {n = n} {n'} {v} {v'} n≠n' (InH {d = d'})
        with <dec n' n
      ... | Inl n'<n
        = tr
            (λ y → (y , v) ∈' ((n' , v') :: ((delta n'<n , v) :: d')))
            (m-n+n==m (n<m→1+n≤m n'<n))
            (InT InH)
      ... | Inr (Inl refl) = abort (n≠n' refl)
      ... | Inr (Inr n<n') = InH
      n∈d→'n∈d+ {n = .(_ + 1+ _)} {n'} {v} {v'} n≠n' (InT {d = d} {n} {s} {v' = v''} n∈d)
        with <dec n' s
      ... | Inl n'<s
        = tr
            (λ y → (y , v) ∈' ((n' , v') :: ((delta n'<s , v'') :: d)))
            ((+assc {b = 1+ (delta n'<s)}) · (ap1 (n +_) (1+ap (m-n+n==m (n<m→1+n≤m n'<s)))))
            (InT (InT n∈d))
      ... | Inr (Inl refl) = InT n∈d
      ... | Inr (Inr s<n') =
              InT (n∈d→'n∈d+ (λ where refl → n≠n' (m-n+n==m (n<m→1+n≤m s<n'))) n∈d)

      mem-dec' : {V : Set} (d : dl V) (n : Nat) → dom' d n ∨ n #' d
      mem-dec' [] n = Inr (λ ())
      mem-dec' ((hn , hv) :: t) n
        with <dec n hn
      ... | Inl n<hn       = Inr (too-small n<hn)
      ... | Inr (Inl refl) = Inl (hv , InH)
      ... | Inr (Inr hn<n)
        with mem-dec' t (delta hn<n)
      mem-dec' ((hn , hv) :: t) n | Inr (Inr hn<n) | Inl (v , rec) =
        Inl (v , tr
                   (λ y → (y , v) ∈' ((hn , hv) :: t))
                   (m-n+n==m (n<m→1+n≤m hn<n))
                   (InT rec))
      mem-dec' {V} ((hn , hv) :: t) n | Inr (Inr hn<n) | Inr dne =
        Inr n∉d
          where
          n∉d : Σ[ v ∈ V ] ((n , v) ∈' ((hn , hv) :: t)) → ⊥
          n∉d (_ , n∈d) with n∈d
          ... | InH = (π2 hn<n) refl
          ... | InT {n = s} n-hn-1∈t
            rewrite ! (undelta hn s hn<n) = dne (_ , n-hn-1∈t)

      extensional' : {V : Set} {d1 d2 : dl V} →
                      ((n : Nat) → d1 lkup n == d2 lkup n) →
                      d1 == d2
      extensional' {d1 = []} {[]} all-bindings-== = refl
      extensional' {d1 = []} {(hn2 , hv2) :: t2} all-bindings-==
        = abort (all-not-none {d = t2} {x = hn2} (all-bindings-== hn2))
      extensional' {d1 = (hn1 , hv1) :: t1} {[]} all-bindings-==
        = abort (all-not-none {d = t1} {x = hn1} (! (all-bindings-== hn1)))
      extensional' {d1 = (hn1 , hv1) :: t1} {(hn2 , hv2) :: t2} all-bindings-==
        rewrite extensional' {d1 = t1} {t2} (all-bindings-==-rec all-bindings-==)
        with all-bindings-== hn1 | all-bindings-== hn2
      ... | hv1== | hv2== rewrite <dec-refl hn1 | <dec-refl hn2
        with <dec hn1 hn2 | <dec hn2 hn1
      ... | Inl hn1<hn2 | _
              = abort (somenotnone hv1==)
      ... | Inr (Inl refl) | Inl hn2<hn1
              = abort (somenotnone (! hv2==))
      ... | Inr (Inr hn2<hn1) | Inl hn2<'hn1
              = abort (somenotnone (! hv2==))
      ... | Inr (Inl refl) | Inr _
              rewrite someinj hv1== = refl
      ... | Inr (Inr hn2<hn1) | Inr (Inl refl)
              rewrite someinj hv2== = refl
      ... | Inr (Inr hn2<hn1) | Inr (Inr hn1<hn2)
              = abort (<antisym hn1<hn2 hn2<hn1)

      delete' : {V : Set} {d : dl V} {n : Nat} {v : V} →
                 (n , v) ∈' d →
                 Σ[ d⁻ ∈ dl V ] (
                    d == d⁻ ,,' (n , v) ∧
                    n #' d⁻)
      delete' {d = (n' , v') :: d} {n} n∈d
        with <dec n n'
      ... | Inl n<n'       = abort (too-small n<n' (_ , n∈d))
      delete' {_} {(n' , v') :: []} {.n'} InH                 | Inr (Inl _) = [] , refl , λ ()
      delete' {_} {(n' , v') :: ((n'' , v'') :: d)} {.n'} InH | Inr (Inl _)
        = ((n'' + 1+ n' , v'') :: d) , lem , λ {(_ , n'∈d+) → abort (too-small (n<m→n<s+m n<1+n) (_ , n'∈d+))}
          where
            lem : ((n' , v') :: ((n'' , v'') :: d)) == ((n'' + 1+ n' , v'') :: d) ,,' (n' , v')
            lem
              with <dec n' (n'' + 1+ n')
            lem | Inl n'<n''+1+n' rewrite ! (undelta n' n'' n'<n''+1+n') = refl
            lem | Inr (Inl false) = abort (lemma-math' {x1 = Z} false)
            lem | Inr (Inr false) = abort (<antisym false (n<m→n<s+m n<1+n))
      delete' {d = (n' , v') :: d} InH       | Inr (Inr n'<n') = abort (<antirefl n'<n')
      delete' {d = (n' , v') :: d} (InT n∈d) | Inr _
        with delete' {d = d} n∈d
      delete' {d = (n' , v') :: d} {.(_ + 1+ n')} {v} (InT {n = x} n∈d) | Inr _ | d⁻ , refl , x#d⁻
        = _ , lem' , lem
          where
            lem : (x + 1+ n') #' ((n' , v') :: d⁻)
            lem (_ , x+1+n'∈d?)
              with sad-lemma x+1+n'∈d?
            ... | _ , _ , refl , n'==x+1+n' , InH = abort (lemma-math' {x1 = Z} n'==x+1+n')
            ... | _ , _ , refl , n'==x+1+n' , InT x+1+n'∈d'
              rewrite +inj {b = 1+ n'} n'==x+1+n'
                = x#d⁻ (_ , x+1+n'∈d')
            lem' : ((n' , v') :: (d⁻ ,,' (x , v))) == (((n' , v') :: d⁻) ,,' (x + 1+ n' , v))
            lem'
              with <dec (x + 1+ n') n'
            lem' | Inl x+1+n'<n'       = abort (<antisym x+1+n'<n' (n<m→n<s+m n<1+n))
            lem' | Inr (Inl false)     = abort (lemma-math' {x1 = Z} (! false))
            lem' | Inr (Inr n'<x+1+n') rewrite ! (undelta n' x n'<x+1+n') = refl

      extend-size' : {V : Set} {d : dl V} {n : Nat} {v : V} →
                      n #' d →
                      ∥ d ,,' (n , v) ∥ == 1+ ∥ d ∥
      extend-size' {d = []} n#d = refl
      extend-size' {d = (n' , v') :: d} {n} n#d
        with <dec n n'
      ... | Inl n<n'       = refl
      ... | Inr (Inl refl) = abort (n#d (_ , InH))
      ... | Inr (Inr n'<n)
              = 1+ap (extend-size' λ {(v , diff∈d) →
                  n#d (v , tr
                             (λ y → (y , v) ∈' ((n' , v') :: d))
                             (m-n+n==m (n<m→1+n≤m n'<n))
                             (InT diff∈d))})

      ---- contrapositives of some previous lemmas ----

      lookup-dec' : {V : Set} (d : dl V) (n : Nat) →
                     Σ[ v ∈ V ] (d lkup n == Some v) ∨ d lkup n == None
      lookup-dec' d n
        with d lkup n
      ... | Some v = Inl (v , refl)
      ... | None   = Inr refl

      lookup-cp-1' : {V : Set} {d : dl V} {n : Nat} →
                      n #' d →
                      d lkup n == None
      lookup-cp-1' {d = d} {n} n#d
        with lookup-dec' d n
      ... | Inl (_ , n∈d) = abort (n#d (_ , lookup-cons-1' n∈d))
      ... | Inr n#'d      = n#'d

      n#d→'n#d+ : {V : Set} {d : dl V} {n n' : Nat} {v' : V} →
                    n ≠ n' →
                    n #' d →
                    n #' (d ,,' (n' , v'))
      n#d→'n#d+ {d = d} {n} {n'} {v'} n≠n' n#d
        with mem-dec' (d ,,' (n' , v')) n
      ... | Inl (_ , n∈d+) = abort (n#d (_ , n∈d+→'n∈d n≠n' n∈d+))
      ... | Inr n#d+       = n#d+

      ---- union, and dlt <=> list conversion definitions

      merge' : {V : Set} → (V → V → V) → Maybe V → V → V
      merge' merge ma1 v2
        with ma1
      ... | None    = v2
      ... | Some v1 = merge v1 v2

      union' : {V : Set} → (V → V → V) → dl V → dl V → Nat → dl V
      union' merge d1 [] _ = d1
      union' merge d1 ((hn , hv) :: d2) offset
        with d1 ,,' (hn + offset , merge' merge (d1 lkup hn + offset) hv)
      ... | d1+ = union' merge d1+ d2 (1+ hn + offset)

      dlt⇒list' : {V : Set} (d : dl V) → dl V
      dlt⇒list' [] = []
      dlt⇒list' ((x , v) :: d) = (x , v) :: map (λ {(x' , v') → x' + 1+ x , v'}) (dlt⇒list' d)

      list⇒dlt' : {V : Set} (d : dl V) → dl V
      list⇒dlt' = foldr _,,'_ []

      ---- union, dlt <=> list, etc lemmas ----

      lemma-union'-0 : {V : Set} {m : V → V → V} {d1 d2 : dl V} {x n : Nat} {v : V} →
                        (x , v) ∈' d1 →
                        (x , v) ∈' (union' m d1 d2 (n + 1+ x))
      lemma-union'-0 {d2 = []} x∈d1 = x∈d1
      lemma-union'-0 {d2 = (x1 , v1) :: d2} {x} {n} x∈d1
        rewrite ! (+assc {1+ x1} {n} {1+ x})
          = lemma-union'-0 {d2 = d2} {n = 1+ x1 + n} (n∈d→'n∈d+ (lemma-math' {x1 = x1} {n}) x∈d1)

      lemma-union'-1 : {V : Set} {m : V → V → V} {d1 d2 : dl V} {x n : Nat} {v : V} →
                        (x , v) ∈' d1 →
                        (n≤x : n ≤ x) →
                        (difference n≤x) #' d2 →
                        (x , v) ∈' (union' m d1 d2 n)
      lemma-union'-1 {d2 = []} {x} x∈d1 n≤x x-n#d2 = x∈d1
      lemma-union'-1 {m = m} {d1} {(x1 , v1) :: d2} {x} {n} {v} x∈d1 n≤x x-n#d2
        with <dec x (x1 + n)
      lemma-union'-1 {m = m} {d1} {(x1 , v1) :: d2} {x} {n} {v} x∈d1 n≤x x-n#d2 | Inl x<x1+n
        with d1 lkup x1 + n
      lemma-union'-1 {m = m} {d1} {(x1 , v1) :: d2} {x} {n} {v} x∈d1 n≤x x-n#d2 | Inl x<x1+n | Some v'
        with expr-eq (λ _ → d1 ,,' (x1 + n , m v' v1))
      lemma-union'-1 {m = m} {d1} {(x1 , v1) :: d2} {x} {n} {v} x∈d1 n≤x x-n#d2 | Inl x<x1+n | Some v' | d1+ , refl
        = tr
             (λ y → (x , v) ∈' (union' m d1+ d2 y))
             (n+1+m==1+n+m {difference (π1 x<x1+n)} · 1+ap (m-n+n==m (π1 x<x1+n)))
             (lemma-union'-0 {d2 = d2} (n∈d→'n∈d+ (π2 x<x1+n) x∈d1))
      lemma-union'-1 {m = m} {d1} {(x1 , v1) :: d2} {x} {n} {v} x∈d1 n≤x x-n#d2 | Inl x<x1+n | None
        with expr-eq (λ _ → d1 ,,' (x1 + n , v1))
      lemma-union'-1 {m = m} {d1} {(x1 , v1) :: d2} {x} {n} {v} x∈d1 n≤x x-n#d2 | Inl x<x1+n | None | d1+ , refl
        = tr
             (λ y → (x , v) ∈' (union' m d1+ d2 y))
             (n+1+m==1+n+m {difference (π1 x<x1+n)} · 1+ap (m-n+n==m (π1 x<x1+n)))
             (lemma-union'-0 {d2 = d2} (n∈d→'n∈d+ (π2 x<x1+n) x∈d1))
      lemma-union'-1 {m = m} {d1} {(x1 , v1) :: d2} {x} {n} {v} x∈d1 n≤x x-n#d2 | Inr (Inl refl)
        rewrite +comm {x1} {n} | n+m-n==m n≤x
          = abort (x-n#d2 (_ , InH))
      lemma-union'-1 {m = m} {d1} {(x1 , v1) :: d2} {x} {n} {v} x∈d1 n≤x x-n#d2 | Inr (Inr x1+n<x)
        rewrite (! (a+b==c→a==c-b (+assc {delta x1+n<x} · m-n+n==m (n<m→1+n≤m x1+n<x)) n≤x))
          = lemma-union'-1
              (n∈d→'n∈d+ (flip (π2 x1+n<x)) x∈d1)
              (n<m→1+n≤m x1+n<x)
              λ {(_ , x-x1-n∈d2) → x-n#d2 (_ , InT x-x1-n∈d2)}

      lemma-union'-2 : {V : Set} {m : V → V → V} {d1 d2 : dl V} {x n : Nat} {v : V} →
                        (x + n) #' d1 →
                        (x , v) ∈' d2 →
                        (x + n , v) ∈' (union' m d1 d2 n)
      lemma-union'-2 {d1 = d1} x+n#d1 (InH {d = d2})
        rewrite lookup-cp-1' x+n#d1
          = lemma-union'-0 {d2 = d2} {n = Z} (n,v∈'d,,n,v {d = d1})
      lemma-union'-2 {d1 = d1} {n = n} x+n#d1 (InT {d = d2} {n = x} {s} x∈d2)
        rewrite +assc {x} {1+ s} {n}
        with d1 lkup s + n
      ... | Some v'
        = lemma-union'-2
            (λ {(_ , x∈d1+) →
                 x+n#d1 (_ , n∈d+→'n∈d (flip (lemma-math' {x1 = Z})) x∈d1+)})
            x∈d2
      ... | None
        = lemma-union'-2
            (λ {(_ , x∈d1+) →
                 x+n#d1 (_ , n∈d+→'n∈d (flip (lemma-math' {x1 = Z})) x∈d1+)})
            x∈d2

      lemma-union'-3 : {V : Set} {m : V → V → V} {d1 d2 : dl V} {x n : Nat} {v1 v2 : V} →
                        (x + n , v1) ∈' d1 →
                        (x , v2) ∈' d2 →
                        (x + n , m v1 v2) ∈' (union' m d1 d2 n)
      lemma-union'-3 {d1 = d1} x+n∈d1 (InH {d = d2})
        rewrite lookup-cons-2' x+n∈d1
          = lemma-union'-0 {d2 = d2} {n = Z} (n,v∈'d,,n,v {d = d1})
      lemma-union'-3 {d1 = d1} {n = n} x+n∈d1 (InT {d = d2} {n = x} {s} x∈d2)
        rewrite +assc {x} {1+ s} {n}
        with d1 lkup s + n
      ... | Some v'
        = lemma-union'-3 (n∈d→'n∈d+ (flip (lemma-math' {x1 = Z})) x+n∈d1) x∈d2
      ... | None
        = lemma-union'-3 (n∈d→'n∈d+ (flip (lemma-math' {x1 = Z})) x+n∈d1) x∈d2

      lemma-union'-4 : {V : Set} {m : V → V → V} {d1 d2 : dl V} {x n : Nat} →
                        dom' (union' m d1 d2 n) x →
                        dom' d1 x ∨ (Σ[ s ∈ Nat ] (x == n + s ∧ dom' d2 s))
      lemma-union'-4 {d2 = []} x∈un = Inl x∈un
      lemma-union'-4 {d1 = d1} {(x1 , _) :: d2} {x} {n} x∈un
        with lemma-union'-4 {d2 = d2} x∈un
      ... | Inr (s , refl , _ , s∈d2)
        rewrite +comm {x1} {n}
              | ! (n+1+m==1+n+m {n + x1} {s})
              | +assc {n} {x1} {1+ s}
              | +comm {x1} {1+ s}
              | ! (n+1+m==1+n+m {s} {x1})
          = Inr (_ , refl , _ , InT s∈d2)
      ... | Inl (_ , x∈d1+)
        with natEQ x (n + x1)
      ... | Inl refl   = Inr (_ , refl , _ , InH)
      ... | Inr x≠n+x1
        rewrite +comm {x1} {n}
          = Inl (_ , n∈d+→'n∈d x≠n+x1 x∈d1+)

      lemma-dlt⇒list' : {V : Set} {d d' : dl V} {n : Nat} {v : V} →
                         foldl
                           (λ {b (n' , v') → b ,,' (n' + 1+ n , v')})
                           ((n , v) :: d')
                           d
                         == ((n , v) :: (foldl _,,'_ d' d))
      lemma-dlt⇒list' {d = []} = refl
      lemma-dlt⇒list' {d = (n2 , v2) :: d} {n = n}
        with <dec (n2 + 1+ n) n
      ... | Inl n2+1+n<n
        = abort (<antisym n2+1+n<n (n<m→n<s+m n<1+n))
      ... | Inr (Inl n2+1+n=n)
        = abort ((flip n≠n+1+m) (n+1+m==1+n+m · (+comm {1+ n} · n2+1+n=n)))
      ... | Inr (Inr n<n2+1+n)
        rewrite ! (undelta n n2 n<n2+1+n)
          = lemma-dlt⇒list' {d = d}

      dlt⇒list-size' : {V : Set} {d : dl V} → ∥ dlt⇒list' d ∥ == ∥ d ∥
      dlt⇒list-size' {d = []} = refl
      dlt⇒list-size' {d = _ :: d} = 1+ap (map-len · dlt⇒list-size')

      dlt⇒list-In-1' : {V : Set} {d : dl V} {n : Nat} {v : V} →
                        (n , v) ∈' d →
                        (n , v) In dlt⇒list' d
      dlt⇒list-In-1' InH = LInH
      dlt⇒list-In-1' (InT ∈h) = LInT <| map-In <| dlt⇒list-In-1' ∈h

      list⇒dlt-In' : {V : Set} {l : dl V} {n : Nat} {v : V} →
                      (n , v) ∈' list⇒dlt' l →
                      (n , v) In l
      list⇒dlt-In' {l = (n' , v') :: l} {n} ∈h
        rewrite foldl-++ {l1 = reverse l} {(n' , v') :: []} {_,,'_} {[]}
        with natEQ n n'
      ... | Inr ne   = LInT (list⇒dlt-In' (n∈d+→'n∈d ne ∈h))
      ... | Inl refl
        rewrite someinj <| (! <| lookup-cons-2' ∈h) · (lookup-cons-2' {n = n} {v'} <| n,v∈'d,,n,v {d = foldl _,,'_ [] (reverse l)})
          = LInH

      list⇒dlt-order' : {V : Set} {l1 l2 : dl V} {n : Nat} {v1 v2 : V} →
                         (n , v1) ∈' (list⇒dlt' ((n , v1) :: l1 ++ ((n , v2) :: l2)))
      list⇒dlt-order' {l1 = l1} {l2} {n} {v1} {v2}
        rewrite foldl-++ {l1 = reverse (l1 ++ ((n , v2) :: l2))} {(n , v1) :: []} {_,,'_} {[]}
          = n,v∈'d,,n,v {d = foldl _,,'_ [] <| reverse (l1 ++ ((n , v2) :: l2))}

      -- TODO the other direction
      dlt⇒list-inversion' : {V : Set} {d : dl V} → list⇒dlt' (dlt⇒list' d) == d
      dlt⇒list-inversion' = {!!}
      {- TODO
      dlt⇒list-inversion' {d = []} = refl
      dlt⇒list-inversion' {d = (x , a) :: d}
        with dlt⇒list-inversion' {d = d}
      ... | rec
        = foldl-map {l = dlt⇒list' d} {_,,'_} {λ {(x' , a') → x' + 1+ x , a'}} {(x , a) :: []}
          · (lemma-dlt⇒list' {d = dlt⇒list' d} · ap1 (λ y → (x , a) :: y) rec)
             -}

      dltmap-func' : {V1 V2 : Set} {d : dl V1} {f : V1 → V2} {n : Nat} {v : V1} →
                      (map (λ { (hn , hv) → hn , f hv }) (d ,,' (n , v)))
                        ==
                      (map (λ { (hn , hv) → hn , f hv }) d ,,' (n , f v))
      dltmap-func' {d = []} = refl
      dltmap-func' {d = (nh , vh) :: d} {f = f} {n}
        with <dec n nh
      ... | Inl n<nh       = refl
      ... | Inr (Inl refl) = refl
      ... | Inr (Inr nh<n) = ap1 ((nh , f vh) ::_) (dltmap-func' {d = d})

      -- TODO these proofs could use refactoring -
      -- contraction should probably make use of ==-dec and
      -- exchange is way too long and repetitive

      contraction' : {V : Set} {d : dl V} {n : Nat} {v v' : V} → (d ,,' (n , v')) ,,' (n , v) == d ,,' (n , v)
      contraction' {d = []} {n} rewrite <dec-refl n = refl
      contraction' {d = (hn , hv) :: t} {n} {v} {v'}
        with <dec n hn
      ... | Inl _          rewrite <dec-refl n  = refl
      ... | Inr (Inl refl) rewrite <dec-refl hn = refl
      ... | Inr (Inr hn<n)
        with <dec n hn
      ... | Inl n<hn        = abort (<antisym n<hn hn<n)
      ... | Inr (Inl refl)  = abort (<antirefl hn<n)
      ... | Inr (Inr hn<'n)
        with contraction' {d = t} {delta hn<'n} {v} {v'}
      ... | eq
        rewrite diff-proof-irrelevance (n<m→1+n≤m hn<n) (n<m→1+n≤m hn<'n) | eq
          = refl

      exchange' : {V : Set} {d : dl V} {n1 n2 : Nat} {v1 v2 : V} →
                   n1 ≠ n2 →
                   (d ,,' (n1 , v1)) ,,' (n2 , v2) == (d ,,' (n2 , v2)) ,,' (n1 , v1)
      exchange' {V} {d} {n1} {n2} {v1} {v2} n1≠n2 = extensional' fun
        where
          fun : (n : Nat) →
                 ((d ,,' (n1 , v1)) ,,' (n2 , v2)) lkup n ==
                 ((d ,,' (n2 , v2)) ,,' (n1 , v1)) lkup n
          fun n
            with natEQ n n1 | natEQ n n2 | mem-dec' d n
          fun n  | Inl refl | Inl refl | _
            = abort (n1≠n2 refl)
          fun n1 | Inl refl | Inr n≠n2 | Inl (_ , n1∈d)
            with n,v∈'d,,n,v {d = d} {n1} {v1}
          ... | n∈d+1
            with n∈d→'n∈d+ {v' = v2} n≠n2 n∈d+1 | n,v∈'d,,n,v {d = d ,,' (n2 , v2)} {n1} {v1}
          ... | n∈d++1 | n∈d++2
            rewrite lookup-cons-2' n∈d++1 | lookup-cons-2' n∈d++2 = refl
          fun n1 | Inl refl | Inr n≠n2 | Inr n1#d
            with n,v∈'d,,n,v {d = d} {n1} {v1}
          ... | n∈d+1
            with n∈d→'n∈d+ {v' = v2} n≠n2 n∈d+1 | n,v∈'d,,n,v {d = d ,,' (n2 , v2)} {n1} {v1}
          ... | n∈d++1 | n∈d++2
            rewrite lookup-cons-2' n∈d++1 | lookup-cons-2' n∈d++2 = refl
          fun n2 | Inr n≠n1 | Inl refl | Inl (_ , n2∈d)
            with n,v∈'d,,n,v {d = d} {n2} {v2}
          ... | n∈d+2
            with n∈d→'n∈d+ {v' = v1} n≠n1 n∈d+2 | n,v∈'d,,n,v {d = d ,,' (n1 , v1)} {n2} {v2}
          ... | n∈d++1 | n∈d++2
            rewrite lookup-cons-2' n∈d++1 | lookup-cons-2' n∈d++2 = refl
          fun n2 | Inr n≠n1 | Inl refl | Inr n2#d
            with n,v∈'d,,n,v {d = d} {n2} {v2}
          ... | n∈d+2
            with n∈d→'n∈d+ {v' = v1} n≠n1 n∈d+2 | n,v∈'d,,n,v {d = d ,,' (n1 , v1)} {n2} {v2}
          ... | n∈d++1 | n∈d++2
            rewrite lookup-cons-2' n∈d++1 | lookup-cons-2' n∈d++2 = refl
          fun n  | Inr n≠n1 | Inr n≠n2 | Inl (_ , n∈d)
            with n∈d→'n∈d+ {v' = v1} n≠n1 n∈d   | n∈d→'n∈d+ {v' = v2} n≠n2 n∈d
          ... | n∈d+1  | n∈d+2
            with n∈d→'n∈d+ {v' = v2} n≠n2 n∈d+1 | n∈d→'n∈d+ {v' = v1} n≠n1 n∈d+2
          ... | n∈d++1 | n∈d++2
            rewrite lookup-cons-2' n∈d++1 | lookup-cons-2' n∈d++2 = refl
          fun n  | Inr n≠n1 | Inr n≠n2 | Inr n#d
            with n#d→'n#d+ {v' = v1} n≠n1 n#d   | n#d→'n#d+ {v' = v2} n≠n2 n#d
          ... | n#d+1  | n#d+2
            with n#d→'n#d+ {v' = v2} n≠n2 n#d+1 | n#d→'n#d+ {v' = v1} n≠n1 n#d+2
          ... | n#d++1 | n#d++2
            rewrite lookup-cp-1' n#d++1 | lookup-cp-1' n#d++2 = refl

    ---- core definitions ----

    data dd (V : Set) : Set where
      DD : dl V → dd V

    -- nil
    ∅ : {V : Set} → dd V
    ∅ = DD []

    -- singleton
    ■_ : {V : Set} → (K ∧ V) → dd V
    ■_ (k , v) = DD <| (nat k , v) :: []

    -- extension/insertion
    _,,_ : ∀{V} → dd V → (K ∧ V) → dd V
    (DD d) ,, (k , v) = DD <| d ,,' (nat k , v)

    infixl 10 _,,_

    -- lookup function
    _⟨_⟩ : {V : Set} → dd V → K → Maybe V
    (DD d) ⟨ k ⟩ = d lkup (nat k)

    destruct : ∀{V} → dd V → Maybe ((K ∧ V) ∧ dd V)
    destruct (DD [])
      = None
    destruct (DD ((n , v) :: []))
      = Some ((key n , v) , DD [])
    destruct (DD ((n , v) :: ((m , v') :: dd)))
      = Some ((key n , v) , DD ((m + 1+ n , v') :: dd))

    -- size
    ||_|| : {V : Set} → dd V → Nat
    || DD d || = ∥ d ∥

    -- membership
    _∈_ : {V : Set} (p : K ∧ V) → (d : dd V) → Set
    _∈_ {V} (k , v) (DD d) = _∈'_ {V} (nat k , v) d

    -- domain
    dom : {V : Set} → dd V → K → Set
    dom {V} (DD d) k = dom' {V} d (nat k)

    -- apartness, i.e. the opposite of dom
    _#_ : {V : Set} (k : K) → (d : dd V) → Set
    k # (DD d) = (nat k) #' d

    -- maps f across the values of the delta dict
    dltmap : {A B : Set} → (A → B) → dd A → dd B
    dltmap f (DD d) = DD <| map (λ {(hn , hv) → (hn , f hv)}) d

    -- TODO theorems
    -- converts a list of key-value pairs into a delta dict, with earlier pairs in
    -- the list overriding bindings defined by later pairs
    list⇒dlt : {V : Set} → List (K ∧ V) → dd V
    list⇒dlt d = d |> map (λ where (k , v) → (nat k , v)) |> list⇒dlt' |> DD

    -- converts a delta dict into a list of key-value pairs; the inverse of list⇒dlt
    dlt⇒list : {V : Set} → dd V → List (K ∧ V)
    dlt⇒list (DD d) = dlt⇒list' d |> map (λ where (n , v) → (key n , v))

    -- TODO theorems
    -- TODO we declare this here, but don't define it til later, due to a dependency.
    --      Ideally we should refactor so that the dependency is hidden in the private section
    -- converts a list of key-value pairs into a multi-delta-dict, where each value of
    -- the result is the sublist of values from the former that were mapped to by the
    -- corresponding key
    list⇒list-dlt : {V : Set} → List (K ∧ V) → dd (List V)

    -- union merge A B is the union of A and B,
    -- with (merge a b) being invoked to handle the mappings they have in common
    union : {V : Set} → (V → V → V) → dd V → dd V → dd V
    union merge (DD d1) (DD d2) = DD <| union' merge d1 d2 0

    ---- core theorems ----

    -- The next two theorems show that lookup (_⟨_⟩) is consistent with membership (_∈_)
    -- As such, future theorems which relate to membership can be taken to appropriately
    -- comment on lookup as well.
    lookup-cons-1 : {V : Set} {d : dd V} {k : K} {v : V} →
                     d ⟨ k ⟩ == Some v →
                     (k , v) ∈ d
    lookup-cons-1 {V} {DD d} {k} {v} h = lookup-cons-1' {d = d} {nat k} h

    lookup-cons-2 : {V : Set} {d : dd V} {k : K} {v : V} →
                     (k , v) ∈ d →
                     d ⟨ k ⟩ == Some v
    lookup-cons-2 {V} {DD d} {k} {v} = lookup-cons-2' {V} {d} {nat k} {v}

    -- membership (_∈_) respects insertion (_,,_)
    k,v∈d,,k,v : {V : Set} {d : dd V} {k : K} {v : V} →
                  (k , v) ∈ (d ,, (k , v))
    k,v∈d,,k,v {V} {d = DD d} {k} = n,v∈'d,,n,v {d = d} {nat k}

    -- insertion can't generate spurious membership
    k∈d+→k∈d : {V : Set} {d : dd V} {k k' : K} {v v' : V} →
                k ≠ k' →
                (k , v) ∈ (d ,, (k' , v')) →
                (k , v) ∈ d
    k∈d+→k∈d {V} {d = DD d} {k} {k'} {v} {v'} ne h
      = n∈d+→'n∈d {V} {d} {nat k} {nat k'} {v} {v'} (inj-cp ne) h

    -- insertion respects membership
    k∈d→k∈d+ : {V : Set} {d : dd V} {k k' : K} {v v' : V} →
                k ≠ k' →
                (k , v) ∈ d →
                (k , v) ∈ (d ,, (k' , v'))
    k∈d→k∈d+ {V} {DD d} {k} {k'} {v} {v'} ne h
      = n∈d→'n∈d+ {V} {d} {nat k} {nat k'} {v} {v'} (inj-cp ne) h

    -- Decidability of membership
    -- This also packages up an appeal to delta dict membership into a form that
    -- lets us retain more information
    mem-dec : {V : Set} (d : dd V) (k : K) → dom d k ∨ k # d
    mem-dec {V} (DD d) k = mem-dec' {V} d (nat k)

    -- delta dicts contain at most one binding for each variable
    mem-unicity : {V : Set} {d : dd V} {k : K} {v v' : V} →
                   (k , v) ∈ d →
                   (k , v') ∈ d →
                   v == v'
    mem-unicity vh v'h
      with lookup-cons-2 vh | lookup-cons-2 v'h
    ... | vh' | v'h' = someinj (! vh' · v'h')

    -- meaning of nil, i.e. nothing is in nil
    k#∅ : {V : Set} {k : K} → _#_ {V} k ∅
    k#∅ (_ , ())

    -- meaning of the singleton
    ■-def : {V : Set} {k : K} {v : V} → (■ (k , v)) == ∅ ,, (k , v)
    ■-def = refl

    -- extensionality of Delta dicts
    -- (i.e. if two dicts represent the same mapping from ids to values,
    -- then they are reflexively equal as judged by _==_)
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

    -- decidable equality of delta dicts
    ==-dec : {V : Set}
              (d1 d2 : dd V) →
              ((v1 v2 : V) → v1 == v2 ∨ v1 ≠ v2) →
              d1 == d2 ∨ d1 ≠ d2
    ==-dec {V} (DD d1) (DD d2) h = ==-dec' {V} d1 d2 h
      where
      ==-dec' : {V : Set}
                 (d1 d2 : dl V) →
                 ((v1 v2 : V) → v1 == v2 ∨ v1 ≠ v2) →
                 DD d1 == DD d2 ∨ DD d1 ≠ DD d2
      ==-dec' [] [] _ = Inl refl
      ==-dec' [] (_ :: _) _ = Inr (λ ())
      ==-dec' (_ :: _) [] _ = Inr (λ ())
      ==-dec' ((hn1 , hv1) :: t1) ((hn2 , hv2) :: t2) V==dec
        with natEQ hn1 hn2 | V==dec hv1 hv2 | ==-dec' t1 t2 V==dec
      ... | Inl refl | Inl refl | Inl refl = Inl refl
      ... | Inl refl | Inl refl | Inr ne   = Inr λ where refl → ne refl
      ... | Inl refl | Inr ne   | _        = Inr λ where refl → ne refl
      ... | Inr ne   | _        | _        = Inr λ where refl → ne refl

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

    -- The destruct theorem as seen in the paper
    destruct-thm : ∀{V} {d d' : dd V} {k : K} {v : V} →
                     (destruct d == None → d == ∅)
                       ∧
                     (destruct d == Some ((k , v) , d') →
                        k # d' ∧ d == d' ,, (k , v))
    destruct-thm = destruct-thm-1 , destruct-thm-2

    -- TODO delete
    -- A useful way to destruct delta dict membership
    dlt-split : {V : Set} {d : dd V} {k1 k2 : K} {a1 a2 : V} →
                  (k1 , a1) ∈ (d ,, (k2 , a2)) →
                  (k1 ≠ k2 ∧ (k1 , a1) ∈ d) ∨ (k1 == k2 ∧ a1 == a2)
    dlt-split {d = d} {k1} {k2} {a1} {a2} n∈d+
      with natEQ (nat k1) (nat k2)
    ... | Inl eq
      rewrite bij.inj bij eq
        = Inr (refl , mem-unicity n∈d+ (k,v∈d,,k,v {d = d}))
    ... | Inr ne = Inl (ne' , k∈d+→k∈d ne' n∈d+)
            where
            ne' = λ eq → abort (ne (ap1 nat eq))

    -- When using destruct or delete, this theorem is useful for establishing termination
    extend-size : {V : Set} {d : dd V} {k : K} {v : V} →
                   k # d →
                   || d ,, (k , v) || == 1+ || d ||
    extend-size {V} {DD d} {k} {v} n#d = extend-size' {V} {d} {nat k} {v} n#d

    -- remove a specific mapping from a delta dict
    delete : {V : Set} {d : dd V} {k : K} {v : V} →
              (k , v) ∈ d →
              Σ[ d⁻ ∈ dd V ] (
                 d == d⁻ ,, (k , v) ∧
                 k # d⁻)
    delete {V} {DD d} {k} {v} h
      with delete' {V} {d} {nat k} {v} h
    ... | _ , refl , # = _ , refl , #

    ---- contraction and exchange ----

    contraction : {V : Set} {d : dd V} {k : K} {v v' : V} →
                   d ,, (k , v') ,, (k , v) == d ,, (k , v)
    contraction {V} {DD d} {k} {v} {v'}
      = ap1 DD <| contraction' {d = d} {nat k} {v} {v'}

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

    dltmap-func : {V1 V2 : Set} {d : dd V1} {f : V1 → V2} {k : K} {v : V1} →
                   dltmap f (d ,, (k , v)) == dltmap f d ,, (k , f v)
    dltmap-func {d = DD d} {f} {k} {v} = ap1 DD (dltmap-func' {d = d})

    ---- remaining definition, list⇒list-dlt ----

    list⇒list-dlt {V} l
      = foldl f ∅ (reverse l)
        where
          f : dd (List V) → K ∧ V → dd (List V)
          f (DD d) (k , v)
            with mem-dec (DD d) k
          ... | Inl (vs , k∈d)
            = DD d ,, (k , v :: vs)
          ... | Inr k#d
            = DD d ,, (k , v :: [])

    ---- dlt <=> list theorems ----

    dlt⇒list-inversion : {V : Set} {d : dd V} → list⇒dlt (dlt⇒list d) == d
    dlt⇒list-inversion {V} {DD d}
      = tr
           (λ y → DD (list⇒dlt' y) == DD d)
           (! (map^2 {f = λ { (k , v) → nat k , v }}
                     {λ { (n , v) → key n , v }}
                     {dlt⇒list' d}))
           lem
        where
        lem' : ∀{l} → map {Nat ∧ V} ((λ { (k , v) → nat k , v }) ⊙ (λ { (n , v) → key n , v })) l == l
        lem' {[]} = refl
        lem' {(n , v) :: t} rewrite lem' {t} | convert-bij2 {t = n} = refl
        lem : DD (list⇒dlt'
                   (map ((λ { (k , v) → nat k , v }) ⊙ (λ { (n , v) → key n , v }))
                     (dlt⇒list' d)))
              == DD d
        lem rewrite lem' {dlt⇒list' d} = ap1 DD dlt⇒list-inversion'
