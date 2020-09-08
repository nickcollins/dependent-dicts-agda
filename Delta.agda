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
module Delta (Key : Set) {{bij : bij Key Nat}} where
  -- Agda 2.6.1 has some bugs involving the 'abstract' keyword, so we can't use it, but ideally,
  -- the following line would be uncommented to ensure proper encapsulation
  -- abstract -- everything in the module is abstract

    ---- gory details - skip to "core definitions" ----
    private
      -- abbreviations for conversion between K and Nat
      K : Nat → Key
      K = convert-inv {{bij}}

      N : Key → Nat
      N = bij.convert bij

      -- another bij-related convenience functions
      inj-cp : ∀{k1 k2} → k1 ≠ k2 → N k1 ≠ N k2
      inj-cp ne eq = abort (ne (bij.inj bij eq))

      -- helper function
      diff-1 : ∀{n m} → n < m → Nat
      diff-1 n<m = difference (n<m→1+n≤m n<m)

      -- raw underlying list-of-pairs type
      rt : (A : Set) → Set
      rt A = List (Nat ∧ A)

      ---- helper definitions ----

      _lkup_ : {A : Set} → rt A → Nat → Maybe A
      [] lkup x = None
      ((hx , ha) :: t) lkup x with <dec x hx
      ... | Inl x<hx       = None
      ... | Inr (Inl refl) = Some ha
      ... | Inr (Inr hx<x) = t lkup (diff-1 hx<x)

      _,,'_ : ∀{A} → rt A → (Nat ∧ A) → rt A
      [] ,,' (x , a) = (x , a) :: []
      ((hx , ha) :: t) ,,' (x , a) with <dec x hx
      ... | Inl x<hx       = (x , a) :: ((diff-1 x<hx , ha) :: t)
      ... | Inr (Inl refl) = (x , a) :: t
      ... | Inr (Inr hx<x) = (hx , ha) :: (t ,,' (diff-1 hx<x , a))

      data _∈'_ : {A : Set} (p : Nat ∧ A) → (Γ : rt A) → Set where
        InH : {A : Set} {Γ : rt A} {n : Nat} {a : A} →
          (n , a) ∈' ((n , a) :: Γ)
        InT : {A : Set} {Γ : rt A} {n s : Nat} {a a' : A} →
          (n , a) ∈' Γ →
          (n + 1+ s , a) ∈' ((s , a') :: Γ)

      dom' : {A : Set} → rt A → Nat → Set
      dom' {A} Γ n = Σ[ a ∈ A ] ((n , a) ∈' Γ)

      _#'_ : {A : Set} (n : Nat) → (Γ : rt A) → Set
      n #' Γ = dom' Γ n → ⊥

      ---- lemmas ----

      undiff-1 : (x s : Nat) → (x<s+1+x : x < s + 1+ x) → s == diff-1 x<s+1+x
      undiff-1 x s x<s+1+x
        rewrite n+1+m==1+n+m {s} {x} | ! (m-n==1+m-1+n n≤m+n (n<m→1+n≤m x<s+1+x)) | +comm {s} {x}
          = ! (n+m-n==m n≤n+m)

      x#'[] : {A : Set} {n : Nat} → _#'_ {A} n []
      x#'[] (_ , ())

      too-small : {A : Set} {Γ : rt A} {xl xb : Nat} {a : A} →
                   xl < xb →
                   dom' ((xb , a) :: Γ) xl →
                   ⊥
      too-small (_ , ne) (_ , InH) = ne refl
      too-small (x+1+xb≤xb , x+1+xb==xb) (_ , InT _) =
        x+1+xb==xb (≤antisym x+1+xb≤xb (≤trans (≤1+ ≤refl) n≤m+n))

      all-not-none : {A : Set} {Γ : rt A} {x : Nat} {a : A} →
                      None ≠ (((x , a) :: Γ) lkup x)
      all-not-none {x = x} rewrite <dec-refl x = λ ()

      all-bindings-==-rec-eq : {A : Set} {Γ1 Γ2 : rt A} {x : Nat} {a : A} →
                                ((x' : Nat) → ((x , a) :: Γ1) lkup x' == ((x , a) :: Γ2) lkup x') →
                                ((x' : Nat) → Γ1 lkup x' == Γ2 lkup x')
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

      all-bindings-==-rec : {A : Set} {Γ1 Γ2 : rt A} {x1 x2 : Nat} {a1 a2 : A} →
                             ((x : Nat) → ((x1 , a1) :: Γ1) lkup x == ((x2 , a2) :: Γ2) lkup x) →
                             ((x : Nat) → Γ1 lkup x == Γ2 lkup x)
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

      sad-lemma : {A : Set} {Γ : rt A} {x n : Nat} {a a' : A} →
                   (x + 1+ n , a') ∈' ((n , a) :: Γ) →
                   Σ[ x' ∈ Nat ] Σ[ Γ' ∈ rt A ] (
                      Γ' == ((n , a) :: Γ) ∧
                      x' == x + 1+ n ∧
                      (x' , a') ∈' Γ')
      sad-lemma h = _ , _ , refl , refl , h

      lemma-math' : ∀{x x1 n} → x ≠ x1 + (n + 1+ x)
      lemma-math' {x} {x1} {n}
        rewrite ! (+assc {x1} {n} {1+ x})
              | n+1+m==1+n+m {x1 + n} {x}
              | +comm {1+ x1 + n} {x}
          = n≠n+1+m

      lookup-cons-1' : {A : Set} {Γ : rt A} {x : Nat} {a : A} → Γ lkup x == Some a → (x , a) ∈' Γ
      lookup-cons-1' {Γ = []} ()
      lookup-cons-1' {Γ = ((hx , ha) :: t)} {x} h
        with <dec x hx
      lookup-cons-1' {Γ = ((hx , ha) :: t)} {x} ()     | Inl _
      lookup-cons-1' {Γ = ((hx , ha) :: t)} {.hx} refl | Inr (Inl refl) = InH
      lookup-cons-1' {Γ = ((hx , ha) :: t)} {x} {a} h  | Inr (Inr hx<x)
        = tr
            (λ y → (y , a) ∈' ((hx , ha) :: t))
            (m-n+n==m (n<m→1+n≤m hx<x))
            (InT (lookup-cons-1' {Γ = t} h))

      lookup-cons-2' : {A : Set} {Γ : rt A} {n : Nat} {a : A} →
                        (n , a) ∈' Γ →
                        Γ lkup n == Some a
      lookup-cons-2' {n = x} InH rewrite <dec-refl x = refl
      lookup-cons-2' (InT {Γ = Γ} {n = x} {s} {a} x∈Γ)
        with <dec (x + 1+ s) s
      ... | Inl x+1+s<s        = abort (<antisym x+1+s<s (n<m→n<s+m n<1+n))
      ... | Inr (Inl x+1+s==s) = abort ((flip n≠n+1+m) (n+1+m==1+n+m · (+comm {1+ s} · x+1+s==s)))
      ... | Inr (Inr s<x+1+s)
        with lookup-cons-2' x∈Γ
      ... | h rewrite ! (undiff-1 s x s<x+1+s) = h

      x,v∈'Γ,,x,v : {A : Set} {Γ : rt A} {x : Nat} {a : A} → (x , a) ∈' (Γ ,,' (x , a))
      x,v∈'Γ,,x,v {Γ = []} {x} {a} = InH
      x,v∈'Γ,,x,v {Γ = ((hx , ha) :: t)} {x} {a}
        with <dec x hx
      ... | Inl _          = InH
      ... | Inr (Inl refl) = InH
      ... | Inr (Inr hx<x) =
              tr
                (λ y → (y , a) ∈' ((hx , ha) :: (t ,,' (diff-1 hx<x , a))))
                (m-n+n==m (n<m→1+n≤m hx<x))
                (InT (x,v∈'Γ,,x,v {Γ = t} {diff-1 hx<x}))

      x∈Γ+→'x∈Γ : {A : Set} {Γ : rt A} {x x' : Nat} {a a' : A} →
                    x ≠ x' →
                    (x , a) ∈' (Γ ,,' (x' , a')) →
                    (x , a) ∈' Γ
      x∈Γ+→'x∈Γ {Γ = []} x≠x' InH = abort (x≠x' refl)
      x∈Γ+→'x∈Γ {Γ = []} x≠x' (InT ())
      x∈Γ+→'x∈Γ {Γ = (hx , ha) :: t} {x' = x'} x≠x' x∈Γ+
        with <dec x' hx
      x∈Γ+→'x∈Γ {_} {(hx , ha) :: t} {x' = x'} x≠x' InH | Inl x'<hx = abort (x≠x' refl)
      x∈Γ+→'x∈Γ {_} {(hx , ha) :: t} {x' = x'} x≠x' (InT InH) | Inl x'<hx
        rewrite m-n+n==m (n<m→1+n≤m x'<hx) = InH
      x∈Γ+→'x∈Γ {_} {(hx , ha) :: t} {x' = x'} x≠x' (InT (InT {n = x} x∈Γ+)) | Inl x'<hx
        rewrite +assc {x} {1+ (diff-1 x'<hx)} {1+ x'} | m-n+n==m (n<m→1+n≤m x'<hx)
          = InT x∈Γ+
      x∈Γ+→'x∈Γ {_} {(hx , ha) :: t} {x' = .hx} x≠x' InH | Inr (Inl refl) = abort (x≠x' refl)
      x∈Γ+→'x∈Γ {_} {(hx , ha) :: t} {x' = .hx} x≠x' (InT x∈Γ+) | Inr (Inl refl) = InT x∈Γ+
      x∈Γ+→'x∈Γ {_} {(hx , ha) :: t} {x' = x'} x≠x' InH | Inr (Inr hx<x') = InH
      x∈Γ+→'x∈Γ {_} {(hx , ha) :: t} {x' = x'} x≠x' (InT x∈Γ+) | Inr (Inr hx<x')
        = InT (x∈Γ+→'x∈Γ (λ where refl → x≠x' (m-n+n==m (n<m→1+n≤m hx<x'))) x∈Γ+)

      x∈Γ→'x∈Γ+ : {A : Set} {Γ : rt A} {x x' : Nat} {a a' : A} →
                   x ≠ x' →
                   (x , a) ∈' Γ →
                   (x , a) ∈' (Γ ,,' (x' , a'))
      x∈Γ→'x∈Γ+ {x = x} {x'} {a} {a'} x≠x' (InH {Γ = Γ'})
        with <dec x' x
      ... | Inl x'<x
        = tr
            (λ y → (y , a) ∈' ((x' , a') :: ((diff-1 x'<x , a) :: Γ')))
            (m-n+n==m (n<m→1+n≤m x'<x))
            (InT InH)
      ... | Inr (Inl refl) = abort (x≠x' refl)
      ... | Inr (Inr x<x') = InH
      x∈Γ→'x∈Γ+ {x = .(_ + 1+ _)} {x'} {a} {a'} x≠x' (InT {Γ = Γ} {x} {s} {a' = a''} x∈Γ)
        with <dec x' s
      ... | Inl x'<s
        = tr
            (λ y → (y , a) ∈' ((x' , a') :: ((diff-1 x'<s , a'') :: Γ)))
            ((+assc {b = 1+ (diff-1 x'<s)}) · (ap1 (_+_ x) (1+ap (m-n+n==m (n<m→1+n≤m x'<s)))))
            (InT (InT x∈Γ))
      ... | Inr (Inl refl) = InT x∈Γ
      ... | Inr (Inr s<x') =
              InT (x∈Γ→'x∈Γ+ (λ where refl → x≠x' (m-n+n==m (n<m→1+n≤m s<x'))) x∈Γ)

      dltindirect' : {A : Set} (Γ : rt A) (x : Nat) → dom' Γ x ∨ x #' Γ
      dltindirect' [] x = Inr (λ ())
      dltindirect' ((hx , ha) :: t) x
        with <dec x hx
      ... | Inl x<hx       = Inr (too-small x<hx)
      ... | Inr (Inl refl) = Inl (ha , InH)
      ... | Inr (Inr hx<x)
        with dltindirect' t (diff-1 hx<x)
      dltindirect' ((hx , ha) :: t) x | Inr (Inr hx<x) | Inl (a , rec) =
        Inl (a , tr
                   (λ y → (y , a) ∈' ((hx , ha) :: t))
                   (m-n+n==m (n<m→1+n≤m hx<x))
                   (InT rec))
      dltindirect' {A} ((hx , ha) :: t) x | Inr (Inr hx<x) | Inr dne =
        Inr x∉Γ
          where
          x∉Γ : Σ[ a ∈ A ] ((x , a) ∈' ((hx , ha) :: t)) → ⊥
          x∉Γ (_ , x∈Γ) with x∈Γ
          ... | InH = (π2 hx<x) refl
          ... | InT {n = s} x-hx-1∈t
            rewrite ! (undiff-1 hx s hx<x) = dne (_ , x-hx-1∈t)

      dlt-==-eqv' : {A : Set} {Γ1 Γ2 : rt A} →
                     ((x : Nat) → Γ1 lkup x == Γ2 lkup x) →
                     Γ1 == Γ2
      dlt-==-eqv' {Γ1 = []} {[]} all-bindings-== = refl
      dlt-==-eqv' {Γ1 = []} {(hx2 , ha2) :: t2} all-bindings-==
        = abort (all-not-none {Γ = t2} {x = hx2} (all-bindings-== hx2))
      dlt-==-eqv' {Γ1 = (hx1 , ha1) :: t1} {[]} all-bindings-==
        = abort (all-not-none {Γ = t1} {x = hx1} (! (all-bindings-== hx1)))
      dlt-==-eqv' {Γ1 = (hx1 , ha1) :: t1} {(hx2 , ha2) :: t2} all-bindings-==
        rewrite dlt-==-eqv' {Γ1 = t1} {t2} (all-bindings-==-rec all-bindings-==)
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

      dlt-delete' : {A : Set} {Γ : rt A} {n : Nat} {a : A} →
                     (n , a) ∈' Γ →
                     Σ[ Γ⁻ ∈ rt A ] (
                        Γ == Γ⁻ ,,' (n , a) ∧
                        n #' Γ⁻)
      dlt-delete' {Γ = (n' , a') :: Γ} {n} n∈Γ
        with <dec n n'
      ... | Inl n<n'       = abort (too-small n<n' (_ , n∈Γ))
      dlt-delete' {_} {(n' , a') :: []} {.n'} InH                 | Inr (Inl _) = [] , refl , λ ()
      dlt-delete' {_} {(n' , a') :: ((n'' , a'') :: Γ)} {.n'} InH | Inr (Inl _)
        = ((n'' + 1+ n' , a'') :: Γ) , lem , λ {(_ , n'∈Γ+) → abort (too-small (n<m→n<s+m n<1+n) (_ , n'∈Γ+))}
          where
            lem : ((n' , a') :: ((n'' , a'') :: Γ)) == ((n'' + 1+ n' , a'') :: Γ) ,,' (n' , a')
            lem
              with <dec n' (n'' + 1+ n')
            lem | Inl n'<n''+1+n' rewrite ! (undiff-1 n' n'' n'<n''+1+n') = refl
            lem | Inr (Inl false) = abort (lemma-math' {x1 = Z} false)
            lem | Inr (Inr false) = abort (<antisym false (n<m→n<s+m n<1+n))
      dlt-delete' {Γ = (n' , a') :: Γ} InH       | Inr (Inr n'<n') = abort (<antirefl n'<n')
      dlt-delete' {Γ = (n' , a') :: Γ} (InT n∈Γ) | Inr _
        with dlt-delete' {Γ = Γ} n∈Γ
      dlt-delete' {Γ = (n' , a') :: Γ} {.(_ + 1+ n')} {a} (InT {n = x} n∈Γ) | Inr _ | Γ⁻ , refl , x#Γ⁻
        = _ , lem' , lem
          where
            lem : (x + 1+ n') #' ((n' , a') :: Γ⁻)
            lem (_ , x+1+n'∈Γ?)
              with sad-lemma x+1+n'∈Γ?
            ... | _ , _ , refl , x'==x+1+n' , InH = abort (lemma-math' {x1 = Z} x'==x+1+n')
            ... | _ , _ , refl , x'==x+1+n' , InT {n = x'} x+1+n'∈Γ'
              rewrite +inj {b = 1+ n'} x'==x+1+n'
                = x#Γ⁻ (_ , x+1+n'∈Γ')
            lem' : ((n' , a') :: (Γ⁻ ,,' (x , a))) == (((n' , a') :: Γ⁻) ,,' (x + 1+ n' , a))
            lem'
              with <dec (x + 1+ n') n'
            lem' | Inl x+1+n'<n'       = abort (<antisym x+1+n'<n' (n<m→n<s+m n<1+n))
            lem' | Inr (Inl false)     = abort (lemma-math' {x1 = Z} (! false))
            lem' | Inr (Inr n'<x+1+n') rewrite ! (undiff-1 n' x n'<x+1+n') = refl

      dlt-elim' : {A : Set} {Γ : rt A} →
                   Γ == []
                      ∨
                   Σ[ n ∈ Nat ] Σ[ a ∈ A ] Σ[ Γ' ∈ rt A ]
                      (Γ == Γ' ,,' (n , a) ∧ n #' Γ')
      dlt-elim' {Γ = []}              = Inl refl
      dlt-elim' {Γ = ((n , a) :: [])} = Inr (_ , _ , _ , refl , x#'[])
      dlt-elim' {Γ = ((n , a) :: ((m , a2) :: Γ''))}
        with expr-eq (λ _ → (m + 1+ n , a2) :: Γ'')
      ... | Γ' , eq
        = Inr (n , a , Γ' , eqP , not-dom)
          where
          eqP : ((n , a) :: ((m , a2) :: Γ'')) == Γ' ,,' (n , a)
          eqP rewrite eq with <dec n (m + 1+ n)
          ... | Inl n<m+1+n
            rewrite ! (undiff-1 n m n<m+1+n) = refl
          ... | Inr (Inl n==m+1+n)
                  = abort (n≠n+1+m (n==m+1+n · (n+1+m==1+n+m · +comm {1+ m})))
          ... | Inr (Inr m+1+n<n)
                  = abort (<antisym m+1+n<n (n<m→n<s+m n<1+n))
          not-dom : dom' Γ' n → ⊥
          not-dom rewrite eq = λ n∈Γ' → too-small (n<m→n<s+m n<1+n) n∈Γ'

      dlt-decreasing' : {A : Set} {Γ : rt A} {n : Nat} {a : A} →
                         n #' Γ →
                         ∥ Γ ,,' (n , a) ∥ == 1+ ∥ Γ ∥
      dlt-decreasing' {Γ = []} n#Γ = refl
      dlt-decreasing' {Γ = (n' , a') :: Γ} {n} n#Γ
        with <dec n n'
      ... | Inl n<n'       = refl
      ... | Inr (Inl refl) = abort (n#Γ (_ , InH))
      ... | Inr (Inr n'<n)
              = 1+ap (dlt-decreasing' λ {(a , diff∈Γ) →
                  n#Γ (a , tr
                             (λ y → (y , a) ∈' ((n' , a') :: Γ))
                             (m-n+n==m (n<m→1+n≤m n'<n))
                             (InT diff∈Γ))})

      ---- contrapositives of some previous theorems ----

      lookup-dec' : {A : Set} (Γ : rt A) (n : Nat) →
                     Σ[ a ∈ A ] (Γ lkup n == Some a) ∨ Γ lkup n == None
      lookup-dec' Γ n
        with Γ lkup n
      ... | Some a = Inl (a , refl)
      ... | None   = Inr refl

      lookup-cp-1' : {A : Set} {Γ : rt A} {n : Nat} →
                      n #' Γ →
                      Γ lkup n == None
      lookup-cp-1' {Γ = Γ} {n} n#Γ
        with lookup-dec' Γ n
      ... | Inl (_ , n∈Γ) = abort (n#Γ (_ , lookup-cons-1' n∈Γ))
      ... | Inr n#'Γ      = n#'Γ

      x#Γ→'x#Γ+ : {A : Set} {Γ : rt A} {x x' : Nat} {a' : A} →
                    x ≠ x' →
                    x #' Γ →
                    x #' (Γ ,,' (x' , a'))
      x#Γ→'x#Γ+ {Γ = Γ} {x} {x'} {a'} x≠x' x#Γ
        with dltindirect' (Γ ,,' (x' , a')) x
      ... | Inl (_ , x∈Γ+) = abort (x#Γ (_ , x∈Γ+→'x∈Γ x≠x' x∈Γ+))
      ... | Inr x#Γ+       = x#Γ+

      ---- union, and dlt <=> list conversion definitions

      merge' : {A : Set} → (A → A → A) → Maybe A → A → A
      merge' merge ma1 a2
        with ma1
      ... | None    = a2
      ... | Some a1 = merge a1 a2

      union' : {A : Set} → (A → A → A) → rt A → rt A → Nat → rt A
      union' merge Γ1 [] _ = Γ1
      union' merge Γ1 ((hx , ha) :: Γ2) offset
        with Γ1 ,,' (hx + offset , merge' merge (Γ1 lkup hx + offset) ha)
      ... | Γ1+ = union' merge Γ1+ Γ2 (1+ hx + offset)

      dlt⇒list' : {A : Set} (Γ : rt A) → rt A
      dlt⇒list' [] = []
      dlt⇒list' ((x , a) :: Γ) = (x , a) :: map (λ {(x' , a') → x' + 1+ x , a'}) (dlt⇒list' Γ)

      list⇒dlt' : {A : Set} (Γ : rt A) → rt A
      list⇒dlt' = foldr _,,'_ []

      ---- union, dlt <=> list, etc lemmas ----

      lemma-union'-0 : {A : Set} {m : A → A → A} {Γ1 Γ2 : rt A} {x n : Nat} {a : A} →
                        (x , a) ∈' Γ1 →
                        (x , a) ∈' (union' m Γ1 Γ2 (n + 1+ x))
      lemma-union'-0 {Γ2 = []} x∈Γ1 = x∈Γ1
      lemma-union'-0 {Γ2 = (x1 , a1) :: Γ2} {x} {n} x∈Γ1
        rewrite ! (+assc {1+ x1} {n} {1+ x})
          = lemma-union'-0 {Γ2 = Γ2} {n = 1+ x1 + n} (x∈Γ→'x∈Γ+ (lemma-math' {x1 = x1} {n}) x∈Γ1)

      lemma-union'-1 : {A : Set} {m : A → A → A} {Γ1 Γ2 : rt A} {x n : Nat} {a : A} →
                        (x , a) ∈' Γ1 →
                        (n≤x : n ≤ x) →
                        (difference n≤x) #' Γ2 →
                        (x , a) ∈' (union' m Γ1 Γ2 n)
      lemma-union'-1 {Γ2 = []} {x} x∈Γ1 n≤x x-n#Γ2 = x∈Γ1
      lemma-union'-1 {m = m} {Γ1} {(x1 , a1) :: Γ2} {x} {n} {a} x∈Γ1 n≤x x-n#Γ2
        with <dec x (x1 + n)
      lemma-union'-1 {m = m} {Γ1} {(x1 , a1) :: Γ2} {x} {n} {a} x∈Γ1 n≤x x-n#Γ2 | Inl x<x1+n
        with Γ1 lkup x1 + n
      lemma-union'-1 {m = m} {Γ1} {(x1 , a1) :: Γ2} {x} {n} {a} x∈Γ1 n≤x x-n#Γ2 | Inl x<x1+n | Some a'
        with expr-eq (λ _ → Γ1 ,,' (x1 + n , m a' a1))
      lemma-union'-1 {m = m} {Γ1} {(x1 , a1) :: Γ2} {x} {n} {a} x∈Γ1 n≤x x-n#Γ2 | Inl x<x1+n | Some a' | Γ1+ , refl
        = tr
             (λ y → (x , a) ∈' (union' m Γ1+ Γ2 y))
             (n+1+m==1+n+m {difference (π1 x<x1+n)} · 1+ap (m-n+n==m (π1 x<x1+n)))
             (lemma-union'-0 {Γ2 = Γ2} (x∈Γ→'x∈Γ+ (π2 x<x1+n) x∈Γ1))
      lemma-union'-1 {m = m} {Γ1} {(x1 , a1) :: Γ2} {x} {n} {a} x∈Γ1 n≤x x-n#Γ2 | Inl x<x1+n | None
        with expr-eq (λ _ → Γ1 ,,' (x1 + n , a1))
      lemma-union'-1 {m = m} {Γ1} {(x1 , a1) :: Γ2} {x} {n} {a} x∈Γ1 n≤x x-n#Γ2 | Inl x<x1+n | None | Γ1+ , refl
        = tr
             (λ y → (x , a) ∈' (union' m Γ1+ Γ2 y))
             (n+1+m==1+n+m {difference (π1 x<x1+n)} · 1+ap (m-n+n==m (π1 x<x1+n)))
             (lemma-union'-0 {Γ2 = Γ2} (x∈Γ→'x∈Γ+ (π2 x<x1+n) x∈Γ1))
      lemma-union'-1 {m = m} {Γ1} {(x1 , a1) :: Γ2} {x} {n} {a} x∈Γ1 n≤x x-n#Γ2 | Inr (Inl refl)
        rewrite +comm {x1} {n} | n+m-n==m n≤x
          = abort (x-n#Γ2 (_ , InH))
      lemma-union'-1 {m = m} {Γ1} {(x1 , a1) :: Γ2} {x} {n} {a} x∈Γ1 n≤x x-n#Γ2 | Inr (Inr x1+n<x)
        rewrite (! (a+b==c→a==c-b (+assc {diff-1 x1+n<x} · m-n+n==m (n<m→1+n≤m x1+n<x)) n≤x))
          = lemma-union'-1
              (x∈Γ→'x∈Γ+ (flip (π2 x1+n<x)) x∈Γ1)
              (n<m→1+n≤m x1+n<x)
              λ {(_ , x-x1-n∈Γ2) → x-n#Γ2 (_ , InT x-x1-n∈Γ2)}

      lemma-union'-2 : {A : Set} {m : A → A → A} {Γ1 Γ2 : rt A} {x n : Nat} {a : A} →
                        (x + n) #' Γ1 →
                        (x , a) ∈' Γ2 →
                        (x + n , a) ∈' (union' m Γ1 Γ2 n)
      lemma-union'-2 {Γ1 = Γ1} x+n#Γ1 (InH {Γ = Γ2})
        rewrite lookup-cp-1' x+n#Γ1
          = lemma-union'-0 {Γ2 = Γ2} {n = Z} (x,v∈'Γ,,x,v {Γ = Γ1})
      lemma-union'-2 {Γ1 = Γ1} {n = n} x+n#Γ1 (InT {Γ = Γ2} {n = x} {s} x∈Γ2)
        rewrite +assc {x} {1+ s} {n}
        with Γ1 lkup s + n
      ... | Some a'
        = lemma-union'-2
            (λ {(_ , x∈Γ1+) →
                 x+n#Γ1 (_ , x∈Γ+→'x∈Γ (flip (lemma-math' {x1 = Z})) x∈Γ1+)})
            x∈Γ2
      ... | None
        = lemma-union'-2
            (λ {(_ , x∈Γ1+) →
                 x+n#Γ1 (_ , x∈Γ+→'x∈Γ (flip (lemma-math' {x1 = Z})) x∈Γ1+)})
            x∈Γ2

      lemma-union'-3 : {A : Set} {m : A → A → A} {Γ1 Γ2 : rt A} {x n : Nat} {a1 a2 : A} →
                        (x + n , a1) ∈' Γ1 →
                        (x , a2) ∈' Γ2 →
                        (x + n , m a1 a2) ∈' (union' m Γ1 Γ2 n)
      lemma-union'-3 {Γ1 = Γ1} x+n∈Γ1 (InH {Γ = Γ2})
        rewrite lookup-cons-2' x+n∈Γ1
          = lemma-union'-0 {Γ2 = Γ2} {n = Z} (x,v∈'Γ,,x,v {Γ = Γ1})
      lemma-union'-3 {Γ1 = Γ1} {n = n} x+n∈Γ1 (InT {Γ = Γ2} {n = x} {s} x∈Γ2)
        rewrite +assc {x} {1+ s} {n}
        with Γ1 lkup s + n
      ... | Some a'
        = lemma-union'-3 (x∈Γ→'x∈Γ+ (flip (lemma-math' {x1 = Z})) x+n∈Γ1) x∈Γ2
      ... | None
        = lemma-union'-3 (x∈Γ→'x∈Γ+ (flip (lemma-math' {x1 = Z})) x+n∈Γ1) x∈Γ2

      lemma-union'-4 : {A : Set} {m : A → A → A} {Γ1 Γ2 : rt A} {x n : Nat} →
                        dom' (union' m Γ1 Γ2 n) x →
                        dom' Γ1 x ∨ (Σ[ s ∈ Nat ] (x == n + s ∧ dom' Γ2 s))
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
          = Inl (_ , x∈Γ+→'x∈Γ x≠n+x1 x∈Γ1+)

      lemma-dlt⇒list' : {A : Set} {Γ Γ' : rt A} {x : Nat} {a : A} →
                            foldl
                              (λ {b (x' , a') → b ,,' (x' + 1+ x , a')})
                              ((x , a) :: Γ')
                              Γ
                            == ((x , a) :: (foldl _,,'_ Γ' Γ))
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

      dlt⇒list-size' : {V : Set} {d : rt V} → ∥ dlt⇒list' d ∥ == ∥ d ∥
      dlt⇒list-size' {d = []} = refl
      dlt⇒list-size' {d = _ :: d} = 1+ap (map-len · dlt⇒list-size')

      dlt⇒list-In-1' : {V : Set} {d : rt V} {n : Nat} {v : V} →
                         (n , v) ∈' d →
                         (n , v) In dlt⇒list' d
      dlt⇒list-In-1' InH = LInH
      dlt⇒list-In-1' (InT ∈h) = LInT <| map-In <| dlt⇒list-In-1' ∈h

      list⇒dlt-In' : {V : Set} {l : rt V} {n : Nat} {v : V} →
                       (n , v) ∈' list⇒dlt' l →
                       (n , v) In l
      list⇒dlt-In' {l = (n' , v') :: l} {n} ∈h
        rewrite foldl-++ {l1 = reverse l} {(n' , v') :: []} {_,,'_} {[]}
        with natEQ n n'
      ... | Inr ne   = LInT (list⇒dlt-In' (x∈Γ+→'x∈Γ ne ∈h))
      ... | Inl refl
        rewrite someinj <| (! <| lookup-cons-2' ∈h) · (lookup-cons-2' {n = n} {v'} <| x,v∈'Γ,,x,v {Γ = foldl _,,'_ [] (reverse l)})
          = LInH

      list⇒dlt-order' : {V : Set} {l1 l2 : rt V} {n : Nat} {v1 v2 : V} →
                          (n , v1) ∈' (list⇒dlt' ((n , v1) :: l1 ++ ((n , v2) :: l2)))
      list⇒dlt-order' {l1 = l1} {l2} {n} {v1} {v2}
        rewrite foldl-++ {l1 = reverse (l1 ++ ((n , v2) :: l2))} {(n , v1) :: []} {_,,'_} {[]}
          = x,v∈'Γ,,x,v {Γ = foldl _,,'_ [] <| reverse (l1 ++ ((n , v2) :: l2))}

      -- TODO the other direction
      dlt⇒list-inversion' : {A : Set} {Γ : rt A} → list⇒dlt' (dlt⇒list' Γ) == Γ
      dlt⇒list-inversion' = {!!}
      {- TODO
      dlt⇒list-inversion' {Γ = []} = refl
      dlt⇒list-inversion' {Γ = (x , a) :: Γ}
        with dlt⇒list-inversion' {Γ = Γ}
      ... | rec
        = foldl-map {l = dlt⇒list' Γ} {_,,'_} {λ {(x' , a') → x' + 1+ x , a'}} {(x , a) :: []}
          · (lemma-dlt⇒list' {Γ = dlt⇒list' Γ} · ap1 (λ y → (x , a) :: y) rec)
             -}

      dltmap-func' : {V1 V2 : Set} {d : rt V1} {f : V1 → V2} {n : Nat} {v : V1} →
                      (map (λ { (hx , ha) → hx , f ha }) (d ,,' (n , v)))
                        ==
                      (map (λ { (hx , ha) → hx , f ha }) d ,,' (n , f v))
      dltmap-func' {d = []} = refl
      dltmap-func' {d = (nh , vh) :: d} {f = f} {n}
        with <dec n nh
      ... | Inl n<nh       = refl
      ... | Inr (Inl refl) = refl
      ... | Inr (Inr nh<n) = ap1 ((nh , f vh) ::_) (dltmap-func' {d = d})

      -- TODO these proofs could use refactoring -
      -- contraction should probably make use of dlt-==-dec and
      -- exchange is way too long and repetitive

      contraction' : {A : Set} {Γ : rt A} {x : Nat} {a a' : A} → (Γ ,,' (x , a')) ,,' (x , a) == Γ ,,' (x , a)
      contraction' {Γ = []} {x} rewrite <dec-refl x = refl
      contraction' {Γ = (hx , ha) :: t} {x} {a} {a'}
        with <dec x hx
      ... | Inl _          rewrite <dec-refl x  = refl
      ... | Inr (Inl refl) rewrite <dec-refl hx = refl
      ... | Inr (Inr hx<x)
        with <dec x hx
      ... | Inl x<hx        = abort (<antisym x<hx hx<x)
      ... | Inr (Inl refl)  = abort (<antirefl hx<x)
      ... | Inr (Inr hx<'x)
        with contraction' {Γ = t} {diff-1 hx<'x} {a} {a'}
      ... | eq
        rewrite diff-proof-irrelevance (n<m→1+n≤m hx<x) (n<m→1+n≤m hx<'x) | eq
          = refl

      exchange' : {A : Set} {Γ : rt A} {x1 x2 : Nat} {a1 a2 : A} →
                   x1 ≠ x2 →
                   (Γ ,,' (x1 , a1)) ,,' (x2 , a2) == (Γ ,,' (x2 , a2)) ,,' (x1 , a1)
      exchange' {A} {Γ} {x1} {x2} {a1} {a2} x1≠x2 = dlt-==-eqv' fun
        where
          fun : (x : Nat) →
                 ((Γ ,,' (x1 , a1)) ,,' (x2 , a2)) lkup x ==
                 ((Γ ,,' (x2 , a2)) ,,' (x1 , a1)) lkup x
          fun x
            with natEQ x x1 | natEQ x x2 | dltindirect' Γ x
          fun x  | Inl refl | Inl refl | _
            = abort (x1≠x2 refl)
          fun x1 | Inl refl | Inr x≠x2 | Inl (_ , x1∈Γ)
            with x,v∈'Γ,,x,v {Γ = Γ} {x1} {a1}
          ... | x∈Γ+1
            with x∈Γ→'x∈Γ+ {a' = a2} x≠x2 x∈Γ+1 | x,v∈'Γ,,x,v {Γ = Γ ,,' (x2 , a2)} {x1} {a1}
          ... | x∈Γ++1 | x∈Γ++2
            rewrite lookup-cons-2' x∈Γ++1 | lookup-cons-2' x∈Γ++2 = refl
          fun x1 | Inl refl | Inr x≠x2 | Inr x1#Γ
            with x,v∈'Γ,,x,v {Γ = Γ} {x1} {a1}
          ... | x∈Γ+1
            with x∈Γ→'x∈Γ+ {a' = a2} x≠x2 x∈Γ+1 | x,v∈'Γ,,x,v {Γ = Γ ,,' (x2 , a2)} {x1} {a1}
          ... | x∈Γ++1 | x∈Γ++2
            rewrite lookup-cons-2' x∈Γ++1 | lookup-cons-2' x∈Γ++2 = refl
          fun x2 | Inr x≠x1 | Inl refl | Inl (_ , x2∈Γ)
            with x,v∈'Γ,,x,v {Γ = Γ} {x2} {a2}
          ... | x∈Γ+2
            with x∈Γ→'x∈Γ+ {a' = a1} x≠x1 x∈Γ+2 | x,v∈'Γ,,x,v {Γ = Γ ,,' (x1 , a1)} {x2} {a2}
          ... | x∈Γ++1 | x∈Γ++2
            rewrite lookup-cons-2' x∈Γ++1 | lookup-cons-2' x∈Γ++2 = refl
          fun x2 | Inr x≠x1 | Inl refl | Inr x2#Γ
            with x,v∈'Γ,,x,v {Γ = Γ} {x2} {a2}
          ... | x∈Γ+2
            with x∈Γ→'x∈Γ+ {a' = a1} x≠x1 x∈Γ+2 | x,v∈'Γ,,x,v {Γ = Γ ,,' (x1 , a1)} {x2} {a2}
          ... | x∈Γ++1 | x∈Γ++2
            rewrite lookup-cons-2' x∈Γ++1 | lookup-cons-2' x∈Γ++2 = refl
          fun x  | Inr x≠x1 | Inr x≠x2 | Inl (_ , x∈Γ)
            with x∈Γ→'x∈Γ+ {a' = a1} x≠x1 x∈Γ   | x∈Γ→'x∈Γ+ {a' = a2} x≠x2 x∈Γ
          ... | x∈Γ+1  | x∈Γ+2
            with x∈Γ→'x∈Γ+ {a' = a2} x≠x2 x∈Γ+1 | x∈Γ→'x∈Γ+ {a' = a1} x≠x1 x∈Γ+2
          ... | x∈Γ++1 | x∈Γ++2
            rewrite lookup-cons-2' x∈Γ++1 | lookup-cons-2' x∈Γ++2 = refl
          fun x  | Inr x≠x1 | Inr x≠x2 | Inr x#Γ
            with x#Γ→'x#Γ+ {a' = a1} x≠x1 x#Γ   | x#Γ→'x#Γ+ {a' = a2} x≠x2 x#Γ
          ... | x#Γ+1  | x#Γ+2
            with x#Γ→'x#Γ+ {a' = a2} x≠x2 x#Γ+1 | x#Γ→'x#Γ+ {a' = a1} x≠x1 x#Γ+2
          ... | x#Γ++1 | x#Γ++2
            rewrite lookup-cp-1' x#Γ++1 | lookup-cp-1' x#Γ++2 = refl

    ---- core definitions ----

    data t (A : Set) : Set where
      TW : rt A → t A

    -- nil
    ∅ : {A : Set} → t A
    ∅ = TW []

    -- singleton
    ■_ : {A : Set} → (Key ∧ A) → t A
    ■_ (k , a) = TW <| (N k , a) :: []

    -- extension/insertion
    _,,_ : ∀{A} → t A → (Key ∧ A) → t A
    (TW Γ) ,, (k , a) = TW <| Γ ,,' (N k , a)

    infixl 10 _,,_

    -- membership
    _∈_ : {A : Set} (p : Key ∧ A) → (Γ : t A) → Set
    _∈_ {A} (k , a) (TW Γ) = _∈'_ {A} (N k , a) Γ

    -- domain
    dom : {A : Set} → t A → Key → Set
    dom {A} (TW Γ) k = dom' {A} Γ (N k)

    -- apartness, i.e. the opposite of dom
    _#_ : {A : Set} (k : Key) → (Γ : t A) → Set
    k # (TW Γ) = (N k) #' Γ

    -- maps f across the values of the delta dict
    dltmap : {A B : Set} → (A → B) → t A → t B
    dltmap f (TW Γ) = TW <| map (λ {(hx , ha) → (hx , f ha)}) Γ

    -- TODO theorems
    -- converts a list of key-value pairs into a delta dict, with earlier pairs in
    -- the list overriding bindings defined by later pairs
    list⇒dlt : {A : Set} → List (Key ∧ A) → t A
    list⇒dlt Γ = Γ |> map (λ where (k , v) → (N k , v)) |> list⇒dlt' |> TW

    -- converts a delta dict into a list of key-value pairs; the inverse of list⇒dlt
    dlt⇒list : {A : Set} → t A → List (Key ∧ A)
    dlt⇒list (TW Γ) = dlt⇒list' Γ |> map (λ where (n , v) → (K n , v))

    -- TODO theorems
    -- TODO we declare this here, but don't define it til later, due to a dependency.
    --      Ideally we should refactor so that the dependency is hidden in the private section
    -- converts a list of key-value pairs into a multi-delta-dict, where each value of
    -- the result is the sublist of values from the former that were mapped to by the
    -- corresponding key
    list⇒list-dlt : {A : Set} → List (Key ∧ A) → t (List A)

    -- union merge A B is the union of A and B,
    -- with (merge a b) being invoked to handle the mappings they have in common
    union : {A : Set} → (A → A → A) → t A → t A → t A
    union merge (TW Γ1) (TW Γ2) = TW <| union' merge Γ1 Γ2 0

    -- lookup function
    _⦃⦃_⦄⦄ : {A : Set} → t A → Key → Maybe A
    (TW Γ) ⦃⦃ k ⦄⦄ = Γ lkup (N k)

    ||_|| : {A : Set} → t A → Nat
    || TW Γ || = ∥ Γ ∥

    ---- core theorems ----

    -- The next two theorems show that lookup (_⦃⦃_⦄⦄) is consistent with membership (_∈_)
    lookup-cons-1 : {A : Set} {Γ : t A} {k : Key} {a : A} →
                     Γ ⦃⦃ k ⦄⦄ == Some a →
                     (k , a) ∈ Γ
    lookup-cons-1 {A} {TW Γ} {k} {a} h = lookup-cons-1' {Γ = Γ} {N k} h

    lookup-cons-2 : {A : Set} {Γ : t A} {k : Key} {a : A} →
                     (k , a) ∈ Γ →
                     Γ ⦃⦃ k ⦄⦄ == Some a
    lookup-cons-2 {A} {TW Γ} {k} {a} = lookup-cons-2' {A} {Γ} {N k} {a}

    -- membership (_∈_) respects insertion (_,,_)
    k,v∈Γ,,k,v : {A : Set} {Γ : t A} {k : Key} {a : A} →
                  (k , a) ∈ (Γ ,, (k , a))
    k,v∈Γ,,k,v {A} {Γ = TW Γ} {k} = x,v∈'Γ,,x,v {Γ = Γ} {N k}

    -- insertion can't generate spurious membership
    k∈Γ+→k∈Γ : {A : Set} {Γ : t A} {k k' : Key} {a a' : A} →
                 k ≠ k' →
                 (k , a) ∈ (Γ ,, (k' , a')) →
                 (k , a) ∈ Γ
    k∈Γ+→k∈Γ {A} {Γ = TW Γ} {k} {k'} {a} {a'} ne h
      = x∈Γ+→'x∈Γ {A} {Γ} {N k} {N k'} {a} {a'} (inj-cp ne) h

    -- insertion respects membership
    k∈Γ→k∈Γ+ : {A : Set} {Γ : t A} {k k' : Key} {a a' : A} →
                 k ≠ k' →
                 (k , a) ∈ Γ →
                 (k , a) ∈ (Γ ,, (k' , a'))
    k∈Γ→k∈Γ+ {A} {TW Γ} {k} {k'} {a} {a'} ne h
      = x∈Γ→'x∈Γ+ {A} {Γ} {N k} {N k'} {a} {a'} (inj-cp ne) h

    -- Decidability of membership
    -- This also packages up an appeal to delta dict membership into a form that
    -- lets us retain more information
    dltindirect : {A : Set} (Γ : t A) (k : Key) → dom Γ k ∨ k # Γ
    dltindirect {A} (TW Γ) k = dltindirect' {A} Γ (N k)

    -- delta dicts give at most one binding for each variable
    dltunicity : {A : Set} {Γ : t A} {k : Key} {a a' : A} →
                   (k , a) ∈ Γ →
                   (k , a') ∈ Γ →
                   a == a'
    dltunicity ah a'h
      with lookup-cons-2 ah | lookup-cons-2 a'h
    ... | ah' | a'h' = someinj (! ah' · a'h')

    -- nothing is in nil
    k#∅ : {A : Set} {k : Key} → _#_ {A} k ∅
    k#∅ (_ , ())

    -- meaning of the singleton
    ■-def : {A : Set} {k : Key} {a : A} → (■ (k , a)) == ∅ ,, (k , a)
    ■-def = refl

    -- extensionality of Delta dicts
    -- (i.e. if two dicts represent the same mapping from ids to values,
    -- then they are reflexively equal as judged by _==_)
    dlt-==-eqv : {A : Set} {Γ1 Γ2 : t A} →
                  ((k : Key) → Γ1 ⦃⦃ k ⦄⦄ == Γ2 ⦃⦃ k ⦄⦄) →
                  Γ1 == Γ2
    dlt-==-eqv {A} {TW Γ1} {TW Γ2} all-bindings-==
      = ap1 TW <| dlt-==-eqv' {A} {Γ1} {Γ2} eqv-nat
        where
        eqv-nat : (n : Nat) → (Γ1 lkup n) == (Γ2 lkup n)
        eqv-nat n
          with bij.surj bij n
        ... | k , surj
          with all-bindings-== k
        ... | eq rewrite surj = eq

    -- decidable equality of delta dicts
    dlt-==-dec : {A : Set}
                  (Γ1 Γ2 : t A) →
                  ((a1 a2 : A) → a1 == a2 ∨ a1 ≠ a2) →
                  Γ1 == Γ2 ∨ Γ1 ≠ Γ2
    dlt-==-dec {A} (TW Γ1) (TW Γ2) h = dlt-==-dec' {A} Γ1 Γ2 h
      where
      dlt-==-dec' : {A : Set}
                     (Γ1 Γ2 : rt A) →
                     ((a1 a2 : A) → a1 == a2 ∨ a1 ≠ a2) →
                     TW Γ1 == TW Γ2 ∨ TW Γ1 ≠ TW Γ2
      dlt-==-dec' [] [] _ = Inl refl
      dlt-==-dec' [] (_ :: _) _ = Inr (λ ())
      dlt-==-dec' (_ :: _) [] _ = Inr (λ ())
      dlt-==-dec' ((hx1 , ha1) :: t1) ((hx2 , ha2) :: t2) A==dec
        with natEQ hx1 hx2 | A==dec ha1 ha2 | dlt-==-dec' t1 t2 A==dec
      ... | Inl refl | Inl refl | Inl refl = Inl refl
      ... | Inl refl | Inl refl | Inr ne   = Inr λ where refl → ne refl
      ... | Inl refl | Inr ne   | _        = Inr λ where refl → ne refl
      ... | Inr ne   | _        | _        = Inr λ where refl → ne refl

    -- A useful way to destruct delta dict membership
    dlt-split : {A : Set} {Γ : t A} {k1 k2 : Key} {a1 a2 : A} →
                  (k1 , a1) ∈ (Γ ,, (k2 , a2)) →
                  (k1 ≠ k2 ∧ (k1 , a1) ∈ Γ) ∨ (k1 == k2 ∧ a1 == a2)
    dlt-split {Γ = Γ} {k1} {k2} {a1} {a2} n∈Γ+
      with natEQ (N k1) (N k2)
    ... | Inl eq
      rewrite bij.inj bij eq
        = Inr (refl , dltunicity n∈Γ+ (k,v∈Γ,,k,v {Γ = Γ}))
    ... | Inr ne = Inl (ne' , k∈Γ+→k∈Γ ne' n∈Γ+)
            where
            ne' = λ eq → abort (ne (ap1 N eq))

    -- remove a specific mapping from a delta dict
    dlt-delete : {A : Set} {Γ : t A} {k : Key} {a : A} →
                  (k , a) ∈ Γ →
                  Σ[ Γ⁻ ∈ t A ] (
                     Γ == Γ⁻ ,, (k , a) ∧
                     k # Γ⁻)
    dlt-delete {A} {TW Γ} {k} {a} h
      with dlt-delete' {A} {Γ} {N k} {a} h
    ... | _ , refl , # = _ , refl , #

    -- Allows the delta dicts to be destructed, by removing an arbitrary item
    dlt-elim : {A : Set} {Γ : t A} →
                Γ == ∅
                  ∨
                Σ[ k ∈ Key ] Σ[ a ∈ A ] Σ[ Γ' ∈ t A ]
                   (Γ == Γ' ,, (k , a) ∧ k # Γ')
    dlt-elim {A} {TW Γ}
      with dlt-elim' {A} {Γ}
    ... | Inl refl = Inl refl
    ... | Inr (n , _ , _ , refl , #)
      with bij.surj bij n
    ... | k , refl = Inr (_ , _ , _ , refl , #)

    -- When using dlt-elim or dlt-delete, this theorem is useful for establishing termination
    dlt-decreasing : {A : Set} {Γ : t A} {k : Key} {a : A} →
                      k # Γ →
                      || Γ ,, (k , a) || == 1+ || Γ ||
    dlt-decreasing {A} {TW Γ} {k} {a} n#Γ = dlt-decreasing' {A} {Γ} {N k} {a} n#Γ

    ---- contraction and exchange ----

    contraction : {A : Set} {Γ : t A} {k : Key} {a a' : A} →
                   Γ ,, (k , a') ,, (k , a) == Γ ,, (k , a)
    contraction {A} {TW Γ} {k} {a} {a'}
      = ap1 TW <| contraction' {Γ = Γ} {N k} {a} {a'}

    exchange : {A : Set} {Γ : t A} {k1 k2 : Key} {a1 a2 : A} →
                k1 ≠ k2 →
                Γ ,, (k1 , a1) ,, (k2 , a2) == Γ ,, (k2 , a2) ,, (k1 , a1)
    exchange {A} {TW Γ} {k1} {k2} {a1} {a2} k1≠k2
      = ap1 TW <| exchange' {Γ = Γ} <| inj-cp k1≠k2

    ---- union theorems ----

    x,a∈Γ1→x∉Γ2→x,a∈Γ1∪Γ2 : {A : Set} {m : A → A → A} {Γ1 Γ2 : t A} {k : Key} {a : A} →
                                (k , a) ∈ Γ1 →
                                k # Γ2 →
                                (k , a) ∈ union m Γ1 Γ2
    x,a∈Γ1→x∉Γ2→x,a∈Γ1∪Γ2 {Γ1 = TW Γ1} {TW Γ2} x∈Γ1 x#Γ2
      = lemma-union'-1 x∈Γ1 0≤n (tr (λ y → y #' Γ2) (! (n+m-n==m 0≤n)) x#Γ2)

    x∉Γ1→x,a∈Γ2→x,a∈Γ1∪Γ2 : {A : Set} {m : A → A → A} {Γ1 Γ2 : t A} {k : Key} {a : A} →
                                k # Γ1 →
                                (k , a) ∈ Γ2 →
                                (k , a) ∈ union m Γ1 Γ2
    x∉Γ1→x,a∈Γ2→x,a∈Γ1∪Γ2 {Γ1 = TW Γ1} {TW Γ2} {x} x#Γ1 x∈Γ2
      with lemma-union'-2 {n = Z} (tr (λ y → y #' Γ1) (! n+Z==n) x#Γ1) x∈Γ2
    ... | rslt
      rewrite n+Z==n {N x}
        = rslt

    x∈Γ1→x∈Γ2→x∈Γ1∪Γ2 : {A : Set} {m : A → A → A} {Γ1 Γ2 : t A} {k : Key} {a1 a2 : A} →
                                (k , a1) ∈ Γ1 →
                                (k , a2) ∈ Γ2 →
                                (k , m a1 a2) ∈ union m Γ1 Γ2
    x∈Γ1→x∈Γ2→x∈Γ1∪Γ2 {Γ1 = TW Γ1} {TW Γ2} {x} {a1} x∈Γ1 x∈Γ2
      with lemma-union'-3 (tr (λ y → (y , a1) ∈' Γ1) (! n+Z==n) x∈Γ1) x∈Γ2
    ... | rslt
      rewrite n+Z==n {N x}
        = rslt

    x∈Γ1∪Γ2→x∈Γ1∨x∈Γ2 : {A : Set} {m : A → A → A} {Γ1 Γ2 : t A} {k : Key} →
                            dom (union m Γ1 Γ2) k →
                            dom Γ1 k ∨ dom Γ2 k
    x∈Γ1∪Γ2→x∈Γ1∨x∈Γ2 {Γ1 = TW Γ1} {TW Γ2} x∈Γ1∪Γ2
      with lemma-union'-4 {n = Z} x∈Γ1∪Γ2
    x∈Γ1∪Γ2→x∈Γ1∨x∈Γ2 x∈Γ1∪Γ2 | Inl x'∈Γ1 = Inl x'∈Γ1
    x∈Γ1∪Γ2→x∈Γ1∨x∈Γ2 x∈Γ1∪Γ2 | Inr (_ , refl , x'∈Γ2) = Inr x'∈Γ2

    ---- dltmap theorem ----

    dltmap-func : {V1 V2 : Set} {d : t V1} {f : V1 → V2} {k : Key} {v : V1} →
                   dltmap f (d ,, (k , v)) == dltmap f d ,, (k , f v)
    dltmap-func {d = TW d} {f} {k} {v} = ap1 TW (dltmap-func' {d = d})

    ---- remaining definition, list⇒list-dlt ----

    list⇒list-dlt {A} l
      = foldl f ∅ (reverse l)
        where
          f : t (List A) → Key ∧ A → t (List A)
          f (TW Γ) (k , a)
            with dltindirect (TW Γ) k
          ... | Inl (as , k∈Γ)
            = TW Γ ,, (k , a :: as)
          ... | Inr k#Γ
            = TW Γ ,, (k , a :: [])

    ---- dlt <=> list theorems ----

    dlt⇒list-inversion : {A : Set} {Γ : t A} → list⇒dlt (dlt⇒list Γ) == Γ
    dlt⇒list-inversion {A} {TW Γ}
      = tr
           (λ y → TW (list⇒dlt' y) == TW Γ)
           (! (map^2 {f = λ { (k , v) → N k , v }}
                     {λ { (n , v) → K n , v }}
                     {dlt⇒list' Γ}))
           lem
        where
        lem' : ∀{l} → map {Nat ∧ A} ((λ { (k , v) → N k , v }) ⊙ (λ { (n , v) → K n , v })) l == l
        lem' {[]} = refl
        lem' {(n , v) :: t} rewrite lem' {t} | convert-bij2 {t = n} = refl
        lem : TW (list⇒dlt'
                   (map ((λ { (k , v) → N k , v }) ⊙ (λ { (n , v) → K n , v }))
                     (dlt⇒list' Γ)))
              == TW Γ
        lem rewrite lem' {dlt⇒list' Γ} = ap1 TW dlt⇒list-inversion'
