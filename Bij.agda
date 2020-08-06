open import Prelude

module Bij where
  record bij (From To : Set) : Set where
    field
      convert : From → To
      inj     : ∀{f1 f2} → convert f1 == convert f2 → f1 == f2
      surj    : (t : To) → Σ[ f ∈ From ] (convert f == t)

  convert-inv : ∀{F T : Set} {{bijFT : bij F T}} → T → F
  convert-inv {{bijFT}} t with bij.surj bijFT t
  ... | f , _ = f

  convert-inv-inj : ∀{F T : Set} {{bijFT : bij F T}} {t1 t2 : T} →
                      convert-inv {{bijFT}} t1 == convert-inv {{bijFT}} t2 →
                      t1 == t2
  convert-inv-inj ⦃ bijFT = bijFT ⦄ {t1} {t2} eq
    with bij.surj bijFT t1 | bij.surj bijFT t2
  ... | _ , p1 | _ , p2
    rewrite eq = ! p1 · p2

  convert-inv-surj : ∀{F T : Set} {{bijFT : bij F T}} (f : F) →
                       Σ[ t ∈ T ] (convert-inv {{bijFT}} t == f)
  convert-inv-surj ⦃ bijFT = bijFT ⦄ f with expr-eq (λ _ → bij.convert bijFT f)
  ... | t , teq with expr-eq (λ _ → bij.surj bijFT t)
  ... | (_ , seq) , refl = _ , bij.inj bijFT (seq · teq)

  convert-bij1 : ∀{F T : Set} {{bijFT : bij F T}} {f : F} →
                   convert-inv (bij.convert bijFT f) == f
  convert-bij1 ⦃ bijFT = bijFT ⦄ {f} with expr-eq (λ _ → convert-inv-surj f)
  ... | (_ , eq) , refl = eq

  convert-bij2 : ∀{F T : Set} {{bijFT : bij F T}} {t : T} →
                   bij.convert bijFT (convert-inv t) == t
  convert-bij2 ⦃ bijFT = bijFT ⦄ {t} with expr-eq (λ _ → bij.surj bijFT t)
  ... | (_ , eq) , refl = eq
