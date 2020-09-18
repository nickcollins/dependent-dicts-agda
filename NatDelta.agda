open import Prelude
open import Nat
open import Bij

module NatDelta where

  instance
    NatBij : bij Nat Nat
    NatBij = record {
      convert = λ n → n;
      inj     = λ n → n;
      surj    = λ n → n , refl}

  open import Delta Nat {{NatBij}}

  nat-dd = dd
