{-# LANGUAGE DataKinds, UnicodeSyntax, GADTs, ScopedTypeVariables, AllowAmbiguousTypes #-}
module DB where

import HOAS

data DB env a where
  Var :: In a env -> DB env a
  App :: DB env (a -> b) -> (DB env a -> DB env b)
  Abs :: DB (a:env) b -> DB env (a -> b)
  Let :: DB env a -> DB (a:env) b -> DB env b

instance Show (DB env a) where
  show (Var x) = "Var (" <> show x <> ")"
  show (App f x) = "App (" <> show f <> ") (" <> show x <> ")"
  show (Abs f) = "Abs (" <> show f <> ")"
  show (Let x f) = "Let (" <> show x <> ") (" <> show f <> ")"

var :: ∀ a env. ∀ env'. (a:env) ≤ env' => DB env' a
var = Var (weaken @(a:env) Z)

instance HOAS DB where
  lam :: ∀ env a b. (∀ env'. env ≤ env' => Var DB env' a -> DB env' b)
      -> DB env (a -> b)

  lam f = Abs (f (var @a @env))
  app = App

  bind :: ∀ env a b. (∀ env'. env ≤ env' => Var DB env' a -> DB env' b) 
       -> (DB env a -> DB env b)
  bind f x = Let x (f (var @a @env))
