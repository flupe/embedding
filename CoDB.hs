{-# LANGUAGE DataKinds, UnicodeSyntax, GADTs, ScopedTypeVariables, AllowAmbiguousTypes #-}

module CoDB where

import Data.Kind (Type)
import HOAS

data Split xs ys zs where
  D :: Split '[] '[] '[]
  L :: Split xs ys zs -> Split (a:xs)    ys  (a:zs)
  R :: Split xs ys zs -> Split    xs  (a:ys) (a:zs)
  B :: Split xs ys zs -> Split (a:xs) (a:ys) (a:zs)

instance Show (Split xs ys zs) where
  show D     = "D"
  show (L s) = "L" <> show s
  show (R s) = "R" <> show s
  show (B s) = "B" <> show s

data Union xs ys env = 
  forall env'. Union 
    { split :: Split xs ys env'
    , subst :: Sub env' env
    }

union :: Sub xs env -> Sub ys env -> Union xs ys env
union SN     SN     = Union D SN
union SN     (SK b) | Union m s <- union SN b = Union (R m) (SK s)
union SN     (SD b) | Union m s <- union SN b = Union m     (SD s)
union (SK a) SN     | Union m s <- union a SN = Union (L m) (SK s)
union (SK a) (SK b) | Union m s <- union a b  = Union (B m) (SK s)
union (SK a) (SD b) | Union m s <- union a b  = Union (L m) (SK s)
union (SD a) SN     | Union m s <- union a SN = Union m     (SD s)
union (SD a) (SK b) | Union m s <- union a b  = Union (R m) (SK s)
union (SD a) (SD b) | Union m s <- union a b  = Union m     (SD s)

data Binding a env env' where
  DoBind   :: Binding a env (a : env)
  DontBind :: Binding a env env

instance Show (Binding a env env') where
  show DoBind   = "DoBind"
  show DontBind = "DontBind"

data CoDB env a where
  CoVar :: CoDB '[a] a
  CoApp :: Split xs ys env -> CoDB xs (a -> b) -> CoDB ys a -> CoDB env b
  CoAbs :: Binding a env env' -> CoDB env' b -> CoDB env (a -> b)
  CoLet :: Split xs ys env -> CoDB xs a -> Binding a ys ys' -> CoDB ys' b -> CoDB env b

instance Show (CoDB env a) where
  show CoVar = "Var"
  show (CoApp s x y) = "App #" <> show s <> " (" <> show x <> ") (" <> show y <> ")"
  show (CoAbs b f) = "Abs " <> show b <> " (" <> show f <> ")"
  show (CoLet s x b f) = "Let " <> show b <> " #" <> show s <> " (" <> show x <> ") (" <> show f <> ")"

data CoDBTerm env a =
  forall env'. CoDBTerm 
    { ctx :: Sub env' env
    , trm :: CoDB env' a
    }

instance Show (CoDBTerm env a) where show (CoDBTerm _ t) = show t

covar :: forall env a. Var CoDBTerm (a:env) a
covar = CoDBTerm (liftSub @(a:env) (SK SN)) CoVar

instance HOAS CoDBTerm where
  lam :: ∀ env a b. (∀ env'. env ≤ env' => Var CoDBTerm env' a -> CoDBTerm env' b)
      -> CoDBTerm env (a -> b)
  lam f =
    case f @(a:env) (covar @env @a) of
      CoDBTerm SN     t -> CoDBTerm SN (CoAbs DontBind t)
      CoDBTerm (SD k) t -> CoDBTerm k  (CoAbs DontBind t)
      CoDBTerm (SK k) t -> CoDBTerm k  (CoAbs DoBind   t)

  app (CoDBTerm xs f) (CoDBTerm ys x)
    | Union usplit usub <- xs `union` ys
    = CoDBTerm usub (CoApp usplit f x)

  bind :: ∀ env a b. (∀ env'. env ≤ env' => Var CoDBTerm env' a -> CoDBTerm env' b) 
       -> (CoDBTerm env a -> CoDBTerm env b)
  bind f (CoDBTerm ctx x) =
    case f @(a:env) (covar @env @a) of
      CoDBTerm SN     t | Union m s <- union ctx SN -> CoDBTerm s (CoLet m x DontBind t)
      CoDBTerm (SD k) t | Union m s <- union ctx k  -> CoDBTerm s (CoLet m x DontBind t)
      CoDBTerm (SK k) t | Union m s <- union ctx k  -> CoDBTerm s (CoLet m x DoBind   t)
