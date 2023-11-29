{-# LANGUAGE DataKinds, GADTs, UnicodeSyntax #-}
module HOAS where

import Data.Kind (Type, Constraint)

type In :: Type -> [Type] -> Type
data In a as where
  Z :: In a (a : as)
  S :: In a as -> In a (b : as)

instance Show (In a as) where
  show Z = "Z"
  show (S k) = "S (" <> show k <> ")"

type Sub :: [Type] -> [Type] -> Type
data Sub xs ys where
  SN :: Sub '[] ys
  SD :: Sub xs ys -> Sub    xs  (a:ys)
  SK :: Sub xs ys -> Sub (a:xs) (a:ys)

infix 4 ≤
class xs ≤ ys where
  weaken  :: In a xs -> In a ys
  liftSub :: Sub zs xs -> Sub zs ys

instance {-# INCOHERENT #-} xs  ≤ xs where
  weaken  = id
  liftSub = id

instance {-# INCOHERENT #-} '[] ≤ xs where
  weaken x = case x of
  liftSub SN = SN

instance (xs ≤ ys) => (xs ≤ a:ys) where
  weaken  = S . weaken
  liftSub = SD . liftSub


type Sem :: Type
type Sem = [Type] -> (Type -> Type)

type Var :: Sem -> Sem
type Var sem env a = ∀ env'. env ≤ env' => sem env' a

type HOAS :: Sem -> Constraint

class HOAS sem where

  -- relative (monotone predicate?) functioral map?
  lam :: (∀ env'. env ≤ env' => Var sem env' a -> sem env' b) 
      -> sem env (a -> b)

  -- applicative application of sem env?
  app :: sem env (a -> b) 
      -> (sem env a -> sem env b)

  -- sem env should be (monotone predicate?) relative monad over Var env
  bind :: (∀ env'. env ≤ env' => Var sem env' a -> sem env' b) 
       -> (sem env a -> sem env b)

