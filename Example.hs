{-# LANGUAGE BlockArguments, DataKinds #-}
module Example where

import HOAS
import DB
import CoDB

ex1 :: HOAS sem => sem env (Bool -> Bool)
ex1 =
  bind (\z ->
    app (lam \x -> app x z)
        (lam \y -> z)) (lam \z -> z)

main :: IO ()
main = do
  print (ex1 :: DB       '[] (Bool -> Bool))
  print (ex1 :: CoDBTerm '[] (Bool -> Bool))
