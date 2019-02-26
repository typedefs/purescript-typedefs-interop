module Typedefs where

import Data.Function.Uncurried (Fn2, runFn2)
import Foreign (Foreign)

--foreign import parseTDefImpl :: String -> Foreign

foreign import deserialize0Impl :: Fn2 String String Foreign

deserialize0 :: String -> String -> Foreign
deserialize0 = runFn2 deserialize0Impl
