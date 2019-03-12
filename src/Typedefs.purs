module Typedefs where

import Prelude (($), pure, bind, (==))
import Control.Monad.Error.Class (throwError)
import Data.Function.Uncurried (Fn2, runFn2)
import Data.Array (length)
import Foreign (F, Foreign, ForeignError(..))
import Foreign.Keys (keys)
import ForeignCtor (ctorName)

foreign import deserialize0Impl :: Fn2 String String Foreign

deserialize0 :: String -> String -> Foreign
deserialize0 = runFn2 deserialize0Impl

data TDTerm
  = TUnit
  | TLeft TDTerm
  | TRIght TDTerm
  | TBoth TDTerm TDTerm
  | TInn TDTerm

termFromForeign :: Foreign -> F TDTerm
termFromForeign f = case ctorName f of 
  "Object" -> do k <- keys f 
                 if length k == 1 then pure TUnit else throwError $ pure $ ForeignError "unknown object"
  _ -> throwError $ pure $ ForeignError "unknown term"  