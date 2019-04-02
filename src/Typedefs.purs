module Typedefs where

import Prelude (($), pure, bind, (==))
import Control.Monad.Error.Class (throwError)
import Data.Function.Uncurried (Fn2, runFn2)
import Data.Array (length)
import Foreign (F, Foreign, ForeignError(..))
import Foreign.Index (readProp)
import Foreign.Keys (keys)
import ForeignCtor (ctorName)

foreign import deserialize0Impl :: Fn2 String String Foreign

deserialize0 :: String -> String -> Foreign
deserialize0 = runFn2 deserialize0Impl

data TDTerm
  = TUnit
  | TLeft TDTerm
  | TRight TDTerm
  | TBoth TDTerm TDTerm
  | TInn TDTerm

termFromForeign :: Foreign -> F TDTerm
termFromForeign f = case ctorName f of 
  "Object" -> do k <- keys f
                 if length k == 1 
                   then pure TUnit 
                   else throwError $ pure $ ForeignError "unknown object"
  "$HC_2_0$Builtins__MkPair" -> do fst <- readProp "$1" f
                                   term1 <- termFromForeign fst
                                   snd <- readProp "$1" f
                                   term2 <- termFromForeign snd 
                                   pure $ TBoth term1 term2
  "$HC_1_0$Prelude__Either__Left" -> do fst <- readProp "$1" f
                                        term1 <- termFromForeign fst
                                        pure $ TLeft term1
  "$HC_1_1$Prelude__Either__Right" -> do fst <- readProp "$1" f
                                         term1 <- termFromForeign fst
                                         pure $ TRight term1
  _ -> throwError $ pure $ ForeignError "unknown term"  