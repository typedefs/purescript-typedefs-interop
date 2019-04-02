module Main where

import Prelude (Unit, bind, pure, unit, ($))
--import Prelude (Unit, unit, ($), (<$>), (<>), (>>=), show, bind, pure, const, discard)
--import Data.Either (Either)
import Control.Monad.Except (runExcept)
import Debug.Trace (spy)
import Effect (Effect)
--import Effect.Console (log, logShow)
import Foreign.Index (readProp)
import Typedefs (deserialize0, termFromForeign)

main :: Effect Unit
main = do
  let full = spy "parsed" $ deserialize0 "(+ 1 1)" "(right ())"
  let ee = spy "run" $ 
           runExcept $ do dpair <- readProp "$1" full 
                          term <- spy "term" $ readProp "$2" dpair
                          termFromForeign term
  pure unit
