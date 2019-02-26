module Main where

import Control.Monad.Except (runExcept)
import Debug.Trace (spy)
import Effect (Effect)
import Effect.Console (logShow)
import Foreign.Index (readProp)
import Foreign.Keys (keys)
import Prelude (Unit, unit, ($), (<$>), pure)
import Typedefs (deserialize0)

main :: Effect Unit
main = do
  let t0 = spy "val" $ deserialize0 "(+ 1 1)" "(left ())"
  pure unit
