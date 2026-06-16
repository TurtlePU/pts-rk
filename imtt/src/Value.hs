module Value where

import Core (Projection)

newtype Level = MkLevel { levelInt :: Int }

data Value
  = VPi Value (Value -> Value)
  | VAbs Value (Value -> Value)
  | VApp Level [Either Projection Value]
  | VSig Value (Value -> Value)
  | VPair Value Value
  | VUniverse
