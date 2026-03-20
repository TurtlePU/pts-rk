module MyLib (someFunc) where

data SUniverse scoped free = MkSUniverse
  { sFun, sTimes, sApp, sPair :: free -> free -> free
  , sAbs :: scoped -> free
  , sFst, sSnd :: free -> free
  }

data STerm scoped free where
  SFun, STimes, SApp, SPair :: free -> free -> STerm scoped free
  SAbs :: free -> scoped -> STerm scoped free
  SFst, SSnd :: free -> STerm scoped free

data DTerm scoped free where
  DPi, DSigma, DAbs :: free -> scoped -> DTerm scoped free
  DApp, DPair :: free -> free -> DTerm scoped free
  DFst, DSnd :: free -> DTerm scoped free

someFunc :: IO ()
someFunc = putStrLn "someFunc"
