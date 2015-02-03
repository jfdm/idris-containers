-- ---------------------------------------------------------- [ TestRunner.idr ]
-- Module      : TestRunner
-- Description : Defines and runs test.x
--
-- Copyright   : (c) Jan de Muijnck-Hughes
-- License     : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
module TestRunner

import public Effects
import public Effect.StdIO
import public Effect.Exception

-- --------------------------------------------------- [ Type Sigs and Aliases ]
TestEffs : List EFFECT
TestEffs = [STDIO, EXCEPTION String]

Test : Type
Test = {TestEffs} Eff ()

-- ------------------------------------------------------------- [ Test Runner ]
tests : Nat -> List Test -> {TestEffs} Eff ()
tests _ Nil = do
    putStrLn "All tests passed"
    pure ()
tests n (t::ts) = do
    result <- t
    putStrLn $ "Test " ++ show n ++ " Passed"
    tests (S n) ts
-- --------------------------------------------------------------------- [ EOF ]
