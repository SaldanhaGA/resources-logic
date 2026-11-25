module Division where

import Test.QuickCheck
import System.Exit (exitFailure, exitSuccess)

import Lexer.Lexer (lexer)
import Parser.Parser (parseProgram)
import Syntax.Syntax
import Semantics.State
import Semantics.Interpreter

-- while (m <= r) do { r := r - m; q := q + 1 }
divisionSource :: String
divisionSource = unlines
  [ "program division"
  , "size n"
  , "inputs { n := n; m := m; r := n; q := 0 }"
  , "complexity O(n)"
  , "while m <= r do {"
  , "  r := r - m;"
  , "  q := q + 1"
  , "}"
  ]

parseOrFail :: String -> Program
parseOrFail src =
  case lexer src of
    Left lexErr -> error $ "Lexical error in the test: " ++ lexErr
    Right tokens ->
      case parseProgram "test" tokens of
        Left parseErr -> error $ "Parse error in the test: " ++ show parseErr
        Right prog    -> prog

-- r = n \land q = 0 \land m > 0 \land n >= 0
mkDivisionState :: Int -> Int -> State
mkDivisionState n m =
    updateVar "n" n
  $ updateVar "m" m
  $ updateVar "r" n
  $ updateVar "q" 0 emptyState

prop_divisionExactAndSound :: NonNegative Int -> Positive Int -> Property
prop_divisionExactAndSound (NonNegative n) (Positive m) =
  let prog       = parseOrFail divisionSource
      st0        = mkDivisionState n m
      globalCap  = 10 ^ (9 :: Int)
      exactCost  = 11 * (n `div` m) + 3
      leanBound  = 20 * n + 5
  in case runProgram unitModel globalCap st0 prog of
       Terminated cost stF ->
         let q = lookupVar "q" stF
             r = lookupVar "r" stF
             -- Pós-condição `post` do Lean: n = r + m * q \land r >= 0 \land r < m
             postHolds   = (n == r + m * q) && (r >= 0) && (r < m)
             exactMatch  = cost == exactCost
             withinLean  = cost <= leanBound
         in counterexample
              ("Failure to n=" ++ show n ++ ", m=" ++ show m ++
               " | cost=" ++ show cost ++ ", exact=" ++ show exactCost)
              (postHolds && exactMatch && withinLean)
       other ->
         counterexample ("Execution did not finish normally: " ++ show other) False

main :: IO ()
main = do
  putStrLn "Testing Successive Division (exact cost 11*floor(n/m)+3 and Lean bound 20n+5)..."
  r <- quickCheckResult prop_divisionExactAndSound

  if isSuccess r
    then do
      putStrLn "\nAnalytical tests passed successfully!"
      exitSuccess
    else do
      putStrLn "\nTest failed."
      exitFailure