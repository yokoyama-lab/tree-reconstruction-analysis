-- Exhaustive enumeration of the comparison counts (exact rational averages).
-- A binary tree on n nodes <-> a Lukasiewicz codeword (x_1..x_{n-1}) with
--   x_i in [0, i - s_{i-1}],  s_i = x_1+...+x_i <= i.
-- For each tree: S = sum x_i (total pops), P2 = #{i : x_i >= 2} (double pops),
--   A_N = S + P2 + (n+2)   (improved algorithm),
--   A_M = S + 2n - 1       (Makinen's algorithm).
-- Lazy generation streams all C_n codewords without storing them; Integer/
-- Rational give exact arithmetic. Run: runghc average.hs
import Data.Ratio (Rational, (%))

-- all codewords of length n-1, generated lazily
codewords :: Int -> [[Int]]
codewords n = gen 0 1
  where gen s i | i == n    = [[]]
                | otherwise = [ x:ys | x <- [0 .. i - s], ys <- gen (s + x) (i + 1) ]

avg :: [Int] -> Rational
avg zs = sum (map toInteger zs) % toInteger (length zs)

main :: IO ()
main = mapM_ report [1 .. 14]
  where
    report n =
      let cs = codewords n
          aN = [ sum xs + length (filter (>= 2) xs) + (n + 2) | xs <- cs ]
          aM = [ sum xs + 2*n - 1                              | xs <- cs ]
      in putStrLn $ show n ++ ": E[A_N]=" ++ show (avg aN)
                          ++ "  E[A_M]=" ++ show (avg aM)
