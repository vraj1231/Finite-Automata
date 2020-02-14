import Data.List (foldl')
import Data.Char (isUpper)

-- CFG G = (Start, Follows)
type CFG = (Char, Char -> Char -> [String])

accept :: CFG -> [Char] -> Bool
accept (s,d) = elem [] . foldl' (\xs c -> concatMap (lq c) xs) [[s]] where
  lq a [] = []
  lq a (x:xs) | isUpper x = map (++ xs) $ d x a          -- nonterminal
              | otherwise = if a == x then [xs] else []  -- terminal

-- Balanced parentheses (not including the empty string)
-- original: S --> () | (S) | SS
-- in TNF:   S --> () | ()S | (S) | (S)S
bp :: CFG
bp = ('S', d) where
  d 'S' '(' = [")", ")S", "S)", "S)S"]
  d 'S' ')' = []

-- {a^i b^j c^{i+j} | i >= 0, j > 0}
-- original: S --> aSc | T
--           T --> bTc | bc
-- in TNF:   S --> aSc | bTc | bc
--           T --> bTc | bc
pl = ('S', d) where
  d 'S' 'a' = ["Sc"]  ;  d 'S' 'b' = ["Tc","c"]  ;  d 'S' 'c' = []
  d 'T' 'a' = []      ;  d 'T' 'b' = ["Tc","c"]  ;  d 'T' 'c' = []

g5 :: CFG
g5 = ('S', d) where
 d 'S' 'a' = ["bS","aS","b","aSbS","bSaS"] ;    
 d 'S' 'b' = ["bS","aS","a","aSbS","bSaS"] ; 

g6 :: CFG
g6 = ('S', d) where
 d 'S' 'a' = ["bS","bSa","aSba","a","b","aSb","aS",""]
 d 'S' 'b' = ["bS","bSa","aSba","a","b","aSb","aS",""]

g2 :: CFG
g2 = ('R', d) where
d 'R' 'a' = ["aF", "bF", "0F", "1F", "aF+R", "bF+R", "0F+R", "1F+R","a","b",""] ; 
d 'R' 'b' = ["aF", "bF", "0F", "1F", "aF+R", "bF+R", "0F+R", "1F+R","a","b",""] ;
    d 'F' 'a' = ["aS", "bS", "b",""] ; d 'F' 'b' = ["b","bFS", "aFS", "baFS", "aaFS", ""];
    d 'S' 'a' = ["aA", "bA", "", "abA", "bbA"] ; d 'S' 'b' = ["bS*", "aS*", "", "a", "b", "ba", "ab"] ;
    d 'A' 'a' = ["", "a", "b", "ba", "ab", "bAa", "aAa"] ;


{-
 
*Main> accept g5 "ab"
True
*Main> accept g5 "abab"
True
*Main> accept g5 "baab"
True
*Main> accept g5 "abba"
 -

True
*Main> accept g6 "ababbbaaa"
True
*Main> accept g6 "ababbbaabababababaaaaaaaa"
True
*Main> accept g6 "ababbbaabababababaaaaaaaaaaaaabbbbbbbbb"
True
-
-
-
-}
