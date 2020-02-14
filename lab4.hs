-- CSci 119, Lab 4

import Data.List (sort, stripPrefix) -- for your solution to Lab 3
import Control.Monad (replicateM)    -- for strings function at the end


-- Normalize a list: sort and remove duplicates
norm :: Ord a => [a] -> [a]
norm xs = rad $ sort xs where
  rad :: Eq a => [a] -> [a]  -- Remove adjacent duplicates
  rad [] = []
  rad [x] = [x]
  rad (x:ys@(y:zs)) | x == y = rad ys
                    | otherwise = x : rad ys

-- Length-Ordered Lists over "character type" a (aka "strings")
-- Invariant: In LOL n xs, n == length xs
data LOL a = LOL Int [a] deriving (Eq,Ord)

instance Show a => Show (LOL a) where
  show (LOL n xs) = show xs

-- Empty list (epsilon)
eps :: LOL a
eps = LOL 0 []

-- Smart constructor for LOL a, establishes invariant
lol :: [a] -> LOL a
lol xs = LOL (length xs) xs

-- Normalized lists of LOLs (aka "languages")
-- Invariant: xs :: Lang a implies xs is sorted with no duplicates
type Lang a = [LOL a]

-- Smart constructor for (finite) languages
lang :: Ord a => [[a]] -> Lang a
lang xs = norm $ map lol xs

---- Regular expressions, along with input and output
data RegExp = Empty                -- Empty language
            | Let Char             -- Single letter language
            | Union RegExp RegExp  -- Union
            | Cat RegExp RegExp    -- Concatenation
            | Star RegExp          -- Kleene star
            deriving (Show, Eq)

-- Compact display form for RegExp
newtype Compact = Compact RegExp

instance (Show Compact) where    -- use precedence to minimize parentheses
  showsPrec d (Compact r) = sp d r where
    sp d Empty         = showString "@"
    sp d (Let c)       = showString [c]
    sp d (Union r1 r2) = showParen (d > 6) $  -- prec(Union) = 6
                         sp 6 r1 .
                         showString "+" .
                         sp 6 r2
    sp d (Cat r1 r2)   = showParen (d > 7) $  -- prec(Cat) = 7
                         sp 7 r1 .
                         sp 7 r2
    sp d (Star r1)     = sp 9 r1 .     -- prec(Star) = 8
                         showString "*"

-- Quick and dirty postfix RegExp parser, gives non-exaustive match on error
toRE :: String -> RegExp
toRE w = go w [] where
  go [] [r]              = r
  go ('+':xs) (r2:r1:rs) = go xs (Union r1 r2:rs)
  go ('.':xs) (r2:r1:rs) = go xs (Cat r1 r2:rs)
  go ('*':xs) (r:rs)     = go xs (Star r:rs)
  go ('@':xs) rs         = go xs (Empty:rs)
  go (x:xs) rs           = go xs (Let x:rs)


---------------- Your solution to Lab 3 ----------------

-- Include part of your solution to Lab 3 here for testing purposes.
-- After a few days, I will release my solution for you to use. Don't
-- duplicate the code just given above.


---------------- Part 1 ----------------

-- Membership for languages that satisfy the invariant (sorted, no duplicates),
-- even if they are infinite. Only look at the contents of a string when it is
-- necessary to do so, and stop as soon as you know the answer.
memb :: Ord a => LOL a -> Lang a -> Bool
memb (LOL a b) [] = False
memb (LOL a b) ((LOL c d):xs) | a < c = False
                              | a > c = memb (LOL a b) xs
							  | (a == c) && (b==d) = True
							  | otherwise = memb (LOL a b) xs


-- Implement the seven recursive predications/operations on RegExp given in
-- Section 3.3 of the notes; call them empty, unitary, byp, inf, rever, lq,
-- and nep. Each should begin with a type declaration. Include several tests
-- for each function.
empty :: RegExp -> Bool
empty Empty = True
empty (Let _) = False
empty (Union r1 r2) = if (r1 == Empty && r2 == Empty) then True else False
empty (Cat r1 r2) = if(r1 == Empty || r2 == Empty) then True else False
empty (Star r1) = if (r1 == Empty) then True else False 


unitarity :: RegExp -> Bool
unitarity (Empty) = False
unitarity (Let r) = False 
unitarity (Union r1 r2) =  if ((unitarity r1 && unitarity r2) || (empty r1 && unitarity r2) || (unitarity r1 && empty r2)) then True else False
unitarity (Cat r1 r2) = if ((unitarity r1 && unitarity r2)) then True else False
unitarity (Star r1) = if ((empty r1 || unitarity r1)) then True else False   




bypassabiltiy :: RegExp -> Bool
bypassabiltiy (Empty) = False
bypassabiltiy (Let a) = False
bypassabiltiy (Union r1 r2) = if (bypassabiltiy r1 || bypassabiltiy r2) then True else False
bypassabiltiy (Cat r1 r2) = if (bypassabiltiy r1 || bypassabiltiy r2) then True else False
bypassabiltiy (Star r) = True





infiniteness :: RegExp -> Bool
infiniteness (Empty) = False
infiniteness (Let a) = False
infiniteness (Union r1 r2) = if(infiniteness r1 || infiniteness r2) then True else False
infiniteness (Cat r1 r2) = if((infiniteness r1 && not (empty r2))||(infiniteness r2 && not (empty r1))) then True else False
infiniteness (Star r) = if((not (empty r)) && (not (unitarity r))) then True else False



reversal :: RegExp -> RegExp
reversal (Empty) = Empty
reversal (Let a) = Let a
reversal (Union r1 r2) = (Union (reversal r1) (reversal r2))
reversal (Cat r1 r2) = (Cat (reversal r1) (reversal r2))
reversal (Star r) = (Star (reversal r))



leftquotient :: Char -> RegExp -> RegExp
leftquotient c (Empty) = (Empty)
leftquotient a1 (Let a2)
 | a1 == a2 = (Star (Empty))
 | otherwise = (Empty)
leftquotient a (Union r1 r2) = (Union (leftquotient a r1) (leftquotient a r2))
leftquotient a (Cat r1 r2)
 | bypassabiltiy r1 = (Union (Cat (leftquotient a r1) r2) (leftquotient a r2))
 | otherwise = (Cat (leftquotient a r1) r2)
leftquotient a (Star r) = (Cat (leftquotient a r) (Star r)) 


nep :: RegExp -> RegExp
nep Empty = Empty
nep (Let a) = (Let a)
nep (Union r1 r2) = (Union (nep r1) (nep r2))
nep (Cat r1 r2) | bypassabiltiy r1 = (Union (Cat (nep r1) r2) (nep r2))
                | otherwise = (Cat (nep r1) r2)
nep (Star r1) = (Cat (nep r1) (Star r1))

--test-case 
----empty (Let 'r')
----empty (Union (Empty) (Empty))
-----empty (Union (Let 'a') (Let 'b'))
-----empty (Cat (Let 'a') (Let 'b'))
----empty (Star (Let 'r'))




-----unitarity (Let 'r')
-----unitarity (Union (Let 'a') (Let 'b'))
-----unitarity (Cat (Let 'a') (Let 'b'))
------unitarity (Star (Let 'r'))

--bypassabiltiy (Empty)
--bypassabiltiy (Letter 'd')
--bypassabiltiy (Union (Letter 'd') (Letter 'c'))
--bypassabiltiy (Union (Letter 'd') (Empty))


--infiniteness (Cat (Empty) (Empty))
--infiniteness (Star (Empty))
--infiniteness (Star (Letter 'a'))


--reversal (Cat (Empty) (Letter 'c'))
--reversal (Cat (Empty) (Empty))
--reversal (Star (Empty))
--reversal (Star (Letter 'a'))

-----leftquotient 'r' (Empty)
-----leftquotient 'r' (Let 'r')
-----leftquotient 'r' (Union (Let 'r') (Let s'))
-----leftquotient 'r' (Cat (Let 'r') (Let 's'))
-----leftquotient 'r' (Star (Let 'r'))

--nep (Cat (Empty) (Empty))
--nep (Star (Empty))
--nep (Star (Letter 'a'))

---------------- Part 2 ----------------

-- Implement the two matching algorithms given in Section 3.4 of the notes.
-- Call them match1 and match2. Start by implementing splits:

-- splits xs = list of all possible splits of xs, in order. For example,
-- splits "abc" = [("","abc"), ("a","bc"), ("ab","c"), ("abc","")]
splits :: [a] -> [([a],[a])]
splits (x:xs) = [((take x xs), (drop x xs)) | x <- [0..(length xs)] ]  


match1 :: RegExp -> String -> Bool
match1 (Empty) w = False
match1 (Let a) " " = False
match1 (Let a) (b:w) = a == b && w == []
match1 (Union r1 r2) w = (match1 r1 w) || (match1 r2 w)
match1 (Cat r1 r2) w = or [ (match1 r1 w1) && (match1 r2 w2) | (w1, w2) <- (splits w) ]
match1 (Star r) w = w == " " || or [ w1 /= "" && (match1 r w1) && (match1 (Star r) w2) | (w1, w2) <- (splits w) ]


match2 :: RegExp -> String -> Bool
match2 r w = match21 r w c
    where
    match21 :: [RegExp] -> String -> Bool -> Bool
    match21 [] w c = w == " "
    match21 ((Empty):rs) w c = False
    match21 ((Let a):rs) " " c = False
    match21 ((Let a):rs) (b:w) c = (a:w) == (b:w) && (match21 rs w False)
    match21 ((Union r1 r2):rs) w c = (match21 (r1:rs) w c) || (match21 (r2:rs) w c)
    match21 ((Cat r1 r2):rs) w c = (match21 (r1:r2:rs) w c)
                            || ( c == True && bypassabiltiy(r1) && (match21 (r2:rs) w True) )
    match2' ((Star r):rs) w c = (c == False && (match21 rs w False)) || (match21 (r:rs) w True)


--Test cases
--match2 [abs] "a" True
--match2 [sasa] "b" True
--match2 [enxxa] "c" True
--match2 [bbq1] "a" True

--match2 [Union tsla ddla] "a" True
--match2 [Union qqlq Empty] "s" True
--match2 [Union Empty Empty] "s" True
--match2 [Union Empty qqlqa] "c" True


--match2 [Star Empty] "b" True
--match2 [Star ttla] "b" True


-- Some regular expressions for testing. Also, test them on other solutions
-- to the exercises of Section 3.2 (as many as you can get). 

sigma = ['a', 'b']                -- Alphabet used in all examples below

ab   = toRE "aa.bb.+*"            -- every letter is duplicated
ttla = toRE "ab+*a.ab+.ab+."      -- third to last letter is a
ena  = toRE "b*a.b*.a.*b*."       -- even number of a's
bb1  = toRE "aba.+*b.b.aab.+*."   -- contains bb exactly once


-- For your tests, you may also find the following helpful. For example,
-- you can generate all strings of length 10 (or 20) or less and then test
-- to see whether match1 r w == memb (lol w) (lang_of r) for each such w.

-- All strings on sigma of length <= n (useful for testing)
strings :: Int -> [String]
strings n = concat $ [replicateM i sigma | i <- [0..n]]

