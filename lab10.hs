--Lab 10
import Data.List
import Data.Array
import Control.Monad (replicateM)  -- for strings function below
-- Fixed alphabet, but everything below should work for any sigma!
sigma :: [Char]
sigma = "ab"

-- Finite state machines, now indexed by the type of their states
-- M = (states, start, finals, transitions)  
type FSM a = ([a], a, [a], a -> Char -> a)


---------------- Given functions ----------------

-- All strings on sigma of length <= n (useful for testing)
strings :: Int -> [String]
strings n = concat $ [replicateM i sigma | i <- [0..n]]

-- Normalize a list: sort and remove duplicates
norm :: Ord a => [a] -> [a]
norm xs = rad $ sort xs where
  rad :: Eq a => [a] -> [a]  -- Remove adjacent duplicates
  rad [] = []
  rad [x] = [x]
  rad (x:ys@(y:zs)) | x == y = rad ys
                    | otherwise = x : rad ys

-- Cartesian product (preserves normalization)
(><) :: [a] -> [b] -> [(a,b)]
xs >< ys = [(x,y) | x <- xs, y <- ys]

-- Powerset  (preserves normalization)
power :: [a] -> [[a]]
power [] = [[]]
power (x:xs) = let ys = power xs
               in [] : map (x:) ys ++ tail ys

-- Check whether two lists overlap
overlap :: Eq a => [a] -> [a] -> Bool
overlap [] ys = False
overlap (x:xs) ys = elem x ys || overlap xs ys

-- Complete the FSM constructions for the regular expression operators
-- and test your functions adquately

-- Machine that accepts the empty language
emptyFSM :: FSM Int
emptyFSM = ([0], 0, [] , d) where
  d 0 _ = 0

-- Machine that accepts the language {"a"} where a in sigma
letterFSM :: Char -> FSM Int
letterFSM a = ([0..2], 0, [1], d) where
  d q x = if (q == 0 && x == a) then 1 else 2

-- Machine that accepts the union of the languages accepted by m1 and m2
unionFSM :: (Eq a, Eq b) => FSM a -> FSM b -> FSM (a, b)
unionFSM (qs1, s1, fs1, d1) (qs2, s2, fs2, d2) = (qs, s, fs, d) where
  qs = (qs1 >< qs2)
  s  = (s1,s2)
  fs = [(q1,q2) | (q1, q2) <- qs, q1 `elem` fs1 || q2 `elem` fs2]
  d (q1,q2) a = ((d1 q1 a), (d2 q2 a))  

-- Machine that accepts the concatenation of the languages accepted by m1 and m2

catFSM :: (Eq a, Ord b) => FSM a -> FSM b -> FSM (a, [b])
catFSM (qs1, s1, fs1, d1) (qs2, s2, fs2, d2) = (qs, s, fs, d) where
  x = power qs2
  correctQX q x = norm (if q `elem` fs1 then union x [s2] else x)
  qs = [(q, (correctQX q x)) | q <- qs1, x <- power qs2]
  s  = (s1, [s2 | s1 `elem` fs1])
  fs = [(q1,x) | (q1,x) <- qs, overlap x fs2]
  d (q,x) a = (q', (correctQX q' (dhat (x,a)))) where
    q' = d1 q a
    dhat (x,a) = norm [d2 q2 a | q2 <- x]

-- Machine that accepts the Kleene star of the language accepted by m1
starFSM :: Ord a => FSM a -> FSM [a]
starFSM (qs1, s1, fs1, d1) = (qs, s, fs, d) where
  x = power qs1
  correctX x = norm (if overlap x fs1 then union x [s1] else x)
  qs = norm [(correctX x) | x <- power qs1]
  s  = []
  fs = union [[]] [x | x <- qs, overlap x fs1]
  d [] a = norm $ [s1 | q `elem` fs1] ++ [q] where q =  d1 s1 a
  d x a = norm $ [s1] ++ dhat((correctX x),a) where
    dhat (x, a) = norm [d1 q a | q <- x]

-- delta* construction
star :: (a -> Char -> a) -> (a -> [Char] -> a)
star = foldl'

-- Unary set closure (where "set" = normalized list)
-- uclosure xs g == smallest set containing xs and closed under g
uclosure :: Ord a => [a] -> (a -> [a]) -> [a]
uclosure xs g = sort $ stable $ iterate close (xs, []) where
  stable ((fr,xs):rest) = if null fr then xs else stable rest
  close (fr, xs) = (fr', xs') where
    xs' = fr ++ xs
    fr' = norm $ filter (`notElem` xs') $ concatMap g fr

-- reachable m == the part of m that is reachable from the start state
reachable :: Ord a => FSM a -> FSM a
reachable m@(qs, s, fs, d) = (qs', s, fs', d) where
  qs' = uclosure [s] (\q -> map (d q) sigma)
  fs' = filter (`elem` fs) qs'

-- Change the states of an FSM from an equality type to Int 
-- and use an array lookup for the transition function
intify :: Eq a => FSM a -> FSM Int
intify (qs, s, fs, d) = ([0..n-1], s', fs', d') where
  n = length qs
  m = length sigma
  s'  = ind qs s
  fs' = map (ind qs) fs
  arr = listArray ((0,0), (n-1,m-1)) [ind qs (d q a) | q <- qs, a <- sigma]
  d' q a = arr ! (q, ind sigma a)
  ind (q':qs) q = if q == q' then 0 else 1 + ind qs q

---- Regular expressions, along with output and input
data RegExp = Empty
             | Let Char
             | Union RegExp RegExp
             | Cat RegExp RegExp
             | Star RegExp
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

-- Quick and dirty postfix regex parser, gives non-exaustive match on error
toRE :: String -> RegExp
toRE w = toRE' w [] where
  toRE' [] [r] = r
  toRE' ('+':xs) (r2:r1:rs) = toRE' xs (Union r1 r2:rs)
  toRE' ('.':xs) (r2:r1:rs) = toRE' xs (Cat r1 r2:rs)
  toRE' ('*':xs) (r:rs) = toRE' xs (Star r:rs)
  toRE' ('@':xs) rs = toRE' xs (Empty:rs)
  toRE' (x:xs) rs = toRE' xs (Let x:rs)

-- All functions below assume that the machine is correct
delta_star :: Eq a => FSM a -> a -> [Char] -> a
delta_star (_, _, _, d) = foldl d

accept1 :: Eq a => FSM a -> [Char] -> Bool
accept1 m@(_, s, fs, _) w = elem (delta_star m s w) fs

accept2_aux :: Eq a => FSM a -> a -> [Char] -> Bool
accept2_aux m@(_, _, fs, _) q [] = elem q fs
accept2_aux m@(_, _, _, d) q (a:w) = accept2_aux m (d q a) w

accept2 :: Eq a => FSM a -> [Char] -> Bool
accept2 m@(_, s, _, _) w = accept2_aux m s w

type Trans a = a -> Char -> [a]
type NFSM a = ([a], [a], [a], Trans a)

-- nap_hat d qs a == normalized list of all transitions possible from qs on a
--nap_hat d qs a = norm(concat[d q' a | q' <- qs])
nap_hat :: Ord a => Trans a -> [a] -> Char -> [a]
nap_hat d qs a = norm (concat [d q' a | q' <- qs])

-- nap_hat_star d qs w == normalized list of transitions possible from qs on w
nap_hat_star :: Ord a => Trans a -> [a] -> [Char] -> [a]
nap_hat_star = foldl'.nap_hat

-- nacc m w == m accepd the string w
nacc :: Ord a => NFSM a -> [Char] -> Bool
nacc (qs, ss, fs, d) w = overlap (nap_hat_star d ss w) fs

-- Easy conversion from FSM to NFSM (given)
fsm_to_nfsm :: Eq a => FSM a -> NFSM a
fsm_to_nfsm (qs1, s1, fs1, d1) = (qs, s, fs, d) where 
  qs = qs1
  s = [s1] 
  fs = fs1
  d q a = [d1 q a]
  
-- Conversion from NFSM to FSM by the "subset construction"  
nfsm_to_fsm :: Ord a => NFSM a -> FSM [a]
nfsm_to_fsm (qs1, ss1, fs1, d1) = (qs, s, fs, d) where
  qs = power(qs1)
  s  = ss1
  fs = [x | x <- qs, x `overlap` fs1] 
  d q a = nap_hat d1 q a


-- Testing machine
oddbs :: FSM Int
oddbs = ([0,1], 0, [1], f) where
  f 0 'b' = 1
  f 1 'b' = 0
  f q c = q

end_ab :: FSM Int
end_ab = ([0..2],0,[2],f) where
    f 0 'a' = 1
    f 1 'b' = 2
    f 2 'a' = 1
    f 1 'a' = 1
    f q c = 0

--exactly 1 a
exactly_a :: FSM Int
exactly_a = ([0,1,2], 0, [1], f) where
  f 0 'a' = 1
  f 0 'b' = 2
  f _ _ = 2

exactly_b :: FSM Int
exactly_b = ([0,1,2], 0, [1], f) where
  f 0 'b' = 1
  f 0 'a' = 2
  f _ _ = 2

-- Boolean binary operation on FSMs. Examples:
-- binopFSM (||) m1 m2 computes union machine
-- binopFSM (&&) m1 m2 computes intersection machine
binopFSM :: (Eq a, Eq b) => (Bool -> Bool -> Bool) -> FSM a -> FSM b -> FSM (a,b)
binopFSM op (qs1, s1, fs1, d1) (qs2, s2, fs2, d2) = (qs, s, fs, d) where
  qs = qs1 >< qs2
  s  = (s1, s2)
  fs = [(q1, q2) | q1 <- qs1, q2 <- qs2, op (elem q1 fs1) (elem q2 fs2)]
  d (qs1, qs2) a = (d1 qs1 a, d2 qs2 a)

-- Reverse FSM to a NFSM. Output machine accepts reverse of language of input machine.
reverseFSM :: Eq a => FSM a -> NFSM a
reverseFSM (qs1, ss1, fs1, d1) = (qs, s, fs, d) where 
    qs = qs1
    s = fs1
    fs = [ss1]
    d q a = [q' | q' <- qs1, q == (d1 q' a)]

-- Reachable states of a NFSM (similar to reachable but on NFSMs)
nreachable :: Ord a => NFSM a -> [a]
nreachable (qs, s, fs, d) = (uclosure s f) where 
  f q = norm $ concat (map (d q) sigma)

--rep :: Ord a => a -> [(a,a)] -> [a]
--rep q eq = [minimum [q2|(q1,q2) <- eq, q1 == q]]

-- Minimize a FSM. Put all of the above together to compute the minimum machine for m
minimize :: Ord a => FSM a -> FSM a
minimize (qs1, s1, fs1, d1) = (qs, s, fs, d) where   
   rep r = (minimum[q2| (q1, q2) <- compl, q1 == r]) where
    xor = (binopFSM (/=) (qs1, s1, fs1, d1) (qs1, s1, fs1, d1))
    rev = (reverseFSM xor)
    noreach = (nreachable rev)
    compl = ([(q1, q2)| q1 <- qs1, q2 <- qs1, (not ((q1, q2) `elem` noreach))])
   qs = (norm [(rep q)| q <- qs1])
   s  = (rep s1)
   fs = (intersect (norm [(rep q)| q <- qs1]) fs1)
   d q a = (rep (d1 q a))
-- Testing
{-
asdf> m@(q, s, f, d) = binopFSM (/=) oddbs oddbs
asdf> q
[(0,0),(0,1),(1,0),(1,1)]
asdf> s
(0,0)
asdf> f
[(0,1),(1,0)]

asdf> m@(q, s, f, d) = binopFSM (/=) end_ab end_ab
asdf> q
[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)]
asdf> s
(0,0)
asdf> f
[(0,2),(1,2),(2,0),(2,1)]

asdf> m@(q, s, f,d) = reverseFSM end_ab
asdf> nacc m "aaabba"
False
asdf> nacc m "baaabba"
True

asdf> m@(q, s, f,d) = reverseFSM oddbs
asdf> nacc m "baaabba"
True
asdf> nacc m "aaabba"
False

asdf> m@(q, s, f,d) = reverseFSM oddbs
asdf> nreachable m
[0,1]

asdf> let m = minimize oddbs
asdf> accept1 m "b"
True
asdf> accept1 m "bb"
False
asdf> (accept1 oddbs "bb") == (accept1 (minimize oddbs) "bb")
True
asdf> (accept1 oddbs "bb") == (accept1 (minimize oddbs) "b")
False
asdf> (accept1 oddbs "b") == (accept1 (minimize oddbs) "b")
True
asdf> let m = minimize end_ab
asdf> accept1 m "abbbb"
False
asdf> accept1 m "abbbab"
True
asdf> (accept1 end_ab "bb") == (accept1 (minimize end_ab) "bb")
True
asdf> (accept1 end_ab "ab") == (accept1 (minimize end_ab) "ab")
True
asdf> (accept1 end_ab "ab") == (accept1 (minimize end_ab) "b")
False

asdf> let ab = catFSM exactly_a exactly_b
asdf> m@(q,s,f,d) = minimize ab
asdf> q
[(0,[]),(0,[0]),(0,[0,1]),(0,[1]),(1,[0]),(1,[0,1]),(2,[]),(2,[1])]
asdf> s
(0,[])
asdf> f
[(0,[0,1]),(0,[1]),(1,[0,1]),(2,[1])]
asdf> accept2 m "b"
False
asdf> accept2 m "ab"
True
-}