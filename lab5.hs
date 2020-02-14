-- CSci 119, Lab 5
-- Reference: Lecture notes, Sections 4.1, 4.2

-- Again, for this (and most) labs, the alphabet will be {a,b} to keep testing
-- easier, but your code should work just as well for any finite list.
sigma = ['a', 'b']

-- Finite State Machine M = (Q, s, F, d) with integer states
type FSM = ([Int], Int, [Int], [(Int,Char,Int)])

-- Check whether a finite state machine (qs, s, fs, ts) is correct/complete:
-- (1) States qs are unique (no duplicates)
-- (2) Start state is a state (s is in qs)
-- (3) Final states are states (fs is a subset of qs)
-- (4) Transition function gives a state in qs for every state in qs and
--     letter from sigma

dulp :: Eq x => [x] -> Bool
dulp [] = True
dulp (x:xs) = not (elem x xs) && dulp xs

subset :: [Int] -> [Int]-> Bool
subset [] _ = True
subset (x: xs) ys = (elem x ys) && subset xs ys

--tqs :: [Int] -> [Char] -> [Int] -> [(Int, Char, Int)]
--tqs ts  
check_trans :: [(Int, Char, Int)] -> [Int] -> Bool
check_trans [] _ = True
check_trans _ [] = False
check_trans (t@(s1, c, s2):ts) states = (elem s1 states) &&
                                 (elem c sigma) &&
                                 (elem s2 states) &&
                (and [s2 == s2'| (s1, c, s2) <- (t:ts), (s1', c', s2') <- (t:ts), c == c', s1 == s1'])&& check_trans ts states

checkFSM :: FSM -> Bool
checkFSM (qs, s, fs, ts) = (dulp qs) && (elem s qs) && (subset fs qs) && (check_trans ts qs)

-- Gives the delta* function (recursive in w)

delta :: FSM -> Int -> Char -> Int
delta (m@(qs, q0, fs, (s1, c, s2):ts)) q a = head [ d | (q', a', d) <-ts, q==q', a==a']


delta_star :: FSM -> Int -> [Char] -> Int
delta_star m q [] = q
delta_star m q (w:ws) = (delta_star m) (delta m q w) ws

accept1_final_state :: FSM -> [Int]
accept1_final_state (qs, q0, fs, ts) = fs

accept1_start_state :: FSM -> Int
accept1_start_state (qs, q0, fs, ts) = q0


-- Machine acceptance, Definition 1 (via delta*)
accept1 :: FSM -> [Char] -> Bool
accept1 m@(qs,q0,fs,ts) w = elem (delta_star m q0 w) fs


-- Machine acceptance, Definition 2 (via L_q(M))

accept2_aux_final_state :: FSM -> Int -> Bool
accept2_aux_final_state (qs, q0, fs, ts) q = q `elem` fs

-- accept2_aux m q w = whether m, starting in q, accepts w (recursive in w)
accept2_aux :: FSM -> Int -> [Char] -> Bool
accept2_aux m@(qs, q0, fs, ts) q [] = elem q fs
accept2_aux m q (w:ws) = accept2_aux m (delta m q w) ws

accept2_start_state :: FSM -> Int
accept2_start_state (qs, q0, fs, ts) = q0

-- Defined (non-recursively) in terms of accept2_aux
accept2 :: FSM -> [Char] -> Bool
accept2 m w = accept2_aux m (accept2_start_state m) w

---- FSM construction

-- Define a machine that accepts exactly the strings with an odd number of b's
-- and test it adequately
oddbs :: FSM
oddbs = ([0,1], 0, [0], [(i, b, d i b) | i <- [0,1], b <- sigma]) where
d i 'b' = (i + 1) `mod` 2
d i 'a' = i

-- Define a machine that accepts exactly the strings that do not contain "aab"
-- as a substring and test it adequately
avoid_aab :: FSM
avoid_aab = ([0..2], 0, [0..1], [(i, a, x i b) | i <- [0..3], a <- sigma, b <- sigma]) where
x i 'a' = min 2 (i + 1)
x i 'b' = min 1 (i + 1)

-- Define a machine that accepts all strings that end in "ab" and test
end_ab :: FSM
end_ab = ([0..2],0,[2],[(i, a ,t i b) | i <- [0..2], a <-sigma, b <- sigma]) where
                             t 0 'a' = 1
                             t 1 'a' = 1
                             t 1 'b' = 2
                             t 2 'a' = 1
                             t _ _ = 0

-- Define a function that takes a string and returns a machine that excepts
-- exactly that string and nothing else
exactly :: String -> FSM
exactly s = undefined
