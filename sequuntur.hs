{- sequitur.info -}
import Data.List;
import Data.Maybe;

data Symbol a     = N Int | T a             deriving Eq;
data Production a = P [Symbol a] [Symbol a] deriving Eq;
data Grammar a    = G [Production a]        deriving Eq;

instance Show a => Show (Symbol a) where
  show (N n) = "S" ++ (show n)
  show (T s) = (show s)

showWord w = concat $ intersperse "." [(show s) | s <- w]
instance Show a => Show (Production a) where
  show (P l r) = showWord l ++ " -> " ++ showWord r

instance Show a => Show (Grammar a) where
  show (G ps) = concat [(show p) ++ "\n" | p <- ps]

instance Eq a => Ord (Symbol a) where
  (<=) (T s) _     = True
  (<=) (N x) (N y) = (x <= y)

instance Enum (Symbol a) where
  fromEnum (N n) = n
  fromEnum (T s) = 0
  toEnum         n = (N n)
  

lhs (P l r) = l
rhs (P l r) = r

lhsG (G ps) = map lhs ps
rhsG (G ps) = map rhs ps

mapG    f (G ps)   = G $ map f ps
mapRhsG f g        = mapG (\(P lhs rhs) -> P lhs (f rhs)) g
applyG  f (G ps)   = G $ f ps
addP    l r (G ps) = G $ ps ++ [(P l r)]
as      ch         = [(T ch)]
dropP   p          = applyG $ filter (/= p)

-- returns the number of non-overlapping occurrences of the given sub-string in
-- the string.
subcount :: Eq a => [a] -> [a] -> Int
subcount ts [] = 0
subcount ts xs = if isPrefixOf ts xs 
                 then 1 + (subcount ts (fromJust $ stripPrefix ts xs)) 
                 else subcount ts (tail xs)

-- count non-overlapping occurrences of the given word in the right-hand-sides of
-- the grammar.
countG :: Eq a => [Symbol a] -> Grammar a -> Int
countG ts g = sum $ map (\xs -> subcount ts xs) (rhsG g)

-- returns maximum non-terminal used in the grammar. This assumes that all
-- left-hand-sides of grammar productions consist of a single non-terminal.
maxG :: Eq a => Grammar a -> Symbol a
maxG = maximum . (map head) . lhsG

-- adds an input symbol to the grammar
addCh (G [])           ch = G [P [(N 0)] (as ch)]
addCh (G ((P l r):ps)) ch = G ((P l (r ++ (as ch)):ps))

-- replaces in the given list all occurences of source with target.
subst :: Eq a => [a] -> [a] -> [a] -> [a]
subst source target []       = []
subst source target l@(x:xs) = maybe (x : subst source target xs) 
                               (\r -> target ++ subst source target r) 
                               (stripPrefix source l)

-- replaces x0 with x1 in the right-hand-sides of a grammar.
substG :: Eq a => [Symbol a] -> [Symbol a] -> (Grammar a -> Grammar a)
substG x0 x1 = mapRhsG $ subst x0 x1

-- replaces occurrences of right-hand-side of a production with its left-hand-side
-- anywhere in the grammar, except for the production itself.
collapse :: Eq a => Grammar a -> Grammar a
collapse (G ps) = G $ collapseWith [] ps

collapseWith :: Eq a => [Production a] -> [Production a] -> [Production a]
collapseWith ps []     = ps
collapseWith ps (q:qs) = let sub = substG (rhs q) (lhs q) . G 
                         in let (G nps0) = sub qs 
                                (G nps1) = sub ps
                            in collapseWith (nps1 ++ [q]) nps0

-- returns the set of digrams in the grammar.
digraphs :: Eq a => Grammar a -> [[Symbol a]]
digraphs g = nub $ concat $ map 
             (\xs -> [ xs!!i : [xs!!(i+1)] | i <- [0 .. (length xs) - 2]]) 
             (rhsG g)

-- modifies the grammar by adding a new rule for any digram that occurs more
-- than once.
balance :: Eq a => Grammar a -> Grammar a
balance g = balanceWith g (digraphs g)

balanceWith :: Eq a => Grammar a -> [[Symbol a]] -> Grammar a
balanceWith g [] = g
balanceWith g (di:ds) = if countG di g > 1 
                        then let new = succ (maxG g) 
                             in balance (addP [new] di (substG di [new] g))
                        else balanceWith g ds

-- returns the list of "unused" productions in the grammar, that is, productions
-- used only once.
unused :: Eq a => Grammar a -> [Production a]
unused g@(G ps) = filter (\p -> countG (lhs p) g == 1) ps

-- removes all unused productions from the grammar.
clean :: Eq a => Grammar a -> Grammar a
clean g = cleanWith g (unused g)

cleanWith :: Eq a => Grammar a -> [Production a] -> Grammar a
cleanWith g ((P [(N 0)] _):ps) = cleanWith g ps
cleanWith g []                 = g
cleanWith g (p:ps)             = clean $ substG (lhs p) (rhs p) (dropP p g)

-- builds the grammar corresponding to the word in the input alphabet.
build :: Eq a => [a] -> Grammar a
build = foldl (\g -> \ch -> clean $ balance $ collapse $ addCh g ch) (G [])
