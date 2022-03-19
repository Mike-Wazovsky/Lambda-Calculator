import Data.List
type Symb = String 
infixl 2 :@
infix 1 `betaEq`, `alphaEq`

data Expr = Var Symb
          | Expr :@ Expr
          | Lam Symb Expr
          deriving (Eq, Read, Show)

subst :: Symb -> Expr -> Expr -> Expr
subst v n (Var x) | x == v     = n
                  | otherwise  = Var x
subst v n (exp1 :@ exp2) = (subst v n exp1) :@ (subst v n exp2)
subst v n (Lam sym exp) | v == sym = Lam sym exp
                        | find (\s -> s == sym) (freeVars n) == Nothing  = Lam sym (subst v n exp)
                        | otherwise = subst v n (alphaRed sym (sym ++ "'") (Lam sym exp))

freeVars :: Expr -> [Symb]
freeVars (Var sym) = [sym]
freeVars (exp1 :@ exp2) = nub $ (freeVars exp1) ++ (freeVars exp2)
freeVars (Lam sym exp) = (freeVars exp) \\ [sym]

alphaRed old new (Var sym) | sym == old  = Var new
                           | otherwise   = Var sym
alphaRed old new (exp1 :@ exp2) = (alphaRed old new exp1) :@ (alphaRed old new exp2)
alphaRed old new (Lam sym exp) | sym == old =  Lam new (alphaRed old new exp)
                               | otherwise  =  Lam sym (alphaRed old new exp)

absNew x exp = let
    y = freeVars exp
    in new1 x y  
    where new1 x listt | elem x listt  = new1 (x ++ "'") listt
                       | otherwise     = x


alphaEq :: Expr -> Expr -> Bool
alphaEq (Var x) (Var y) | x == y     = True
                        | otherwise  = False
alphaEq (exp1 :@ exp2) (exp3 :@ exp4) = (alphaEq exp1 exp3) && (alphaEq exp2 exp4)
alphaEq (Lam sym1 exp1) (Lam sym2 exp2) = let new = absNew sym1 (exp1 :@ exp2)
                                          in alphaEq (subst sym1 (Var new) exp1) (subst sym2 (Var new) exp2)
alphaEq _ _ = False


reduceOnce :: Expr -> Maybe Expr
reduceOnce ((Lam x exp1) :@ exp2) = Just (subst x exp2 exp1)
reduceOnce (Lam sym exp) = case reduceOnce exp of
         Nothing -> Nothing
         Just e -> Just (Lam sym e)
reduceOnce (Var x) = Nothing
reduceOnce (e1 :@ e2) = case reduceOnce e1 of
         Just e -> Just (e :@ e2)
         Nothing -> case reduceOnce e2 of
                  Just ee -> Just (e1 :@ ee)
                  Nothing -> Nothing

nf :: Expr -> Expr
nf expr = case reduceOnce expr of
        Nothing -> expr
        Just e -> nf e    


betaEq :: Expr -> Expr -> Bool 
betaEq exp1 exp2 = alphaEq (nf exp1) (nf exp2)
