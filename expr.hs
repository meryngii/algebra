
import Data.Char
import Data.List
import Data.Maybe

-- 以下から引用。標準のreadは失敗するとエラーを投げる。
-- http://d.hatena.ne.jp/sshi/20060630/p2
read' :: (Read a) => String -> Maybe a
read' s = case [x | (x,t) <- reads s, ("","") <- lex t] of
    [x] -> Just x
    _ -> Nothing


-- 式表現
data Expr = Const Integer | Symbol String
    | Sum [Expr] | Prod [Expr] | Power Expr Expr
        deriving (Show, Eq, Ord)

equals :: Expr -> Expr -> Bool
equals x y = s x == s y
    where
        s (Const x) = Const x
        s (Symbol x) = Symbol x
        s (Sum x) = Sum (sort $ map s x)
        s (Prod x) = Prod (sort $ map s x)
        s (Power x y) = Power (s x) (s y)

showExpr :: Expr -> String
showExpr (Const x) = show x
showExpr (Symbol x) = x
showExpr (Sum x) = "(" ++ (concat $ intersperse " + " $ map showExpr x) ++ ")"
showExpr (Prod x) = (concat $ intersperse " * " $ map showExpr x)
showExpr (Power x y) = showExpr x ++ "^" ++ showExpr y


mul (Prod x) (Prod y) = Prod $ x ++ y
mul (Prod x) y = Prod $ x ++ [y]
mul x (Prod y) = Prod $ x : y
mul x y = Prod [x, y]

add (Sum x) (Sum y) = Sum $ x ++ y
add x (Sum y) = Sum $ x : y
add (Sum x) y = Sum $ x ++ [y]
add x y = Sum [x, y]


-- 構文解析
term, power, factor, expression :: [String] -> (Expr, [String])

term ("-":is) = let (e', is') = factor is in (mul (Const $ -1) e', is')

term ("(":is) = let (e', (")":is')) = expression is in (e', is')
term (i:is) = case read' i of
    Just x -> (Const x, is)
    Nothing -> (Symbol i, is)

power = pow . term 
    where
        pow (e, "^":is) = let (e', is') = power is in (Power e e', is')
        pow x = x

factor = fac . power
    where
        fac (e, "*":is) = let (e', is') = power is in fac (mul e e', is')
        fac (e, "/":is) = let (e', is') = power is in fac (mul e (Power e' (Const $ -1)), is')
        fac x = x

expression = exp . factor
    where
        exp (e, "+":is) = let (e', is') = factor is in exp (add e e', is')
        exp (e, "-":is) = let (e', is') = factor is in exp (add e (mul (Const $ -1) e'), is')
        exp x = x


-- 字句解析
lexer :: String -> [String]
lexer [] = []
lexer (x:xs)
    | isAlpha x = wordWhile (\x -> isAlpha x && isDigit x)
    | isDigit x = wordWhile isDigit
    | isSpace x = lexer xs
    | isAscii x = [x] : lexer xs
        where wordWhile p = (x : takeWhile p xs) : (lexer $ dropWhile p xs)


-- 構文解析 + 字句解析
parse = fst . expression . lexer


assign (Symbol p) p' = a
    where
        a :: Expr -> Expr
        a (Symbol x) | x == p = p'
        a (Sum x) = Sum (map a x)
        a (Prod x) = Prod (map a x)
        a (Power x y) = Power (a x) (a y)
        a x = x

isConst :: Expr -> Bool
isConst (Const _) = True
isConst _ = False

getConsts :: [Expr] -> [Integer]
getConsts e = [g v | v<-e, isConst v]
    where g (Const x) = x

getTerms :: Expr -> Expr
getTerms (Prod x) = simplify $ Prod [v | v<-x, not $ isConst v]
getTerms (Symbol x) = Symbol x
getTerms (Const _) = Const 1
getTerms (Power x y) = Power x y

getConstTerm :: Expr -> Integer
getConstTerm (Prod x) = product $ getConsts x
getConstTerm (Symbol _) = 1
getConstTerm (Const x) = x
getConstTerm (Power _ _) = 1

getBase :: Expr -> Expr
getBase (Const x) = Const x
getBase (Symbol x) = Symbol x
getBase (Power x y) = x
getBase (Sum x) = Sum x

getExpo :: Expr -> Expr
getExpo (Const x) = Const 1
getExpo (Symbol x) = Const 1
getExpo (Power x y) = y
getExpo (Sum x) = Const 1


simplify :: Expr -> Expr

simplify (Sum x)
    = case foldl add' [] . map simplify $ x of
        [] -> Const 0
        [x] -> x
        x -> Sum x
        where
            add' :: [Expr] -> Expr -> [Expr]
            add' x (Sum y) = foldl add' x y
            add' x (Const y)
                = [v | v<-x, not $ isConst v] ++
                    case sum $ y : getConsts x of
                        0 -> []
                        x -> [Const x]
            add' x y
                = [v | v<-x, not $ getTerms v `equals` getTerms y] ++
                    [simplify $
                        (Const . sum $ [getConstTerm v | v<-x, getTerms v `equals` getTerms y] ++ [getConstTerm y])
                            `mul` getTerms y]

simplify (Prod x)
    = case foldl mul' [] . map simplify $ x of
        [] -> Const 1
        [x] -> x
        x -> Prod x
        where
            mul' :: [Expr] -> Expr -> [Expr]
            mul' x (Prod y) = foldl mul' x y
            mul' x (Const y)
                = case product $ y : getConsts x of                
                    0 -> [Const 0]
                    1 -> r
                    x -> Const x : r
                    where r = [v | v<-x, not $ isConst v]
            
            mul x y
                = [v | v<-x, not $ getBase v `equals` getBase y] ++
                    [simplify $
                        Power (getBase y)
                            (foldl1 add $ [getExpo v | v<-x, getBase v `equals` getBase y] ++ [getExpo y])]

simplify (Power x y)
    = pow' (simplify x) (simplify y)
        where
            pow' (Power (Const x) y) (Const z) = Power (Const (x^z)) y
            pow' (Power x y) z = pow' x (simplify $ mul y z)
            pow' (Const 1) x = Const 1
            pow' x (Const 1) = x
            pow' x (Const 0) = Const 1
            pow' (Const x) (Const y) = Const (x^y)
            pow' x y = Power x y

--pow' (Prod x) (Const y) = simplify $ Prod $ (Const $ (^y) $ product $ getConsts x) : Power (Prod [v | v<-x, not $ isConst v]) (Const y)  -- endless

simplify (Const x) = Const x
simplify (Symbol x) = Symbol x


