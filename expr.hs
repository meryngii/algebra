
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



isConst :: Expr -> Bool
isConst (Const _) = True
isConst _ = False

getConst :: Expr -> Integer
getConst (Const x) = x


simplify :: Expr -> Expr

simplify (Sum x)
    = case foldl add' [] . map simplify $ x of
        [] -> Const 0
        [x] -> x
        x -> Sum x
        where
            add' :: [Expr] -> Expr -> [Expr]
            add' x (Const y)
                = [v | v<-x, not.isConst $ v] ++ [Const . (+y) . maybe 0 getConst . find isConst $ x]
            add' x y
                = [v | v<-x, getTerms v /= getTerms y] ++
                    [simplify $
                        (Const . (+ getConstTerm y) . maybe 0 getConstTerm
                        . find (== getTerms y) . map getTerms $ x)
                            `mul` (getTerms y)]

            getTerms (Prod x) = simplify . Prod . sort $ [v | v<-x, not . isConst $ v]
            getTerms (Symbol x) = Symbol x
            getTerms (Const _) = Const 1
            getTerms (Power x y) = Power x y

            getConstTerm (Prod x) = maybe 1 getConst . find isConst $ x
            getConstTerm (Symbol _) = 1
            getConstTerm (Const x) = x
            getConstTerm (Power _ _) = 1

simplify (Prod x)
    = case foldl mul' [] . map simplify $ x of
        [] -> Const 1
        [x] -> x
        x -> Prod x
        where
            mul' :: [Expr] -> Expr -> [Expr]
            mul' x (Const 0) = [Const 0]
            mul' x (Const y)
                = (Const . (*y) . maybe 1 getConst . find isConst $ x)
                    : [v | v<-x, not . isConst $ v]
            mul' x y
                = [v | v<-x, getBase v /= getBase y] ++
                    [simplify $
                        Power (getBase y)
                            ((maybe (Const 0) getExp . find (== getBase y) . map getBase $ x)
                                `add` (getExp y))]
            
            getBase (Const x) = Const x
            getBase (Symbol x) = Symbol x
            getBase (Power x y) = x
            getBase (Sum x) = Sum x

            getExp (Const x) = Const 1
            getExp (Symbol x) = Const 1
            getExp (Power x y) = y
            getExp (Sum x) = Const 1

simplify (Power x y)
    = s (simplify x) (simplify y)
        where
            s (Power (Const x) y) (Const z) = Power (Const (x^z)) y
            s (Power x y) z = s x (simplify $ mul y z)
            s (Const 1) x = Const 1
            s x (Const 1) = x
            s x (Const 0) = Const 1
            s (Const x) (Const y) = Const (x^y)
            s x y = Power x y

simplify (Const x) = Const x
simplify (Symbol x) = Symbol x

