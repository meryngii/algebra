algebra
=======
minimal algebra system in Haskell

How to Use
----------
1. Install GHC
`sudo apt-get install ghc`
2. Load "expr.hs"
`ghci expr.hs`

Examples
--------
    *Main> showExpr $ simplify $ parse "a^2*b+2/a*b*a*a*a"
    "3 * b * a^2"
    *Main> showExpr $ expand $ parse "(a+b)^2"
    "(a^2 + 2 * b * a + b^2)"

