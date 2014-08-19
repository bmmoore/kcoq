{- | Multiline string literals, as a quasiquoter. -}
module Util.StringQ(str) where
import Language.Haskell.TH(stringE)
import Language.Haskell.TH.Quote(QuasiQuoter(QuasiQuoter))

-- | Return the body of the quasiquote as a string literal. Only usable as an expression.
str = QuasiQuoter stringE (complain "pattern") (complain "type") (complain "declaration")
 where complain = const . fail . (++) "str quasiquoter can only produce expressions, used here as "
