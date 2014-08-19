{-# LANGUAGE QuasiQuotes #-}
module Util.Zencode where
import Data.Maybe(fromMaybe)
import Data.Char(isAlpha)

import qualified Util.StringQ as Q(str)

-- | Translate symbols to alphanumerics, to help turn labels
-- into legal Coq identifiers. Based on GHC's z-encoding convention.
zencode :: String -> String
zencode = prefix . concatMap encChar
  where encChar c = fromMaybe [c] (lookup c replacements)
        replacements =
            [(c,r) | ([c]:r:_) <- map words . lines $ encodings]
        prefix l@(c:_) | isAlpha c = l
                       | otherwise = "z0"++l
        encodings = [Q.str|
             z 	zz      z and Z must be escaped
             Z 	ZZ
             ( 	ZL 	Left
             ) 	ZR 	Right
             [ 	ZM 	'M' before 'N' in []
             ] 	ZN
             : 	ZC 	Colon
             ; 	ZS      Semicolon
             & 	za 	Ampersand
             | 	zb 	Bar
             ^ 	zc 	Caret
             $ 	zd 	Dollar
             = 	ze 	Equals
             > 	zg 	Greater than
             # 	zh 	Hash
             . 	zi 	The dot of the 'i'
             < 	zl 	Less than
             - 	zm 	Minus
             ! 	zn 	Not
             + 	zp 	Plus
             ' 	zq 	Quote
             \ 	zr 	Reverse slash
             / 	zs 	Slash
             * 	zt 	Times sign
             _ 	zu 	Underscore
             % 	zv      Divide

             { 	ZO      Open
             } 	ZP      'P' after 'O' in {}

             ~   zw      tWiddle
             ,   zx      neXt
             @   zW      Whorl
             |]
