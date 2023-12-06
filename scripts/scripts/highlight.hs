import System.Process
import Text.Printf
import Data.List

highlight :: String -> String
highlight = intercalate " \\: " . map replace . words

replace :: String -> String
replace s = case lookup s fmt of
              Nothing -> "\\abnd{" ++ s ++ "}"  
              Just s' -> s'
  where
    -- Datatypes
    dt = [ "Laws" 
         , "Pushout"
         , "Syntax"
         , "Term"
         ]
    dtFmt :: [(String, String)]
    dtFmt = map (\d -> (d, "\\adt{" ++ d ++ "}") ) dt
              ++ [ ("_/_", "\\AgdaUnderscore / \\AgdaUnderscore")
                 , ("_~t_", "\\atilde")
                 , ("~t", "\\adt{\\textasciitilde_t}")
                 ]

    -- Inductive constructors
    ic = [ "inl"
         , "inr"
         , "push"
         , "trunc"
         , "var"
         , "op"
         , "["
         , "]"
         , "eq/"
         , "squash/"
         , ","
         ] 
    icFmt = map (\d -> (d, "\\aic{" ++ d ++ "}") ) ic

    -- Keywords
    kw = [ "do"
         ] 
    kwFmt = map (\d -> (d, "\\akw{" ++ d ++ "}") ) kw

    -- Special symbols
    sym = [ "=", ";", ":", "(", ")"] 
    symFmt = map (\d -> (d, "\\AgdaSymbol{" ++ d ++ "}") ) sym
               ++ [("->", "\\AgdaSymbol{→}")] ++ [("<-", "\\AgdaSymbol{←}")]


    -- Built-in types
    bi = ["Type", "\\equiv"]
    biFmt = map (\d -> (d, "\\AgdaPrimitive{" ++ d ++ "}")) bi

    -- Functions
    fun = [ "isSet"
          , "isProp"
          , "Fin"
          , "Arity"
          , "interp"
          , "op_t"
          , "odds"
          , "all-int"
          ]
    funFmt = map (\d -> (d, "\\afn{" ++ d ++ "}")) fun
               ++ [ ("[[", "\\afn{\\lhbracket}")
                  , ("]]", "\\afn{\\rhbracket}")
                  , (">>=", "\\afn{\\bind}")
                  ]


    fmt :: [(String, String)]
    fmt = dtFmt ++ icFmt ++ symFmt ++ biFmt ++ funFmt ++ kwFmt


main :: IO ()
main = do l <- getLine
          let f = highlight l
          putStrLn f
          --readProcess "pbcopy" [] f
          --main

{-
The following vim keybinding allows you to select a range, press <leader>h, and
the selected range will be passed to this program and replaced with the output.
 
" Invoking highlight.hs for the selected range
vnoremap <leader>h s<C-R>=system("runghc scripts/highlight.hs", @")[:-2]<CR><ESC>

-}
