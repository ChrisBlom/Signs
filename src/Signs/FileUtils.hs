module Signs.FileUtils where

import Control.Monad.State
import Control.Monad

import Signs.Sign
import Signs.Grammar
import Signs.GrammarParser
import System.FilePath.Posix
import System.Directory
import Data.Maybe
import Data.Either
import System.IO
import System.IO.Unsafe
import Data.List
import Text.ParserCombinators.Parsec hiding ((<|>))

isSignsFile :: FilePath -> Bool
isSignsFile    file = ".signs"    `isSuffixOf` file
isFragmentFile file = ".fragment" `isSuffixOf` file

getAllSignsFiles    path = liftM (filter isSignsFile) $ getDirectoryContents path
getAllFragmentFiles path = liftM (filter isFragmentFile) $ getDirectoryContents path

--getGrammarFiles :: FilePath -> [FilePath]
getGrammarFiles path = join $ do
 isFile <- doesFileExist path
 isDirectory <- doesDirectoryExist path
 return ( if isFile then return [path] else getAllSignsFiles path  )

getFragmentFiles path = join $ do
 isFile <- doesFileExist path
 isDirectory <- doesDirectoryExist path
 return ( if isFile then return [path] else getAllFragmentFiles path  )

prelude x = unlines
 ["\\documentclass{article}"
 ,"\\usepackage{amsmath}"
 ,"\\newcommand{\\txt}[1]{\\mbox{\\sf #1}}"
 ,"\\newcommand{\\unit}{{\\Large \\ensuremath{ \\ast} }}"
 ,"\\newcommand{\\provided}[1]{ \\overline{#1}}"
 ,"\\newcommand{\\omitted}{\\ast\\,}"
 ,"\\newcommand{\\combinator}[1]{{\\sf #1}}"
 ,"\\newcommand{\\at}[1]{{\\sf #1}}"
 ,"\\newcommand{\\str}[1]{\\texttt{#1}}"
 ,"\\newcommand{\\abs}[1]{\\textsc{#1}}"
 ,"\\newcommand{\\sem}[1]{\\textsf{#1}}"
 , ""
 ,"\\begin{document}"
 , x
 ,"\\end{document}"

 ]
