{-# LANGUAGE TypeFamilies, QuasiQuotes, MultiParamTypeClasses,
             TemplateHaskell, OverloadedStrings, TypeSynonymInstances #-}
import Yesod

import Commands
import Term
import Interpreter
import System.IO.Unsafe
import Data.Text (Text,unpack)
import Control.Applicative ((<$>), (<*>))
import Yesod.Form.Jquery
import Parse
import Debug.Trace
import MyError

main :: IO ()
main = warpDebug 3000 Signs

data Signs = Signs

mkYesod "Signs" [parseRoutes|
/expr ExprR POST
/ RootR GET
|]

instance Yesod Signs
instance YesodJquery Signs
instance RenderMessage Signs FormMessage where
    renderMessage _ _ = defaultFormMessage

data InputExpr = InputExpr
    { getExpr :: Text }
  deriving Show

exprForm :: Html -> MForm Signs Signs (FormResult InputExpr, Widget)
exprForm = renderDivs $ InputExpr
    <$> areq textField "Expr" Nothing

string = show (unsafePerformIO (run [Load "opt.signs",Listing ""]))

getRootR :: Handler RepHtml
getRootR = do
    -- Generate the form to be displayed
    (widget, enctype) <- generateFormPost exprForm
    defaultLayout [whamlet|
<p>Enter an expression to evaluate it:
<form method=post action=@{ExprR} enctype=#{enctype}>
    ^{widget}
    <input type=submit>
|]

{-
getHomeR :: forall sub. GHandler sub a0 RepHtml
getHomeR = defaultLayout $ do
        [whamlet|<h1>#{string}|]
  -}
        
        
parseITerm :: InputExpr -> Either ParseError Term        
parseITerm input = let result = parse term "" (unpack $ getExpr input)  
  in trace ("result " ++ show result) result
        
postExprR :: Handler RepHtml
postExprR = do
    ((result, widget), enctype) <- runFormPost exprForm
    case result of
        FormSuccess expr -> defaultLayout [whamlet|<p>#{show $ parseITerm expr}|]
        _ -> defaultLayout [whamlet|
<p>Invalid input, let's try again.
<form method=post action=@{ExprR} enctype=#{enctype}>
    ^{widget}
    <input type=submit>
|]       

