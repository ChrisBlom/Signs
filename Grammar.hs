module Grammar where

import Sign
import Term
import Parse
import Type
import MyError
import Inference
import Reductions
import qualified Data.Map as Map
import Data.List
import Data.Maybe
import Control.Monad
import Control.Monad.Error
import Control.Monad.State
import Control.Monad.Reader
import Text.PrettyPrint.HughesPJ 
import Tex
import Data.Either


data Grammar = Grammar 
  { signatureNames :: (SigName,[SigName])
  , typemappings   :: Map.Map Type [Type]
  , signs           :: [Sign]
  }

type GrammarEnv a = Reader Grammar a

type SigName = String  
type Sig a = (a,SigName)


concatEithers :: [Either a b] -> ([a],[b])
concatEithers eithers = (lefts eithers,rights eithers)


-- pretty prints a sign as LaTex, with types
prettyPrintSignTex :: Sign -> GrammarEnv Doc
prettyPrintSignTex sign  = do
 g <- ask
 let  addType (term,index) = (reduce term , typ)   where
         sig = snd (signatureNames g) !! index 
         typ = fromJust $ fromRight $ liftM (typeHomomorphism g sig) (typeOfE (abstract sign)) 
 let (stringTerm,stringTyp) = addType ( (concretes sign) !! 0 , 0)
 let (semTerm,semTyp)       = addType ( (concretes sign) !! 1 , 1)
 return $ mathmode $ array
  [ [ hcat [tex $ abstract sign, text " : ", (either tex (texStyle "ABSTRACT") ) (typeOfE $ abstract sign) ,text " = " ]] 
  , [narray [ [ text "\\langle" , tex " "  , texTerm "STRING" stringTerm , tex " : " <> texStyle "STRING"  stringTyp  ]
            , [ text ","        , tex " "  , texTerm "SEM" semTerm       , tex " : " <> texStyle "SEM"  semTyp        , text "\\ \\rangle"  ] 
            ]
    ]
  ] 


prettyPrintSign :: Sign -> GrammarEnv String    
prettyPrintSign sign  = do
 g <- ask
 let addType (term,index) = show (reduce term) ++ " :: " ++ typ   where
          sig = snd (signatureNames g) !! index 
          typ = showAbbt $ fromJust $ fromRight $ liftM (typeHomomorphism g sig) (typeOfE (abstract sign))
 return $ concat
  [ concat [show $ abstract sign," :: ", (either id show) (typeOfE $ abstract sign)]
  , " = \n\t< "
  ,   concat $ intersperse "\n\t, " $ map (\(x,i) -> addType (x,i)  ) (zip (concretes sign) [0..])
  , "\n \t>"
  ]    
          


-- | for a given grammar, gets the abstract signature of a sign
getAbstractSig :: GrammarEnv SigName
getAbstractSig = reader $  fst . signatureNames

-- | for a given grammar, gets the concrete signatures of a sign
getConcreteSigs :: GrammarEnv [SigName]
getConcreteSigs = reader $  snd . signatureNames

getIndexG :: SigName -> GrammarEnv (Maybe Int)
getIndexG name = do 
  grammar <- ask
  return (elemIndex name (uncurry (:) $ signatureNames grammar))

-- | Adds the types declared an a Grammar to a Term with the given Sig
addTypesToConstantG :: Term -> SigName -> GrammarEnv (MyError Term)
addTypesToConstantG (Con x _) sig = do
  index <- getIndexG sig 
  sign  <- getSignG x   
  sign' <- return $ case index of
    Just i  -> do { s <- sign ; return ( (asList s) !! i) }
    Nothing ->  Left $ "Signature '" ++ sig ++ "' is not defined."   
  return sign'


-- | Given a grammar, add types of Sig to a term
addTypesToTermG :: SigName -> Term -> GrammarEnv (MyError Term)
addTypesToTermG sig term = let cmap' = addTypesToTermG sig  in
 case term  of
  constant@(Con c Void) ->  (addTypesToConstantG constant sig)
  constant@(Con c _) -> (addTypesToConstantG constant sig) 
  Var c         -> return $ return $ Var c
  App m n       -> (liftM2.liftM2) App (cmap' m) (cmap' n)
  Pair m n      -> (liftM2.liftM2) Pair (cmap' m) (cmap' n)
  Fst m         -> (liftM.liftM) Fst (cmap' m) 
  Snd n         -> (liftM.liftM) Snd (cmap' n) 
  L m           -> (liftM.liftM) L (cmap' m) 
  R n           -> (liftM.liftM) R (cmap' n) 
  Case o l r    -> (liftM3.liftM3) Case (cmap' o) (cmap' l) (cmap' r)
  Nil           -> return $ return Nil
  NotNil j      -> (liftM.liftM) NotNil (cmap' j)
  CaseO o j d   -> (liftM3.liftM3) CaseO (cmap' o) (cmap' j) (cmap' d)
  Lam v term    -> (liftM.liftM) (Lam v) (cmap' term) 
  x -> error $ concat ["no case for " , show x ]

  
getSignG :: String -> GrammarEnv ( Either ErrorMessage Sign )
getSignG name = reader $ 
  maybeToError (\_ -> concat ["error : no sign named ",name," could be found"]  ) id
  . find ( (==name) . constantName . abstract) 
  . signs

abstractTermToSignG :: Term -> GrammarEnv (MyError Sign)
abstractTermToSignG term = do
 sigs           <- getConcreteSigs 
 concreteTerms  <- mapM  (termHomomorphismG term)  sigs
 return $ if all isRight concreteTerms
    then  Right $ Sign { abstract = term
            , concretes = map fromRight concreteTerms
            }

    else Left $ unlines $ nub $ lefts concreteTerms

{-
interpret' :: SigName -> Term -> GrammarEnv (Either ErrorMessage Term)
interpret' conSig absTerm = 
  reader ( \grammar -> termMapping grammar conSig absTerm )
-}

unifiable :: Type -> Type -> Either ErrorMessage InfoMessage
unifiable typeA typeB = let subst = typeA `mgu` typeB in
  if  validSubst subst
    then Right $ "correctly typed"
    else Left $ concat ["found type\t\t",show typeA,"\n\t   but expected type\t",show typeB]


-- |for a given grammar, typechecks the constants of a grammar for constitency with the abstract type

typeCheckG constant concreteSig = do 
 grammar <- ask
 return $
  case (typeOfE constant) of 
   Left  error -> Left error
   Right typ -> 
     let
     concreteTerm  = (termHomomorphism grammar concreteSig) constant
     concreteTypeA = (typeHomomorphism grammar concreteSig) typ
     in if isJust concreteTypeA && isRight concreteTerm
      then let concreteTypeB = fromRight $ typeOfE $ fromRight concreteTerm in
       (\x -> "typing error in " ++ show concreteSig ++ " component of " ++ show constant 
           ++"\n\t : "++x )
       .|.
       (\x -> (show constant) ++" is "++ x ++ " for the "++ concreteSig ++ " component.")
       $ unifiable concreteTypeB (fromJust concreteTypeA)
      else
       Left $ "missing "++ concreteSig ++" term in " ++ show constant

typeCheckTermG :: Term -> GrammarEnv [Either ErrorMessage InfoMessage]
typeCheckTermG constant = do 
  sigs <- getConcreteSigs
  msg <-   mapM (typeCheckG constant) sigs
  return msg

typeCheckSigns = do
  constants <- reader $ ( (map abstract) . signs )
  messages <- mapM typeCheckTermG constants
  return messages


validate g = map lefts $ runReader typeCheckSigns g

signListToTermMap :: [Sign] -> Map.Map Term [Term]
signListToTermMap = foldr (\sign map -> Map.insert (abstract sign) (concretes sign) map) Map.empty

ofSig :: SigName -> Sig a -> Bool
ofSig name sigged = (snd sigged) == name

-- selectSig :: SigName -> [Sig a] -> Maybe (Sig a) 
selectSig name list = listToMaybe $ filter (ofSig name) list

  
assignSig :: String -> a  -> Sig a
assignSig sig a  = (a,sig)  

dropSig = fst
  
assignSigs = zipWith assignSig

assignAbstract :: Grammar -> a -> Sig a
assignAbstract grammar  = assignSig  (runReader getAbstractSig grammar)
assignConcretes grammar = assignSigs (runReader getConcreteSigs grammar) 


sigedTypeMappings :: Grammar -> Map.Map (Sig Type) [Sig Type] 
sigedTypeMappings g 
  = Map.map     (assignConcretes g)
  $ Map.mapKeys (assignAbstract g) 
  (typemappings g)
 
sigedTermMappings :: Grammar -> Map.Map (Sig Term) [Sig Term] 
sigedTermMappings g
  = Map.map     (assignConcretes g)
  $ Map.mapKeys (assignAbstract g) 
  (signListToTermMap $ signs g)


-- retrieve the type mapping from a grammar
typeMapping grammar@g targetSig sourceType = let abstract = runReader getAbstractSig grammar in do 
  { concreteTypes <- Map.lookup (assignAbstract g sourceType) (sigedTypeMappings g)
  ; liftM dropSig $ selectSig targetSig concreteTypes
  }

  
typeMapping' grammar@g targetSig sourceType = let
  abstract = runReader getAbstractSig grammar
  concreteTypes = Map.lookup (assignAbstract g sourceType) (sigedTypeMappings g)
  in case concreteTypes of
    Just types -> liftM  dropSig $  fromJust' (selectSig targetSig types) targetSig
    Nothing -> Left $ "could not find : " ++ show sourceType
  where fromJust' x z = case x of { Just y -> Right y ; Nothing -> Left $ "could not find " ++ show z }


termMappingG t s = reader (\g -> termMapping g t s)
typeMappingG t s = reader (\g -> typeMapping g t s)

termMapping :: Grammar -> SigName -> Term -> Either ErrorMessage Term

termMapping grammar@g targetSig sourceTerm = let
  abstract = runReader getAbstractSig grammar
  concreteTerms = Map.lookup (assignAbstract g sourceTerm) (sigedTermMappings g)
  in case concreteTerms of
    Just terms -> liftM dropSig $ fromJust' (selectSig targetSig terms) targetSig
    Nothing -> Left $ "could not find : " ++ show sourceTerm 
  where fromJust' x z = case x of { Just y -> Right y ; Nothing -> Left $ "could not find " ++ show z ++ " component of " ++show sourceTerm }

  
typeHomomorphismG targetSig sourceType = do
  grammar <- ask
  return (typeHomomorphism grammar targetSig sourceType )

typeHomomorphism grammar targetSig sourceType=  let tmap = typeHomomorphism grammar targetSig in
 case sourceType of
  a@(Atom _) ->  (typeMapping grammar targetSig) a
  TVar v      -> return $ TVar v
  f :-> g     -> (liftM2 (:->)) (tmap f) (tmap g)
  f :*: g     -> (liftM2 (:*:)) (tmap f) (tmap g)
  f :+: g     -> (liftM2 (:+:)) (tmap f) (tmap g)
  Option a    -> liftM Option (tmap a)
  Marker a str -> tmap a
  Unit        -> return Unit
  Void        -> return Void

termHomomorphism :: Grammar -> SigName -> Term -> MyError Term  
termHomomorphism grammar targetSig sourceTerm =  hextendM (termMapping grammar targetSig) sourceTerm
  
termHomomorphismG sourceTerm targetSig  = do
  grammar <- ask
  return (termHomomorphism grammar targetSig sourceTerm )

type SignName = String  



collectAbstractTypes :: Grammar -> [Sig Type]
collectAbstractTypes g
  = let abstract = runReader getAbstractSig g in
  [ assignSig abstract key | key <- (Map.keys . typemappings) g ] 

collectConcreteTypes :: Grammar -> [[Sig Type]]
collectConcreteTypes g = let sigs = snd $ signatureNames g in
  [ zipWith assignSig sigs concretes  | concretes <- Map.elems $ typemappings g ] 
  
  
ppTypeMappings mappings = "type_interpretations =\n" ++ gasList
 [  concat [show abs," = ", chevrons $ concat $ intersperse "," $ map show concr]       |  (abs,concr) <- Map.toList mappings ]

chevrons x = "<"++x++">"


gasList (h:t) = "\t[" ++ h ++ gasList' t
gasList' [last] = "\n\t," ++ last ++ "]"
gasList' (h:t) = "\n\t," ++ h ++ gasList' t 

instance Show Grammar where
  show g = concat $ intersperse "\n"
    [ "signatures " ++ (showTuple $ signatureNames g )
    , ppTypeMappings $ typemappings g 
    , concat $ intersperse "" $ map (( ++ "\n") . show) $ signs g
    ]

showTuple (abs,concs) = abs ++ " = " ++ (chevrons $ concat $ intersperse "," $ concs)



