module Grammar where

import Sign
import Term
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
import Control.Applicative 


type SignName = String  

data Grammar = Grammar
  { signatureNames :: (SigName,[SigName])
  , typemappings   :: Map.Map Type [Type]
  , signs          :: [Sign]
  }

type SigName = String
type Sig a = (a,SigName)


-- A GrammerEnv is a Reader monad with a Grammer fixes as its source to read from,
-- it is used to evaluate terms in the context of a grammar.
type GrammarEnv a = Reader Grammar a

-- A Signature is an alternative way to represent a Grammar
data Signature = Signature
  { sigName    :: SigName
  , constants  :: [(String,Type)]
  , basicTypes :: [String]
  } deriving (Eq,Show)


data Mapping = Mapping
  { source  :: Signature
  , target  :: Signature
  , typeMap :: Map.Map Type Type
  , termMap :: Map.Map Term Term
  }

getAbstractSignature :: Grammar -> Signature
getAbstractSignature g = Signature
 { sigName = fst $ signatureNames g
 , constants = map ( (\(Con name typ) -> (name,typ)) . abstract ) (signs g)
 , basicTypes = nub $ map (\(Atom a) -> a) $ Map.keys (typemappings g)
 }

-- builds a Signature by extracting all the req. info from a Grammer given SigName
getSignature :: SigName -> Grammar -> Signature
getSignature name g = 
  let sigIndex = fromJust . elemIndex name . snd . signatureNames $ g
      extractConstant :: Term -> (String,Type)
      extractConstant (Con name typ) = (name,typ) 
      getConstant sign = concretes sign !! sigIndex
  in Signature
    { sigName = name
    , constants = map (extractConstant . getConstant) (signs g)
    , basicTypes = nub $ map (\(Atom a) -> a) $ Map.keys (typemappings g)
    } 
 

concatEithers :: [Either a b] -> ([a],[b])
concatEithers eithers = (lefts eithers,rights eithers)


-- pretty prints a sign as LaTex, with types
prettyPrintSignTex :: Sign -> GrammarEnv Doc
prettyPrintSignTex sign  = do
 g <- ask
 let  addType (term,sigIndex) = (reduce term ,fromJust typ) where
         sig = snd (signatureNames g) !! sigIndex
         typingAttempt = liftM (typeHomomorphism g sig) (typeOfE (abstract sign))
         typ = join $ case typingAttempt of Right derivedType -> Just derivedType ; _ -> Nothing
 let (stringTerm,stringTyp) = addType ( (concretes sign) !! 0 , 0)
 let (semTerm,semTyp)       = addType ( (concretes sign) !! 1 , 1)
 return $ mathmode $ array
  [ [ hcat [tex $ abstract sign, text " : ", (either tex (texStyle "ABSTRACT") ) (typeOfE $ abstract sign) ,text " = " ]]
  , [narray [ [ text "\\langle", tex " "   , texTerm "STRING" stringTerm , tex " : " <> texStyle "STRING"  stringTyp  ]
            , [ text ","       , tex " "   , texTerm "SEM" semTerm       , tex " : " <> texStyle "SEM"  semTyp        , text "\\ \\rangle"  ]
            ]
    ]
  ]

fromRight (Right r) = r
fromRight x = error $ "Is not Right " ++ show x

prettyPrintSign :: Sign -> GrammarEnv String
prettyPrintSign sign  = do
 g <- ask
 let addType (term,index) = show (reduce term) ++ " :: " ++ typ   where
          sig = snd (signatureNames g) !! index
          typ = showAbbt $ fromJust $ fromRight $ liftM (typeHomomorphism g sig) (typeOfE (abstract sign))
 return $ concat
  [ concat [show $ abstract sign," :: ", (either show show) (typeOfE $ abstract sign)]
  , " = \n\t< "
  ,   concat $ intersperse "\n\t, " $ map (\(x,i) -> addType (x,i)  ) (zip (concretes sign) [0..])
  , "\n \t>"
  ]


-- | for a given grammar, gets the abstract signature of a sign
getAbstractSig :: GrammarEnv SigName
getAbstractSig = reader $ fst . signatureNames

-- | for a given grammar, gets the concrete signatures of a sign
getConcreteSigs :: GrammarEnv [SigName]
getConcreteSigs = reader $ snd . signatureNames

getIndexG :: SigName -> GrammarEnv (Maybe Int)
getIndexG name = do
  grammar <- ask
  return (elemIndex name (uncurry (:) $ signatureNames grammar))


-- Adds the types declared in a Grammar to a Term with the given Sig
addTypesToConstantG :: Term -> SigName -> GrammarEnv (Either ErrorMessage Term)
addTypesToConstantG (Con x _) sig = do
  sigIndex <- getIndexG sig
  sign  <- getSignG x
  sign' <- return $ case sigIndex of
    Just i  ->  do { s <- sign ; return ( (asList s) !! i) }
    Nothing ->  Left $ "Signature '" ++ sig ++ "' is not defined."
  return sign'
  
-- Given a grammar, add types of Sig to a term
addTypesToTerm :: SigName -> Term -> GrammarEnv (Either ErrorMessage Term)
addTypesToTerm sig term = let cmap' = addTypesToTerm sig  in
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
--  x -> error $ concat ["no case for " , show x ]


getSignG :: String -> GrammarEnv ( Either ErrorMessage Sign )
getSignG name = reader $
  maybeToError (\ _ -> concat ["error : no sign named ",name," could be found"]  ) id
  . find ( (==name) . constantName . abstract)
  . signs

abstractTermToSignG :: Term -> GrammarEnv (Either ErrorMessage Sign)
abstractTermToSignG term = do
 sigs           <- getConcreteSigs
 concreteTerms  <- mapM  (termHomomorphismG term)  sigs
 return $ if all isRight concreteTerms
    then  Right $ Sign { abstract = term
            , concretes = map fromRight concreteTerms
            }
    else Left $ unlines $ nub $ lefts concreteTerms

-- checks if two types are unifyable
unifiable :: Type -> Type -> Bool
unifiable typeA typeB = validSubst substitution where substitution = typeA `mgu` typeB
--    then Right $ "correctly typed"
--    else Left $ concat ["found type\t\t",show typeA,"\n\t   but expected type\t",show typeB]

-- |for a given grammar, typechecks the constants of a grammar for constitency with the abstract type
typeCheckG constant concreteSig = do
 grammar <- ask
 case (typeOfE constant) of
   Left  error -> return $ Left $ show error
   Right typ -> return $ pp constant typ grammar concreteSig

     
-- maps a type and term to a signature, w.r.t grammar
pp :: Term -> Type -> Grammar -> SigName -> Either ErrorMessage String
pp term typ grammar concreteSig =      
  let concreteTerm  = (termHomomorphism grammar concreteSig) term
      maybeConcreteTypeA = (typeHomomorphism grammar concreteSig) typ
  in case maybeConcreteTypeA of 
    Just concreteTypeA | isRight concreteTerm ->
       let concreteTypeB = fromRight $ typeOfE $ fromRight concreteTerm in
        if concreteTypeB `unifiable` concreteTypeA
         then Right $ unwords [show term,"is correctly typed for the",concreteSig,"component."]
         else Right $ unwords ["found type\t\t",show concreteTypeB,"\n\t   but expected type\t",show concreteTypeA,"in",show concreteSig,"component of",show term]
    _ -> Left $ "missing "++ concreteSig ++" term in " ++ show term   

typeCheckTermG :: Term -> GrammarEnv [Either ErrorMessage SuccesMessage]
typeCheckTermG constant = do
  sigs <- getConcreteSigs
  msg  <- mapM (typeCheckG constant) sigs
  return msg


typeCheckSigns = do
  constants <- reader $ (map abstract) . signs -- get the abstract terms of a grammar
  messages  <- mapM typeCheckTermG constants -- typecheck each term
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
typeMapping :: Grammar -> SigName -> Type -> Maybe Type
typeMapping grammar@g targetSig sourceType = let abstract = runReader getAbstractSig grammar in do
  { concreteTypes <- Map.lookup (assignAbstract g sourceType) (sigedTypeMappings g)
  ; liftM fst $ selectSig targetSig concreteTypes
  }


typeMapping' grammar@g targetSig sourceType = let
  abstract = runReader getAbstractSig grammar
  concreteTypes = Map.lookup (assignAbstract g sourceType) (sigedTypeMappings g)
  in case concreteTypes of
    Just types -> liftM  fst $  fromJust' (selectSig targetSig types) targetSig
    Nothing -> Left $ "could not find : " ++ show sourceType
  where fromJust' x z = case x of { Just y -> Right y ; Nothing -> Left $ "could not find " ++ show z }


termMappingG t s = reader (\g -> termMapping g t s)
typeMappingG t s = reader (\g -> typeMapping g t s)


termMapping :: Grammar -> SigName -> Term -> Either ErrorMessage Term
termMapping grammar@g targetSig sourceTerm = let
  abstract = runReader getAbstractSig grammar
  concreteTerms = Map.lookup (assignAbstract g sourceTerm) (sigedTermMappings g)
  in case concreteTerms of
    Just terms -> liftM fst $ fromJust' (selectSig targetSig terms) targetSig
    Nothing -> Left $ "could not find : " ++ show sourceTerm
  where fromJust' x z = case x of { Just y -> Right y ; Nothing -> Left $ "could not find " ++ show z ++ " component of " ++show sourceTerm }


typeHomomorphismG targetSig sourceType = do
  grammar <- ask
  return (typeHomomorphism grammar targetSig sourceType )

-- Given a grammar and a target signature, maps a type from the source sig to the target sig
typeHomomorphism :: Grammar -> SigName -> Type -> Maybe Type
typeHomomorphism grammar targetSig sourceType=  let typeMap = typeHomomorphism grammar targetSig in
 case sourceType of
  a@(Atom _) ->  (typeMapping grammar targetSig) a
  TVar v      -> return $ TVar v
  f :-> g     -> (liftM2 (:->)) (typeMap f) (typeMap g)
  f :*: g     -> (liftM2 (:*:)) (typeMap f) (typeMap g)
  f :+: g     -> (liftM2 (:+:)) (typeMap f) (typeMap g)
  Option a    -> liftM Option (typeMap a)
  Marker a str -> typeMap a
  Unit        -> return Unit
  Void        -> return Void

termHomomorphism :: Grammar -> SigName -> Term -> Either ErrorMessage Term  
termHomomorphism grammar targetSig sourceTerm =  hextendM (termMapping grammar targetSig) sourceTerm
  
termHomomorphismG sourceTerm targetSig  = do
  grammar <- ask
  return (termHomomorphism grammar targetSig sourceTerm )


collectAbstractTypes :: Grammar -> [Sig Type]
collectAbstractTypes g
  = let abstract = runReader getAbstractSig g in
  [ assignSig abstract key | key <- (Map.keys . typemappings) g ] 

collectConcreteTypes :: Grammar -> [[Sig Type]]
collectConcreteTypes g = let sigs = snd $ signatureNames g in
  [ zipWith assignSig sigs concretes  | concretes <- Map.elems $ typemappings g ] 
  


  
-- pretty printing of signs
instance Show Grammar where
  show grammar = concat $ intersperse "\n"
    [ "signatures " ++ (showTuple $ signatureNames grammar)
    , ppTypeMappings $ typemappings grammar 
    , concatMap (( ++ "\n") . show) $ signs grammar
    ]

showTuple (abs,concs) = abs ++ " = " ++ (chevrons $ concat $ intersperse "," $ concs)

ppTypeMappings mappings = concat 
  ["type_interpretations =\n"
  , ppList [ concat 
              [show abstractTerm," = ", chevrons $ concat $ intersperse "," $ map show concreteTerms] | (abstractTerm,concreteTerms) <- Map.toList mappings 
           ]
  ]
  where 
    ppList (h:t) = "\t[" ++ h ++ ppList' t
    ppList' [last] = "\n\t," ++ last ++ "]"
    ppList' (h:t) = "\n\t," ++ h ++ ppList' t 
  
  

chevrons x = "<"++x++">"


