module Grammar where

import Sign
import Term
import Parse
import Type
import Inference
import Reductions
import qualified Data.Map as Map
import Data.List
import Data.Maybe
import Control.Monad
import Control.Monad.Error
import Data.Either

data Grammar = Grammar 
  { signatureNames :: (SigName,[SigName])
  , typemappings :: Map.Map Type [Type]
  , signs :: [Sign]
  }

type SigName = String  
type Sig a = (a,SigName)
  
isRight (Right _) = True
isRight _ = False
  


type MyError a = Either ErrorMessage a

type ErrorMessage = String
type InfoMessage = String


--getAbstractConstant :: Grammar -> String -> Either ErrorMessage Term
getSign name g = case find ( (==name) . constantName . abstract) (signs g) of
  Just con -> Right con
  Nothing  -> Left $ "could not find " ++ name


--abstractTermToSign :: Term -> Grammar -> MyError Sign
abstractTermToSign term grammar = let concretesE = map (\sig -> termHomomorphism grammar sig term) ( snd $ signatureNames grammar) in
  if all isRight concretesE
    then   Right $ Sign { abstract = term
            , concretes = map fromRight concretesE
            }

    else Left $ unlines $ nub $ lefts concretesE







interpret :: Grammar -> SigName -> Term -> Either ErrorMessage Term
interpret grammar conSig absTerm = termMapping grammar conSig absTerm


unifiable :: Type -> Type -> Either ErrorMessage InfoMessage
unifiable typeA typeB = let subst = typeA `mgu` typeB in
  if  validSubst subst
    then Right $ "correctly typed"
    else Left $ concat ["could not unify ",show typeA," with expected type ",show typeB]


(f .|. g) x = case x of
  Left  x' -> Left  (f x')
  Right x' -> Right (g x')

left  f = (f .|. id)
right f = (id .|. f)


typeCheck grammar constant concreteSig = let
  concreteTerm  = termHomomorphism grammar concreteSig constant
  concreteTypeA = typeHomomorphism grammar concreteSig (typeOf constant)
  in if isJust concreteTypeA && isRight concreteTerm
   then let concreteTypeB = typeOf $ fromRight concreteTerm in
    (\x -> "typing error in abstract constant " ++ show constant ++"\n\t : "++x ++ " in "++ show concreteSig )
    .|.
    (\x -> (show constant) ++" is "++ x ++ " for the "++ concreteSig ++ " component.")
    $ unifiable concreteTypeB (fromJust concreteTypeA)
   else
    Left $ "missing "++ concreteSig ++" term in " ++ show constant


typeCheckTerm grammar constant =
  map (typeCheck grammar constant) (getConcreteSigs grammar)


typeCheckSigns grammar = map (typeCheckTerm grammar) (map abstract $ signs grammar)


-- atomicTypes :: Grammar -> SigName -> Type  

  

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

assignAbstract grammar  = assignSig  (getAbstractSig grammar)
assignConcretes grammar = assignSigs (getConcreteSigs grammar) 



getAbstractSig :: Grammar -> SigName = fst . signatureNames
getConcreteSigs :: Grammar -> [SigName] = snd . signatureNames


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
typeMapping grammar@g targetSig sourceType = let abstract = getAbstractSig grammar in do 
  { concreteTypes <- Map.lookup (assignAbstract g sourceType) (sigedTypeMappings g)
  ; liftM dropSig $ selectSig targetSig concreteTypes
  }
  
typeMapping' grammar@g targetSig sourceType = let
  abstract = getAbstractSig grammar
  concreteTypes = Map.lookup (assignAbstract g sourceType) (sigedTypeMappings g)
  in case concreteTypes of
    Just types -> liftM  dropSig $  fromJust' (selectSig targetSig types) targetSig
    Nothing -> Left $ "could not find : " ++ show sourceType
  where fromJust' x z = case x of { Just y -> Right y ; Nothing -> Left $ "could not find " ++ show z }



termMapping :: Grammar -> SigName -> Term -> Either ErrorMessage Term

termMapping grammar@g targetSig sourceTerm = let
  abstract = getAbstractSig grammar
  concreteTerms = Map.lookup (assignAbstract g sourceTerm) (sigedTermMappings g)
  in case concreteTerms of
    Just terms -> liftM dropSig $ fromJust' (selectSig targetSig terms) targetSig
    Nothing -> Left $ "could not find : " ++ show sourceTerm
  where fromJust' x z = case x of { Just y -> Right y ; Nothing -> Left $ "could not find " ++ show z }

  
typeHomomorphism grammar targetSig sourceType=  let tmap = typeHomomorphism grammar targetSig in
 case sourceType of
  a@(Atom _) ->  (typeMapping grammar targetSig) a
  TVar v      -> return $ TVar v
  f :-> g     -> (liftM2 (:->)) (tmap f) (tmap g)
  f :*: g     -> (liftM2 (:*:)) (tmap f) (tmap g)
  f :+: g     -> (liftM2 (:+:)) (tmap f) (tmap g)
  Option a    -> liftM Option (tmap a)
  Unit        -> return Unit
  Void        -> return Void

termHomomorphism :: Grammar -> SigName -> Term -> MyError Term
termHomomorphism grammar targetSig sourceTerm =  let cmap' = termHomomorphism grammar targetSig in
 case sourceTerm  of
  constant@(Con c t) -> (termMapping grammar targetSig) constant
  Var c         -> return $ Var c
  App m n       -> liftM2 App (cmap' m) (cmap' n)
  Lam v m       -> cmap' m >>= (\x -> return $ Lam v x)
  Pair m n      -> liftM2 Pair (cmap' m) (cmap' n)
  Fst m         -> liftM Fst (cmap' m) 
  Snd n         -> liftM Snd (cmap' n) 
  L m           -> liftM L (cmap' m) 
  R n           -> liftM R (cmap' n) 
  Case o l r    -> liftM3 Case (cmap' o) (cmap' l) (cmap' r)
  Nil           -> return Nil
  NotNil j      -> liftM NotNil (cmap' j)
  CaseO o j d   -> liftM3 CaseO (cmap' o) (cmap' j) (cmap' d)

  
type SignName = String  



collectAbstractTypes :: Grammar -> [Sig Type]
collectAbstractTypes g
  = let abstract = getAbstractSig g in
  [ assignSig abstract key | key <- (Map.keys . typemappings) g ] 

collectConcreteTypes :: Grammar -> [[Sig Type]]
collectConcreteTypes g = let sigs = snd $ signatureNames g in
  [ zipWith assignSig sigs concretes  | concretes <- Map.elems $ typemappings g ] 
  
  

-- buildTypeMapping :: Grammar -> Type -> SigName -> Sig Type
-- buildTypeMapping ::




instance Show Grammar where
  show g = concat $ intersperse "\n"
    [ show $ signatureNames g
    , show $typemappings g 
    , show $ signs g
    ]
  

