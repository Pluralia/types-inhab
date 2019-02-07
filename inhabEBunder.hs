--lambda(/\E)
{-# LANGUAGE TupleSections #-}

import Data.Char (ord)
import Data.List (nub, intersect)
import Data.Bifunctor (first)


type Symb = String 

infixr 3 :->
infixr 4 :&:

data Type = TVar Symb      -- типовой атом
          | Type :-> Type  -- стрелочный тип
          | Type :&: Type  -- тип-пересечение
    deriving (Read,Show,Eq,Ord)

type Ctx = [([Int], Type)] -- контекст (с пересечениями)

------------------------------------------------------------------------------------------------------
--step 1

subTerms :: Type -> (Type, [Type])
subTerms (arg :-> args) = (arg :) <$> subTerms args
subTerms sigma          = (sigma, [])

------------------------------------------------------------------------------------------------------
--step 2

removeIntersect :: [Type] -> [[Type]]
removeIntersect = fmap eliminate . nub

eliminate :: Type -> [Type]
eliminate (arg :&: args) = arg : eliminate args
eliminate res            = [res]

getIdx :: [[Type]] -> Ctx
getIdx = mconcat . fmap go . zip [0..]
  where
    go :: (Int, [Type]) -> Ctx
    go (idx, [])       = []
    go (idx, x : xs) = ([idx], x) : go (idx, xs)

------------------------------------------------------------------------------------------------------
--steps 3 & 4

arrowTypes :: Ctx -> [([Int], (Type, Type))]
arrowTypes []                          = []
arrowTypes ((abst, arg :-> args) : xs) = (abst, (arg, args)) : arrowTypes xs
arrowTypes (_ : xs)                    = arrowTypes xs

try2App :: ([Int], (Type, Type)) -> Ctx -> Ctx
try2App (abst, (alpha, args)) =
  foldr (\(idxs, betta) -> if alpha == betta then ((abst ++ idxs, args) :) else id) []

eliminateCtx :: Ctx -> Ctx
eliminateCtx []                           = []
eliminateCtx ((idxs, res@(_ :&: _)) : xs) = ((idxs,) <$> eliminate res) ++ eliminateCtx xs
eliminateCtx (res : xs)                   = res : eliminateCtx xs

check :: Type -> Ctx -> Ctx
check wantedType = filter (\(_, res) -> wantedType == res)

------------------------------------------------------------------------------------------------------
-- final logic

inhab :: Type -> ([Type], [Int])
inhab mtype =
  let (betta, args) = subTerms mtype
      ctx           = getIdx . removeIntersect $ args
   in (args, inhabArgs betta ctx)

inhabArgs :: Type -> Ctx -> [Int]
inhabArgs betta ctx =
  let resList = check betta ctx
      newCtx  = extendCtx ctx
   in if not . null $ resList
        then fst . head $ resList
        else if ctx == newCtx
               then error "uninhabited"
               else inhabArgs betta newCtx

extendCtx :: Ctx -> Ctx
extendCtx ctx =
  let forApp = arrowTypes ctx
   in eliminateCtx . nub $ ctx ++ mconcat $ fmap (`try2App` ctx) forApp

------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------

