--lambda()
import Prelude hiding (lookup)
import Data.Char (ord)
import Data.Map.Lazy (Map(..), empty, insert, lookup)


type Symb = String 

infixr 3 :->
infixr 4 :&:

data Type = TVar Symb      -- типовой атом
          | Type :-> Type  -- стрелочный тип
          | Type :&: Type  -- тип-пересечение
    deriving (Read,Show,Eq,Ord)

type Ctx = [Type] -- контекст

data TNF = Meta   -- метапеременная (пока еще бесструктурная часть схемы)
             Type   -- типизированна
         | TNF    -- структурированная часть схемы
             Ctx    -- абстрактор 
             Int    -- головная переменная как индекс Де Брауна
             [TNF]  -- бёмовы хвостики
    deriving (Read,Show,Eq,Ord) 

------------------------------------------------------------------------------------------------------

uncurry2List :: Type -> (Symb,[Type])
uncurry2List (TVar symb)         = (symb, [])
uncurry2List (arg :-> args)      = (arg :) <$> uncurry2List args

uncurry2RevList  :: Type -> (Symb,[Type])
uncurry2RevList = go (undefined, [])
  where
    go :: (Symb, [Type]) -> Type -> (Symb, [Type])
    go (_, acc) (TVar symb)    = (symb, acc)
    go (_, acc) (arg :-> args) = go (undefined, arg : acc) args

------------------------------------------------------------------------------------------------------

suitTypesWithId :: (Symb, [Type]) -> [(Int, Type)]
suitTypesWithId (alpha, sigmas) = filter ((alpha ==) . getLast . snd) (zip [0..] sigmas)
  where
    getLast :: Type -> Symb
    getLast (TVar symb)  = symb
    getLast (_ :-> args) = getLast args

removeLast :: Type -> [Type]
removeLast (TVar _)         = []
removeLast (arg :-> TVar _) = [arg]
removeLast (arg :-> args)   = (arg :->) <$> removeLast args

------------------------------------------------------------------------------------------------------

unMeta :: Ctx -> TNF -> [TNF]
unMeta zetas (Meta mtype) =
  let (alpha, sigmas) = uncurry2RevList mtype
      isigmas         = suitTypesWithId (alpha, sigmas ++ zetas)
      iYs             = fmap (fmap Meta . snd . uncurry2List) <$> isigmas
   in uncurry (TNF sigmas) <$> iYs
unMeta zetas (TNF abst headId tails) =
  let tnfList = unMeta (abst ++ zetas) <$> tails
   in TNF abst headId <$> sequence tnfList

------------------------------------------------------------------------------------------------------

isTerm :: TNF -> Bool
isTerm (Meta _)     = False
isTerm (TNF _ _ xs) = and $ isTerm <$> xs

allTNFGens :: Type -> [[TNF]]
allTNFGens tau = go [Meta tau]
  where
    go []  = []
    go atd =
      let atd1 = go $ concat $ unMeta [] <$> filter (not . isTerm) atd
       in atd : atd1

inhabGens :: Type -> [[TNF]]
inhabGens = fmap (filter isTerm) . allTNFGens

------------------------------------------------------------------------------------------------------

int2TVarName :: Int -> Symb
int2TVarName n
  | n < 0     = undefined
  | n < 26    = [['a'..'z'] !! n]
  | otherwise = ['a'..'z'] !! (n `mod` 26) : int2TVarName (n `div` 26)

tvarName2Int :: Symb -> Int
tvarName2Int []       = 0
tvarName2Int (x : xs) = (ord x - 97) + 26 * tvarName2Int xs

getInitInt :: Type -> Int
getInitInt tau = case fmap tvarName2Int . notIntersTVarName $ tau of
                   []      -> 0
                   idxList -> succ . maximum $ idxList 
  where
    notIntersTVarName :: Type -> [Symb]
    notIntersTVarName (TVar name)       = [name]
    notIntersTVarName (sigma1 :-> sigma2) = notIntersTVarName sigma1 ++ notIntersTVarName sigma2
    --the type [(a :-> b) :&: c] is impossible in lambda()
    --check arrows in intersect?
    notIntersTVarName (sigma1 :&: sigma2) = notIntersTVarName sigma1 ++ notIntersTVarName sigma2

intersect2simple :: Type -> Type
intersect2simple tau = (\(_, _, x) -> x) $ go empty (getInitInt tau) tau
  where
    go :: Map Type Symb -> Int -> Type -> (Map Type Symb, Int, Type)
    go dict st tau@(TVar _)        = (dict, st, tau)
    go dict st (sigma1 :-> sigma2) =
      let (dict1, st1, tau1) = go dict st sigma1
          (dict2, st2, tau2) = go dict1 st1 sigma2
       in (dict2, st2, tau1 :-> tau2)
    go dict st sigma@(_ :&: _) =
      maybe
        (let name = int2TVarName st in (insert sigma name dict, succ st, TVar name))
        (\x -> (dict, st, TVar x))
        (lookup sigma dict)

------------------------------------------------------------------------------------------------------

inhabs :: Type -> [TNF]
inhabs = concat . inhabGens . intersect2simple

------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------

