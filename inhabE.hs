--lambda(/\E)
import Data.Char (ord)
import Data.List (nub)


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

-----------------------------------------------------------------------------------------------------

uncurry2List :: Type -> (Symb, [Type])
uncurry2List (TVar symb)    = (symb, [])
uncurry2List (arg :-> args) = (arg :) <$> uncurry2List args
uncurry2List (arg :&: args) = error "uncurry2List :&:" 

uncurry2RevList  :: Type -> [(Symb, [Type])]
uncurry2RevList = go (undefined, [])
  where
    go :: (Symb, [Type]) -> Type -> [(Symb, [Type])]
    go (_, acc) (TVar symb)    = [(symb, acc)]
    go (_, acc) (arg :-> args) = go (undefined, arg : acc) args
    go (_, acc) (arg :&: args) = go (undefined, acc) arg ++ go (undefined, acc) args

-----------------------------------------------------------------------------------------------------

suitTypesWithId :: (Symb, [Type]) -> [(Int, Type)]
suitTypesWithId (alpha, sigmas) = filter (elem alpha . lastType . snd) (getId sigmas)
  where
    lastType :: Type -> [Symb]
    lastType (TVar symb)    = [symb]
    lastType (_ :-> args)   = lastType args
    lastType (arg :&: args) = lastType arg ++ lastType args

getId :: [Type] -> [(Int, Type)]
getId = concatMap eliminate . zip [0..] . nub
  where
    eliminate :: (Int, Type) -> [(Int, Type)]
    eliminate arg@(_, TVar _)     = [arg]
    eliminate (idx, arg :-> args) = fmap (arg :->) <$> eliminate (idx, args)
    eliminate (idx, arg :&: args) = (idx, arg) : eliminate (idx, args)

-----------------------------------------------------------------------------------------------------

unMeta :: Ctx -> TNF -> [TNF]
unMeta zetas (Meta mtype) = concatMap go alphaSigmasList
  where
     alphaSigmasList = uncurry2RevList mtype
     go :: (Symb, [Type]) -> [TNF]
     go alphaSigmas =
       let isigmas         = suitTypesWithId . fmap (++ zetas) $ alphaSigmas
           iYs             = fmap (fmap Meta . snd . uncurry2List) <$> isigmas
        in uncurry (TNF . snd $ alphaSigmas) <$> iYs
unMeta zetas (TNF abst headId tails) =
  let tnfList = unMeta (abst ++ zetas) <$> tails
   in TNF abst headId <$> sequence tnfList

-----------------------------------------------------------------------------------------------------

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

inhabs :: Type -> [TNF]
inhabs = nub . concat . inhabGens

-----------------------------------------------------------------------------------------------------
-----------------------------------------------------------------------------------------------------

