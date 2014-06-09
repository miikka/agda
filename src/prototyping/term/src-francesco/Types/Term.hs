{-# OPTIONS_GHC -fno-warn-orphans #-}
module Types.Term where

import           Prelude                          hiding (pi)

import           Bound                            hiding (instantiate)
import           Data.Foldable                    (Foldable)
import           Data.Traversable                 (Traversable)
import           Prelude.Extras                   (Eq1((==#)))
import           Data.Void                        (Void)
import           Data.Monoid                      ((<>), mconcat, mempty)
import qualified Data.HashSet                     as HS
import           Control.Monad                    (liftM)
import           Data.Typeable                    (Typeable)

import qualified Text.PrettyPrint.Extended        as PP
import           Syntax.Abstract                  (Name)
import           Syntax.Abstract.Pretty           ()
import           Types.Var
import           Types.Definition

-- Terms
------------------------------------------------------------------------

-- | A 'Head' heads a neutral term -- something which can't reduce
-- further.
data Head v
    = Var v
    | Def Name
    | J
    | Meta MetaVar
    deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

instance (IsVar v) => PP.Pretty (Head v) where
    pretty (Var v)   = PP.text (show (varIndex v) ++ "#") <> PP.pretty (varName v)
    pretty (Def f)   = PP.pretty f
    pretty J         = PP.text "J"
    pretty (Meta mv) = PP.pretty mv

instance Eq1 Head

-- | 'Elim's are applied to 'Head's.  They're either arguments applied
-- to functions, or projections applied to records.
data Elim term v
    = Apply (term v)
    | Proj Name Field
    deriving (Show, Eq, Functor, Foldable, Traversable)

instance (Eq1 term) => Eq1 (Elim term) where
    Apply t1   ==# Apply t2   = t1 ==# t2
    Proj n1 f1 ==# Proj n2 f2 = n1 == n2 && f1 == f2
    _          ==# _          = False

instance Bound Elim where
    Apply t      >>>= f = Apply (t >>= f)
    Proj n field >>>= _ = Proj n field

instance (IsTerm t, IsVar v) => PP.Pretty (Elim t v) where
    prettyPrec p (Apply e)  = PP.prettyPrec p $ view e
    prettyPrec _ (Proj n _) = PP.text $ show n

data TermView term v
    = Lam (Abs term v)
    | Pi (term v) (Abs term v)
    | Equal (term v) (term v) (term v)
    | Refl
    | Con Name [term v]
    | Set
    | App (Head v) [Elim term v]

deriving instance (IsTerm term) => Functor (TermView term)
deriving instance (IsTerm term) => Foldable (TermView term)
deriving instance (IsTerm term) => Traversable (TermView term)

instance (Eq v, IsTerm t) => Eq (TermView t v) where
    t1 == t2 = t1 ==# t2

instance (IsTerm term) => Eq1 (TermView term) where
    Lam body1 ==# Lam body2 =
        body1 ==# body2
    Pi domain1 codomain1 ==# Pi domain2 codomain2 =
        domain1 ==# domain2 && codomain1 ==# codomain2
    Equal type1 x1 y1 ==# Equal type2 x2 y2 =
        type1 ==# type2 && x1 ==# x2 && y1 ==# y2
    App h1 els1 ==# App h2 els2 =
        h1 == h2 && and (zipWith (==#) els1 els2)
    Set ==# Set =
        True
    _ ==# _ =
        False

type ClosedTermView term = TermView term Void

instance (IsTerm t, IsVar v) => PP.Pretty (TermView t v) where
  prettyPrec p t = case t of
    Set ->
      PP.text "Set"
    Equal a x y ->
      PP.prettyApp p (PP.text "_==_") [view a, view x, view y]
    Pi a0 b0 ->
      let a = view a0
          b = view $ fromAbs b0
          n = getName b
      in PP.condParens (p > 0) $
          PP.sep [ PP.parens (PP.pretty n <> PP.text " : " <> PP.pretty a) PP.<+>
                   PP.text "->"
                 , PP.nest 2 $ PP.pretty b
                 ]
    Lam b0 ->
      let b = view $ fromAbs b0
          n = getName b
      in PP.condParens (p > 0) $
         PP.sep [ PP.text "\\" <> PP.pretty n <> PP.text " ->"
                , PP.nest 2 $ PP.pretty b
                ]
    App h es ->
      PP.prettyApp p (PP.pretty h) es
    Refl ->
      PP.text "refl"
    Con dataCon args ->
      PP.prettyApp p (PP.pretty dataCon) (map view args)

instance (IsTerm t) => PP.Pretty (Definition t) where
  pretty _ = PP.text "TODO Pretty Definition"

-- Term typeclass
------------------------------------------------------------------------

class MetaVars t where
    metaVars :: t v -> HS.HashSet MetaVar

    default metaVars :: (View t, HasAbs t) => t v -> HS.HashSet MetaVar
    metaVars t = case view t of
        Lam body           -> metaVars (fromAbs body)
        Pi domain codomain -> metaVars domain <> metaVars (fromAbs codomain)
        Equal type_ x y    -> metaVars type_ <> metaVars x <> metaVars y
        App h elims        -> metaVars h <> mconcat (map metaVars elims)
        Set                -> mempty
        Refl               -> mempty
        Con _ elims        -> mconcat (map metaVars elims)

instance MetaVars Head where
    metaVars (Meta mv) = HS.singleton mv
    metaVars _         = mempty

instance MetaVars t => MetaVars (Elim t) where
    metaVars (Apply t)  = metaVars t
    metaVars (Proj _ _) = mempty

class (Monad t) => HasAbs t where
    data Abs t :: * -> *

    toAbs   :: t (TermVar v) -> Abs t v
    fromAbs :: Abs t v -> t (TermVar v)

    -- Methods present in the typeclass so that the instances can
    -- support a faster version.

    weaken :: t v -> Abs t v
    weaken = toAbs . liftM F

    instantiate :: Abs t v -> t v -> t v
    instantiate abs' t = fromAbs abs' >>= \v -> case v of
        B _  -> t
        F v' -> return v'

    abstract :: (Eq v, VarName v) => v -> t v -> Abs t v
    abstract v t = toAbs $ liftM f t
      where
        f v' = if v == v' then boundTermVar (varName v) else F v'

class View t where
    unview :: TermView t v -> t v
    view   :: t v -> TermView t v

class ( Eq1 t,       Functor t,       Foldable t,       Traversable t, Monad t, Typeable t
      , Eq1 (Abs t), Functor (Abs t), Foldable (Abs t), Traversable (Abs t)
      , View t, MetaVars t, HasAbs t
      ) => IsTerm t

deriving instance Typeable Abs

-- Term utils
-------------

lam :: View t => Abs t v -> t v
lam body = unview $ Lam body

pi :: View t => t v -> Abs t v -> t v
pi domain codomain = unview $ Pi domain codomain

equal :: View t => t v -> t v -> t v -> t v
equal type_ x y = unview $ Equal type_ x y

app :: View t => Head v -> [Elim t v] -> t v
app h elims = unview $ App h elims

set :: View t => t v
set = unview Set

var :: View t => v -> t v
var v = unview (App (Var v) [])

metaVar :: View t => MetaVar -> [Elim t v] -> t v
metaVar mv = unview . App (Meta mv)

def :: View t => Name -> [Elim t v] -> t v
def f = unview . App (Def f)

con :: View t => Name -> [t v] -> t v
con c args = unview (Con c args)

refl :: View t => t v
refl = unview Refl

renderView :: (IsVar v, IsTerm t) => t v -> String
renderView = PP.render . view

prettyView :: (IsVar v, IsTerm t) => t v -> PP.Doc
prettyView = PP.pretty . view

-- Useful type synonyms
-----------------------

type Type (t :: * -> *) = t
type Term (t :: * -> *) = t
