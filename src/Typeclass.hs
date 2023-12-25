
module Typeclass where

import Data.Traversable
import Data.Foldable
import Data.Set qualified as Set
import Control.Unification
import Polysemy
import Polysemy.Error
import Polysemy.State
import GHC.Generics (Generic1)
import Data.Tree

data Constraint n t v = Constraint
  { label    :: n
  , priority ::  Float
  , preqs    :: [Term t v]
  , header   ::  Term t v
  }
  deriving stock
    ( Generic1
    , Functor
    , Foldable
    , Traversable
    )

deriving instance (Eq  n, Eq  v, Eq  (t (Term t v))) => Eq  (Constraint n t v)
deriving instance (Ord n, Ord v, Ord (t (Term t v))) => Ord (Constraint n t v)

data CallTree n it
  = Use n
  | App it [it]
  deriving stock
    ( Generic1
    , Functor
    , Foldable
    , Traversable
    )
  deriving anyclass (Unifiable)

deriving instance Unifiable []

indent :: String -> String
indent = unlines . map ("  " ++) . lines

instance (Show n, Show it) => Show (CallTree n it) where
  show = \case
    Use s -> show s ++ "\n"
    App f xs -> concat (show f : map (indent . show) xs)

type Solution n t v = Term (CallTree n) (Term t v)

tryDischarge
  :: ( Members '[Unifies t v, Refreshes v] r
     , Ord (t (Term t v))
     , Traversable t
     , Ord v
     )
  => Term t v
  -> Scheme (Constraint n t) v
  -> Sem r (n, [Term t v])
tryDischarge goal constr = do
  constr <- instantiate constr
  constr.header =:= goal
  return (constr.label, constr.preqs)

discharge
  :: forall n t v r
  .  ( Members '[Unifies t v, Refreshes v, Error (Mismatch t v)] r
     , Ord (t (Term t v))
     , Traversable t
     , Ord v
     )
  => Term t v
  -> [Scheme (Constraint n t) v]
  -> Sem r (Solution n t v, Set.Set (Term t v))
discharge goal constrs = loop constrs
  where
    loop
      :: [Scheme (Constraint n t) v]
      -> Sem r (Term (CallTree n) (Term t v), Set.Set (Term t v))
    loop [] = do
      apply goal
      return (Var goal , Set.singleton goal)

    loop (c : cs) = do
      state <- save @t @v
      catch @(Mismatch t v) do
          (f , preqs) <- tryDischarge goal c
          (xs , moar) <- unzip <$> for preqs (`discharge` constrs)
          return (Struct (App (Struct (Use f)) xs) , fold moar)
        \Mismatch{} -> do
          restore state
          loop cs

data Type_ it
  = Const_ String
  | App_ it it
  deriving stock
    ( Functor
    , Foldable
    , Traversable
    , Generic1
    , Eq
    , Ord
    )
  deriving anyclass
    ( Unifiable
    )

instance Show it => Show (Type_ it) where
  show = \case
    Const_ s -> s
    App_   f x -> "(" ++ show f ++ " " ++ show x ++ ")"

type Type = Term Type_ String

infixl 1 $$
($$) :: Type -> Type -> Type
f $$ x = Struct (App_ f x)

c :: String -> Type
c = Struct . Const_

v :: String -> Type
v = Var

test
  :: (Members
        '[ Unifies Type_ String
         , Refreshes String
         , Error (Mismatch Type_ String)
         ]
        r)
  => Sem r (Solution String Type_ String, [Type])
test = do
  (f , results) <- discharge (c "Eq" $$ (c "List" $$ (c "Pair" $$ c "Int" $$ c "String")))
    [ Scheme ["a"] Constraint
        { label    = "eq-list"
        , priority = 0
        , preqs    = [ c "Eq" $$ v "a" ]
        , header   =   c "Eq" $$ (c "List" $$ v "a")
        }
    , Scheme ["b", "c"] Constraint
        { label    = "eq-pair"
        , priority = 0
        , preqs    = [ c "Eq" $$ v "b"
                     , c "Eq" $$ v "c" ]
        , header   =   c "Eq" $$ (c "Pair" $$ v "b" $$ v "c")
        }
    , Scheme [] Constraint
        { label    = "eq-str"
        , priority = 0
        , preqs    = []
        , header   = c "Eq" $$ c "String"
        }
    ]
  xs <- for (toList results) apply
  return (f, xs)

-- main = do
--   case runM test emptyUnifierState of
--     Left err -> putStrLn (show err)
--     Right ((f, terms), us) -> do
--       print f
--       for_ terms print
--       {-
--         Prints:
--           App_ (Const_ "Eq") (Const_ "String")
--       -}