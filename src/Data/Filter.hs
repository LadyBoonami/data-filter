{-# LANGUAGE DeriveFunctor
           , DeriveGeneric
           , FlexibleContexts
           , FlexibleInstances
           , FunctionalDependencies
           , KindSignatures
           , MultiParamTypeClasses
           , ScopedTypeVariables
           , TypeOperators
           , TypeSynonymInstances
           , UndecidableInstances
           #-}

{-|
Module      : Data.Filter
Description : Utilities for filtering
Copyright   : (c) Sophie Hirn, 2018
License     : BSD2
Maintainer  : sophie.hirn@wyvernscale.com

Some helpers to make using Prelude.filter and similar value selection a bit
easier. Includes combinators for predicates as well as an operator to match
the constructor used for the given value.
-}

module Data.Filter
    ( -- * Constructors
      -- | The @(=?=)@-operator can be used to check whether two values were
      --   generated using the same constructor. For this to work, the
      --   underlying data type must instantiate 'GHC.Generics.Generic',
      --   parameters to the constructor can additionally be left out if their
      --   type implements 'ReduceWith'.
      constrName
    , HasConstructor (..)
      -- * Reduction
      -- | Constructors can be /reduced/ to values by passing them arbitrary
      --   arguments. The actual value of those does not impact the result of
      --   the @(=?=)@-operator. For lazy members, passing 'undefined' works
      --   just fine, but putting 'undefined' into strict fields causes carnage.
      --   'ReduceWith' provides arbitrary values, deriving from `Default` where
      --   possible.
    , ReduceWith (..)
    , Reduce (..)
      -- * Operators
    , (=?=)
    , (==>)
    , (<||>)
    , any_
    , (<&&>)
    , all_
      -- * Matching Wrappers
    , Infinite (..)
      -- * Useful functions from other modules
    , mapMaybe
    ) where


import Control.Monad
import Data.Default
import Data.List
import Data.Maybe
import GHC.Generics



-- | Retrieve the constructor name of the given value as a string. This
--   implementation is taken from https://stackoverflow.com/questions/48179380/getting-the-data-constructor-name-as-a-string-using-ghc-generics .
constrName :: (HasConstructor (Rep a), Generic a) => a -> String
constrName = genericConstrName . from

-- | Automatically derived from 'Generic' instances.
class HasConstructor (f :: * -> *) where
    genericConstrName :: f x -> String

instance HasConstructor f => HasConstructor (D1 c f) where
    genericConstrName (M1 x) = genericConstrName x

instance (HasConstructor x, HasConstructor y) => HasConstructor (x :+: y) where
    genericConstrName (L1 l) = genericConstrName l
    genericConstrName (R1 r) = genericConstrName r

instance Constructor c => HasConstructor (C1 c f) where
    genericConstrName x = conName x

-- end from



-- | Type that can be reduced away from a constructor. Use this to make your
--   data types compatible. The reduction process and the @(=?=)@-operator do
--   not evaluate fields, therefore creating an empty instance which defaults to
--   @'reduceWith' = 'undefined'@ is okay __as long as no reduced field of__
--   __this type is strict__.
class ReduceWith a where
    reduceWith :: a
    reduceWith = undefined

instance {-# OVERLAPPING  #-} ReduceWith Bool where
    reduceWith = True

instance {-# OVERLAPPING  #-} ReduceWith Char where
    reduceWith = ' '

instance {-# OVERLAPPABLE #-} (Default a) => ReduceWith a where
    reduceWith = def



-- | Reduction of a constructor @a -> ... -> c@ to a value of type @c@.
class (HasConstructor (Rep c), Generic c) => Reduce a c | a -> c where
    reduce :: a -> c

instance {-# OVERLAPPABLE #-} (HasConstructor (Rep a), Generic a) => Reduce a a where
    reduce = id

instance {-# OVERLAPPABLE #-} (ReduceWith a, Reduce b c) => Reduce (a -> b) c where
    reduce = reduce . ($ reduceWith)



-- | Checks whether two values are created by the same data constructor. Also
--   works with constructors that have not yet received all their arguments.
--   This allows for very convenient constructs, e.g.:
--
-- >>> Just 1 =?= Just
-- True
--
-- >>> Just 1 =?= Nothing
-- False
--
-- >>> let filterJust = filter (=?= Just)
-- >>> filterJust [Just 1, Nothing, Just 9001]
-- [Just 1, Just 9001]
--
-- >>> let filterJust_ = mapMaybe $ (=?= Just) ==> fromJust
-- >>> filterJust_ [Just 1, Nothing, Just 9001]
-- [1, 9001]
--
-- >>> let over9000 = mapMaybe $ ((=?= Just) <&&> (>9000) . fromJust) ==> fromJust
-- >>> over9000 [Just 1, Nothing, Just 9001]
-- [9001]
(=?=) :: (Reduce a c, Reduce b c) => a -> b -> Bool
infixl 4 =?=
(=?=) a b = constrName (reduce a) == constrName (reduce b)



-- | @(pred ==> f) x@ returns @'Just' (f x)@ if @pred x@ succeeds and
--   @'Nothing'@ otherwise.
(==>) :: (a -> Bool) -> (a -> b) -> a -> Maybe b
(==>) p f x = if p x then Just $ f x else Nothing



(<||>) :: (a -> Bool) -> (a -> Bool) -> a -> Bool
infixl 2 <||>
(<||>) = liftM2 (||)

any_ :: [a -> Bool] -> a -> Bool
any_ = foldl' (<||>) $ const False

(<&&>) :: (a -> Bool) -> (a -> Bool) -> a -> Bool
infixl 3 <&&>
(<&&>) = liftM2 (&&)

all_ :: [a -> Bool] -> a -> Bool
all_ = foldl' (<&&>) $ const True



-- | Adds negative and positive infinity to an ordered type. The 'fromEnum'
--   function is inherently susceptible to overflow since the class 'Enum' is
--   defined using 'Int' instead of 'Integer', but this should not cause trouble
--   with \"small\" enums.
data Infinite a
    = NegInfin
    | Exact !a
    | PosInfin
    deriving (Eq, Functor, Read, Show, Ord, Generic)

instance (Eq a, Bounded a, Enum a) => Enum (Infinite a) where
    fromEnum NegInfin  = fromEnum (minBound :: a) - 1
    fromEnum (Exact x) = fromEnum x
    fromEnum PosInfin  = fromEnum (maxBound :: a) + 1

    toEnum x | x == fromEnum (minBound :: a) - 1 = NegInfin
             | x == fromEnum (maxBound :: a) + 1 = PosInfin
             | otherwise                         = Exact $ toEnum x

    succ NegInfin = Exact minBound
    succ PosInfin = PosInfin
    succ (Exact x)
        | x == maxBound = PosInfin
        | otherwise     = Exact $ succ x

    pred NegInfin = NegInfin
    pred PosInfin = Exact maxBound
    pred (Exact x)
        | x == minBound = NegInfin
        | otherwise     = Exact $ pred x

instance (Default a) => Default (Infinite a) where
    def = Exact def
