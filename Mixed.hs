{-# LANGUAGE AllowAmbiguousTypes       #-}
{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE FunctionalDependencies    #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE ImplicitParams            #-}
{-# LANGUAGE IncoherentInstances       #-}
{-# LANGUAGE KindSignatures            #-}
{-# LANGUAGE LiberalTypeSynonyms       #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE StandaloneDeriving        #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE TypeSynonymInstances      #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE UndecidableSuperClasses   #-}

import Prelude hiding ()
import Data.Constraint

-- Definitions on enriched category theory from Day's "On closed
-- categories".

-- Please let me know if you plan to use this file or take ideas from
-- here.

-- A V-enriched category, whose objects are given by a constraint.
class Category c where
  type Obj c a :: Constraint
  id :: (Obj c x) => c x x
  comp :: (Obj c x) => c x y -> c y z -> c x z

-- A V-functor, a bifunctor, a profunctor.
class (Category (Dom f), Category (Cod f)) => Functor f where
  type Dom f :: * -> * -> *
  type Cod f :: * -> * -> *
  fmap :: (Obj (Dom f) x, Obj (Cod f) y, Obj (Cod f) (f x), Obj (Cod f) (f y))
       => (Dom f) x y -> (Cod f) (f x) (f y)

class (Category (Dom1 f), Category (Dom2 f), Category (Codb f)) => Bifunctor f where
  type Dom1 f :: * -> * -> *
  type Dom2 f :: * -> * -> *
  type Codb f :: * -> * -> *
  bimap :: (Obj (Dom1 f) x1, Obj (Dom1 f) x2, Obj (Dom2 f) y1, Obj (Dom2 f) y2,
            Obj (Codb f) (f x1 y1), Obj (Codb f) (f x2 y2))
        => c x1 x2 -> d y1 y2 -> e (f x1 y1) (f x2 y2)

class (Category (LDom p), Category (RDom p)) => Profunctor p where
  type LDom p :: * -> * -> *
  type RDom p :: * -> * -> *
  dimap :: (Obj (LDom p) x1, Obj (LDom p) x2, Obj (RDom p) y1, Obj (RDom p) y2)
        => c x2 x1 -> d y1 y2 -> p x1 y1 -> p x2 y2

-- V-monoidal category.
class (Category m
      , Bifunctor (Tensor m), m ~ Dom1 (Tensor m), m ~ Dom2 (Tensor m), m ~ Codb (Tensor m)
      , Obj m (Unit m))
      => MonoidalCategory m where
  type Tensor m :: * -> * -> *
  type Unit m :: *

  alpha :: (Obj m x, Obj m y, Obj m z)
        => m (x `o` (y `o` z)) ((x `o` y) `o` z)
  lambda :: (Obj m x) => m (x `o` i) x
  rho :: (Obj m x) => m (i `o` x) x

-- V-monoidal action                        
class ( MonoidalCategory (Maction f), Category (Caction f)
      , Bifunctor f , Dom1 f ~ (Maction f) , Dom2 f ~ (Caction f) , Codb f ~ (Caction f)
      ) => MonoidalAction f where
  type Maction f :: * -> * -> *
  type Caction f :: * -> * -> *
  unitor :: (Obj (Caction f) x) => (Caction f) (f i x) x
  multiplicator :: (Obj (Caction f) x, Obj (Maction f) p, Obj (Maction f) q)
                => c (f p (f q x)) (f ((tensor m) p q) x)

-- Existential mixed V-optics
data Optic f g a b s t where
  Optic :: ( MonoidalAction f
           , MonoidalAction g
           , Maction f ~ Maction g
           , Obj (Maction f) m
           , Obj (Caction f) a, Obj (Caction f) s
           , Obj (Caction g) b, Obj (Caction g) t
           )
        => c s ((f m) a) -> d ((g m) b) t -> Optic f g a b s t


-- --------------
-- -- EXAMPLES --
-- --------------
instance Category (->) where
  type Obj (->) a = ()
  id = \x -> x
  comp = \f g x -> g (f x)

-- instance MonoidalCategory (->) where
--   type Tensor (->) a = 

-- instance Category (->) where
--   type Obj (->) a = ()
--   id = \x -> x
--   comp = (.)


