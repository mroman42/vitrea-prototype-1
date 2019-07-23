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

module Vitrea where

import           Control.Monad.State
import           Data.Foldable
import           Data.Functor.Compose
import           Data.Functor.Identity
import           Data.Profunctor
import           Data.Void
import           GHC.Exts              hiding (toList)



-------------------------------------------
-- PROFUNCTOR/EXISTENTIAL REPRESENTATION --
-------------------------------------------
-- Existential optics.
data ExOptic mon a b s t where
  ExOptic :: (mon f) => (s -> f a) -> (f b -> t) -> ExOptic mon a b s t

-- A submonoid is unital if we can have some identity optic.  It is
-- functorial and multiplicative if we can create a bigger optic from
-- a small one.
class Tensorial mon where
  idOptic   :: ExOptic mon a b a b
  multOptic :: (mon f) => ExOptic mon a b s t -> ExOptic mon a b (f s) (f t)


-- Profunctor optics.
class (Profunctor p) => Tambara mon p where
  action :: forall f a b . (mon f) => p a b -> p (f a) (f b)

type ProfOptic mon a b s t = forall p . Tambara mon p => p a b -> p s t

-- Equivalence profunctor to existential.
instance Profunctor (ExOptic mon a b) where
  dimap u v (ExOptic l r) = ExOptic (l . u) (v . r)

instance (Tensorial mon) => Tambara mon (ExOptic mon a b) where
  action = multOptic

crOptic :: (Tensorial mon) => ProfOptic mon a b s t -> ExOptic mon a b s t
crOptic p = p idOptic

mkOptic :: forall mon a b s t . ExOptic mon a b s t -> ProfOptic mon a b s t
mkOptic (ExOptic l r) = dimap l r . (action @mon)


------------
-- OPTICS --
------------
-- Lenses.
class (f ~ ((,) (Arg f))) => Product f
class (f ~ ((,) (Arg f))) => Lens f
instance Product ((,) a)

instance Tensorial Product where
  idOptic = ExOptic ((,) ()) snd
  multOptic (ExOptic l r) = ExOptic (\(d,s) -> ((d , fst (l s)), snd (l s))) (\((d,c),b) -> (d,r (c,b)))

type ExLens   s t a b = ExOptic   Product a b s t
type ProfLens s t a b = ProfOptic Product a b s t
type ExLens'    t a   = ExOptic   Product a a t t
type ProfLens'  t a   = ProfOptic Product a a t t

mkLens :: forall a t . ExLens' t a -> ProfLens' t a
mkLens = mkOptic

-- Prisms.
class (f ~ (Either (Arg f))) => Sum f
instance Sum (Either a)

instance Tensorial Sum where
  idOptic = ExOptic Right (either absurd id)
  multOptic (ExOptic l r) = ExOptic
    (either (Left . Left) (either (Left . Right) Right . l))
    (either (either Left (Right . r . Left)) (Right . r . Right))

type ExPrism   s t a b = ExOptic   Sum a b s t
type ProfPrism s t a b = ProfOptic Sum a b s t
type ExPrism'    t a   = ExOptic   Sum a a t t
type ProfPrism'  t a   = ProfOptic Sum a a t t

mkPrism :: forall a t . ExPrism' t a -> ProfPrism' t a
mkPrism = mkOptic


-- Grates.
class (f ~ ((->) (Arg f))) => Exponential f
instance Exponential ((->) a)

instance Tensorial Exponential where
  idOptic = ExOptic const ($ ())
  multOptic (ExOptic l r) = ExOptic (\f (d , c) -> l (f d) c) ((r .) . curry)

type ExGrate   s t a b  = ExOptic   Exponential a b s t
type ProfGrate s t a b  = ProfOptic Exponential a b s t


-- Traversals.
instance Tensorial Traversable where
  idOptic   = ExOptic Identity runIdentity
  multOptic (ExOptic l r) = ExOptic (Compose . fmap l) (fmap r . getCompose)

type ExTraversal   s t a b = ExOptic   Traversable a b s t
type ProfTraversal s t a b = ProfOptic Traversable a b s t
type ExTraversal'    t a   = ExOptic   Traversable a a t t
type ProfTraversal'  t a   = ProfOptic Traversable a a t t

mkTraversal :: forall a t . ExTraversal' t a -> ProfTraversal' t a
mkTraversal = mkOptic

instance (Profunctor p , Tambara Traversable p) => Tambara AffineTransf p where
  action = dimap (Compose . unAff) (Aff . getCompose) . action @Traversable


-- Setters.
instance Tensorial Functor where
  idOptic = ExOptic Identity runIdentity
  multOptic (ExOptic l r) = ExOptic (Compose . fmap l) (fmap r . getCompose)

type ExSetter   s t a b = ExOptic   Functor a b s t
type ProfSetter s t a b = ProfOptic Functor a b s t


-- Affine, which is both Sum and Product.
data Aff a b c = Aff { unAff :: Either a (b , c) }
class (f ~ Aff (Arg1 f) (Arg2 f)) => AffineTransf f
instance AffineTransf (Aff a b)

instance Tensorial AffineTransf where
  idOptic   = ExOptic (Aff . Right . ((,) ())) (either absurd snd . unAff)
  multOptic (ExOptic l r) = ExOptic (u l) (v r)
    where
      u :: (s -> Aff c d a) -> Aff e f s -> Aff (Either e (f,c)) (f,d) a
      u l (Aff (Left e))      = Aff $ Left $ Left e
      u l (Aff (Right (f,s))) = Aff $ case unAff (l s) of
        (Left c)      -> (Left (Right (f,c)))
        (Right (d,a)) -> (Right ((f,d),a))
      v :: (Aff c d b -> t) -> Aff (Either e (f,c)) (f,d) b -> Aff e f t
      v r (Aff (Left  (Left e)))         = Aff $ Left e
      v r (Aff (Left  (Right (f,c))))    = Aff $ Right (f,r $ Aff $ Left c)
      v r (Aff (Right ((f,d),b)))        = Aff $ Right (f , r . Aff $ Right (d,b))

instance (Profunctor p , Tambara AffineTransf p) => Tambara Sum p where
  action = dimap
    (Aff . either (Left . id) (Right . ((,) ())))
    (either Left (Right . snd) . unAff)
    . action @AffineTransf

instance (Profunctor p , Tambara AffineTransf p) => Tambara Product p where
  action = dimap (Aff . Right) (either absurd id . unAff) . action @AffineTransf

type ExAffine   s t a b = ExOptic   AffineTransf a b s t
type ProfAffine s t a b = ProfOptic AffineTransf a b s t
type ExAffine'   t a = ExOptic   AffineTransf a a t t
type ProfAffine'  t a = ProfOptic AffineTransf a a t t



-- Glass.
data Gls a b c = Gls (a , b -> c)
class (f ~ Gls (Arg1 f) (Arg2 f)) => GlassTransf f
instance GlassTransf (Gls a b)


-- Achromatic lens.
data Achl a b = Achl (Maybe a , b)
class (f ~ Achl (Arg f)) => Achromatic f
instance Achromatic (Achl a)



-- -- Adapters.  (TODO: Composition of identities is not the identity, maybe we could use Yoneda)
-- class (f ~ Identity) => IsIdentity f
-- instance IsIdentity Identity

-- instance Tensorial IsIdentity where
--   idOptic = ExOptic coerce runIdentity
--   multOptic (ExOptic l r) = ExOptic _ _




-----------------
-- COMBINATORS --
-----------------
-- Now some combinators.
data CrAff s t a b = CrAff
  { aoriginal :: s
  , aget      :: Maybe a
  , aset      :: Maybe (b -> t)
  }

instance (Show s, Show a) => Show (CrAff s t a b) where
  show (CrAff o Nothing t)  = "Nothing"
  show (CrAff o (Just a) t) = show a

(^.) :: s -> ProfAffine s t a b -> CrAff s t a b
s ^. p = CrAff s (getter (crOptic p) s) (setter (crOptic p) s)
  where
    getter :: ExAffine s t a b -> s -> Maybe a
    getter (ExOptic l _) = either (const Nothing) (Just . snd) . unAff . l
    setter :: ExAffine s t a b -> s -> Maybe (b -> t)
    setter (ExOptic l r) =
      either (const Nothing)
        (Just . curry (r . Aff . Right) . fst) . unAff . l

(<~) :: CrAff s s a a -> a -> s
(<~) (CrAff s _ Nothing)  b = s
(<~) (CrAff _ _ (Just f)) b = f b

(<~~) :: CrAff s s a a -> (a -> a) -> s
(<~~) (CrAff s _ Nothing) g         = s
(<~~) (CrAff s Nothing _) g         = s
(<~~) (CrAff _ (Just a) (Just f)) g = f $ g a


data TrAff s t a b = TrAff
  { tor  :: s
  , tget :: [a]
  , tset :: [b] -> t
  }


(<~~~) :: TrAff s s a a -> (a -> a) -> s
(<~~~) (TrAff _ a f) g = f $ fmap g a


instance (Show s, Show a) => Show (TrAff s t a b) where
  show = show . tget

(^..) :: s -> ProfTraversal s t a b -> TrAff s t a b
s ^.. p = TrAff s (getter (crOptic p) s) (setter (crOptic p) s)
  where
    getter :: ExTraversal s t a b -> s -> [a]
    getter (ExOptic l _) = toList . l
    setter :: ExTraversal s t a b -> s -> [b] -> t
    setter (ExOptic l r) s list = r . fst . ($ 0) . runState . mapM (counter list) . l $ s
      where
        counter :: [b] -> a -> State Int b
        counter list _ = do
          n <- get
          modify (+1)
          return $ list !! n

infixr 8 ^.
infixr 8 ^..
infixl 6 <~
infixl 6 <~~
infixl 6 <~~~


-- Auxiliary functions
type family Arg  (x :: * -> *) where Arg  (f a)   = a
type family Arg1 (x :: * -> *) where Arg1 (f a b) = a
type family Arg2 (x :: * -> *) where Arg2 (f a b) = b
