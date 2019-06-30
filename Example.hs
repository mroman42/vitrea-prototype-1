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

module Example where

import           Vitrea



-- The data structures.
data PostalAddr = PostalAddr
  { street' :: String
  , code'   :: String
  , city'   :: String
  }

type Address = String
type Street = String
type ZipCode = String

instance Show PostalAddr where
  show (PostalAddr s z c) =
    "   Street:   " ++ s ++
    "\n   Code:     " ++ z ++
    "\n   City:     " ++ c


-- A lens that allows us to see the street from an adress.
-- And a prism that tries to match an address into a postal one.
zipcode :: ProfLens' PostalAddr ZipCode
zipcode = mkLens $ ExOptic viewCode updateCode
  where
    viewCode    p      = (p , code' p)
    updateCode (p , s) = p {code' = s}

street :: ProfLens' PostalAddr Street
street = mkLens $ ExOptic viewStreet updateStreet
  where
    viewStreet    p      = (p , street' p)
    updateStreet (p , s) = p {street' = s}


postal :: ProfPrism' Address PostalAddr
postal = mkPrism $ ExOptic matchPostal buildPostal
  where
    matchPostal :: Address -> Either Address PostalAddr
    matchPostal a = case matchPostal' a of
                      Nothing -> Left a
                      Just x  -> Right x
    matchPostal' :: Address -> Maybe PostalAddr
    matchPostal' a = do
      (street, b) <- readUntilComma a
      (city, c) <- readUntilComma (tail $ tail b)
      return $ PostalAddr street city (tail $ tail c)
        where
          readUntilComma a =
             if elem ',' a
               then Just (takeWhile (/= ',') a, dropWhile (/= ',') a)
               else Nothing

    buildPostal :: Either Address PostalAddr -> Address
    buildPostal (Left a)                   = a
    buildPostal (Right (PostalAddr s t c)) = s ++ ", " ++ t ++ ", " ++ c


-- Now some combinators.
data CrAff s t a b = CrAff
  { original :: s
  , get      :: Maybe a
  , set      :: Maybe (b -> t)
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


infixr 8 ^.
infixl 6 <~
infixl 6 <~~


-------------
-- EXAMPLE --
-------------
--  "High Street, OX46NA, Oxford"^.postal.street
--    >> "High Street"
--  "High Street, OX46NA, Oxford"^.postal.street <~ "Banbury Road"
--    >> "Banbury Road, OX46NA, Oxford"
--  "High Street, OX46NA, Oxford"^.postal.zipcode <~~ (++ "-UK")
--    >> "High Street, OX46NA-UK, Oxford"
-------------
