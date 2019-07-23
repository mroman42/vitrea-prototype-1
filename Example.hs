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

import           Control.Arrow
import           Data.Char
import           Data.Foldable
import           Data.Functor.Compose
import           Text.Printf

-- The data structures.
data PostalAddr = PostalAddr
  { street' :: String
  , code'   :: String
  , city'   :: String
  }

data EmailAddr = EmailAddr
  { user'   :: String
  , domain' :: String
  }

data MailList = MailList
  { unMailList :: [(Name, Address, Subscription)]
  }

type Address = String
type Street = String
type ZipCode = String
type Domain = String
type Name = String
data Subscription = Daily | Monthly | Weekly deriving (Show)


instance Show PostalAddr where
  show (PostalAddr s z c) =
    " Street:   " ++ s ++
    "\n  Code:     " ++ z ++
    "\n  City:     " ++ c

instance Show EmailAddr where
  show (EmailAddr u d) =
    " User:" ++ u ++
    " Domain:" ++ d


someMailingList :: MailList
someMailingList = MailList
  [ ("Turing, Alan" , "turing@princeton.edu" , Daily)
  , ("Noether, Emily" , "emmynoether@fau.eu" , Monthly)
  , ("Gauss, Carl F." , "gauss@goettingen.de" , Weekly)
  ]

someAddress :: Address
someAddress = "High Street, OX46NA, Oxford"


-- Lenses.
-- We are explicitly writing down the view/update.
zipcode :: ProfLens' PostalAddr ZipCode
zipcode = mkLens $ ExOptic (id &&& code') (\(p , s) ->  p {code' = s})

street :: ProfLens' PostalAddr Street
street = mkLens $ ExOptic (id &&& street') (\(p , s) -> p {street' = s})

city :: ProfLens' PostalAddr Street
city = mkLens $ ExOptic (id &&& city') (\(p , s) -> p {city' = s})

domain :: ProfLens' EmailAddr Domain
domain = mkLens $ ExOptic (id &&& domain') (\(p , s) -> p {domain' = s})

-- Prisms.
postal :: ProfPrism' Address PostalAddr
postal = mkPrism $ ExOptic matchPostal buildPostal
  where
    matchPostal :: Address -> Either Address PostalAddr
    matchPostal a = maybe (Left a) Right $ do
      (street, b) <- readUntil ',' a
      (city, c)   <- readUntil ',' (tail $ tail b)
      return $ PostalAddr street city (tail $ tail c)
    buildPostal :: Either Address PostalAddr -> Address
    buildPostal (Left a)                   = a
    buildPostal (Right (PostalAddr s t c)) = s ++ ", " ++ t ++ ", " ++ c

email :: ProfPrism' Address EmailAddr
email = mkPrism $ ExOptic matchEmail buildEmail
  where
    matchEmail :: Address -> Either Address EmailAddr
    matchEmail a = maybe (Left a) Right $ do
      (u, d) <- readUntil '@' a
      return $ EmailAddr u $ tail d
    buildEmail :: Either Address EmailAddr -> Address
    buildEmail (Left a)                = a
    buildEmail (Right (EmailAddr u d)) = u ++ "@" ++ d


-- Traversals.
mails :: ProfTraversal' MailList Address
mails = mkTraversal $ ExOptic (\m -> Compose (m , fst $ extractAddr m)) set
  where
    extractAddr :: MailList -> ([Address], [Address] -> MailList)
    extractAddr (MailList m) = (map (\(_,a,_) -> a) m, MailList . fmap (\((n,_,s),a) -> (n,a,s)) . zip m)

    set :: (Compose ((,) MailList) []) Address -> MailList
    set (Compose (m , a)) = (snd $ extractAddr m) a

instance Show MailList where
  show = unlines
    . ((:) (printf "| %20s | %30s | %10s |" "Name" "Email" "Frequency"))
    . ((:) (replicate 70 '-'))
    . fmap (\(n,a,s) -> printf "| %20s | %30s | %10s |" n a (show s)) . unMailList





---------------
-- EXAMPLE 1 --
---------------
--  "15 Parks Rd, OX1 3QD, Oxford"^.postal.street
--    >> "High Street"
--  "High Street, OX46NA, Oxford"^.postal.street <~ "Banbury Road"
--    >> "Banbury Road, OX46NA, Oxford"
--  "High Street, OX46NA, Oxford"^.postal.zipcode <~~ (++ "(UK)")
--    >> "High Street, OX46NA(UK), Oxford"
---------------


---------------
-- EXAMPLE 2 --
---------------
-- someMailingList^..mails.email.domain <~~~ uppercase
--
-- >> |                 Name |                          Email |  Frequency |
-- >> ----------------------------------------------------------------------
-- >> |         Turing, Alan |           turing@PRINCETON.EDU |      Daily |
-- >> |       Noether, Emily |             emmynoether@FAU.EU |    Monthly |
-- >> |       Gauss, Carl F. |            gauss@GOETTINGEN.DE |     Weekly |
---------------

-- Auxiliary functions.
uppercase, lowercase :: String -> String
uppercase = fmap toUpper
lowercase = fmap toLower

readUntil :: Char -> String -> Maybe (String , String)
readUntil c a = if elem c a
  then Just (takeWhile (/= c) a, dropWhile (/= c) a)
  else Nothing
