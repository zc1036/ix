
module ReversibleMap where

import qualified Data.Map as Map
import Data.Map (Map, empty, lookup, insert, toList)
import Data.List (delete)
import Data.Maybe (fromJust)

type Keys k = Map Int [k]

data RMap k v = RMap Int (Map k Int) (Map Int v) (Keys k)

rempty :: RMap k v
rempty = RMap 0 empty empty empty

rlookup :: (Ord k) => k -> RMap k v -> Maybe v
rlookup k (RMap _ m1 m2 _) =
    case Map.lookup k m1 of
      Nothing -> Nothing
      Just k2 -> Map.lookup k2 m2

ksRemove :: Eq k => Int -> k -> Keys k -> Keys k
ksRemove i k ks =
    case Map.lookup i ks of
      Nothing -> ks
      Just lst ->
          insert i (delete k lst) ks

ksAdd :: Int -> k -> Keys k -> Keys k
ksAdd i k ks =
    case Map.lookup i ks of
      Nothing -> insert i [k] ks
      Just old -> insert i (k:old) ks

keyGet :: (Ord k) => k -> RMap k v -> Maybe Int
keyGet k (RMap _ m1 _ _) =
    Map.lookup k m1 

rinsertnew :: (Ord k) => k -> v -> RMap k v -> RMap k v
rinsertnew k v rm@(RMap i m1 m2 ks) =
    let newid = i
        m1' = insert k newid m1
        m2' = insert newid v m2
    in case keyGet k rm of
         Nothing ->
             RMap (i + 1) m1' m2' (ksAdd newid k ks)
         Just oldid ->
             RMap (i + 1) m1' m2' (ksAdd newid k (ksRemove oldid k ks))

rinsert :: (Ord k) => k -> v -> RMap k v -> RMap k v
rinsert k v rm@(RMap i m1 m2 ks) =
    case keyGet k rm of
      Nothing -> rinsertnew k v rm
      Just key ->
          RMap i m1 (insert key v m2) ks

rassociate :: (Ord k) => k -> k -> RMap k v -> RMap k v

rassociate k1 k2 rm@(RMap i m1 m2 ks) =
    case keyGet k1 rm of
      Nothing ->
          RMap (i + 1) (insert k1 i (insert k2 i m1)) m2 ks'
      Just key ->
          RMap i (insert k2 key m1) m2 ks'
    where
      ks' = case keyGet k2 rm of
              Nothing -> ksAdd i k1 (ksAdd i k2 ks)
              Just oldkey ->
                  ksAdd i k1 (ksAdd i k2 (ksRemove oldkey k2 ks))

rtoList :: RMap k v -> [(k, Maybe v)]
rtoList (RMap _ m1 m2 _) =
    let f (k, v) = (k, Map.lookup v m2) in
    map f $ toList m1
