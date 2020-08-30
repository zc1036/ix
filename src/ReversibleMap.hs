
module ReversibleMap where

import qualified Data.Map as Map
import Data.Map (Map, lookup)
import Data.Maybe (fromJust, fromMaybe)
import qualified Data.Set as Set
import Data.Set (Set, fromList, union)

type Keys k = Map Int (Set k)

data RMap k v = RMap Int (Map k Int) (Map Int v) (Keys k)

rempty :: RMap k v
rempty = RMap 0 Map.empty Map.empty Map.empty

rlookup :: (Ord k) => k -> RMap k v -> Maybe v
rlookup k (RMap _ m1 m2 _) =
    case Map.lookup k m1 of
      Nothing -> Nothing
      Just k2 -> Map.lookup k2 m2

ksRemove :: (Eq k, Ord k) => Int -> k -> Keys k -> Keys k
ksRemove i k ks =
    case Map.lookup i ks of
      Nothing -> ks
      Just set ->
          Map.insert i (Set.delete k set) ks

ksAdd :: Ord k => Int -> k -> Keys k -> Keys k
ksAdd i k ks =
    case Map.lookup i ks of
      Nothing -> Map.insert i (Set.singleton k) ks
      Just old -> Map.insert i (Set.insert k old) ks

ksGet :: Int -> Keys k -> Maybe (Set k)
ksGet i ks = Map.lookup i ks

keyGet :: (Ord k) => k -> RMap k v -> Maybe Int
keyGet k (RMap _ m1 _ _) = Map.lookup k m1

rinsertnew :: (Ord k) => k -> v -> RMap k v -> RMap k v
rinsertnew k v rm@(RMap i m1 m2 ks) =
    let newid = i
        m1' = Map.insert k newid m1
        m2' = Map.insert newid v m2
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
          RMap i m1 (Map.insert key v m2) ks

rassociate' :: (Ord k) => Int -> [k] -> RMap k v -> RMap k v
rassociate' _ [] rm = rm
rassociate' k1_key (k2:k2s) rm@(RMap i m1 m2 ks) =
    let m1' = Map.insert k2 k1_key m1
    in rassociate' k1_key k2s (RMap i m1' m2 ks)

rassociate :: (Ord k) => k -> k -> RMap k v -> RMap k v
rassociate k1 k2 rm@(RMap i m1 m2 ks) =
    let k1_key = fromMaybe i $ keyGet k1 rm
        k2_key = fromMaybe (-1) $ keyGet k2 rm
        m1' = Map.insert k1 k1_key m1 -- Map.Insert even if already exists
        i' = i + 1 -- Increment even if we don't need to
        k1_otherkeys = fromMaybe Set.empty $ ksGet k1_key ks
        k2_otherkeys = fromMaybe Set.empty $ ksGet k2_key ks
        ks' = Map.insert k1_key ((Set.fromList [k1, k2]) `union` k1_otherkeys `union` k2_otherkeys) (Map.delete k2_key ks)
    in rassociate' k1_key (k2:Set.toList k2_otherkeys) (RMap i' m1' m2 ks')

rtoList :: RMap k v -> [(k, Int, Maybe v)]
rtoList (RMap _ m1 m2 _) =
    let f (k, v) = (k, v, Map.lookup v m2) in
    map f $ Map.toList m1
