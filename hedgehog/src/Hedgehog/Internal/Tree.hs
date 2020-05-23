{-# OPTIONS_HADDOCK not-home #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-} -- MonadBase
#if __GLASGOW_HASKELL__ < 802
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
#endif
module Hedgehog.Internal.Tree
--  (
--    Tree
--  , mapTreeT
--  , treeValue
--  , treeChildren
--
--  , Node
--  , pattern Node
--  , NodeT(..)
--  , fromNodeT
--
--  , unfold
--  , unfoldForest
--
--  , expand
--  , prune
--
--  , catMaybes
--  , filter
--  , mapMaybe
--  , filterMaybeT
--  , mapMaybeMaybeT
--  , filterT
--  , mapMaybeT
--  , depth
--  , interleave
--
--  , render
--  , renderT
--  )
  where

import           Control.Applicative (Alternative(..), liftA2)

import Control.Monad

import Data.Monoid
import qualified Data.List as List
import qualified Data.Maybe as Maybe

import           Hedgehog.Internal.Distributive
import           Control.Monad.Trans.Control (MonadBaseControl (..))

import           Prelude hiding (filter)

------------------------------------------------------------------------

data Tree a
  = Empty
  | Node a [Tree a]
  deriving (Eq, Show, Functor)

treeMaybe :: Tree a -> Maybe (a, [Tree a])
treeMaybe Empty = Nothing
treeMaybe (Node x l) = Just (x, l)

maybeTree :: Maybe (a, [Tree a]) -> Tree a
maybeTree Nothing = Empty
maybeTree (Just (x, xs)) = Node x xs

-- | Create a tree from a value and an unfolding function.
--
unfold :: (a -> [a]) -> a -> Tree a
unfold f x = Node x $ fmap (unfold f) (f x)

-- | Expand a tree using an unfolding function.
--
expand :: (a -> [a]) -> Tree a -> Tree a
expand _ Empty = Empty
expand f (Node x xs) = Node x
  $ fmap (expand f) xs <> fmap (unfold f) (f x)

-- | Throw away @n@ levels of a tree's children.
--
--   /@prune 0@ will throw away all of a tree's children./
--
prune :: Int -> Tree a -> Tree a
prune _ Empty = Empty
prune n (Node x xs)
  | n <= 0 = Node x []
  | otherwise =  Node x $ fmap (prune (n - 1)) xs

-- | Returns the depth of the deepest leaf node in the tree.
--
depth :: Tree a -> Int
depth Empty = 0
depth (Node _ xs) = 1 + maximum (fmap depth xs)

{-
-- | Takes a tree of 'Maybe's and returns a tree of all the 'Just' values.
--
--   If the root of the tree is 'Nothing' then 'Nothing' is returned.
--
catMaybes :: Tree (Maybe a) -> Maybe (Tree a)
catMaybes m =
  let
    NodeT mx mxs =
      runTree m
  in
    case mx of
      Nothing -> do
        case Maybe.mapMaybe catMaybes mxs of
          [] ->
            Nothing
          Tree (NodeT x xs0) : xs1 ->
            Just . Tree $
              Node x (xs0 ++ xs1)
      Just x ->
        Just . Tree $
          Node x (Maybe.mapMaybe catMaybes mxs)
-}


fromPred :: (a -> Bool) -> a -> Maybe a
fromPred p a = a <$ guard (p a)

-- | Returns a tree containing only elements that match the predicate.
--
--   If the root of the tree does not match the predicate then 'Nothing' is
--   returned.
--
filter :: (a -> Bool) -> Tree a -> Tree a
filter p = mapMaybe (fromPred p)

mapMaybe :: (a -> Maybe b) -> Tree a -> Tree b
mapMaybe _ Empty = Empty
mapMaybe p (Node x xs) = case p x of
  Nothing -> Empty
  Just x' -> Node x' $ fmap (mapMaybe p) xs


------------------------------------------------------------------------

-- | All ways a list can be split
--
-- > splits [1,2,3]
-- > ==
-- > [ ([], 1, [2, 3])
--   , ([1], 2, [3])
--   , ([1, 2], 3, [])
--   ]
--
splits :: [a] -> [([a], a, [a])]
splits xs0 =
  let
    go (front : fronts) (x : xs) =
      (front, x, xs) : go fronts xs
    go _ _ =
      []
  in
    go (List.inits xs0) xs0

-- | @removes n@ computes all ways we can remove chunks of size @n@ from a list
--
-- Examples
--
-- > removes 1 [1..3] == [[2,3],[1,3],[1,2]]
-- > removes 2 [1..4] == [[3,4],[1,2]]
-- > removes 2 [1..5] == [[3,4,5],[1,2,5],[1,2,3,4]]
-- > removes 3 [1..5] == [[4,5],[1,2,3]]
--
-- Note that the last chunk we delete might have fewer elements than @n@.
removes :: forall a. Int -> [a] -> [[a]]
removes k = \xs -> go xs
  where
    go :: [a] -> [[a]]
    go [] = []
    go xs = xs2 : map (xs1 ++) (go xs2)
      where
        (xs1, xs2) = splitAt k xs

dropSome :: [Tree a] -> [Tree [a]]
dropSome ts = do
  n   <- takeWhile (> 0) $ iterate (`div` 2) (length ts)
  ts' <- removes n ts
  pure $ interleave ts'

shrinkOne :: [Tree a] -> [Tree [a]]
shrinkOne ts = do
  (xs, Node _ ys, zs) <- splits ts
  y <- ys
  pure $ interleave (xs ++ [y] ++ zs)

interleave :: [Tree a] -> Tree [a]
interleave ts = case sequenceA ts of
  Empty -> Empty
  Node x _ -> Node x (dropSome ts <> shrinkOne ts)

instance Foldable Tree where
  foldMap _ Empty = mempty
  foldMap f (Node x xs) = f x <> (foldMap . foldMap) f xs

instance Traversable Tree where
  traverse _ Empty = pure Empty
  traverse f (Node x xs)
    = Node <$> f x <*> (traverse . traverse) f xs

-- NOTE: this implementation does not satisfy the ap law (@ap = <*>@)
--
-- Instead, this implementation enables parallel shrinking, that is it
-- shrinks the left and right arguments independently.
instance Applicative Tree where
  pure x = Node x []
  Empty <*> _ = Empty
  _ <*> Empty = Empty
  nab@(Node ab tabs) <*> na@(Node a tas) = Node (ab a) $
    fmap (<*> na) tabs <> fmap (nab <*>) tas

--
-- implementation: satisfies law (ap = <*>)
--
-- instance Applicative m => Applicative (NodeT m) where
--   pure x =
--     NodeT x []
--   (<*>) (NodeT ab tabs) na@(NodeT a tas) =
--     NodeT (ab a) $
--       map (<*> (fromNodeT na)) tabs ++ map (fmap ab) tas

instance Monad Tree where
  return =
    pure

  Empty >>= _ = Empty
  Node x xs >>= k = case k x of
    Empty -> Empty
    Node y ys -> Node y $
      fmap (>>= k) xs <> ys

------------------------------------------------------------------------
-- Pretty Printing

--
-- Rendering implementation based on the one from containers/Data.Tree
--

-- renderTreeTLines :: Monad m => TreeT m String -> m [String]
-- renderTreeTLines (TreeT m) = do
--   NodeT x xs0 <- m
--   xs <- renderForestLines xs0
--   pure $
--     lines (renderNodeT x) ++ xs
-- 

renderVal :: String -> String
renderVal xs =
  case xs of
    [_] -> ' ' : xs
    _ -> xs

renderForestLines :: [Tree String] -> [String]
renderForestLines xs0 =
  let
    xs = [ n | n@(Node _ _) <- xs0 ]

    shift hd other =
      zipWith (++) (hd : repeat other)

    go ys0 = case ys0 of
      [] -> []

      [y] -> do
        shift " └╼" "   " (renderTree y)

      y : ys
        -> shift " ├╼" " │ " (renderTree y) <> go ys
  in go xs

-- | Render a tree of strings.
--
renderTree :: Tree String -> [String]
renderTree Empty = ["empty tree"]
renderTree (Node x xs) = lines (renderVal x) <> renderForestLines xs

render :: Tree String -> String
render = unlines . renderTree
