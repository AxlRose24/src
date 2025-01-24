{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RebindableSyntax  #-}
{-# LANGUAGE TypeOperators     #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use const" #-}
{-# HLINT ignore "Avoid lambda" #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# HLINT ignore "Redundant flip" #-}
{-# HLINT ignore "Use head" #-}
{-# HLINT ignore "Use second" #-}
{-# HLINT ignore "Evaluate" #-}

module Quickhull (

  Point, Line, SegmentedPoints,
  quickhull,

  -- Exported for display
  initialPartition,
  partition,

  -- Exported just for testing
  propagateL, shiftHeadFlagsL, segmentedScanl1,
  propagateR, shiftHeadFlagsR, segmentedScanr1,

) where

import Data.Array.Accelerate
import Data.Array.Accelerate.Debug.Trace
import qualified Prelude                      as P
import Data.Array.Accelerate.Data.Maybe


-- Points and lines in two-dimensional space
--
type Point = (Int, Int)
type Line  = (Point, Point)

-- This algorithm will use a head-flags array to distinguish the different
-- sections of the hull (the two arrays are always the same length).
--
-- A flag value of 'True' indicates that the corresponding point is
-- definitely on the convex hull. The points after the 'True' flag until
-- the next 'True' flag correspond to the points in the same segment, and
-- where the algorithm has not yet decided whether or not those points are
-- on the convex hull.
--
type SegmentedPoints = (Vector Bool, Vector Point)

readInputFile :: P.FilePath -> P.IO (Vector Point)
readInputFile filename = (\l -> fromList (Z :. P.length l) l) P.. P.map (\l -> let ws = P.words l in (P.read (ws P.!! 0), P.read (ws P.!! 1))) P.. P.lines P.<$> P.readFile filename

-- Core implementation
-- -------------------

-- Initialise the algorithm by first partitioning the array into two
-- segments. Locate the left-most (p₁) and right-most (p₂) points. The
-- segment descriptor then consists of the point p₁, followed by all the
-- points above the line (p₁,p₂), followed by the point p₂, and finally all
-- of the points below the line (p₁,p₂).
--
-- To make the rest of the algorithm a bit easier, the point p₁ is again
-- placed at the end of the array.
--
-- We indicate some intermediate values that you might find beneficial to
-- compute.
--
initialPartition :: Acc (Vector Point) -> Acc SegmentedPoints
initialPartition points =
  let
      p1, p2 :: Exp Point
      p1 = -- locate the left-most point"
           let point = foldAll (\point1 point2 -> if fst point1 < fst point2 then point1 else point2) (points !! 0) point
           in uncurry T2 (the point)
      p2 = -- locate the right-most point"
           let point = foldAll (\point1 point2 -> if fst point1 > fst point2 then point1 else point2) (points !! 0) point
           in uncurry T2 (the point)

      -- determines which points lie above the line (p₁, p₂)"
      isUpper :: Acc (Vector Bool)
      isUpper = map func points
                  where func point = let dx = fst point2 - fst point1
                                         dy = snd point2 - snd point1
                                         mx = fst point - fst point1
                                         my = snd point - snd point1
                                         cross = dx * my - dy * mx
                                     in cross < 0
                                      where point1 = p1
                                            point2 = p2

      -- determines which points lie below the line (p₁, p₂)"
      isLower :: Acc (Vector Bool)
      isLower = map func points
                  where func point = let dx = fst point2 - fst point1
                                         dy = snd point2 - snd point1
                                         mx = fst point - fst point1
                                         my = snd point - snd point1
                                         cross = dx * my - dy * mx
                                     in cross > 0
                                      where point1 = p1
                                            point2 = p2

      offsetUpper :: Acc (Vector Int) -- relative index of points above the line
      countUpper  :: Acc (Scalar Int) -- number of points above the line 
      T2 offsetUpper countUpper =  T2 offset count
                                   where offset = tail (scanl (+) 0 (map (\b -> if b then 1 else 0) isUpper))
                                         count = fold1All (+) (map (\elem -> if elem then 1 else 0) isUpper)

      offsetLower :: Acc (Vector Int) -- relative index of points below the line
      countLower  :: Acc (Scalar Int) -- number of points below the line
      T2 offsetLower countLower = T2 offset count
                                    where offset = tail (scanl (+) (the countUpper + 1) (map (\b -> if b then 1 else 0) isLower))
                                          count = fold1All (+) (map (\elem -> if elem then 1 else 0) isLower)

      -- p1 -> 0 and size + 1, p2 -> the countUpper + 1
      destination :: Acc (Vector (Maybe DIM1)) -- compute the index in the result array for each point (if it is present), destination for the permute
      destination = imap (\index point -> if isUpper!index then Just_ (I1 (offsetUpper!index)) 
                          else if isLower!index then Just_ (I1 (offsetLower!index)) 
                          else if point == p1 then Just_ (I1 0) 
                          else if point == p2 then Just_ (I1 (the countUpper + 1)) 
                          else Nothing_) points

      newPoints :: Acc (Vector Point) -- place each point into its corresponding segment of the result
      newPoints = permute (\point _ -> point) (fill (constant (Z:.fullSize)) (T2 0 0)) (\ix -> destination!ix) points
                    where fullSize = P.fromEnum (the countUpper + the countLower) + 3

      headFlags :: Acc (Vector Bool) -- create head flags array demarcating the initial segments
      headFlags = map (\point -> if point == p1 || point == p2 then True_ else False_) newPoints
  in
  T2 headFlags newPoints


-- The core of the algorithm processes all line segments at once in
-- data-parallel. This is similar to the previous partitioning step, except
-- now we are processing many segments at once.
--
-- For each line segment (p₁,p₂) locate the point furthest from that line
-- p₃. This point is on the convex hull. Then determine whether each point
-- p in that segment lies to the left of (p₁,p₃) or the right of (p₂,p₃).
-- These points are undecided.
--
partition :: Acc SegmentedPoints -> Acc SegmentedPoints
partition (T2 headFlags points) = undefined
                                     where pointDistance :: Exp Point -> Exp Point -> Exp Point -> Exp Int
                                           pointDistance a b p = abs ((fst a - fst p) * (snd b - snd a) - (fst a - fst b) * (snd p - snd a)) -- neglected (1/2) * because it is irrelevant and doesn't work
                                           findP3 p1 p2 ps = maximum (map (\x -> pointDistance p1 p2 x) ps)

-- The completed algorithm repeatedly partitions the points until there are
-- no undecided points remaining. What remains is the convex hull.
--
quickhull :: Acc (Vector Point) -> Acc (Vector Point)
quickhull points = loop initPart
                    where initPart = initialPartition points
                          loop part = if predicate then asnd part else loop (partition part)
                                   where predicate = the (and (afst part))


-- Helper functions
-- ----------------

propagateL :: Elt a => Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
propagateL = segmentedScanl1 const

propagateR :: Elt a => Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
propagateR = segmentedScanr1 (flip const)

shiftHeadFlagsL :: Acc (Vector Bool) -> Acc (Vector Bool)
shiftHeadFlagsL = stencil f boundary
                    where f :: Stencil3 Bool -> Exp Bool
                          f (_,_,r) = r

shiftHeadFlagsR :: Acc (Vector Bool) -> Acc (Vector Bool)
shiftHeadFlagsR = stencil f boundary
                    where f :: Stencil3 Bool -> Exp Bool
                          f (l,_,_) = l

-- boundary for the stencil function in shiftHeadFlagsL and shiftHeadFlagsR
boundary :: Boundary (Vector Bool)
boundary = function (\_ -> True_)

segmentedScanl1 :: Elt a => (Exp a -> Exp a -> Exp a) -> Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
segmentedScanl1 f headFlags values = map snd (scanl1 (segmented f) tuples)
                                    where tuples = zip headFlags values

segmentedScanr1 :: Elt a => (Exp a -> Exp a -> Exp a) -> Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
segmentedScanr1 f headFlags values = map snd (scanr1 (segmented f) tuples)
                                    where tuples = zip headFlags values


-- Given utility functions
-- -----------------------

pointIsLeftOfLine :: Exp Line -> Exp Point -> Exp Bool
pointIsLeftOfLine (T2 (T2 x1 y1) (T2 x2 y2)) (T2 x y) = nx * x + ny * y > c
  where
    nx = y1 - y2
    ny = x2 - x1
    c  = nx * x1 + ny * y1

nonNormalizedDistance :: Exp Line -> Exp Point -> Exp Int
nonNormalizedDistance (T2 (T2 x1 y1) (T2 x2 y2)) (T2 x y) = nx * x + ny * y - c
  where
    nx = y1 - y2
    ny = x2 - x1
    c  = nx * x1 + ny * y1

segmented :: Elt a => (Exp a -> Exp a -> Exp a) -> Exp (Bool, a) -> Exp (Bool, a) -> Exp (Bool, a)
segmented f (T2 aF aV) (T2 bF bV) = T2 (aF || bF) (bF ? (bV, f aV bV))

