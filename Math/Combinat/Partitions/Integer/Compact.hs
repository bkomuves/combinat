
{- | Compact representation of integer partitions.

Partitions are conceptually nonincreasing sequences of /positive/ integers.

This implementation uses the @compact-word-vectors@ library internally to provide
a much more memory-efficient Partition type that the naive lists of integer.
This is very helpful when building large tables indexed by partitions, for example; 
and hopefully quite a bit faster, too.

Note: This is an internal module, you are not supposed to import it directly.
It is also not fully ready to be used yet...

-}

{-# LANGUAGE BangPatterns, PatternSynonyms, ViewPatterns #-}
module Math.Combinat.Partitions.Integer.Compact where

--------------------------------------------------------------------------------

import Data.Bits
import Data.Word
import Data.Ord
import Data.List ( intercalate , group , sort , sortBy , foldl' , scanl' ) 

import Data.Vector.Compact.WordVec ( WordVec , Shape(..) )
import qualified Data.Vector.Compact.WordVec as V

import Math.Combinat.Compositions ( compositions' )

--------------------------------------------------------------------------------
-- * The compact partition data type

newtype Partition 
  = Partition WordVec 
  deriving Eq

instance Show Partition where
  showsPrec = showsPrecPartition

showsPrecPartition :: Int -> Partition -> ShowS
showsPrecPartition prec (Partition vec)
  = showParen (prec > 10) 
  $ showString "Partition"
  . showChar ' ' 
  . shows (V.toList vec)

instance Ord Partition where
  compare = cmpLexico
               
--------------------------------------------------------------------------------
-- * Pattern synonyms 

-- | Pattern sysnonyms allows us to use existing code with minimal modifications
pattern Nil :: Partition
pattern Nil <- (isEmpty -> True) where
        Nil =  empty

pattern Cons :: Int -> Partition -> Partition
pattern Cons x xs <- (uncons -> Just (x,xs)) where
        Cons x xs = cons x xs

-- | Simulated newtype constructor 
pattern Partition_ :: [Int] -> Partition
pattern Partition_ xs <- (toList -> xs) where
        Partition_ xs = fromDescList xs

pattern Head :: Int -> Partition 
pattern Head h <- (height -> h)

pattern Tail :: Partition -> Partition
pattern Tail xs <- (partitionTail -> xs)

pattern Length :: Int -> Partition 
pattern Length n <- (width -> n)        

--------------------------------------------------------------------------------
-- * Lexicographic comparison

-- | The lexicographic ordering
cmpLexico :: Partition -> Partition -> Ordering
cmpLexico (Partition vec1) (Partition vec2) = compare (V.toList vec1) (V.toList vec2)

--------------------------------------------------------------------------------
-- * Basic (de)constructrion

empty :: Partition
empty = Partition (V.empty)

isEmpty :: Partition -> Bool
isEmpty (Partition vec) = V.null vec

--------------------------------------------------------------------------------

singleton :: Int -> Partition
singleton x 
  | x >  0     = Partition (V.singleton $ i2w x)
  | x == 0     = empty
  | otherwise  = error "Parittion/singleton: negative input"

--------------------------------------------------------------------------------

uncons :: Partition -> Maybe (Int,Partition)
uncons (Partition vec) = case V.uncons vec of
  Nothing     -> Nothing
  Just (h,tl) -> Just (w2i h, Partition tl)

-- | @partitionTail p == snd (uncons p)@
partitionTail :: Partition -> Partition
partitionTail (Partition vec) = Partition (V.tail vec)

-------------------------------------------------------------------------------

-- | We assume that @x >= partitionHeight p@!
cons :: Int -> Partition -> Partition
cons !x (Partition !vec) 
  | V.null vec = Partition (if x > 0 then V.singleton y else V.empty) 
  | y >= h     = Partition (V.cons y vec)
  | otherwise  = error "Partition/cons: invalid element to cons"
  where  
    y = i2w x
    h = V.head vec

--------------------------------------------------------------------------------

-- | We assume that the element is not bigger than the last element!
snoc :: Partition -> Int -> Partition
snoc (Partition !vec) !x
  | x == 0           = Partition vec
  | V.null vec       = Partition (V.singleton y)
  | y <= V.last vec  = Partition (V.snoc vec y)
  | otherwise        = error "Partition/snoc: invalid element to snoc"
  where
    y = i2w x

--------------------------------------------------------------------------------
-- * exponential form

toExponentialForm :: Partition -> [(Int,Int)]
toExponentialForm = map (\xs -> (head xs,length xs)) . group . toAscList

fromExponentialForm :: [(Int,Int)] -> Partition
fromExponentialForm = fromDescList . concatMap f . sortBy g where
  f (!i,!e) = replicate e i
  g (!i, _) (!j,_) = compare j i

--------------------------------------------------------------------------------
-- * Width and height of the bounding rectangle

-- | Width, or the number of parts
width :: Partition -> Int
width (Partition vec) = V.vecLen vec

-- | Height, or the first (that is, the largest) element
height :: Partition -> Int
height (Partition vec) = w2i (V.head vec)

-- | Width and height 
widthHeight :: Partition -> (Int,Int)
widthHeight (Partition vec) = (V.vecLen vec , w2i (V.head vec))

--------------------------------------------------------------------------------
-- * Differential sequence

-- | From a non-increasing sequence @[a1,a2,..,an]@ this computes the sequence of differences
-- @[a1-a2,a2-a3,...,an-0]@
diffSequence :: Partition -> [Int]
diffSequence = go . toDescList where
  go (x:ys@(y:_)) = (x-y) : go ys 
  go [x] = [x]
  go []  = []

----------------------------------------

-- | From a non-increasing sequence @[a1,a2,..,an]@ this computes the reversed sequence of differences
-- @[ a[n]-0 , a[n-1]-a[n] , ... , a[2]-a[3] , a[1]-a[2] ] @
reverseDiffSequence :: Partition -> [Int]
reverseDiffSequence p = go (0 : toAscList p) where
  go (x:ys@(y:_)) = (y-x) : go ys 
  go [x] = []
  go []  = []

--------------------------------------------------------------------------------
-- *  Dual partition

dualPartition :: Partition -> Partition
dualPartition compact@(Partition vec) 
  | V.null vec  = Partition V.empty
  | otherwise   = Partition (V.fromList' shape $ map i2w dual)
  where
    height = V.head   vec
    len    = V.vecLen vec
    shape  = Shape (w2i height) (V.bitsNeededFor $ i2w len)
    dual   = concat
      [ replicate d j
      | (j,d) <- zip (descendToOne len) (reverseDiffSequence compact)
      ]

--------------------------------------------------------------------------------
-- * Conversion to list

toList :: Partition -> [Int]
toList = toDescList

-- | returns a descending (non-increasing) list
toDescList :: Partition -> [Int]
toDescList (Partition vec) = map w2i (V.toList vec)

-- | Returns a reversed (ascending; non-decreasing) list
toAscList :: Partition -> [Int]
toAscList (Partition vec) = map w2i (V.toRevList vec)

--------------------------------------------------------------------------------
-- * Conversion from list

fromDescList :: [Int] -> Partition
fromDescList list = fromDescList' (length list) list

-- | We assume that the input is a non-increasing list of /positive/ integers!
fromDescList' 
  :: Int          -- ^ length
  -> [Int]        -- ^ the list
  -> Partition
fromDescList' !len !list = Partition (V.fromList' (Shape len bits) $ map i2w list) where
  bits = case list of
    []     -> 4
    (x:xs) -> V.bitsNeededFor (i2w x)

--------------------------------------------------------------------------------
-- * Partial orderings

-- @ |p `isSubPartitionOf` q@
isSubPartitionOf :: Partition -> Partition -> Bool
isSubPartitionOf p q = and $ zipWith (<=) (toList p) (toList q ++ repeat 0)

-- | @q `dominates` p@
dominates :: Partition -> Partition -> Bool
dominates (Partition vec_q) (Partition vec_p) = and $ zipWith (>=) (sums (qs ++ repeat 0)) (sums ps) where 
  sums = tail . scanl' (+) 0
  ps = V.toList vec_p
  qs = V.toList vec_q

--------------------------------------------------------------------------------
-- * Pieri rule

-- | Expands to product @s[lambda]*h[k]@ as a sum of @s[mu]@-s. See <https://en.wikipedia.org/wiki/Pieri's_formula>
pieriRule :: Partition -> Int -> [Partition]
pieriRule = error "Partitions/Integer/Compact: pieriRule not implemented yet"

{-
-- | Expands to product @s[lambda]*h[1] = s[lambda]*e[1]@ as a sum of @s[mu]@-s. See <https://en.wikipedia.org/wiki/Pieri's_formula>
pieriRuleSingleBox :: Partition -> [Partition]
pieriRuleSingleBox !compact = case compact of

  Nibble 0 -> [ singleton 1 ]

  Nibble w | h < 15 -> 
    [ Nibble  (w + shiftL 1 (60-4*i)) | (i,d)<-zip [0..n-1] diffs1 , d>0 ] ++ [ snoc compact 1 ]

  Medium1 w | h < 255 -> 
    [ Medium1 (w + shiftL 1 (56-8*i)) | (i,d)<-zip [0..n-1] diffs1 , d>0 ] ++ [ snoc compact 1 ]

  Medium2 w1 w2 | h < 255 -> 
    let (diffs1a,diffs1b) = splitAt 8 diffs1 
    in  [ Medium2    (w1 + shiftL 1 (56-8*i)) w2 | (i,d)<-zip [0..7  ] diffs1a , d>0 ] ++
        [ Medium2 w1 (w2 + shiftL 1 (56-8*i))    | (i,d)<-zip [0..n-9] diffs1b , d>0 ] ++
        [ snoc compact 1 ]

  Medium3 w1 w2 w3 | h < 255 -> 
    let (diffs1a,tmp    ) = splitAt 8 diffs1 
        (diffs1b,diffs1c) = splitAt 8 tmp
    in  [ Medium3       (w1 + shiftL 1 (56-8*i)) w2 w3 | (i,d)<-zip [0..7   ] diffs1a , d>0 ] ++
        [ Medium3    w1 (w2 + shiftL 1 (56-8*i)) w3    | (i,d)<-zip [0..7   ] diffs1b , d>0 ] ++
        [ Medium3 w1 w2 (w3 + shiftL 1 (56-8*i))       | (i,d)<-zip [0..n-17] diffs1c , d>0 ] ++
        [ snoc compact 1 ]
    
  _ -> genericSingleBox

  where
    (n,h)  =     widthHeight  compact
    list   =     toDescList   compact
    diffs1 = 1 : diffSequence compact

    genericSingleBox :: [Partition]
    genericSingleBox = map (fromDescList' n) (go list diffs1) ++ [ fromDescList' (n+1) (list ++ [1]) ] where
      go :: [Int] -> [Int] -> [[Int]]
      go (a:as) (d:ds) = if d > 0 then ((a+1):as) : map (a:) (go as ds) 
                                  else              map (a:) (go as ds)
      go []     _      = []

-- | Expands to product @s[lambda]*h[k]@ as a sum of @s[mu]@-s. See <https://en.wikipedia.org/wiki/Pieri's_formula>
pieriRule :: Partition -> Int -> [Partition]
pieriRule !compact !k 
  | k <  0                  = []
  | k == 0                  = [ compact ]
  | k == 1                  = pieriRuleSingleBox compact
  | h == 0                  = [ singleton k ]
  | h + k <= 15  && n < 15  = case compact of { Nibble w -> 
                              [ Nibble (w + encode c)  | c <- comps ] }
  | otherwise               = [ fromDescList' (n+b) xs | c <- comps , let (b,xs) = add c ] 

  where
    (n,h)  = widthHeight compact
    list   = toDescList compact
    bounds = k : {- map (min k) -} (diffSequence compact) 
    comps = compositions' bounds k

    add clist = go list clist where
      go (!p:ps) (!c:cs) = let (b,rest) = go ps cs in (b, (p+c):rest)
      go []      [c]     = if c>0 then (1,[c]) else (0,[])
      go _       _       = error "Compact/pieriRule/add: shouldn't happen"

    encode :: [Int] -> Word64
    encode = go 60 where
      go !k [c]    = if c==0 then 0 else shiftL (i2w c) k + 1
      go !k (c:cs) = shiftL (i2w c) k + go (k-4) cs
      go !k []     = error "Compact/pieriRule/encode: shouldn't happen"
-}

--------------------------------------------------------------------------------
-- * local (internally used) utility functions

{-# INLINE i2w #-}
i2w :: Int -> Word
i2w = fromIntegral

{-# INLINE w2i #-}
w2i :: Word -> Int
w2i = fromIntegral

{-# INLINE sum' #-}
sum' :: [Word] -> Word
sum' = foldl' (+) 0

{-# INLINE safeTail #-}
safeTail :: [Int] -> [Int]
safeTail xs = case xs of { [] -> [] ; _ -> tail xs }

{-# INLINE descendToZero #-}
descendToZero :: Int -> [Int]
descendToZero !n
  | n >  0  = n : descendToZero (n-1) 
  | n == 0  = [0]
  | n <  0  = []

{-# INLINE descendToOne #-}
descendToOne :: Int -> [Int]
descendToOne !n
  | n >  1  = n : descendToOne (n-1) 
  | n == 1  = [1]
  | n <  1  = []

--------------------------------------------------------------------------------


