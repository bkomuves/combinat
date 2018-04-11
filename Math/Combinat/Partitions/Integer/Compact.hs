
{- | Compact representation of integer partitions.

Partitions are conceptually nonincreasing sequences of /positive/ integers.

When the partition fits into a 15x15 rectangle, we encode the parts as nibbles in a single 64-bit word.
The most significant nibble is the first element, and the least significant nibble is used to encode
the length. This way equality and comparison of 64-bit words is the same as the corresponding operations
for partitions (lexicographic ordering).

This will make working with small partitions much more memory efficient (very helpful when
building tables indexed by partitions, for example!) and hopefully quite a bit faster, too.

When they do not fit into a 15x15 rectangle, but fit into 255x7, 255x15, 255x23 or 255x31, respectively,
then we extend the above to use the bytes of 1, 2, 3 or 4 64-bit words.

In the general case, we encode the partition as a list of 64-bit words, each encoding 4 16-bit parts.

Partitions with elements bigger than 65535 are not supported.

Note: This is an internal module, you are not supposed to import it directly.
-}

{-# LANGUAGE BangPatterns, PatternSynonyms, ViewPatterns, ForeignFunctionInterface #-}
module Math.Combinat.Partitions.Integer.Compact where

--------------------------------------------------------------------------------

import Data.Bits
import Data.Word
import Data.Ord
import Data.List ( intercalate , group , sort , sortBy , foldl' , scanl' ) 

import Math.Combinat.Compositions ( compositions' )


--------------------------------------------------------------------------------
-- * The compact partition data type

data Partition
  = Nibble   {-# UNPACK #-} !Word64
  | Medium1  {-# UNPACK #-} !Word64
  | Medium2  {-# UNPACK #-} !Word64 {-# UNPACK #-} !Word64
  | Medium3  {-# UNPACK #-} !Word64 {-# UNPACK #-} !Word64 {-# UNPACK #-} !Word64
  | Medium4  {-# UNPACK #-} !Word64 {-# UNPACK #-} !Word64 {-# UNPACK #-} !Word64 {-# UNPACK #-} !Word64
  | WordList {-# UNPACK #-} !Int ![Word64]
  deriving (Eq,Show)

--------------------------------------------------------------------------------
  
-- | for debugging
partitionPrefixChar :: Partition -> Char
partitionPrefixChar p = case p of
  Nibble   {} -> 'N'
  Medium1  {} -> '1'
  Medium2  {} -> '2' 
  Medium3  {} -> '3' 
  Medium4  {} -> '4' 
  WordList {} -> 'L'

{- 
instance Show Partition where
  show compact = partitionPrefixChar compact 
               : '<' : intercalate "," (map show $ toList compact) ++ ">"
-}

instance Ord Partition where
  compare = cmp
               
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
cmp :: Partition -> Partition -> Ordering
cmp (Nibble  a)           (Nibble  b)           = compare  a             b
cmp (Medium1 a1)          (Medium1 b1)          = compare  a1            b1
cmp (Medium2 a1 a2)       (Medium2 b1 b2)       = compare (a1,a2)       (b1,b2)
cmp (Medium3 a1 a2 a3)    (Medium3 b1 b2 b3)    = compare (a1,a2,a3)    (b1,b2,b3)
cmp (Medium4 a1 a2 a3 a4) (Medium4 b1 b2 b3 b4) = compare (a1,a2,a3,a4) (b1,b2,b3,b4)
cmp (WordList _ as)       (WordList _ bs)       = compare  as            bs
cmp p                     q                     = compare (toList p)    (toList q)
  
--------------------------------------------------------------------------------
-- * Basic (de)constructrion

empty :: Partition
empty = Nibble 0

isEmpty :: Partition -> Bool
isEmpty compact = case compact of
  Nibble x -> (x == 0)
  _        -> False

--------------------------------------------------------------------------------

singleton :: Int -> Partition
singleton x
  | x == 0      = Nibble 0
  | x <= 15     = Nibble     $ shiftL (i2w x) 60 + 1
  | x <= 255    = Medium1    $ shiftL (i2w x) 56 + 1
  | x <= 65535  = WordList 1 [ shiftL (i2w x) 48 ]
  | otherwise   = error "singleton: partitions with elements bigger than 65535 are not supported"

--------------------------------------------------------------------------------

uncons :: Partition -> Maybe (Int,Partition)
uncons compact = case compact of
  Nibble  0           -> Nothing
  Nibble  w           -> Just ( w2i (shiftR w  60) , Nibble $ shiftL (w .&. 0x0ffffffffffffff0) 4 + ((w .&. 15) - 1) )
  Medium1 w1          -> Just ( w2i (shiftR w1 56) , partitionTail compact )
  Medium2 w1 w2       -> Just ( w2i (shiftR w1 56) , partitionTail compact )
  Medium3 w1 w2 w3    -> Just ( w2i (shiftR w1 56) , partitionTail compact )
  Medium4 w1 w2 w3 w4 -> Just ( w2i (shiftR w1 56) , partitionTail compact )
  WordList n (w:rest) -> Just ( w2i (shiftR w  48) , partitionTail compact )

--------------------------------------------------------------------------------

-- | @partitionTail p == snd (uncons p)@
partitionTail :: Partition -> Partition
partitionTail compact = case compact of

  Nibble  0 -> Nibble 0
  Nibble  w -> Nibble $ shiftL (w .&. 0x0ffffffffffffff0) 4 + ((w .&. 15) - 1) 

  Medium1 w1 ->
    let !y = (shiftR w1 48) .&. 255     -- next element
        !n = w1 .&. 15
    in  if y <= 15 
          then makeNibble (w2i $ n-1) $ safeTail $ toList compact
          else Medium1    $ shiftL (w1 .&. 0x00ffffffffffff00) 8 + (n-1) 

  Medium2 w1 w2 ->      
    let !y = (shiftR w1 48) .&. 255
        !n = w2 .&. 255
    in  if y <= 15 
          then makeNibble (w2i $ n-1) $ safeTail $ toList compact
          else if n <= 8
            then Medium1 $ shiftL (w1 .&. 0x00ffffffffffffff) 8 + shiftL (shiftR w2 56) 8 + (n-1) 

            else Medium2 ( shiftL  w1 8 + shiftR w2 56 ) 
                         ( shiftL (w2 .&. 0x00ffffffffffff00) 8 + (n-1) )

  Medium3 w1 w2 w3 ->   
    let !y = (shiftR w1 48) .&. 255
        !n = w3 .&. 255
    in  if y <= 15 && n <= 16
          then makeNibble (w2i $ n-1) $ safeTail $ toList compact
          else if n <= 16
            then Medium2 ( shiftL  w1 8 + shiftR w2 56 ) 
                         ( shiftL  w2 8 + shiftR w3 56 + shiftL (shiftR w3 56) 8 + (n-1) )
 
            else Medium3 ( shiftL  w1 8 + shiftR w2 56 ) 
                         ( shiftL  w2 8 + shiftR w3 56 ) 
                         ( shiftL (w3 .&. 0x00ffffffffffff00) 8 + (n-1) )
 
  _ -> 
    let n = width compact
    in  fromDescList' (n-1) $ safeTail $ toList compact 

--------------------------------------------------------------------------------

-- | We assume that @x >= partitionHeight p@!
cons :: Int -> Partition -> Partition
cons !x !compact = case compact of

  Nibble 0                -> singleton x
  
  Nibble word
    | x <= 15  && n < 15  -> Nibble $ shiftR word 4 + shiftL xw 60 + (n+1)
    | x <= 255            -> makeMedium   (w2i $ n+1) (x : toList compact)
    | otherwise           -> makeWordList (w2i $ n+1) (x : toList compact)
    where  
      n  = word .&. 15
      xw = i2w x
      
  Medium1 w1
    | x <= 255 && n < 7   -> Medium1 (shiftR w1 8 + shiftL xw 56 + (n+1))
    | x <= 255            -> Medium2 (shiftR w1 8 + shiftL xw 56        ) 8
    | otherwise           -> makeWordList (w2i $ n+1) (x : toList compact)
    where  
      n  = w1 .&. 255
      xw = i2w x

  Medium2 w1 w2
    | x <= 255 && n < 15  -> Medium2 (shiftR w1 8 + shiftL xw 56) (shiftR w2 8 + shiftL (w1 .&. 255) 56 + (n+1))
    | x <= 255            -> Medium3 (shiftR w1 8 + shiftL xw 56) (shiftR w2 8 + shiftL (w1 .&. 255) 56        ) 16
    | otherwise           -> makeWordList (w2i $ n+1) (x : toList compact)
    where  
      n  = w2 .&. 255
      xw = i2w x

  Medium3 w1 w2 w3
    | x <= 255 && n < 23  -> Medium3 (shiftR w1 8 + shiftL xw 56) (shiftR w2 8 + shiftL (w1 .&. 255) 56) (shiftR w3 8 + shiftL (w2 .&. 255) 56 + (n+1))
    | x <= 255            -> Medium4 (shiftR w1 8 + shiftL xw 56) (shiftR w2 8 + shiftL (w1 .&. 255) 56) (shiftR w3 8 + shiftL (w2 .&. 255) 56        ) 24
    | otherwise           -> makeWordList (w2i $ n+1) (x : toList compact)
    where  
      n  = w3 .&. 255
      xw = i2w x

  Medium4 w1 w2 w3 w4
    | x <= 255 && n < 31  -> Medium4 (shiftR w1 8 + shiftL  xw          56) 
                                     (shiftR w2 8 + shiftL (w1 .&. 255) 56) 
                                     (shiftR w3 8 + shiftL (w2 .&. 255) 56) 
                                     (shiftR w4 8 + shiftL (w3 .&. 255) 56 + (n+1))
    | otherwise           -> makeWordList (w2i $ n+1) (x : toList compact)
    where  
      n = w4 .&. 255
      xw = i2w x
      
  _ -> 
    let n = width compact
    in  fromDescList' (n+1) (x : toList compact)

--------------------------------------------------------------------------------

-- | We assume that the element is not bigger than the last element!
snoc :: Partition -> Int -> Partition
snoc !compact  0 = compact
snoc !compact !x = case compact of

  Nibble 0 -> singleton x

  Nibble word
    | n < 15    -> Nibble $ (word + 1) .|. shiftL (i2w x) ((15-n)*4)
    | otherwise -> makeMedium (n+1) (toList compact ++ [x])
    where  
      n = w2i (word .&. 15)
      
  Medium1 w1
    | n < 7     -> Medium1 $ (w1 + 1) .|. shiftL (i2w x) ((7-n)*8)
    | otherwise -> Medium2 ((w1 .&. 0xffffffffffffff00) + i2w x) 8
    where  
      n = w2i (w1 .&. 255)

  Medium2 w1 w2
    | n < 15    -> Medium2 w1 $ (w2 + 1) .|. shiftL (i2w x) ((15-n)*8)
    | otherwise -> Medium3 w1 ((w2 .&. 0xffffffffffffff00) + i2w x) 16
    where  
      n = w2i (w2 .&. 255)

  Medium3 w1 w2 w3
    | n < 23    -> Medium3 w1 w2 $ (w3 + 1) .|. shiftL (i2w x) ((23-n)*8)
    | otherwise -> Medium4 w1 w2 ((w3 .&. 0xffffffffffffff00) + i2w x) 24
    where  
      n = w2i (w3 .&. 255)

  Medium4 w1 w2 w3 w4
    | n < 31    -> Medium4 w1 w2 w3 $ (w4 + 1) .|. shiftL (i2w x) ((31-n)*8)
    | otherwise -> makeWordList (n + 1) (toList compact ++ [x])
    where  
      n = w2i (w4 .&. 255)
  
  WordList n list -> WordList (n+1) (go list) where
    go :: [Word64] -> [Word64]
    go (w:[]) = case mod n 4 of
                  0 -> w : shiftL (i2w x) 48 : []
                  1 -> w + shiftL (i2w x) 32 : []
                  2 -> w + shiftL (i2w x) 16 : []
                  3 -> w +        (i2w x)    : []
    go (w:ws) = w : go ws
    go []     = shiftL (i2w x) 48 : []
 
{-   
  _ -> 
    let n = width compact
    in  makeWordList (n+1) (toList compact ++ [x])
-}

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
width compact = case compact of
  Nibble        word -> w2i (word .&.  15)
  Medium1       word -> w2i (word .&. 255)
  Medium2 _     word -> w2i (word .&. 255)
  Medium3 _ _   word -> w2i (word .&. 255)
  Medium4 _ _ _ word -> w2i (word .&. 255)
  WordList n    _    -> n

-- | Height, or the first (that is, the largest) element
height :: Partition -> Int
height compact = case compact of
  Nibble  word        -> w2i (shiftR word 60)
  Medium1 word        -> w2i (shiftR word 56)
  Medium2 word _      -> w2i (shiftR word 56)
  Medium3 word _ _    -> w2i (shiftR word 56)
  Medium4 word _ _ _  -> w2i (shiftR word 56)
  WordList _ (word:_) -> w2i (shiftR word 48)

-- | Width and height 
widthHeight :: Partition -> (Int,Int)
widthHeight compact = case compact of 
  Nibble  word            -> ( w2i (word  .&.  15) , w2i (shiftR word  60) )
  Medium1 word            -> ( w2i (word  .&. 255) , w2i (shiftR word  56) )
  Medium2 word1     word2 -> ( w2i (word2 .&. 255) , w2i (shiftR word1 56) )
  Medium3 word1 _   word3 -> ( w2i (word3 .&. 255) , w2i (shiftR word1 56) )
  Medium4 word1 _ _ word4 -> ( w2i (word4 .&. 255) , w2i (shiftR word1 56) )
  WordList n (word:_)     -> ( n                   , w2i (shiftR word  48) )

--------------------------------------------------------------------------------
-- * Differential sequence

-- | From a non-increasing sequence @[a1,a2,..,an]@ this computes the sequence of differences
-- @[a1-a2,a2-a3,...,an-0]@
diffSequence :: Partition -> [Int]
diffSequence compact = case compact of

  Nibble 0 -> []

  Nibble w -> 
    let !nw = (w .&. 15) 
        !w' = w - nw
        !n  = w2i nw
    in  [ w2i $ (shiftR w (60 - i*4) - shiftR w' (56 - i*4)) .&. 15 | i<-[0..n-1] ]

  Medium1 w -> 
    let !nw = (w .&. 255) 
        !w' = w - nw
        !n  = w2i nw
    in  [ w2i $ (shiftR w (56 - i*8) - shiftR w' (48 - i*8)) .&. 255 | i<-[0..n-1] ]

  Medium2 w1 w2 -> 
    let !nw = (w2 .&. 255) 
        !w2' = w2 - nw
        !n  = w2i nw
    in  [ w2i $ (shiftR w1 (56 - i*8) - shiftR w1  (48 - i*8)) .&. 255 | i<-[0..6]   ] ++ 
        ( w2i $ (       w1            - shiftR w2   56       ) .&. 255               ) : 
        [ w2i $ (shiftR w2 (56 - i*8) - shiftR w2' (48 - i*8)) .&. 255 | i<-[0..n-9] ] 

  Medium3 w1 w2 w3 -> 
    let !nw = (w3 .&. 255) 
        !w3' = w3 - nw
        !n  = w2i nw
    in  [ w2i $ (shiftR w1 (56 - i*8) - shiftR w1  (48 - i*8)) .&. 255 | i<-[0..6]    ] ++ 
        ( w2i $ (       w1            - shiftR w2   56       ) .&. 255                ) : 
        [ w2i $ (shiftR w2 (56 - i*8) - shiftR w2  (48 - i*8)) .&. 255 | i<-[0..6]    ] ++
        ( w2i $ (       w2            - shiftR w3   56       ) .&. 255                ) : 
        [ w2i $ (shiftR w3 (56 - i*8) - shiftR w3' (48 - i*8)) .&. 255 | i<-[0..n-17] ] 

  Medium4 w1 w2 w3 w4 -> 
    let !nw = (w4 .&. 255) 
        !w4' = w4 - nw
        !n  = w2i nw
    in  [ w2i $ (shiftR w1 (56 - i*8) - shiftR w1  (48 - i*8)) .&. 255 | i<-[0..6]    ] ++ 
        ( w2i $ (       w1            - shiftR w2   56       ) .&. 255                ) : 
        [ w2i $ (shiftR w2 (56 - i*8) - shiftR w2  (48 - i*8)) .&. 255 | i<-[0..6]    ] ++
        ( w2i $ (       w2            - shiftR w3   56       ) .&. 255                ) : 
        [ w2i $ (shiftR w3 (56 - i*8) - shiftR w3  (48 - i*8)) .&. 255 | i<-[0..6]    ] ++
        ( w2i $ (       w3            - shiftR w4   56       ) .&. 255                ) : 
        [ w2i $ (shiftR w4 (56 - i*8) - shiftR w4' (48 - i*8)) .&. 255 | i<-[0..n-25] ] 

  WordList {} -> go (toList compact) where
    go (x:ys@(y:_)) = (x-y) : go ys 
    go [x] = [x]
    go []  = []

----------------------------------------

-- | From a non-increasing sequence @[a1,a2,..,an]@ this computes the reversed sequence of differences
-- @[ a[n]-0 , a[n-1]-a[n] , ... , a[2]-a[3] , a[1]-a[2] ] @
reverseDiffSequence :: Partition -> [Int]
reverseDiffSequence compact = case compact of

  Nibble 0 -> []

  Nibble w -> 
    let !nw = (w .&. 15) 
        !w' = w - nw
        !n  = w2i nw
    in  [ w2i $ (shiftR w (60 - i*4) - shiftR w' (56 - i*4)) .&. 15 | i<-toZero (n-1) ]

  Medium1 w -> 
    let !nw = (w .&. 255) 
        !w' = w - nw
        !n  = w2i nw
    in  [ w2i $ (shiftR w (56 - i*8) - shiftR w' (48 - i*8)) .&. 255 | i<-toZero (n-1) ]

  Medium2 w1 w2 -> 
    let !nw = (w2 .&. 255) 
        !w2' = w2 - nw
        !n  = w2i nw
    in  [ w2i $ (shiftR w2 (56 - i*8) - shiftR w2' (48 - i*8)) .&. 255 | i<-toZero (n-9) ] ++
        ( w2i $ (       w1            - shiftR w2   56       ) .&. 255                   ) : 
        [ w2i $ (shiftR w1 (56 - i*8) - shiftR w1  (48 - i*8)) .&. 255 | i<-toZero 6     ]  
        
  Medium3 w1 w2 w3 -> 
    let !nw = (w3 .&. 255) 
        !w3' = w3 - nw
        !n  = w2i nw
    in  [ w2i $ (shiftR w3 (56 - i*8) - shiftR w3' (48 - i*8)) .&. 255 | i<-toZero (n-17) ] ++
        ( w2i $ (       w2            - shiftR w3   56       ) .&. 255                    ) : 
        [ w2i $ (shiftR w2 (56 - i*8) - shiftR w2  (48 - i*8)) .&. 255 | i<-toZero 6      ] ++
        ( w2i $ (       w1            - shiftR w2   56       ) .&. 255                    ) : 
        [ w2i $ (shiftR w1 (56 - i*8) - shiftR w1  (48 - i*8)) .&. 255 | i<-toZero 6      ] 

  Medium4 w1 w2 w3 w4 -> 
    let !nw = (w4 .&. 255) 
        !w4' = w4 - nw
        !n  = w2i nw
    in  [ w2i $ (shiftR w4 (56 - i*8) - shiftR w4' (48 - i*8)) .&. 255 | i<-toZero (n-25) ] ++
        ( w2i $ (       w3            - shiftR w4   56       ) .&. 255                    ) : 
        [ w2i $ (shiftR w3 (56 - i*8) - shiftR w3  (48 - i*8)) .&. 255 | i<-toZero 6      ] ++
        ( w2i $ (       w2            - shiftR w3   56       ) .&. 255                    ) : 
        [ w2i $ (shiftR w2 (56 - i*8) - shiftR w2  (48 - i*8)) .&. 255 | i<-toZero 6      ] ++
        ( w2i $ (       w1            - shiftR w2   56       ) .&. 255                    ) : 
        [ w2i $ (shiftR w1 (56 - i*8) - shiftR w1  (48 - i*8)) .&. 255 | i<-toZero 6      ] 

  WordList {} -> (h : go asclist) where
    asclist@(h:_) = toAscList compact
    go (x:ys@(y:_)) = (y-x) : go ys 
    go [_] = []
    go []  = []

--------------------------------------------------------------------------------
-- *  Dual partition

foreign import ccall unsafe "c_dual_nibble" c_dual_nibble :: Word64 -> Word64

dualPartition :: Partition -> Partition
dualPartition compact = case compact of

  Nibble 0 -> Nibble 0
  Nibble w -> Nibble (c_dual_nibble w)  
  _        -> if (w <= 255 && h <= 31)
                then makeMedium   h dualList
                else makeWordList h dualList
  where
    (w,h) = widthHeight compact
    dualList = concat
      [ replicate d j
      | (j,d) <- zip (toOne w) (reverseDiffSequence compact)
      ]

--------------------------------------------------------------------------------
-- * Conversion to list

toList :: Partition -> [Int]
toList = toDescList

-- | returns a descending (non-increasing) list
toDescList :: Partition -> [Int]
toDescList compact = case compact of

  Nibble 0 -> []

  Nibble word -> 
    let !n = w2i (word .&. 15) 
    in  [ w2i (shiftR word  (60 - i*4) .&. 15 ) | i<-[0..n-1] ]

  Medium1 word1 -> 
    let !n = w2i (word1 .&. 255)
    in  [ w2i (shiftR word1 (56 - i*8) .&. 255) | i<-[0..n-1] ]

  Medium2 word1 word2 -> 
    let !n = w2i (word2 .&. 255) 
    in  [ w2i (shiftR word1 (56 - i*8) .&. 255) | i<-[0..7]   ] ++
        [ w2i (shiftR word2 (56 - i*8) .&. 255) | i<-[0..n-9] ] 

  Medium3 word1 word2 word3 -> 
    let !n = w2i (word3 .&. 255) 
    in  [ w2i (shiftR word1 (56 - i*8) .&. 255) | i<-[0..7]    ] ++
        [ w2i (shiftR word2 (56 - i*8) .&. 255) | i<-[0..7]    ] ++
        [ w2i (shiftR word3 (56 - i*8) .&. 255) | i<-[0..n-17] ] 

  Medium4 word1 word2 word3 word4 -> 
    let !n = w2i (word4 .&. 255) 
    in  [ w2i (shiftR word1 (56 - i*8) .&. 255) | i<-[0..7]    ] ++
        [ w2i (shiftR word2 (56 - i*8) .&. 255) | i<-[0..7]    ] ++
        [ w2i (shiftR word3 (56 - i*8) .&. 255) | i<-[0..7]    ] ++
        [ w2i (shiftR word4 (56 - i*8) .&. 255) | i<-[0..n-25] ] 

  WordList _ list -> go list where
    go :: [Word64] -> [Int]
    go !wlist = case wlist of
      (!w):(!ws) -> case ws of 
        (_:_)      -> w2i (shiftR w 48          ) :
                      w2i (shiftR w 32 .&. 65535) :
                      w2i (shiftR w 16 .&. 65535) :
                      w2i (       w    .&. 65535) : go ws
        []         -> takeWhile (/=0) (fromWord w)
      []         -> []

    fromWord :: Word64 -> [Int]
    fromWord !word = 
      [ w2i (shiftR word 48          )
      , w2i (shiftR word 32 .&. 65535)
      , w2i (shiftR word 16 .&. 65535)
      , w2i (       word    .&. 65535)
      ]

----------------------------------------

-- | Returns a reversed (ascending; non-decreasing) list
toAscList :: Partition -> [Int]
toAscList compact = case compact of

  Nibble 0 -> []

  Nibble word -> 
    let !n = w2i (word .&. 15) 
    in  [ w2i (shiftR word  (60 - i*4) .&. 15 ) | i<-toZero (n-1) ]

  Medium1 word1 -> 
    let !n = w2i (word1 .&. 255)
    in  [ w2i (shiftR word1 (56 - i*8) .&. 255) | i<-toZero (n-1) ]

  Medium2 word1 word2 -> 
    let !n = w2i (word2 .&. 255) 
    in  [ w2i (shiftR word2 (56 - i*8) .&. 255) | i<-toZero (n-9) ] ++
        [ w2i (shiftR word1 (56 - i*8) .&. 255) | i<-toZero 7     ] 

  Medium3 word1 word2 word3 -> 
    let !n = w2i (word3 .&. 255) 
    in  [ w2i (shiftR word3 (56 - i*8) .&. 255) | i<-toZero (n-17) ] ++
        [ w2i (shiftR word2 (56 - i*8) .&. 255) | i<-toZero 7      ] ++
        [ w2i (shiftR word1 (56 - i*8) .&. 255) | i<-toZero 7      ]
        
  Medium4 word1 word2 word3 word4 -> 
    let !n = w2i (word4 .&. 255) 
    in  [ w2i (shiftR word4 (56 - i*8) .&. 255) | i<-toZero (n-25) ] ++
        [ w2i (shiftR word3 (56 - i*8) .&. 255) | i<-toZero 7      ] ++
        [ w2i (shiftR word2 (56 - i*8) .&. 255) | i<-toZero 7      ] ++
        [ w2i (shiftR word1 (56 - i*8) .&. 255) | i<-toZero 7      ]

  WordList _ list -> dropWhile (==0) $ go (reverse list) where
    go :: [Word64] -> [Int]
    go !wlist = case wlist of
      (!w):ws -> w2i (       w    .&. 65535) : 
                 w2i (shiftR w 16 .&. 65535) :
                 w2i (shiftR w 32 .&. 65535) :
                 w2i (shiftR w 48          ) : go ws
      [] -> []

{-
    go :: [Word64] -> [Int]
    go (w:[]) = fromWord w
    go (w:ws) = fromWord w ++ go ws
    go []     = []
    fromWord :: Word64 -> [Int]
    fromWord word = [ w2i (shiftR word (48 - i*16) .&. 65535) | i<-toZero 3 ] 
-}

--------------------------------------------------------------------------------
-- * Conversion from list

fromDescList :: [Int] -> Partition
fromDescList list = fromDescList' (length list) list

-- | We assume that the input is a non-increasing list of /positive/ integers!
fromDescList' 
  :: Int          -- ^ length
  -> [Int]        -- ^ the list
  -> Partition
fromDescList' !n !list =
  case list of
    []                           -> empty
    (h:_) | h <= 0               -> empty
          | h <= 15 && n <= 15   -> makeNibble   n list
          | h >  65535           -> error "partitions with elements bigger than 65535 are not supported"
          | h >  255 || n > 31   -> makeWordList n list
          | otherwise            -> makeMedium   n list

makeNibble :: Int -> [Int] -> Partition
makeNibble !n list = Nibble $ go (i2w n) 60 list where
  go !acc !k (x:xs) = go (acc + shiftL (i2w x) k) (k-4) xs
  go !acc _  []     = acc
{-   
makeNibble :: Int -> [Int] -> Partition
makeNibble !n list = Nibble 
  $ sum' [ shiftL (i2w x) (60 - 4*i) | (i,x) <- zip [0..] list ] 
  + i2w n
-}

makeMedium :: Int -> [Int] -> Partition
makeMedium !n list 
  | n <= 7   = makeMedium1 n list
  | n <= 15  = makeMedium2 n list
  | n <= 23  = makeMedium3 n list
  | n <= 31  = makeMedium4 n list
  | otherwise = error "makeMedium: input list too big (should be smaller than 32)"

makeMedium1 :: Int -> [Int] -> Partition
makeMedium1 !n list = Medium1 
  $ sum' [ shiftL (fromIntegral x) (56 - 8*i) | (i,x) <- zip [0..] list ] 
  + fromIntegral n

makeMedium2 :: Int -> [Int] -> Partition
makeMedium2 !n list = Medium2 word1 word2 where
  (list1,list2) = splitAt 8 list
  word1 = sum' [ shiftL (i2w x) (56 - 8*i) | (i,x) <- zip [0..] list1 ] 
  word2 = sum' [ shiftL (i2w x) (56 - 8*i) | (i,x) <- zip [0..] list2 ] 
        + fromIntegral n

makeMedium3 :: Int -> [Int] -> Partition
makeMedium3 !n list = Medium3 word1 word2 word3 where
  (list1,tmp  ) = splitAt 8 list
  (list2,list3) = splitAt 8 tmp
  word1 = sum' [ shiftL (i2w x) (56 - 8*i) | (i,x) <- zip [0..] list1 ] 
  word2 = sum' [ shiftL (i2w x) (56 - 8*i) | (i,x) <- zip [0..] list2 ] 
  word3 = sum' [ shiftL (i2w x) (56 - 8*i) | (i,x) <- zip [0..] list3 ] 
        + i2w n

makeMedium4 :: Int -> [Int] -> Partition
makeMedium4 !n list = Medium4 word1 word2 word3 word4 where
  (list1,tmp1 ) = splitAt 8 list
  (list2,tmp2 ) = splitAt 8 tmp1
  (list3,list4) = splitAt 8 tmp2
  word1 = sum' [ shiftL (i2w x) (56 - 8*i) | (i,x) <- zip [0..] list1 ] 
  word2 = sum' [ shiftL (i2w x) (56 - 8*i) | (i,x) <- zip [0..] list2 ] 
  word3 = sum' [ shiftL (i2w x) (56 - 8*i) | (i,x) <- zip [0..] list3 ] 
  word4 = sum' [ shiftL (i2w x) (56 - 8*i) | (i,x) <- zip [0..] list4 ] 
        + i2w n
    
makeWordList :: Int -> [Int] -> Partition
makeWordList !n list = WordList n (go list) where   
  go :: [Int] -> [Word64]
  go !xs = case xs of
    (x:y:z:w:rest) -> makeWord x y z w : go rest
    (x:y:z:  []  ) -> makeWord x y z 0 : []
    (x:y:    []  ) -> makeWord x y 0 0 : []
    (x:      []  ) -> makeWord x 0 0 0 : []
    []             -> []
  makeWord !x !y !z !w = shiftL (i2w x) 48  
                       + shiftL (i2w y) 32  
                       + shiftL (i2w z) 16 
                       +        (i2w w)
{-
  go [] = []
  go xs = case splitAt 4 xs of
    (this,rest) -> case rest of
      [] -> makeWord (take 4 $ this ++ repeat 0) : []
      _  -> makeWord this : go rest
  makeWord [x,y,z,w] = shiftL (i2w x) 48  
                     + shiftL (i2w y) 32  
                     + shiftL (i2w z) 16 
                     +        (i2w w)
-}

--------------------------------------------------------------------------------
-- * Partial orderings

isSubPartitionOf :: Partition -> Partition -> Bool
isSubPartitionOf p q = case (p,q) of

  (Nibble 0 , _       ) -> True
  
  (Nibble u , Nibble v) -> let !n = w2i (u .&. 15) 
                           in  and [    (shiftR u (60 - i*4) .&. 15)
                                     <= (shiftR v (60 - i*4) .&. 15) 
                                   | i<-[0..n-1] 
                                   ]

  _                     -> and $ zipWith (<=) (toList p) (toList q ++ repeat 0)

dominates :: Partition -> Partition -> Bool
dominates q p = case (q,p) of

  (_        , Nibble 0 ) -> True

  (Nibble v , Nibble u ) -> go 60 0 0 where
                              n = u .&. 15                              
                              klimit = w2i (4*(15-n))
                              go !k !b !a = if k <= klimit 
                                then True
                                else let !b' = b + (shiftR v k .&. 15)
                                         !a' = a + (shiftR u k .&. 15)
                                     in  if b' < a' 
                                           then False 
                                           else go (k-4) b' a'

  _                      -> and $ zipWith (>=) (sums $ toList q ++ repeat 0) (sums $ toList p) where
                              sums = tail . scanl' (+) 0

--------------------------------------------------------------------------------
-- * Pieri rule

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

--------------------------------------------------------------------------------
-- * local (internally used) utility functions

{-# INLINE i2w #-}
i2w :: Int -> Word64
i2w = fromIntegral

{-# INLINE w2i #-}
w2i :: Word64 -> Int
w2i = fromIntegral

{-# INLINE sum' #-}
sum' :: [Word64] -> Word64
sum' = foldl' (+) 0

{-# INLINE safeTail #-}
safeTail :: [Int] -> [Int]
safeTail xs = case xs of { [] -> [] ; _ -> tail xs }

{-# INLINE toZero #-}
toZero :: Int -> [Int]
toZero !n
  | n >  0  = n : toZero (n-1) 
  | n == 0  = [0]
  | n <  0  = []

{-# INLINE toOne #-}
toOne :: Int -> [Int]
toOne !n
  | n >  1  = n : toOne (n-1) 
  | n == 1  = [1]
  | n <  1  = []

--------------------------------------------------------------------------------


