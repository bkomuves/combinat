
-- | A mini-DSL for ASCII drawing of structures.
--
--
-- From some structures there is also Graphviz and\/or @diagrams@ 
-- (<http://projects.haskell.org/diagrams>) visualization support 
-- (the latter in the separate libray @combinat-diagrams@).
--

module Math.Combinat.ASCII where

--------------------------------------------------------------------------------

import Data.List

import Math.Combinat.Helper

--------------------------------------------------------------------------------
-- * The basic type

-- | The type of a (rectangular) ASCII figure. 
-- Internally it is a list of lines of the same length plus the size.
--
-- Note: The Show instance is pretty-printing, so that it\'s convenient in ghci.
--
data ASCII = ASCII 
  { asciiSize  :: (Int,Int) 
  , asciiLines :: [String]
  }

instance Show ASCII where
  show = asciiString

-- | An empty (0x0) rectangle
emptyRect :: ASCII
emptyRect = ASCII (0,0) []

asciiXSize, asciiYSize :: ASCII -> Int
asciiXSize = fst . asciiSize
asciiYSize = snd . asciiSize

asciiString :: ASCII -> String
asciiString (ASCII sz ls) = unlines ls

printASCII :: ASCII -> IO ()
printASCII = putStrLn . asciiString

asciiFromLines :: [String] -> ASCII
asciiFromLines ls = ASCII (x,y) (map f ls) where
  y   = length ls
  x   = maximum (map length ls)
  f l = l ++ replicate (x - length l) ' '

asciiFromString :: String -> ASCII
asciiFromString = asciiFromLines . lines

--------------------------------------------------------------------------------
-- * Alignment

-- | Horizontal alignment
data HAlign 
  = HLeft 
  | HCenter 
  | HRight 
  deriving (Eq,Show)

-- | Vertical alignment
data VAlign 
  = VTop 
  | VCenter 
  | VBottom 
  deriving (Eq,Show)

data Alignment = Align HAlign VAlign
                                        
--------------------------------------------------------------------------------
-- * Extension

-- | Extends an ASCII figure with spaces horizontally to the given width 
hExtendTo :: HAlign -> Int -> ASCII -> ASCII
hExtendTo halign n0 rect@(ASCII (x,y) ls) = hExtendWith halign (max n0 x - x) rect
  
-- | Extends an ASCII figure with spaces vertically to the given height
vExtendTo :: VAlign -> Int -> ASCII -> ASCII
vExtendTo valign n0 rect@(ASCII (x,y) ls) = vExtendWith valign (max n0 y - y) rect

-- | Extend horizontally with the given number of spaces
hExtendWith :: HAlign -> Int -> ASCII -> ASCII
hExtendWith alignment d (ASCII (x,y) ls) = ASCII (x+d,y) (map f ls) where
  f l = case alignment of
    HLeft   -> l ++ replicate d ' '   
    HRight  -> replicate d ' ' ++ l
    HCenter -> replicate a ' ' ++ l ++ replicate (d-a) ' ' 
  a = div d 2

-- | Extend vertically with the given number of empty lines
vExtendWith :: VAlign -> Int -> ASCII -> ASCII
vExtendWith valign d (ASCII (x,y) ls) = ASCII (x,y+d) (f ls) where
  f ls = case valign of
    VTop     -> ls ++ replicate d emptyline   
    VBottom  -> replicate d emptyline ++ ls
    VCenter  -> replicate a emptyline ++ ls ++ replicate (d-a) emptyline
  a = div d 2
  emptyline = replicate x ' '

-- | Horizontal indentation
hIndent :: Int -> ASCII -> ASCII
hIndent d = hExtendWith HRight d

-- | Vertical indentation
vIndent :: Int -> ASCII -> ASCII
vIndent d = vExtendWith VBottom d

--------------------------------------------------------------------------------
-- * Separators

-- | Horizontal separator
data HSep 
  = HSepEmpty           -- ^ empty separator
  | HSepSpaces Int      -- ^ @n@ spaces
  | HSepString String   -- ^ some custom string, eg. @\" | \"@
  deriving Show

hSepSize :: HSep -> Int
hSepSize hsep = case hsep of
  HSepEmpty    -> 0
  HSepSpaces k -> k
  HSepString s -> length s

hSepString :: HSep -> String
hSepString hsep = case hsep of
  HSepEmpty    -> ""
  HSepSpaces k -> replicate k ' '
  HSepString s -> s

-- | Vertical separator
data VSep 
  = VSepEmpty           -- ^ empty separator
  | VSepSpaces Int      -- ^ @n@ spaces
  | VSepString [Char]   -- ^ some custom list of characters, eg. @\" - \"@ (the characters are interpreted as below each other)
  deriving Show

vSepSize :: VSep -> Int
vSepSize vsep = case vsep of
  VSepEmpty    -> 0
  VSepSpaces k -> k
  VSepString s -> length s

vSepString :: VSep -> [Char]
vSepString vsep = case vsep of
  VSepEmpty    -> []
  VSepSpaces k -> replicate k ' '
  VSepString s -> s

--------------------------------------------------------------------------------
-- * Padding

-- | Horizontally pads with the given number of spaces, on both sides
hPad :: Int -> ASCII -> ASCII
hPad k (ASCII (x,y) ls) = ASCII (x+2*k,y) (map f ls) where
  f l = pad ++ l ++ pad 
  pad = replicate k ' '

-- | Vertically pads with the given number of empty lines, on both sides
vPad :: Int -> ASCII -> ASCII
vPad k (ASCII (x,y) ls) = ASCII (x,y+2*k) (pad ++ ls ++ pad) where
  pad = replicate k (replicate x ' ')

-- | Pads by single empty lines vertically and two spaces horizontally
pad :: ASCII -> ASCII
pad = vPad 1 . hPad 2 

--------------------------------------------------------------------------------
-- * Concatenation

-- | Horizontal concatenation
hCatWith :: VAlign -> HSep -> [ASCII] -> ASCII
hCatWith valign hsep rects = ASCII (x',maxy) final where
  n    = length rects
  maxy = maximum [ y | ASCII (_,y) _ <- rects ]
  xsz  =         [ x | ASCII (x,_) _ <- rects ]
  sep   = hSepString hsep
  sepx  = length sep
  rects1 = map (vExtendTo valign maxy) rects
  x' = sum' xsz + (n-1)*sepx
  final = map (intercalate sep) $ transpose (map asciiLines rects1)

-- | Vertical concatenation
vCatWith :: HAlign -> VSep -> [ASCII] -> ASCII
vCatWith halign vsep rects = ASCII (maxx,y') final where
  n    = length rects
  maxx = maximum [ x | ASCII (x,_) _ <- rects ]
  ysz  =         [ y | ASCII (_,y) _ <- rects ]
  sepy    = vSepSize vsep
  fullsep = transpose (replicate maxx $ vSepString vsep) :: [String]
  rects1  = map (hExtendTo halign maxx) rects
  y'    = sum' ysz + (n-1)*sepy
  final = intercalate fullsep $ map asciiLines rects1

--------------------------------------------------------------------------------
-- * Tabulate

tabulate :: (HAlign,VAlign) -> (HSep,VSep) -> [[ASCII]] -> ASCII
tabulate (halign,valign) (hsep,vsep) rects0 = final where
  n = length rects0
  m = maximum (map length rects0)
  rects1 = map (\rs -> rs ++ replicate (m - length rs) emptyRect) rects0
  ys = map (\rs -> maximum (map asciiYSize rs)) rects1
  xs = map (\rs -> maximum (map asciiXSize rs)) (transpose rects1)
  rects2 = map (\rs -> [      hExtendTo halign x  r  | (x,r ) <- zip xs rs     ]) rects1
  rects3 =             [ map (vExtendTo valign y) rs | (y,rs) <- zip ys rects2 ]  
  final  = vCatWith HLeft vsep 
         $ map (hCatWith VTop hsep) rects3

-- | Order of elements in a matrix
data MatrixOrder 
  = RowMajor
  | ColMajor
  deriving (Eq,Ord,Show,Read)

-- | Automatically tabulates ASCII rectangles.
--
autoTabulate 
  :: MatrixOrder      -- ^ whether to use row-major or column-major ordering of the elements
  -> Either Int Int   -- ^ @(Right x)@ creates x columns, while @(Left y)$ creates y rows
  -> [ASCII]          -- ^ list of ASCII rectangles
  -> ASCII
autoTabulate mtxorder ei list = final where
  
  final = tabulate (HLeft,VBottom) (HSepSpaces 2,VSepSpaces 1) rects 

  n = length list

  rects = case ei of

    Left y  -> case mtxorder of
                 ColMajor -> transpose (parts y list)
                 RowMajor -> invparts y list

    Right x -> case mtxorder of
                 ColMajor -> transpose (invparts x list)
                 RowMajor -> parts x list

  transposeIf b = if b then transpose else id

  -- chops into parts (the last one can be smaller)
  parts d = go where
    go [] = []
    go xs = take d xs : go (drop d xs)

  invparts d xs = parts' ds xs where
    (q,r) = divMod n d
    ds = replicate r (q+1) ++ replicate (d-r) q

  parts' ds xs = go ds xs where
    go _  [] = []                                      
    go [] _  = []
    go (d:ds) xs = take d xs : go ds (drop d xs)

--------------------------------------------------------------------------------
-- * Captions

-- | Adds a caption to the bottom, with default settings.
caption :: String -> ASCII -> ASCII
caption = caption' False HLeft

-- | Adds a caption to the bottom. The @Bool@ flag specifies whether to add an empty between 
-- the caption and the figure
caption' :: Bool -> HAlign -> String -> ASCII -> ASCII
caption' emptyline halign str rect = vCatWith halign sep [rect,capt] where
  sep  = if emptyline then VSepSpaces 1 else VSepEmpty 
  capt = asciiFromString str

--------------------------------------------------------------------------------
-- * Testing \/ miscellanea

-- | An ASCII box of the given size
asciiBox :: (Int,Int) -> ASCII
asciiBox (x,y) = ASCII (max x 2, max y 2) (h : replicate (y-2) m ++ [h]) where
  h = "+" ++ replicate (x-2) '-' ++ "+"
  m = "|" ++ replicate (x-2) ' ' ++ "|"

-- | An \"rounded\" ASCII box of the given size
roundedAsciiBox :: (Int,Int) -> ASCII
roundedAsciiBox (x,y) = ASCII (max x 2, max y 2) (a : replicate (y-2) m ++ [b]) where
  a = "/"  ++ replicate (x-2) '-' ++ "\\"
  m = "|"  ++ replicate (x-2) ' ' ++ "|"
  b = "\\" ++ replicate (x-2) '-' ++ "/"

asciiNumber :: Int -> ASCII
asciiNumber = asciiShow

asciiShow :: Show a => a -> ASCII
asciiShow = asciiFromLines . (:[]) . show

--------------------------------------------------------------------------------
