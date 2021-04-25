
-- | The Littlewood-Richardson rule

module Math.Combinat.Tableaux.LittlewoodRichardson 
  ( lrCoeff , lrCoeff'
  , lrMult
  , lrRule  , _lrRule , lrRuleNaive
  , lrScalar , _lrScalar
  ) 
  where

--------------------------------------------------------------------------------

import Data.List
import Data.Maybe

import Math.Combinat.Partitions.Integer
import Math.Combinat.Partitions.Skew
import Math.Combinat.Tableaux
import Math.Combinat.Tableaux.Skew
import Math.Combinat.Helper

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

--------------------------------------------------------------------------------

-- | Naive (very slow) reference implementation of the Littlewood-Richardson rule, based 
-- on the definition "count the semistandard skew tableaux whose row content is a lattice word"
--
lrRuleNaive :: SkewPartition -> Map Partition Int
lrRuleNaive skew = final where
  n     = skewPartitionWeight skew
  ssst  = semiStandardSkewTableaux n skew 
  final = foldl' f Map.empty $ catMaybes [ skewTableauRowContent skew | skew <- ssst  ]
  f old nu = Map.insertWith (+) nu 1 old

--------------------------------------------------------------------------------
-- SKEW EXPANSION

-- | @lrRule@ computes the expansion of a skew Schur function 
-- @s[lambda\/mu]@ via the Littlewood-Richardson rule.
--
-- Adapted from John Stembridge's Maple code: 
-- <http://www.math.lsa.umich.edu/~jrs/software/SFexamples/LR_rule>
--
-- > lrRule (mkSkewPartition (lambda,nu)) == Map.fromList list where
-- >   muw  = weight lambda - weight nu
-- >   list = [ (mu, coeff) 
-- >          | mu <- partitions muw 
-- >          , let coeff = lrCoeff lambda (mu,nu)
-- >          , coeff /= 0
-- >          ] 
--
lrRule :: SkewPartition -> Map Partition Int
lrRule skew = _lrRule lam mu where
  (lam,mu) = fromSkewPartition skew

-- | @_lrRule lambda mu@ computes the expansion of the skew
-- Schur function @s[lambda\/mu]@ via the Littlewood-Richardson rule.
--
_lrRule :: Partition -> Partition -> Map Partition Int
_lrRule plam@(Partition lam) pmu@(Partition mu0) = 
  if not (pmu `isSubPartitionOf` plam) 
    then Map.empty
    else foldl' f Map.empty [ nu | (nu,_) <- fillings n diagram ]
  where
    f old nu = Map.insertWith (+) (Partition nu) 1 old
    diagram  = [ (i,j) | (i,a,b) <- reverse (zip3 [1..] lam mu) , j <- [b+1..a] ]    
    mu       = mu0 ++ repeat 0
    n        = sum' $ zipWith (-) lam mu    -- n == length diagram

{-
LR_rule:=proc(lambda) local l,mu,alpha,beta,i,j,dgrm;
  if not `LR_rule/fit`(lambda,args[2]) then RETURN(0) fi;
  l:=nops(lambda); mu:=[op(args[2]),0$l];
  dgrm:=[seq(seq([i,-j],j=-lambda[i]..-1-mu[i]),i=1..l)];
  if nargs>2 then alpha:=args[3];
    if nargs>3 then beta:=args[4] else beta:=[] fi;
    if not `LR_rule/fit`(alpha,beta) then RETURN(0) fi;
    l:=convert([op(lambda),op(beta)],`+`);
    if l<>convert([op(alpha),op(mu)],`+`) then RETURN(0) fi;
    nops(LR_fillings(dgrm,[alpha,beta]))
  else
    convert([seq(s[op(i[1])],i=LR_fillings(dgrm))],`+`)
  fi
end;
-}

--------------------------------------------------------------------------------

-- | A filling is a pair consisting a shape @nu@ and a lattice permutation @lp@
type Filling = ( [Int] , [Int] )

-- | A diagram is a set of boxes in a skew shape (in the right order)
type Diagram = [ (Int,Int) ]

-- | Note: we use reverse ordering in Diagrams compared the Stembridge's code.
-- Also, for performance reasons, we need the length of the diagram
fillings :: Int -> Diagram -> [Filling]
fillings _ []                   = [ ([],[]) ]
fillings n diagram@((x,y):rest) = concatMap (nextLetter lower upper) (fillings (n-1) rest) where
  upper = case findIndex (==(x  ,y+1)) diagram of { Just j -> n-j ; Nothing -> 0 }
  lower = case findIndex (==(x-1,y  )) diagram of { Just j -> n-j ; Nothing -> 0 }

{-
LR_fillings:=proc(dgrm) local n,x,upper,lower;
  if dgrm=[] then
    if nargs=1 then x:=[] else x:=args[2][2] fi;
    RETURN([[x,[]]])
  fi;
  n:=nops(dgrm); x:=dgrm[n];
  if not member([x[1],x[2]+1],dgrm,'upper') then upper:=0 fi;
  if not member([x[1]-1,x[2]],dgrm,'lower') then lower:=0 fi;
  if nargs=1 then
    map(`LR/nextletter`,LR_fillings([op(1..n-1,dgrm)]),lower,upper)
  else
    map(`LR/nextletter`,LR_fillings([op(1..n-1,dgrm)],args[2]),
      lower,upper,args[2][1])
  fi;
end:
-}

--------------------------------------------------------------------------------

nextLetter :: Int -> Int -> Filling -> [Filling]
nextLetter lower upper (nu,lpart) = stuff where
  stuff = [ ( incr i shape , lpart++[i] ) | i<-nlist ] 
  shape = nu ++ [0] 
  lb = if lower>0
    then lpart !! (lower-1)
    else 0
  ub = if upper>0 
    then min (length shape) (lpart !! (upper-1))  
    else      length shape

  nlist = filter (>0) $ map f [lb+1..ub] 
  f j   = if j==1 || shape!!(j-2) > shape!!(j-1) then j else 0

{-
  -- another nlist implementation, but doesn't seem to be faster
  (h0:hs0) = drop lb (-666:shape)
  nlist = go h0 hs0 [lb+1..ub] where
    go !lasth (h:hs) (j:js) = if j==1 || lasth > h 
      then j : go h hs js 
      else     go h hs js
    go _      _      []     = []
-}

  -- increments the i-th element (starting from 1)
  incr :: Int -> [Int] -> [Int]
  incr i (x:xs) = case i of
    0 ->         finish (x:xs)
    1 -> (x+1) : finish xs
    _ -> x     : incr (i-1) xs
  incr _ []     = []

  -- removes tailing zeros
  finish :: [Int] -> [Int]
  finish (x:xs) = if x>0 then x : finish xs else []    
  finish []     = [] 

{-
`LR/nextletter`:=proc(T) local shape,lp,lb,ub,i,nl;
  shape:=[op(T[1]),0]; lp:=T[2]; ub:=nops(shape);
  if nargs>3 then ub:=min(ub,nops(args[4])) fi;
  if args[2]=0 then lb:=0 else lb:=lp[args[2]] fi;
  if args[3]>0 then ub:=min(lp[args[3]],ub) fi;
  if nargs<4 then
    nl:=map(proc(x,y) if x=1 or y[x-1]>y[x] then x fi end,[$lb+1..ub],shape)
  else
    nl:=map(proc(x,y,z) if y[x]<z[x] and (x=1 or y[x-1]>y[x]) then x fi end,
      [$lb+1..ub],shape,args[4])
  fi;
  nl:=[seq([subsop(i=shape[i]+1,shape),[op(lp),i]],i=nl)];
  op(subs(0=NULL,nl))
end:
-}

--------------------------------------------------------------------------------
-- COEFF

-- | @lrCoeff lam (mu,nu)@ computes the coressponding Littlewood-Richardson coefficients.
-- This is also the coefficient of @s[lambda]@ in the product @s[mu]*s[nu]@
--
-- Note: This is much slower than using 'lrRule' or 'lrMult' to compute several coefficients
-- at the same time!
lrCoeff :: Partition -> (Partition,Partition) -> Int
lrCoeff lam (mu,nu) = 
  if nu `isSubPartitionOf` lam
    then lrScalar (mkSkewPartition (lam,nu)) (mkSkewPartition (mu,emptyPartition))
    else 0

-- | @lrCoeff (lam\/nu) mu@ computes the coressponding Littlewood-Richardson coefficients.
-- This is also the coefficient of @s[mu]@ in the product @s[lam\/nu]@
--
-- Note: This is much slower than using 'lrRule' or 'lrMult' to compute several coefficients
-- at the same time!
lrCoeff' :: SkewPartition -> Partition -> Int
lrCoeff' skew p = lrScalar skew (mkSkewPartition (p,emptyPartition))
  
--------------------------------------------------------------------------------
-- SCALAR PRODUCT

-- | @lrScalar (lambda\/mu) (alpha\/beta)@ computes the scalar product of the two skew
-- Schur functions @s[lambda\/mu]@ and @s[alpha\/beta]@ via the Littlewood-Richardson rule.
--
-- Adapted from John Stembridge Maple code: 
-- <http://www.math.lsa.umich.edu/~jrs/software/SFexamples/LR_rule>
--
lrScalar :: SkewPartition -> SkewPartition -> Int
lrScalar lambdaMu alphaBeta = _lrScalar (fromSkewPartition lambdaMu) (fromSkewPartition alphaBeta)

_lrScalar :: (Partition,Partition) -> (Partition,Partition) -> Int
_lrScalar ( plam@(  Partition lam  ) , pmu@(  Partition mu0 ) ) 
          ( palpha@(Partition alpha) , pbeta@(Partition beta) ) = 
  if    not (pmu   `isSubPartitionOf` plam  ) 
     || not (pbeta `isSubPartitionOf` palpha) 
     || (sum' lam + sum' beta) /= (sum' alpha + sum' mu0)     -- equivalent to (lambda-mu) /= (alpha-beta)
    then 0
    else length $ fillings' n diagram (alpha,beta) 
  where
    f old nu = Map.insertWith (+) (Partition nu) 1 old
    diagram  = [ (i,j) | (i,a,b) <- reverse (zip3 [1..] lam mu) , j <- [b+1..a] ]    
    mu       = mu0 ++ repeat 0
    n        = sum' $ zipWith (-) lam mu    -- n == length diagram

{-
LR_rule:=proc(lambda) local l,mu,alpha,beta,i,j,dgrm;
  if not `LR_rule/fit`(lambda,args[2]) then RETURN(0) fi;
  l:=nops(lambda); mu:=[op(args[2]),0$l];
  dgrm:=[seq(seq([i,-j],j=-lambda[i]..-1-mu[i]),i=1..l)];
  if nargs>2 then alpha:=args[3];
    if nargs>3 then beta:=args[4] else beta:=[] fi;
    if not `LR_rule/fit`(alpha,beta) then RETURN(0) fi;
    l:=convert([op(lambda),op(beta)],`+`);
    if l<>convert([op(alpha),op(mu)],`+`) then RETURN(0) fi;
    nops(LR_fillings(dgrm,[alpha,beta]))
  else
    convert([seq(s[op(i[1])],i=LR_fillings(dgrm))],`+`)
  fi
end;
-}

--------------------------------------------------------------------------------

-- | Note: we use reverse ordering in Diagrams compared the Stembridge's code.
-- Also, for performance reasons, we need the length of the diagram
fillings' :: Int -> Diagram -> ([Int],[Int]) -> [Filling]
fillings' _         []                     (alpha,beta) = [ (beta,[]) ]
fillings' n diagram@((x,y):rest) alphaBeta@(alpha,beta) = stuff where
  stuff = concatMap (nextLetter' lower upper alpha) (fillings' (n-1) rest alphaBeta) 
  upper = case findIndex (==(x  ,y+1)) diagram of { Just j -> n-j ; Nothing -> 0 }
  lower = case findIndex (==(x-1,y  )) diagram of { Just j -> n-j ; Nothing -> 0 }

{-
LR_fillings:=proc(dgrm) local n,x,upper,lower;
  if dgrm=[] then
    if nargs=1 then x:=[] else x:=args[2][2] fi;
    RETURN([[x,[]]])
  fi;
  n:=nops(dgrm); x:=dgrm[n];
  if not member([x[1],x[2]+1],dgrm,'upper') then upper:=0 fi;
  if not member([x[1]-1,x[2]],dgrm,'lower') then lower:=0 fi;
  if nargs=1 then
    map(`LR/nextletter`,LR_fillings([op(1..n-1,dgrm)]),lower,upper)
  else
    map(`LR/nextletter`,LR_fillings([op(1..n-1,dgrm)],args[2]),
      lower,upper,args[2][1])
  fi;
end:
-}

--------------------------------------------------------------------------------

nextLetter' :: Int -> Int -> [Int] -> Filling -> [Filling]
nextLetter' lower upper alpha (nu,lpart) = stuff where
  stuff = [ ( incr i shape , lpart++[i] ) | i<-nlist ] 
  shape = nu ++ [0] 
  lb = if lower>0
    then lpart !! (lower-1)
    else 0
  ub1 = if upper>0 
    then min (length shape) (lpart !! (upper-1))  
    else      length shape
  ub = min (length alpha) ub1
  nlist = filter (>0) $ map f [lb+1..ub] 
  f j   = if (        shape!!(j-1) < alpha!!(j-1)) &&
             (j==1 || shape!!(j-2) > shape!!(j-1)) 
          then j 
          else 0

  -- increments the i-th element (starting from 1)
  incr :: Int -> [Int] -> [Int]
  incr i (x:xs) = case i of
    0 ->         finish (x:xs)
    1 -> (x+1) : finish xs
    _ -> x     : incr (i-1) xs
  incr _ []     = []

  -- removes tailing zeros
  finish :: [Int] -> [Int]
  finish (x:xs) = if x>0 then x : finish xs else []    
  finish []     = [] 

{-
`LR/nextletter`:=proc(T) local shape,lp,lb,ub,i,nl;
  shape:=[op(T[1]),0]; lp:=T[2]; ub:=nops(shape);
  if nargs>3 then ub:=min(ub,nops(args[4])) fi;
  if args[2]=0 then lb:=0 else lb:=lp[args[2]] fi;
  if args[3]>0 then ub:=min(lp[args[3]],ub) fi;
  if nargs<4 then
    nl:=map(proc(x,y) if x=1 or y[x-1]>y[x] then x fi end,[$lb+1..ub],shape)
  else
    nl:=map(proc(x,y,z) if y[x]<z[x] and (x=1 or y[x-1]>y[x]) then x fi end,
      [$lb+1..ub],shape,args[4])
  fi;
  nl:=[seq([subsop(i=shape[i]+1,shape),[op(lp),i]],i=nl)];
  op(subs(0=NULL,nl))
end:
-}

--------------------------------------------------------------------------------
-- MULTIPLICATION

type Part = [Int]

-- | Computes the expansion of the product of Schur polynomials @s[mu]*s[nu]@ using the
-- Littlewood-Richardson rule. Note: this is symmetric in the two arguments.
--
-- Based on the wikipedia article <https://en.wikipedia.org/wiki/Littlewood-Richardson_rule>
--
-- > lrMult mu nu == Map.fromList list where
-- >   lamw = weight nu + weight mu
-- >   list = [ (lambda, coeff) 
-- >          | lambda <- partitions lamw 
-- >          , let coeff = lrCoeff lambda (mu,nu)
-- >          , coeff /= 0
-- >          ] 
--
lrMult :: Partition -> Partition -> Map Partition Int
lrMult pmu@(Partition mu) pnu@(Partition nu) = result where
  result = foldl' add Map.empty (addMu mu nu) where
  add !old lambda = Map.insertWith (+) (Partition lambda) 1 old

-- | This basically lists all the outer shapes (with multiplicities) which can be result from the LR rule
addMu :: Part -> Part -> [Part]
addMu mu part = go ubs0 mu dmu part where

  go _   []     _      part = [part]
  go ubs (m:ms) (d:ds) part = concat [ go (drop d ubs') ms ds part' | (ubs',part') <- addRowOf ubs part ]

  ubs0 = take (headOrZero mu) [headOrZero part + 1..]
  dmu  = diffSeq mu


-- | Adds a full row of @(length pcols)@ boxes containing to a partition, with
-- pcols being the upper bounds of the columns, respectively. We also return the
-- newly added columns
addRowOf :: [Int] -> Part -> [([Int],Part)]
addRowOf pcols part = go 0 pcols part [] where
  go !lb []        p ncols = [(reverse ncols , p)]
  go !lb (!ub:ubs) p ncols = concat [ go col ubs (addBox ij p) (col:ncols) | ij@(row,col) <- newBoxes (lb+1) ub p ]

-- | Returns the (row,column) pairs of the new boxes which 
-- can be added to the given partition with the given column bounds
-- and the 1-Rieri rule 
newBoxes :: Int -> Int -> Part -> [(Int,Int)]
newBoxes lb ub part = reverse $ go [1..] part (headOrZero part + 1) where
  go (!i:_ ) []      !lp
    | lb <= 1 && 1 <= ub && lp > 0  =  [(i,1)]
    | otherwise                     =  []
  go (!i:is) (!j:js) !lp 
    | j1 <  lb            =  []
    | j1 <= ub && lp > j  =  (i,j1) : go is js j       
    | otherwise           =           go is js j
    where 
      j1 = j+1

-- | Adds a box to a partition
addBox :: (Int,Int) -> Part -> Part
addBox (k,_) part = go 1 part where
  go !i (p:ps) = if i==k then (p+1):ps else p : go (i+1) ps
  go !i []     = if i==k then [1] else error "addBox: shouldn't happen"

-- | Safe head defaulting to zero           
headOrZero :: [Int] -> Int
headOrZero xs = case xs of 
  (!x:_) -> x
  []     -> 0

-- | Computes the sequence of differences from a partition (including the last difference to zero)
diffSeq :: Part -> [Int]
diffSeq = go where
  go (p:ps@(q:_)) = (p-q) : go ps
  go [p]          = [p]
  go []           = []

--------------------------------------------------------------------------------  
