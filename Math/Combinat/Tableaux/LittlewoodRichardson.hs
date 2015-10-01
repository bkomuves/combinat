
-- | The Littlewood-Richardson rule

module Math.Combinat.Tableaux.LittlewoodRichardson 
  ( lrRule , _lrRule 
  , lrRuleNaive
  ) 
  where

--------------------------------------------------------------------------------

import Data.List
import Data.Maybe

import Math.Combinat.Partitions.Integer
import Math.Combinat.Partitions.Skew
import Math.Combinat.Tableaux
import Math.Combinat.Tableaux.Skew

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

--------------------------------------------------------------------------------

-- | Naive, reference implementation of the Littlewood-Richardson rule, based on the definition
-- "count the semistandard skew tableaux whose row content is a lattice word"
--
lrRuleNaive :: SkewPartition -> Map Partition Int
lrRuleNaive skew = final where
  n     = skewPartitionWeight skew
  ssst  = semiStandardSkewTableaux n skew 
  final = foldl' f Map.empty $ catMaybes [ skewTableauRowContent skew | skew <- ssst  ]
  f old nu = Map.insertWith (+) nu 1 old

--------------------------------------------------------------------------------

-- | @lrRule@ computes the expansion of a skew Schur function 
-- @s[lambda/mu]@ via the Littlewood-Richardson rule.
--
-- Adapted from John Stembridge's Maple code: 
-- <http://www.math.lsa.umich.edu/~jrs/software/SFexamples/LR_rule>
--
lrRule :: SkewPartition -> Map Partition Int
lrRule skew = _lrRule lam mu where
  (lam,mu) = fromSkewPartition skew

-- | @_lrRule lambda mu@ computes the expansion of the skew
-- Schur function @s[lambda/mu]@ via the Littlewood-Richardson rule.
---
{-# SPECIALIZE _lrRule :: Partition -> Partition -> Map Partition Int     #-}
{-# SPECIALIZE _lrRule :: Partition -> Partition -> Map Partition Integer #-}
_lrRule :: Num coeff => Partition -> Partition -> Map Partition coeff
_lrRule plam@(Partition lam) pmu@(Partition mu0) = 
  if not (pmu `isSubPartitionOf` plam) 
    then Map.empty
    else foldl' f Map.empty [ nu | (nu,_) <- fillings n diagram ]
  where
    f old nu = Map.insertWith (+) (Partition nu) 1 old
    diagram  = [ (i,j) | (i,a,b) <- reverse (zip3 [1..] lam mu) , j <- [b+1..a] ]    
    mu       = mu0 ++ repeat 0
    n        = sum $ zipWith (-) lam mu    -- n == length diagram

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


