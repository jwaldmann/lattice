{-# language NoMonomorphismRestriction #-}

import qualified Data.ByteString as BS
import Data.Attoparsec.ByteString.Char8 
    (parseOnly, endOfInput, decimal, signed,  char, skipSpace, )
import Control.Applicative
import Control.Monad 
import System.IO
import System.Environment
import System.Random
import Data.List ( sort, sortBy, inits, minimumBy, partition, transpose )
import Data.Function (on)

import Numeric.Limp.Rep
import Numeric.Limp.Program
import qualified Numeric.Limp.Solvers.Cbc as C
import qualified Data.Map as M
       
powers :: Double -> Int -> Double -> [[Int]]
powers alpha d n = for [0..d] $ \ e ->
    round (n * alpha ^ e) : for [0..d] ( \ i -> 
       if e == i then 1 else 0 )

q = [ [ 1901 , 2914 , 1906 , -3444 ]
    , [ 550 , 845 , 553 , -997 ]
    , [ 1347 , 2368 , 1427 , -2848 ]
    , [ 1061 , 1849 , 1133 , -2202 ]
    ]

qq = [ [ 1 , 0 , 0 , 0 , 0 , 0 , 0 , 7253 ]
    , [ 0 , 1 , 0 , 0 , 0 , 0 , 0 , 20717 ]
    , [ 0 , 0 , 1 , 0 , 0 , 0 , 0 , 59179 ]
    , [ 0 , 0 , 0 , 1 , 0 , 0 , 0 , 169045 ]
    , [ 0 , 0 , 0 , 0 , 1 , 0 , 0 , 482872 ]
    , [ 0 , 0 , 0 , 0 , 0 , 1 , 0 , 1379306 ]
    , [ 0 , 0 , 0 , 0 , 0 , 0 , 1 , 3939938 ]
    ]

for = flip map

main = do
    [ f ] <- getArgs
    h <- openFile f ReadMode
    base <- getChallenge h

    let n = length base
        q = round $ (fromIntegral n) ** (1/2)
    -- ( until_stable (full1 . sortN ) >=>
    reduce ( permute >=> ( blocked q $ find_smaller ))  base
    
    -- reduce ( while (full1 . sortN) size_reduce_fully ) base
    -- ( while (size_reduce_fully >=> swap) (error "done") ) base

    -- let obase = gso base
    --    det = product $ map (sqrt . norm2) obase
    --    d = fromIntegral $ length base
    -- print $ det ** (1/d) * sqrt d

    -- reduce (while (full1 . sortN ) (restarts 2) ) base

    -- NAIV
    -- reduce ( choices [ random_full, full1 . sortN  ]) base
    -- reduce ( choices [ full1 . sortN ,  random_full ]) base
    -- reduce ( while  random_full (full1 . sortN) ) base
    -- reduce ( random_full ) base
    -- reduce ( full1 . sortN ) base
    -- reduce ( while (full1 . reverse) permute) base

    -- L3:
    -- let sr = size_reduce base
    -- print $ map (\ (x,xo) -> (norm2 x, norm2 xo)) sr
    -- lll (2/1) $ sortN base

-- * strategies

reduce step base = do
    inform base
    step base >>= reduce step 

while s1 s2 base = do
    next <- s1 base
    if sortN next /= sortN base then while s1 s2 next
    else s2 base

ifnochange s1 s2 base = do
    next <- s1 base
    if next /= base then return next 
    else s2 base

choices ss base = do s <- one ss ; s base
choice s1 s2 = choices [s1,s2]

rept k step base = 
    if k > 0 then step base >>= rept(k-1) step 
    else return base

andthen s1 s2 base = do
    next <- s1 base
    s2 next

blocked k step base = do
    let bases = inblocks k base
    outputs <- forM (zip [0..] bases) $ \(k,b) -> step b
    return $ concat outputs
        
until_stable_blocked k step base = do
    let bases = inblocks k base
    outputs <- forM (zip [0..] bases) $ \(k,b) -> do
        out <- until_stable step b
        -- putStrLn $ unwords [ "****************", show k, "stable *******************" ]
        return out
    putStrLn "**************** all stable *******************"
    return $ concat outputs

until_stable s base = do
    next <- s base
    if sortN next == sortN base 
    then return base else until_stable s next

inblocks k xs = 
    let h [] = []
        h xs = let (pre, post) = splitAt k xs
               in  pre : h post
    in  transpose  $ h xs

-- * find integer linear combination via CBC

find_smaller_random_subset k base = do
    bs <- permute base
    let (pre, post) = splitAt k bs
    pre' <- find_smaller pre
    return $ pre' ++ post
             

find_smaller base = do
    let b j = r1 $ "B" ++ show j
        f i = z $ "f" ++ show i
        y j = r $ "y" ++ show j
        ycon = for ( zip [0..] $ transpose base ) $ \ (j, xs) ->
               (j , foldr1 (.+.) ( for (zip [0 .. ] xs) $ \ (i,x) -> f i $ Z x ) )
        ybound = for ycon $ \ (j, _) -> y j 1 :<= b j :&& y j (-1) :<= b j
        p = minimise ( foldr1 (.+.) $ for ycon $ \ (j,_) -> b j )
          ( foldr1 (:&&) $ ( f 0 ( Z 1 ) :== con 1 ) : for ycon (\(j,s) -> y j 1 :== s) ++ ybound )
          []
    case C.solve p of
         Left {} -> do
             putStrLn "no solution"
             return base
         Right ass -> do
             -- putStrLn "solution" ; print ass
             let old = head base
                 new = foldr1 plus $ for (zip [0..] base) $ \ (i, b) ->
                     scale (fromIntegral $  zOf ass ("f" ++ show i)) b
                 good = norm2 old > norm2 new
             putStr $ unwords [ show $ norm2 old
                              , if good then ">" else "?"
                              , show $ norm2 new , "."]
             hFlush stdout
             return $ if (norm2 new < norm2 old) then new : tail base else base
    
-- * steps

pairs0 (x:y:zs) = reduce_by x y : y : pairs0 zs
pairs0 base = base

pairs1 (x:ys) = x : pairs0 ys

full1 =  return . fullstep1 
full2 =  return . fullstep2

perturbs k = rept k perturb

perturb base = do
    (x,ys) <- pick base
    (y,zs) <- pick ys
    q <- randomRIO (-5,5)
    return $ minus x (scale q y) : ys

restarts k = rept k restart

restart [] = return []
restart [b] = return [b]
restart base = do
    (x, ys) <- pick base
    ys' <- restart ys
    (y,zs) <- pick ys'
    q <- randomRIO (-1,1)
    return $ minus x (scale q y) : ys'
    

reduce_by this that = 
    let q :: Rat
        q = fromIntegral ( inner this that )
          / fromIntegral ( inner that that )
        m :: Int
        m = -- signum $ 
          round q
    in  if m == 0 then this 
        else minus this $ scale (round q) that


random_full base = do
    (b, ase) <- pick base
    return $ b : map (\a -> reduce_by a b) ase

sortN base = sortBy (compare `on` norm2) base
sort1 base = sortBy (compare `on` norm1) base

fullstep1 base = case base of
    [] -> []
    b : ase -> 
        let ase' = fullstep1 ase
        in  b : map (\ v -> reduce_by v b ) ase'

fullstep2 base = case base of
    [] -> []
    b : ase -> 
        let ase' = id
                 -- $ sortN 
                 $ map (\ v -> reduce_by v b ) ase
        in  b : fullstep2 ase'

-- | select random subset (of size k)
-- replace one of the vectors from subset
-- by a random linear combination
multi k base = do
    base' <- permute base
    let (pre, post) = splitAt k base'
        pre' = sortBy (compare `on` norm2) pre
        vs = for ( filter ( (>= 2) . length . filter (/= 0) )
                 $ sequence $ replicate k [-1 .. 1 ]) 
           $ \ fs ->
             ( foldr1 plus $ zipWith scale fs pre
             , partition ( ((==0) . fst)) $ zip fs pre
             )
        (v,(zeroes, nonzeroes)) = 
             minimumBy (compare `on` (norm2 . fst)) vs
    -- let (dropped : nzs) = reverse $ sortN $ map snd nonzeroes
    (dropped, nzs) <- pick $ map snd nonzeroes 
    putStrLn $ unwords 
        ["multi", show $ norm2 dropped , "->", show $norm2 v]
    return $ v : nzs ++ map snd zeroes ++ post


-- * bookkeeping

inform base = inform_with "" base

inform_with msg base = do
    let vs = sortBy (compare `on` norm2) base
        ns = map norm2 vs
        gs = map (log . norm2) $ gso base
        weight = sum $ for (inits gs) $ sum 

    putStrLn $ unwords $
        [ msg, "total", show $ sum ns, ":" ] ++
        map show (take 5 ns) ++ [ ".." ] 
        ++ map show (ekat 5 ns)
        ++ [ ":" , show $ head vs ]

    
    hFlush stdout

ekat n xs = reverse $ take n $ reverse xs

-- * L3

{-

lll delta base = do
    inform base
    let sr = size_reduce base
    case mswap delta sr of
        Just base' -> lll delta base'
        Nothing -> do
            putStrLn "done"
            inform $ map fst sr
            putStrLn "base is"
            mapM_ print sr

mswap :: Rat -> Base -> Maybe Base
mswap delta base = case base of
    x : y : rest -> 
            if norm2 (ortho x) > delta * norm2 (ortho y)
            then  return $ gsoV y : x : map fst rest
            else (x:) <$> mswap delta ((y,yo):rest)
    _ -> Nothing


-}

swap_fully base = do
    inform_with "swap_fully" base   
    return $ map fst 
           $ sortBy (compare `on` snd) 
           $ zip base $ map norm2 $ gso base

    
swap :: [[Int]] -> IO [[Int]]
swap base = do
    inform_with "swap" base   
    let handle ((x,xo):(y,yo):rest) = 
            if (xo > 2* yo) 
            then y : x : handle rest 
            else x : handle ((y,yo):rest)
        handle [(x,xo)]=[x]
        handle []=[]
    let result = handle $ zip base $ map norm2 $ gso base
    -- inform_with "after swap" result
    return result

size_reduce_fully base = do
    inform_with "size_reduce_fully" base
    let run b = do
            case b of 
                [] -> return []
                x : ys -> (x :) <$> run (map (\ y -> reduce_by' y x) ys )
    base' <- run $ for base $ \ b -> (b, map fromIntegral b)
    let result = map fst base'
    -- inform_with "after size_reduce" result
    return result
    
reduce_by' :: ([Int],[Rat]) -> ([Int],[Rat]) 
           -> ([Int],[Rat])
reduce_by' (this, thiso) (that, thato) = 
    let q :: Rat
        q = ( inner (map fromIntegral this) thato )
          / ( inner thato thato )
    in  ( minus this $ scale (round q) that
        , minus thiso $ scale q thato 
        )


reduceOrtho_by this that = 
    let q :: Rat
        q = inner this that 
          / inner that that 
    in  minus this $ scale q that

-- * selection    

permute xs = case xs of
    [] -> return []
    _ -> do (y,ys) <- pick xs ; (y :) <$> permute ys 

one xs = fst <$> pick xs

pick :: [a] -> IO (a, [a])
pick xs = do
    i <- randomRIO (0, length xs - 1)
    let (pre, this : post) = splitAt i xs
    return (this, pre ++ post)

wpick [x] = return (x,[])
wpick (x:xs) = do
    f <- randomRIO (False,True)
    if f then return (x,xs) 
         else do (y,ys) <- wpick xs ; return (y, x:ys)

-- * L3




-- * GSO

gso :: [[Int]] -> [[Rat]]
gso b = 
    let run b = case b of 
            [] -> []
            x : ys -> 
                x : run ( map (\y -> reduceOrtho_by y x) ys )
    in  run $ map (map fromIntegral) b

-- * computations with vectors

type Rat = Double -- Rational

data Vector = Vector { this :: [Int]
                     , coeff :: [Int] -- ^ w.r.t. original base
                     , ortho :: [Rat]
                     }
    deriving (Show)

instance Eq Vector where (==) = (==) `on` this
instance Ord Vector where compare = compare `on` this

{-

gsoV :: Base -> Base
gsoV base = case b of 
    [] -> []
    x : ys -> x : gsoV ( map (\y -> 
        y { ortho = reduceOrtho_by (ortho y) (ortho x) }
      ) ys )

-}

build :: [[Int]] -> [Vector]
build base = for (zip [0..] base) $ \ (k,b) ->
            Vector { this = b
                   , ortho = map fromIntegral b
                   , coeff = for [0.. length base-1] 
                               $ \ i-> if i == k then 1 else 0
                   }


-- * vector ops

minus xs ys = plus xs $ scale (-1) ys
plus xs ys = zipWith (+) xs ys
scale x ys = map (x*) ys
inner xs ys = sum $ zipWith (*) xs ys
norm2 xs = inner xs xs
norm1 xs = sum $ map abs xs

-- * input

getChallenge :: Handle -> IO  [[Int]]
getChallenge h = do
    s <- BS.hGetContents h
    let p = do
            dim <- decimal <* skipSpace
            p <- decimal <* skipSpace
            q <- decimal <* skipSpace
            brac $ brac $ signed decimal <* skipSpace
        brac item = char '[' *> many item <* char ']'
                  <* skipSpace
    case parseOnly ( p <* endOfInput ) s of
        Left msg -> error msg
        Right m -> return m



    
