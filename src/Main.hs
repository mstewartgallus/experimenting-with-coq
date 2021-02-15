module Main where

import Data.IORef
-- import Prelude hiding (pure, fst, snd, lookup)
import Data.Word (Word64)
import Step
import System.IO.Unsafe (unsafeInterleaveIO)

main :: IO ()
main = do
  s0 <- streamTags
  let (s1, t) = identity s0
  loop s1 t

identity :: State (Stream v) (Term v)
identity (Build_stream x (Build_stream y t)) =
  (t, App (Lam x (Var x)) (Lam y (Var y)))

pretty :: Show v => Term v -> String
pretty expr = case expr of
  Var x -> "v" ++ show x
  Lam x e -> "(λ v" ++ show x ++ ". " ++ pretty e ++ ")"
  App e_f e_x -> "(" ++ pretty e_f ++ " " ++ pretty e_x ++ ")"

loop :: (Show v, Eq v) => Stream v -> Term v -> IO ()
loop s0 e = do
  putStrLn (pretty e)
  let (s1, e') = step (==) e s0
  case e' of
    Just e'' -> loop s1 e''
    Nothing -> return ()

data Tag = Tag Int (IORef ())

instance Eq Tag where
  Tag _ x == Tag _ y = (x == y)

instance Show Tag where
  show (Tag hash _) = show hash

streamTags :: IO (Stream Tag)
streamTags = do
  refs <- streamRefs
  ns <- streamHash
  return (zipTags refs ns)

zipTags :: Stream (IORef ()) -> Stream Int -> Stream Tag
zipTags ~(Build_stream ref rt) ~(Build_stream n nt) = Build_stream (Tag n ref) (zipTags rt nt)

streamRefs :: IO (Stream (IORef ()))
streamRefs = go
  where
    go = unsafeInterleaveIO $ do
      ref <- unsafeInterleaveIO $ newIORef ()
      t <- go
      return (Build_stream ref t)

streamHash :: IO (Stream Int)
streamHash = do
  let seed = 4
  ix <- newIORef seed
  let go = unsafeInterleaveIO $ do
        newIx <- unsafeInterleaveIO $ atomicModifyIORef ix (\n -> (hash n, fromIntegral n))
        t <- go
        return (Build_stream newIx t)
  go

-- lcgs are dumb but whatever
hash :: Word64 -> Word64
hash n = (multiplier * n + increment) `mod` modulus
  where
    -- prime
    modulus = 7
    multiplier = 3
    increment = 5
