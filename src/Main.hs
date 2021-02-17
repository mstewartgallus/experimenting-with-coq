module Main where

import Data.IORef
import Data.Word (Word64)
import Step
import System.IO.Unsafe (unsafeInterleaveIO)
import Text.Show
import Prelude hiding (head)

main :: IO ()
main = do
  s <- fontTags
  y <- loop (right s) [] Hole identity
  putStrLn (pretty (left s) y)

identity :: Term v
identity = Pass (Lam_ $ \x -> Var x) (Lam_ $ \y -> Var y)

left :: (Font a1) -> Font a1
left f =
  case f of
    Build_font _ left0 _ -> left0

right :: (Font a1) -> Font a1
right f =
  case f of
    Build_font _ _ right -> right

prettyHole :: Show v => Font v -> Stack v -> String
prettyHole fnt k = case k of
  Hole -> "."
  Lpass e_f e_x ->
    let l = left fnt
        r = right fnt
     in "(" ++ prettyHole l e_f ++ " " ++ pretty r e_x ++ ")"

prettyHeap :: Show v => Font v -> Heap v -> String
prettyHeap fnt h = showListWith (\(k, v) s -> (show k ++ " → " ++ pretty fnt v) ++ s) h ""

pretty :: Show v => Font v -> Term v -> String
pretty fnt expr = case expr of
  Var x -> "v" ++ show x
  Lam_ f ->
    let x = head fnt
        l = left fnt
     in "(λ v" ++ show x ++ ". " ++ pretty l (f x) ++ ")"
  Pass e_f e_x ->
    let l = left fnt
        r = right fnt
     in "(" ++ pretty l e_f ++ " " ++ pretty r e_x ++ ")"

loop :: (Show v, Eq v) => Font v -> Heap v -> Stack v -> Term v -> IO (Term v)
loop fnt e0 k0 c0 = do
  let l = left fnt
  let r = right fnt
  putStrLn ("Heap:\t" ++ (prettyHeap l e0))
  putStrLn ("Stack:\t" ++ (prettyHole l k0))
  putStrLn ("Expr:\t" ++ (pretty l c0))
  putStrLn ""
  case go (==) l e0 k0 c0 of
    Just ((e1, k1), c1) -> loop r e1 k1 c1
    Nothing -> return c0

data Tag = Tag Int (IORef ())

instance Eq Tag where
  Tag _ x == Tag _ y = (x == y)

instance Show Tag where
  show (Tag hash _) = show hash

fontTags :: IO (Font Tag)
fontTags = do
  refs <- fontRefs
  ns <- fontHash
  return (zipTags refs ns)

zipTags :: Font (IORef ()) -> Font Int -> Font Tag
zipTags ~(Build_font ref rl rr) ~(Build_font n nl nr) = Build_font (Tag n ref) (zipTags rl nl) (zipTags rr nr)

fontRefs :: IO (Font (IORef ()))
fontRefs = go
  where
    go = unsafeInterleaveIO $ do
      ref <- unsafeInterleaveIO $ newIORef ()
      l <- go
      r <- go
      return (Build_font ref l r)

fontHash :: IO (Font Int)
fontHash = do
  let seed = 4
  ix <- newIORef seed
  let go = unsafeInterleaveIO $ do
        newIx <- unsafeInterleaveIO $ atomicModifyIORef ix (\n -> (hash n, fromIntegral n))
        l <- go
        r <- go
        return (Build_font newIx l r)
  go

-- lcgs are dumb but whatever
hash :: Word64 -> Word64
hash n = (multiplier * n + increment) `mod` modulus
  where
    -- prime
    modulus = 7
    multiplier = 3
    increment = 5
