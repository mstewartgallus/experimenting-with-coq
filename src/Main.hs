module Main where

import Data.IORef
import Data.Word (Word64)
import Step
import System.IO.Unsafe (unsafeInterleaveIO)
import Prelude hiding (head)

main :: IO ()
main = do
  s <- fontTags
  y <- loop (right s) emptyEnv Hole identity
  putStrLn (pretty (left s) y)

identity :: Term v
identity = Pass (Lam $ \x -> (Var x)) (Lam $ \y -> (Var y))

left :: (Font a1) -> Font a1
left f =
  case f of
    Build_font _ left0 _ -> left0

prettyHole :: Show v => Font v -> Term' v -> String
prettyHole fnt k = case k of
  Hole -> "."
  Lpass e_f e_x ->
    let l = left fnt
        r = right fnt
     in "(" ++ prettyHole l e_f ++ " " ++ pretty r e_x ++ ")"

pretty :: Show v => Font v -> Term v -> String
pretty fnt expr = case expr of
  Var x -> "v" ++ show x
  Lam f ->
    let x = head fnt
        l = left fnt
     in "(λ v" ++ show x ++ ". " ++ pretty l (f x) ++ ")"
  Pass e_f e_x ->
    let l = left fnt
        r = right fnt
     in "(" ++ pretty l e_f ++ " " ++ pretty r e_x ++ ")"

emptyEnv :: v -> Term v
emptyEnv _ = error "should never happen"

loop :: (Show v, Eq v) => Font v -> Environ v -> Term' v -> Term v -> IO (Term v)
loop fnt e0 k0 c0 = do
  let l = left fnt
  let r = right fnt
  putStrLn (prettyHole l k0)
  putStrLn (pretty l c0)
  case go (==) l e0 k0 c0 of
    Just (Build_state e1 (Build_ck c1 k1)) -> loop r e1 k1 c1
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
