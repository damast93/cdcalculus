import Data.List (intercalate)
import Control.Monad (guard, forM_)

{----- CD calculus terms and types -----}

data Generator = Generator { name :: String, dom_ty :: Ty, cod_ty :: Ty } deriving (Eq, Show)

data Ty = Unit | N | Cross Ty Ty deriving (Eq,Show)

data Term = 
    Var String
    | Emp 
    | Pair Term Term 
    | App Generator Term
    | Let String Term Term 
    | Mat String String Term Term deriving Eq

instance Show Term where
    show (Var x) = x
    show Emp = "()"
    show (Pair u v) = "(" ++ show u ++ ", " ++ show v ++ ")"
    show (App f u) = (name f) ++ show u
    show (Let x e u) = "let " ++ x ++ " = " ++ show e ++ " in " ++ show u
    show (Mat x y e u) = "match (" ++ x ++ "," ++ y ++ ") = " ++ show e ++ " in " ++ show u

-- type inference for a term in context 

type Context = [(String,Ty)]

infer :: Context -> Term -> Maybe Ty
infer e (Var x) = lookup x e
infer e Emp = Just Unit
infer e (Pair a b) = do 
    s <- infer e a
    t <- infer e b
    return $ Cross s t
infer e (App f u) = do
    t <- infer e u
    guard (t == dom_ty f)
    return $ cod_ty f
infer e (Let x u v) = do
    t <- infer e u
    infer ((x,t) : e) v
infer e (Mat x y u v) = do
    p <- infer e u
    case p of
        (Cross s t) -> infer ((x,s) : (y,t) : e) v
        _ -> Nothing

{----- Representation of morphisms in a CD category -----}

data Mor = 
    Id Ty
    | Gen Generator
    | Seq Mor Mor
    | Tensor Mor Mor
    | Swap Ty Ty
    | Copy Ty 
    | Discard Ty deriving (Eq,Show) 

dom :: Mor -> Ty
dom (Id t) = t 
dom (Gen f) = dom_ty f
dom (Seq f g) = dom f
dom (Tensor f g) = Cross (dom f) (dom g)
dom (Swap s t) = Cross s t
dom (Copy t) = t
dom (Discard t) = t

cod :: Mor -> Ty
cod (Id t) = t
cod (Gen f) = cod_ty f
cod (Seq f g) = cod g
cod (Tensor f g) = Cross (cod f) (cod g)
cod (Swap s t) = Cross t s
cod (Copy t) = Cross t t
cod (Discard t) = Unit

{----- Compiling CD calculus terms to morphisms -----}

-- shorthand to extract type: assume a term is well-typed; error if not
ty :: Context -> Term -> Ty
ty e u = 
  case infer e u of
    Just t -> t
    Nothing -> error "working with term that is not well-typed"

-- turn a context into a type 
tyc :: Context -> Ty
tyc [] = Unit
tyc ((x,t):es) = Cross t (tyc es)

-- project a variable out of a context
proj_var :: Context -> String -> Mor
proj_var [] x = error "!Variable not found"
proj_var ((x,t):es) y
  | x == y = (Id t) `Tensor` (Discard (tyc es))
  | x /= y = (Discard t) `Tensor` (proj_var es y)

-- compile a term in context to a morphism
compile :: Context -> Term -> Mor
compile e (Var x) = proj_var e x
compile e Emp = Discard (tyc e)
compile e (Pair u v) = (Copy (tyc e)) `Seq` (Tensor (compile e u) (compile e v))
compile e (App f u) = Seq (compile e u) (Gen f)
compile e (Let x w u) = ((Copy t) `Seq` (Tensor (compile e w) (Id t))) `Seq` (compile ((x,ty e w):e) u)
  where t = tyc e
compile e (Mat x y w u) = ((Copy t) `Seq` (Tensor (compile e w) (Id t))) `Seq` (compile ((x,t1):(y,t2):e) u)
  where t = tyc e
        (Cross t1 t2) = ty e w

{----- Compilation to chyp -----}

ty_context :: Ty -> Int
ty_context Unit = 0
ty_context N = 1
ty_context (Cross s t) = ty_context s + ty_context t

-- encoding the coherence isos in chyp
id_chyp :: Int -> String
id_chyp 0 = "id0"
id_chyp n = intercalate "*" (replicate n "id")

swap_chyp :: Int -> Int -> String
swap_chyp 0 0 = "id0"
swap_chyp m 0 = id_chyp m
swap_chyp 0 n = id_chyp n
swap_chyp m n = "sw[" ++ intercalate ", " (map show ix) ++ "]"
  where ix = [m..n+m-1] ++ [0..m-1]

copy_chyp :: Int -> String
copy_chyp 0 = "id0"
copy_chyp 1 = "c"
copy_chyp n = "(" ++ intercalate " * " (replicate n "c") ++ "; sw[" ++ intercalate ", " (map show ix) ++ "])"
  where ix = [ 2*i | i <- [0..n-1]] ++ [ 2*i + 1| i <- [0..n-1]]

discard_chyp :: Int -> String
discard_chyp 0 = "id0"
discard_chyp n = intercalate " * " (replicate n "d")

-- Compile to chyp

chyp :: Mor -> String
chyp (Id t) = id_chyp (ty_context t)
chyp (Gen f) = name f
chyp (Seq f g) = "(" ++ chyp f ++ " ; " ++ chyp g ++ ")"
chyp (Tensor f g) = chyp f ++ " * " ++ chyp g
chyp (Swap s t) = swap_chyp (ty_context s) (ty_context t)
chyp (Copy t) = copy_chyp (ty_context t)
chyp (Discard t) = discard_chyp (ty_context t)

{----- Examples -----}

-- example signature
f = Generator "f" (N `Cross` N) N
n = Generator "n" Unit N 
e = Generator "e" (N `Cross` N) Unit 

-- x : N |- let y = n() in f(y,x)
ex1 = ([("x", N)], Let "y" (App n Emp) (App f (Pair (Var "y") (Var "x"))))

-- p : N * N |- match (x,y) = p in (y,x)
ex2 = ([("p", Cross N N)], Mat "x" "y" (Var "p") $ Pair (Var "y") (Var "x"))

-- x : N |- let y = n() in let u = (x =:= y); y
ex3 = ([("x", N)], Let "y" (App n Emp) $ Let "_u" (App e (Pair (Var "x") (Var "y"))) $ (Var "y"))

-- p : N * N |- match (u,v) = (match (x,y) = p in (y,x)) in v
ex4 = ([("p", Cross N N)], Mat "u" "v" (Mat "x" "y" (Var "p") $ Pair (Var "y") (Var "x")) $ Var "v")

-- x : N |- match (u,v) = (x,x) in (v,u)
ex5 = ([("x", N)], Mat "u" "v" (Pair (Var "x") (Var "x")) $ (Pair (Var "v") (Var "u")))

-- call `example "f" ex1`
example :: String -> (Context,Term) -> IO ()
example name (e,u) = do 
  let mor = compile e u
  putStrLn $ "# " ++ show u
  putStrLn $ "let " ++ name ++ " = " ++ chyp mor
  putStrLn $ "rewrite " ++ name ++ "_simp : " ++ name ++ " = ? by simp(assoc,counitL,counitR,cocomm)" 

examples = [("ex1", ex1), ("ex2", ex2), ("ex3", ex3), ("ex4", ex4), ("ex5", ex5)]

main :: IO ()
main = do
  forM_ examples $ \(name, ex) -> example name ex