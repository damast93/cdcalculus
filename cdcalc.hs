import Data.List

-- CD calculus terms and types

data Generator = Generator { name :: String, dom_gen :: Ty, cod_gen :: Ty } deriving (Eq, Show)

data Ty = Unit | N | Cross Ty Ty deriving (Eq,Show)

data Term = 
    Var String Ty
    | Emp 
    | Pair Term Term 
    | App Generator Term
    | Let String Term Term 
    | Mat String String Term Term deriving Eq

instance Show Term where
    show (Var x t) = x
    show Emp = "()"
    show (Pair u v) = "(" ++ show u ++ ", " ++ show v ++ ")"
    show (App f u) = (name f) ++ show u
    show (Let x e u) = "let " ++ x ++ " = " ++ show e ++ " in " ++ show u
    show (Mat x y e u) = "match (" ++ x ++ "," ++ y ++ ") = " ++ show e ++ " in " ++ show u

ty :: Term -> Ty
ty (Var x t) = t
ty Emp = Unit
ty (Pair u v) = Cross (ty u) (ty v)
ty (App f u) = cod_gen f
ty (Let x e u) = ty u
ty (Mat x y e u) = ty u

-- Morphisms

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
dom (Gen f) = dom_gen f
dom (Seq f g) = dom f
dom (Tensor f g) = Cross (dom f) (dom g)
dom (Swap s t) = Cross s t
dom (Copy t) = t
dom (Discard t) = t

cod :: Mor -> Ty
cod (Id t) = t
cod (Gen f) = cod_gen f
cod (Seq f g) = cod g
cod (Tensor f g) = Cross (cod f) (cod g)
cod (Swap s t) = Cross t s
cod (Copy t) = Cross t t
cod (Discard t) = Unit

-- Compiling CD calculus terms to morphisms

type Env = [(String,Ty)]

ty_env :: Env -> Ty
ty_env [] = Unit
ty_env ((x,t):es) = Cross t (ty_env es)

proj_var :: Env -> String -> Ty -> Mor
proj_var [] x t2 = error "Variable not found"
proj_var ((x,t):es) y t2
  | x == y && (t == t2) = (Id t) `Tensor` (Discard (ty_env es))
  | x /= y = (Discard t) `Tensor` (proj_var es y t2)
  | otherwise = error "Type error"

compile :: Env -> Term -> Mor
compile e (Var x t) = proj_var e x t
compile e Emp = Discard (ty_env e)
compile e (Pair u v) = Seq (Copy (ty_env e)) (Tensor (compile e u) (compile e v))
compile e (App f u) = Seq (compile e u) (Gen f)
compile e (Let x w u) = ((Copy t) `Seq` (Tensor (compile e w) (Id t))) `Seq` (compile ((x,ty w):e) u)
  where t = ty_env e
compile e (Mat x y w u) = ((Copy t) `Seq` (Tensor (compile e w) (Id t))) `Seq` (compile ((x,t1):(y,t2):e) u)
  where t = ty_env e
        (Cross t1 t2) = ty w


-- Compile to chyp

ty_chyp :: Ty -> Int
ty_chyp Unit = 0
ty_chyp N = 1
ty_chyp (Cross s t) = ty_chyp s + ty_chyp t

id_chyp 0 = "id0"
id_chyp n = intercalate "*" (replicate n "id")

swap_chyp 0 0 = "id0"
swap_chyp m 0 = id_chyp m
swap_chyp 0 n = id_chyp n
swap_chyp m n = "sw[" ++ intercalate ", " (map show ix) ++ "]"
  where ix = [m..n+m-1] ++ [0..m-1]

copy_chyp 0 = "id0"
copy_chyp 1 = "c"
copy_chyp n = "(" ++ intercalate " * " (replicate n "c") ++ "; sw[" ++ intercalate ", " (map show ix) ++ "])"
  where ix = [ 2*i | i <- [0..n-1]] ++ [ 2*i + 1| i <- [0..n-1]]

discard_chyp 0 = "id0"
discard_chyp n = intercalate " * " (replicate n "d")

chyp :: Mor -> String
chyp (Id t) = id_chyp (ty_chyp t)
chyp (Gen f) = name f
chyp (Seq f g) = "(" ++ chyp f ++ " ; " ++ chyp g ++ ")"
chyp (Tensor f g) = chyp f ++ " * " ++ chyp g
chyp (Swap s t) = swap_chyp (ty_chyp s) (ty_chyp t)
chyp (Copy t) = copy_chyp (ty_chyp t)
chyp (Discard t) = discard_chyp (ty_chyp t)

{------- Examples -------}

f = Generator "f" (N `Cross` N) N
n = Generator "n" Unit N 
e = Generator "e" (N `Cross` N) Unit 

-- x : N |- let y = n() in f(y,x)
u1_env = [("x", N)]
u1 = Let "y" (App n Emp) (App f (Pair (Var "y" N) (Var "x" N)))
m1 = compile u1_env u1

-- p : N * N |- match (x,y) = p in (y,x)

u2_env = [("p", Cross N N)]
u2 = Mat "x" "y" (Var "p" (N `Cross` N)) $ Pair (Var "y" N) (Var "x" N)
m2 = compile u2_env u2

-- x : N |- let y = n() in let u = (x =:= y); y

u3_env = [("x", N)]
u3 = Let "y" (App n Emp) $ Let "_u" (App e (Pair (Var "x" N) (Var "y" N))) $ (Var "y" N)
m3 = compile u3_env u3

-- p : N * N |- match (u,v) = (match (x,y) = p in (y,x)) in v

u4_env = [("p", Cross N N)]
u4 = Mat "u" "v" u2 $ Var "v" N
m4 = compile u4_env u4

-- x : N |- match (u,v) = (x,x) in (v,u)

u5_env = [("x", N)]
u5 = Mat "u" "v" (Pair (Var "x" N) (Var "x" N)) $ (Pair (Var "v" N) (Var "u" N))
m5 = compile u5_env u5