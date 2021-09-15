
------------------------- Auxiliary functions

find :: (Show a,Eq a) => a -> [(a,b)] -> b
find x [] = error ("find: " ++ show x ++ " not found")
find x ((y,z):zs)
  | x == y    = z
  | otherwise = find x zs


merge :: Ord a => [a] -> [a] -> [a]
merge xs [] = xs
merge [] ys = ys
merge (x:xs) (y:ys)
    | x == y    = x : merge xs ys
    | x <= y    = x : merge xs (y:ys)
    | otherwise = y : merge (x:xs) ys

minus :: Ord a => [a] -> [a] -> [a]
minus xs [] = xs
minus [] ys = []
minus (x:xs) (y:ys)
    | x <  y    = x : minus    xs (y:ys)
    | x == y    =     minus    xs    ys
    | otherwise =     minus (x:xs)   ys


------------------------- Lambda-terms

type Var = String

data Term =
    Variable Var
  | Lambda   Var  Term
  | Apply    Term Term
  deriving Eq


instance Show Term where
  show = f 0
    where
      f i (Variable x) = x
      f i (Lambda x m) = if i /= 0 then "(" ++ s ++ ")" else s where s = "\\" ++ x ++ ". " ++ f 0 m 
      f i (Apply  n m) = if i == 2 then "(" ++ s ++ ")" else s where s = f 1 n ++ " " ++ f 2 m

free :: Term -> [Var]
free (Variable x) = [x]
free (Lambda x n) = free n `minus` [x]
free (Apply  n m) = free n `merge` free m


------------------------- Types

infixr 5 :->

type Atom = String
data Type = At Atom | Type :-> Type
  deriving Eq

instance Show Type where
  show (At a)       = a
  show (At a :-> s) = a ++ " -> " ++ show s
  show    (t :-> s) = "(" ++ show t ++ ") -> " ++ show s

variables :: [Var] 
variables = [ [x] | x <- ['a'..'z'] ] ++ [ x : show i | i <- [1..] , x <- ['a'..'z'] ]

atoms :: [Atom]
atoms = map (:[]) ['a'..'z'] ++ [ a : show i | i <- [1..], a <- ['a'..'z'] ]

t1 :: Type
t1 = At "a" :-> At "b"

t2 :: Type
t2 = (At "c" :-> At "d") :-> At "e"

t3 :: Type
t3 = At "a" :-> At "c" :-> At "c"


------------------------- Assignment 1

occurs :: Atom -> Type -> Bool
occurs  a (At t) 
    | a == t    = True
    | otherwise = False 
occurs  a (x :-> y) = occurs a x || occurs a y 


findAtoms :: Type -> [Atom]
findAtoms (At a)    = [a]
findAtoms (x :-> y) = sort (findAtoms x ++ findAtoms y)
  where 
    sort []  = []
    sort [x] = [x]
    sort xs  = sort ys `merge` sort zs
      where
        (ys,zs) = splitAt (length xs `div` 2) xs
 


------------------------- Type substitution

type Sub = (Atom,Type)

s1 :: Sub
s1 = ("a", At "e")

s2 :: Sub
s2 = ("e", At "b" :-> At "c")

s3 :: Sub
s3 = ("c", At "a" :-> At "a")


------------------------- Assignment 2

sub :: Sub -> Type -> Type
sub (a,t) (At b)
    | a == b    =  t
    | otherwise = At b
sub (a,t) (x :-> y) = sub (a,t) x :-> sub (a,t) y

subs :: [Sub] -> Type -> Type
subs [] b = b
subs xs b 
    | length xs == 1 = sub (head xs) b
    | otherwise      = subs (init xs) (sub (last xs) b)

------------------------- Unification

type Upair = (Type,Type)
type State = ([Sub],[Upair])

u1 :: Upair
u1 = (t1,At "c")

u2 :: Upair
u2 = (At "a" :-> At "a",At "a" :-> At "c")

u3 :: Upair
u3 = (t1,t2)

u4 :: Upair
u4 = (t2,t3)

st1 :: State
st1 = ([],[u1,u2])

st2 :: State
st2 = ([s1,s2], [])
------------------------- Assignment 3

sub_u :: Sub -> [Upair] -> [Upair]
sub_u s []     = [] 
sub_u s (x:xs) = [ssub_u s x] ++ sub_u s xs
    where ssub_u s (x,y) = (sub s x , sub s y) 


step :: State -> State
step (ss , []) = (ss,[])
step (ss, (At a ,At b):us)
    | a == b    = (ss, us)
    | otherwise = (ss ++ [(a ,At b)], sub_u (a, At b) us)

step (ss, (At a, x :-> y):us)
    | occurs a (x :-> y) = error ("step: Atom "  ++ show a ++ " occurs in " ++ show (x :-> y) )
    | otherwise          = (ss ++ [(a, x :-> y)], sub_u (a, x :-> y) us)

step (ss, (x :-> y, At a):us)
    | occurs a (x :-> y) = error ("step: Atom "  ++ show a ++ " occurs in " ++ show (x :-> y) )
    | otherwise          = (ss ++ [(a, x :-> y)], sub_u (a, x :-> y) us)

step (ss, ( x :-> y , f :-> g):us) = (ss, [(x,f),(y,g)] ++ us)


unify :: [Upair] -> [Sub]
unify [] = []
unify us =  unify (snd (step ([],us))) ++ fst (step ([], us))

------------------------- Assignment 4

type Context   = [(Var, Type)]
type Judgement = (Context, Term, Type)

data Derivation = Axiom Judgement | Abstraction Judgement Derivation| Application Judgement Derivation Derivation


n1 = Apply (Lambda "x" (Variable "x")) (Variable "y")

d1 = Application ([("y",At "a")], n1 , At "a") (
       Abstraction ([("y",At "a")],Lambda "x" (Variable "x"),At "a" :-> At "a") (
         Axiom ([("x",At "a"),("y",At "a")],Variable "x",At "a")
     ) ) (
       Axiom ([("y",At "a")], Variable "y", At "a")
     )

d2 = Application ([("y",At "b")],Apply (Lambda "x" (Apply (Variable "x") (Variable "y"))) (Lambda "z" (Variable "z")),At "a") (
       Abstraction ([("y",At "b")],Lambda "x" (Apply (Variable "x") (Variable "y")),At "c") (
         Application ([("x",At "d"),("y",At "b")],Apply (Variable "x") (Variable "y"),At "e") (
           Axiom ([("x",At "d"),("y",At "b")],Variable "x",At "f")
         ) (
           Axiom ([("x",At "d"),("y",At "b")],Variable "y",At "g")
     ) ) ) (
       Abstraction ([("y",At "b")],Lambda "z" (Variable "z"),At "h") (
         Axiom ([("z",At "i"),("y",At "b")],Variable "z",At "j")
     ) )


------- Tests -------

d3 :: Derivation
d3 = Axiom  ([("x",At "d"),("y",At "b")], Apply (Variable "x") (Variable "y") ,At "e")
d4 :: Derivation
d4 =  Abstraction ([("x",At "d"),("y",At "b")], Apply (Variable "x") (Variable "y") ,At "e")  (Axiom ([("z",At "i"),("y",At "b")],Variable "z",At "j"))

ctx1 = [("a", At "b" :-> At "c"), ("d", At "e" :-> At "f")]
----------------

conclusion :: Derivation -> Judgement
conclusion (Axiom j) = j 
conclusion (Abstraction j d) = j
conclusion (Application j d1 d2) = j

subs_ctx :: [Sub] -> Context -> Context
subs_ctx ss []     = []
subs_ctx ss (c:cs) = (fst c, subs ss (snd c)) : subs_ctx ss cs

subs_jdg :: [Sub] -> Judgement -> Judgement
subs_jdg ss (c,term,t) = (subs_ctx ss c , term, subs ss t)

subs_der :: [Sub] -> Derivation -> Derivation
subs_der ss (Axiom j)             = Axiom (subs_jdg ss j)
subs_der ss (Abstraction j d)     = Abstraction (subs_jdg ss j) (subs_der ss d)
subs_der ss (Application j d1 d2) = Application (subs_jdg ss j) (subs_der ss d1) (subs_der ss d2)

------------------------- Typesetting derivations


instance Show Derivation where
  show d = unlines (reverse strs)
    where
      (_,_,_,strs) = showD d

      showC :: Context -> String
      showC [] = []
      showC [(x,t)]    = x ++ ": " ++ show t
      showC ((x,t):cx) = x ++ ": " ++ show t  ++ " , " ++ showC cx

      showJ :: Judgement -> String
      showJ ([],n,t) =              "|- " ++ show n ++ " : " ++ show t
      showJ (cx,n,t) = showC cx ++ " |- " ++ show n ++ " : " ++ show t

      showL :: Int -> Int -> Int -> String
      showL l m r = replicate l ' ' ++ replicate m '-' ++ replicate r ' '

      showD :: Derivation -> (Int,Int,Int,[String])
      showD (Axiom j) = (0,k,0,[s,showL 0 k 0]) where s = showJ j; k = length s
      showD (Abstraction j d)   = addrule (showJ j) (showD d)
      showD (Application j d e) = addrule (showJ j) (sidebyside (showD d) (showD e))

      addrule :: String -> (Int,Int,Int,[String]) -> (Int,Int,Int,[String])
      addrule x (l,m,r,xs)
        | k <= m     = (ll,k,rr, (replicate ll ' ' ++ x ++ replicate rr ' ') : showL  l m r  : xs)
        | k <= l+m+r = (ll,k,rr, (replicate ll ' ' ++ x ++ replicate rr ' ') : showL ll k rr : xs)
        | otherwise  = (0,k,0, x : replicate k '-' : [ replicate (-ll) ' ' ++ y ++ replicate (-rr) ' ' | y <- xs])
        where
          k = length x
          i = div (m - k) 2
          ll = l+i
          rr = r+m-k-i

      extend :: Int -> [String] -> [String]
      extend i strs = strs ++ repeat (replicate i ' ')

      sidebyside :: (Int,Int,Int,[String]) -> (Int,Int,Int,[String]) -> (Int,Int,Int,[String])
      sidebyside (l1,m1,r1,d1) (l2,m2,r2,d2)
        | length d1 > length d2 = ( l1 , m1+r1+2+l2+m2 , r2 , [ x ++ "  " ++ y | (x,y) <- zip d1 (extend (l2+m2+r2) d2)])
        | otherwise             = ( l1 , m1+r1+2+l2+m2 , r2 , [ x ++ "  " ++ y | (x,y) <- zip (extend (l1+m1+r1) d1) d2])



------------------------- Assignment 5

------- Tests -------

n3 :: Term
n3 = Lambda "x" (Apply (Variable "x") (Variable "x"))

n4 :: Term
n4 = Lambda "x" (Lambda "y" (Lambda "z" (Apply (Variable "z") (Variable "x") )))

n5 :: Term
n5 = Lambda "f" (Lambda "g" (Apply (Variable "f") (Lambda "x" (Apply (Apply (Variable"g") (Variable "x")) (Variable "x") ))))

n6 :: Term
n6 = Apply( Apply (Apply (Lambda "x" (Variable "x")) (Lambda "y" (Variable "y")) ) ((Lambda "x" (Variable "y")))) (Lambda "y" (Variable "y"))

n7 :: Term
n7 = Apply (Apply (Lambda "x" (Variable "x")) (Lambda "y" (Variable "y"))) (Lambda "x" (Variable "x"))

n8 :: Term
n8 = Apply (Apply (Lambda "x" (Variable "x")) (Lambda "y" (Variable "y"))) (Lambda "z" (Variable "z"))

n9 :: Term
n9 = Apply( Apply (Apply (Lambda "x" (Variable "x")) (Lambda "y" (Variable "y")) ) ((Lambda "z" (Variable "z")))) (Lambda "w" (Variable "w"))

n10 :: Term
n10 = Lambda "x" (Lambda "y" (Lambda "z" (Apply (Apply (Variable "x") (Variable "z")) (Apply (Variable "y") (Variable "z")) )) )  

n11 :: Term
n11 = (Apply (Lambda "x" (Variable "x")) (Lambda "x" (Variable "x")) ) 

n12 :: Term
n12 =  Lambda "f" (Lambda "x" (Apply (Variable "f") (Apply (Variable "f") (Variable"x") ))) 

n13 :: Term
n13 = Lambda "x" (Lambda "x" (Variable "x")) 

n14 :: Term
n14 = Lambda "a" (Lambda "b" (Lambda "g" (Apply (Variable "a") (Apply (Variable "b") (Variable "g")))))

n15 :: Term
n15 =  Apply(Lambda "f" (Lambda "x" (Apply (Variable "f") (Apply (Variable "f") (Variable"x") )))) (Lambda "f" (Lambda "x" (Apply (Variable "f") (Apply (Variable "f") (Variable"x") ))))

n16 :: Term
n16 = Apply (Lambda "y" (Variable "y")) (Lambda "x" (Variable "y")) 

n17 :: Term
n17 = Apply (Lambda "x" (Variable "y")) (Lambda "y" (Variable "y")) 

n18 :: Term
n18 = Lambda "m" (Lambda "n" (Lambda "f" (Lambda "x" (Apply (Apply (Variable "m" )(Variable "f")) (Apply (Apply (Variable "n") (Variable "f")) (Variable "x")))))) -- forum teut 8B q2c checked

n19 :: Term
n19 = Lambda "x" (Lambda "x" (Lambda "x" (Variable "x")) )

n20 :: Term
n20  = Apply (Lambda "x" (Variable "x")) (Lambda "x" (Variable "x")) 


----- n21 is typable bur n22 is not
n21 :: Term
n21 = Lambda "x" (Lambda "y" (Apply( Apply (Variable "y") (Variable "x")) (Variable "x")))

n22 :: Term
n22 = Apply n21 n21


n23 = Lambda "f" (Lambda "x" (Apply( Apply (Variable "f") (Variable "x")) (Variable "x")))

----
-- M1 = λf.λg.λx.g(fxx)

n24 = Lambda "f" (Lambda "g" (Lambda "x" (Apply (Variable "g") ( Apply ( Apply (Variable "f") (Variable "x") ) (Variable "x") )   )))
n25 = Lambda "x" (Lambda "y" (Variable "x") )

n26 = Apply n24 n25

n27 = Lambda "x" (Lambda "y" (Lambda "z" (Variable "y") ))

n28 = Lambda "w" (Variable "w")

n29 = Apply (Apply n24 n27 ) n28
----



------- Aauxiliary -------

remove :: Eq a => [a] -> a -> [a]
remove [] _ = []
remove (x:xs) y
    | x == y    = xs
    | otherwise = x: remove xs y 

findBool :: (Eq a, Show a) => a -> [(a, b)] -> Bool
findBool x [] = False
findBool x ((y,z):zs)
  | x == y    = True
  | otherwise = findBool x zs

findAt :: Type -> Atom
findAt (At a)    =  a
findAt (x :-> y) = error "not an atom"

ctx_update :: Context -> Var -> Type -> Context
ctx_update c x t
    | findBool x c = subs_ctx [ (findAt (find x c) , t) ] c
    | otherwise    = [(x,t)] ++ c

--------------------


derive0 :: Term -> Derivation
derive0 y = aux ( [ (m, At "") | m <- free y ], y , At "" )
  where
    aux :: Judgement -> Derivation
    aux (c, Variable x, t) = Axiom (c, Variable x, t)
    aux (c, Lambda x m, t) = Abstraction (c, Lambda x m, t) (aux (ctx_update c x t , m, t))
    aux (c, Apply m n, t)  = Application (c, Apply m n, t) (aux (c, m, t)) (aux (c, n, t))


------- Aauxiliary -------
  
removeAll :: [Atom] -> [Atom] -> [Atom]
removeAll xs ys = [ x | x <- xs , not (elem x ys) ]

fresh :: [Atom] -> Atom
fresh = head . removeAll (drop 26 atoms)   
  where
    removeAll xs ys = [ x | x <- xs , not (elem x ys) ]

fresh2 :: [Atom] -> Atom
fresh2 xs =  (removeAll (drop 26 atoms) xs) !!2
  where
    removeAll xs ys = [ x | x <- xs , not (elem x ys) ]

freshn :: [Atom] -> Int -> Atom
freshn xs n
   | n < 1      = ""
   | n == 1     = fresh xs
   | otherwise  = freshn (fresh xs : xs) (n-1)

freshnLst :: [Atom] -> Int -> [Atom]
freshnLst xs n
   | n < 1      = []
   | n == 1     = [fresh xs]
   | otherwise  = freshnLst xs (n-1) ++ [freshn (fresh xs : xs) (n-1)]

bound :: Term -> Int
bound (Variable x) = 1
bound (Lambda x m) = 1 + bound m 
bound (Apply m n ) = 1 + bound m +bound n

findAtomsJudgement :: Judgement -> [Atom]
findAtomsJudgement ([], _ , t) = findAtoms t
findAtomsJudgement (c:cs,term,t) = findAtoms (snd c) ++ findAtomsJudgement (cs, term, t) ++ findAtoms t

--------------------

derive1 :: Term -> Derivation
derive1 y = aux (findAtomsJudgement j) j
  where
    aux :: [Atom] -> Judgement -> Derivation
    aux a (c, Variable x, t) = Axiom (c, Variable x, t  )
    aux a (c, Lambda x m, t) = Abstraction (c, Lambda x m, t) (aux ([fresh a] ++ a ++ [fresh2 a] )  (ctx_update c x (At (fresh2 a)), m, At (fresh a)))
    aux a (c, Apply m n, t)  = Application (c, Apply m n, t) (aux ( [fresh a] ++ [fresh2 a] ++ a ++ freshnLst a (bound y) ) (c, m, At (fresh a))) (aux ( [fresh a] ++ [fresh2 a] ++ a) (c, n, At (fresh2 a  )))
    j = ( [ (m, At f) | (m,f) <- zip (free y) atoms ], y , At ( head (removeAll atoms [k | k <- [snd r | r <-  zip (free y) atoms ]  ]  ) ) )



------- Aauxiliary -------

trd :: (a,b,c) -> c
trd (a,b,c) = c

getCont :: Judgement -> Context
getCont (c, ter, t)   = c
-------------------

upairs :: Derivation -> [Upair]
upairs (Axiom (c, Variable x, t)) 
    | findBool x c = [(t, find x c)]
    | otherwise    = []
upairs (Abstraction (c, Lambda x m, t) d) 
    | findBool x (getCont (conclusion d)) = (t, find x (getCont (conclusion d)) :-> trd (conclusion d)) : upairs d
    | otherwise                           = []
upairs (Application (c, Apply m n , t) d1 d2) = [ (trd (conclusion d1), trd (conclusion d2) :-> t  )] ++ upairs d1 ++ upairs d2


derive :: Term -> Derivation
derive x = subs_der ( unify ( upairs ( derive1 x ))) (derive1 x)

