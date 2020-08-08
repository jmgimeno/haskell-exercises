{-# LANGUAGE GADTs              #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE FlexibleContexts   #-}

{-# OPTIONS_GHC -Wall #-}

module Exercises where





{- ONE -}

-- | Let's introduce a new class, 'Countable', and some instances to match.
class Countable a where count :: a -> Int
instance Countable Int  where count   = id
instance Countable [a]  where count   = length
instance Countable Bool where count x = if x then 1 else 0

-- | a. Build a GADT, 'CountableList', that can hold a list of 'Countable'
-- things.

data CountableList where
  CountNil :: CountableList
  CountCons :: Countable a => a -> CountableList -> CountableList


-- | b. Write a function that takes the sum of all members of a 'CountableList'
-- once they have been 'count'ed.

countList :: CountableList -> Int
countList CountNil         = 0
countList (CountCons c cs) = count c + countList cs 


-- | c. Write a function that removes all elements whose count is 0.

dropZero :: CountableList -> CountableList
dropZero CountNil = CountNil
dropZero (CountCons c cs)
  | count c == 0 = dropZero cs
  | otherwise    = CountCons c (dropZero cs)


-- | d. Can we write a function that removes all the things in the list of type
-- 'Int'? If not, why not?

filterInts :: CountableList -> CountableList
filterInts = error "Contemplate me!"

-- No, we can't because the only thing we can do with the elements in the
-- list is count them



{- TWO -}

-- | a. Write a list that can take /any/ type, without any constraints.

data AnyList where
  AnyNil :: AnyList
  AnyCons :: a -> AnyList -> AnyList

-- | b. How many of the following functions can we implement for an 'AnyList'?

reverseAnyList :: AnyList -> AnyList
reverseAnyList l = go l AnyNil
                   where go AnyNil r         = r
                         go (AnyCons a as) r = go as (AnyCons a r)

filterAnyList :: (a -> Bool) -> AnyList -> AnyList
filterAnyList = undefined -- impossible caller chooses a -> Bool

lengthAnyList :: AnyList -> Int
lengthAnyList AnyNil         = 0
lengthAnyList (AnyCons _ as) = 1 + lengthAnyList as

foldAnyList :: Monoid m => AnyList -> m
foldAnyList = undefined -- impossible (no way to relate a with m)
 
isEmptyAnyList :: AnyList -> Bool
isEmptyAnyList AnyNil = True
isEmptyAnyList _      = False

instance Show AnyList where
  show = error "What about me?" -- cannot show a's, only counts



{- THREE -}

-- | Consider the following GADT:

data TransformableTo output where
  TransformWith
    :: (input -> output)
    ->  input
    -> TransformableTo output

-- Added Show instance to 'view' the results

instance Show a => Show (TransformableTo a) where
  show (TransformWith f a) = show (f a)

-- | ... and the following values of this GADT:

transformable1 :: TransformableTo String
transformable1 = TransformWith show 2.5

transformable2 :: TransformableTo String
transformable2 = TransformWith (uncurry (++)) ("Hello,", " world!")

-- | a. Which type variable is existential inside 'TransformableTo'?

-- input

-- What is the only thing we can do to it?

-- apply input -> output to input

-- | b. Could we write an 'Eq' instance for 'TransformableTo'? 

-- Yes

-- What would we be able to check?

-- If the results of applying the function to input are equal

instance Eq a => Eq (TransformableTo a) where
  TransformWith f a == TransformWith f' a' = f a == f' a' 

-- | c. Could we write a 'Functor' instance for 'TransformableTo'? 

-- Yes
-- If so, write it. If not, why not?

instance Functor TransformableTo where
  fmap g (TransformWith f a) = TransformWith (g . f) a




{- FOUR -}

-- | Here's another GADT:

data EqPair where
  EqPair :: Eq a => a -> a -> EqPair

{-
*GADTs Exercises GADTs> t =  EqPair (+1) (*2)

<interactive>:18:6: error:
    • No instance for (Eq (Integer -> Integer))
        arising from a use of ‘EqPair’
        (maybe you haven't applied a function to enough arguments?)
    • In the expression: EqPair (+ 1) (* 2)
      In an equation for ‘t’: t = EqPair (+ 1) (* 2)
-}

-- | a. There's one (maybe two) useful function to write for 'EqPair'; what is
-- it?

equals :: EqPair -> Bool
equals (EqPair x y) = x == y

notEquals :: EqPair -> Bool
notEquals (EqPair x y) = x /= y

-- | b. How could we change the type so that @a@ is not existential? (Don't
-- overthink it!)

-- Adding it as a type parameter

data EqPair' a where
  EqPair' :: Eq a => a -> a -> EqPair' a

-- | c. If we made the change that was suggested in (b), would we still need a
-- GADT? Or could we now represent our type as an ADT?

-- Yes, but we loose the Eq a constraint

data EqPair'' a = EqPair'' a a

{-
This does not work !!!
data EqPair'' a = Eq a => EqPair'' a a

*GADTs Exercises GADTs> t =  EqPair'' (+1) (*2)

<interactive>:19:1: error:
    • Non type-variable argument in the constraint: Eq (a -> a)
      (Use FlexibleContexts to permit this)
    • When checking the inferred type
        t :: forall a. (Eq (a -> a), Num a) => EqPair'' (a -> a)
-}


{- FIVE -}

-- | Perhaps a slightly less intuitive feature of GADTs is that we can set our
-- type parameters (in this case @a@) to different types depending on the
-- constructor.

data MysteryBox a where
  EmptyBox  ::                                MysteryBox ()
  IntBox    :: Int    -> MysteryBox ()     -> MysteryBox Int
  StringBox :: String -> MysteryBox Int    -> MysteryBox String
  BoolBox   :: Bool   -> MysteryBox String -> MysteryBox Bool

-- | When we pattern-match, the type-checker is clever enough to
-- restrict the branches we have to check to the ones that could produce
-- something of the given type.

getInt :: MysteryBox Int -> Int
getInt (IntBox int _) = int

-- | a. Implement the following function by returning a value directly from a
-- pattern-match:

getInt' :: MysteryBox String -> Int
getInt' (StringBox _ (IntBox int _)) = int 

-- | b. Write the following function. Again, don't overthink it!

countLayers :: MysteryBox a -> Int
countLayers EmptyBox        = 0
countLayers (IntBox _ _)    = 1
countLayers (StringBox _ _) = 2
countLayers (BoolBox _ _)   = 3 

-- | c. Try to implement a function that removes one layer of "Box". For
-- example, this should turn a BoolBox into a StringBox, and so on. What gets
-- in our way? What would its type be?

-- You can't write a function to do this because we have no way of figuring out
-- the type of the layer below. However, if you're willing to be a bit
-- sneaky... (hat-tip @LiamGoodacre):

data Layer a b where -- We can use a GADT to encode the layers...
  Int'    :: Layer Int ()
  String' :: Layer String Int
  Bool'   :: Layer Bool String

-- And now we can write this function:
unpeel :: Layer a b -> MysteryBox a -> MysteryBox b
unpeel Int'    (IntBox    _ xs) = xs
unpeel String' (StringBox _ xs) = xs
unpeel Bool'   (BoolBox   _ xs) = xs

-- It's definitely not perfect, but it's a pretty good go!

{- SIX -}

-- | We can even use our type parameters to keep track of the types inside an
-- 'HList'!  For example, this heterogeneous list contains no existentials:

data HList a where
  HNil  :: HList ()
  HCons :: head -> HList tail -> HList (head, tail)

exampleHList :: HList (String, (Int, (Bool, ())))
exampleHList = HCons "Tom" (HCons 25 (HCons True HNil))

-- | a. Write a 'head' function for this 'HList' type. This head function
-- should be /safe/: you can use the type signature to tell GHC that you won't
-- need to pattern-match on HNil, and therefore the return type shouldn't be
-- wrapped in a 'Maybe'!

head :: HList (a,b) -> a
head (HCons h _) = h

-- | b. Currently, the tuples are nested. Can you pattern-match on something of
-- type @HList (Int, String, Bool, ())@? Which constructor would work?

-- No constructor works because there is no way to construct an HList of a four-tuple type.

patternMatchMe :: HList (Int, String, Bool, ()) -> Int
patternMatchMe = undefined

-- | c. Can you write a function that appends one 'HList' to the end of
-- another? What problems do you run into?

-- No way to append types for the result.



{- SEVEN -}

-- | Here are two data types that may help:

data Empty
data Branch left centre right

-- | a. Using these, and the outline for 'HList' above, build a heterogeneous
-- /tree/. None of the variables should be existential.

data HTree a where
  HEmpty :: HTree Empty
  HBranch :: HTree left -> centre -> HTree right -> HTree (Branch left centre right)

-- | b. Implement a function that deletes the left subtree. The type should be
-- strong enough that GHC will do most of the work for you. Once you have it,
-- try breaking the implementation - does it type-check? If not, why not?

removeLeft :: HTree (Branch left centre right) -> HTree (Branch Empty centre right)
removeLeft (HBranch _ centre right) = HBranch HEmpty centre right

-- | c. Implement 'Eq' for 'HTree's. Note that you might have to write more
-- than one to cover all possible HTrees. You might also need an extension or
-- two, so look out for something... flexible... in the error messages!
-- Recursion is your friend here - you shouldn't need to add a constraint to
-- the GADT!

instance Eq (HTree Empty) where
  _ == _ = True

instance (Eq (HTree left), Eq centre, Eq (HTree right)) => Eq (HTree (Branch left centre right)) where
  HBranch left centre right == HBranch left' centre' right'
    = left == left' && centre == centre' && right == right' 



{- EIGHT -}

-- | a. Implement the following GADT such that values of this type are lists of
-- values alternating between the two types. For example:
--
-- @
--   f :: AlternatingList Bool Int
--   f = ACons True (ACons 1 (ACons False (ACons 2 ANil)))
-- @

data AlternatingList a b where
  -- ...

-- | b. Implement the following functions.

getFirsts :: AlternatingList a b -> [a]
getFirsts = error "Implement me!"

getSeconds :: AlternatingList a b -> [b]
getSeconds = error "Implement me, too!"

-- | c. One more for luck: write this one using the above two functions, and
-- then write it such that it only does a single pass over the list.

foldValues :: (Monoid a, Monoid b) => AlternatingList a b -> (a, b)
foldValues = error "Implement me, three!"





{- NINE -}

-- | Here's the "classic" example of a GADT, in which we build a simple
-- expression language. Note that we use the type parameter to make sure that
-- our expression is well-formed.

data Expr a where
  Equals    :: Expr Int  -> Expr Int            -> Expr Bool
  Add       :: Expr Int  -> Expr Int            -> Expr Int
  If        :: Expr Bool -> Expr a   -> Expr a  -> Expr a
  IntValue  :: Int                              -> Expr Int
  BoolValue :: Bool                             -> Expr Bool

-- | a. Implement the following function and marvel at the typechecker:

eval :: Expr a -> a
eval = error "Implement me"

-- | b. Here's an "untyped" expression language. Implement a parser from this
-- into our well-typed language. Note that (until we cover higher-rank
-- polymorphism) we have to fix the return type. Why do you think this is?

data DirtyExpr
  = DirtyEquals    DirtyExpr DirtyExpr
  | DirtyAdd       DirtyExpr DirtyExpr
  | DirtyIf        DirtyExpr DirtyExpr DirtyExpr
  | DirtyIntValue  Int
  | DirtyBoolValue Bool

parse :: DirtyExpr -> Maybe (Expr Int)
parse = error "Implement me"

-- | c. Can we add functions to our 'Expr' language? If not, why not? What
-- other constructs would we need to add? Could we still avoid 'Maybe' in the
-- 'eval' function?





{- TEN -}

-- | Back in the glory days when I wrote JavaScript, I could make a composition
-- list like @pipe([f, g, h, i, j])@, and it would pass a value from the left
-- side of the list to the right. In Haskell, I can't do that, because the
-- functions all have to have the same type :(

-- | a. Fix that for me - write a list that allows me to hold any functions as
-- long as the input of one lines up with the output of the next.

data TypeAlignedList a b where
  -- ...

-- | b. Which types are existential?

-- | c. Write a function to append type-aligned lists. This is almost certainly
-- not as difficult as you'd initially think.

composeTALs :: TypeAlignedList b c -> TypeAlignedList a b -> TypeAlignedList a c
composeTALs = error "Implement me, and then celebrate!"

