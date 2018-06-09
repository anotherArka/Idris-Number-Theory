module total_Gcd


import associativePlus
import commutativePlus
import properties_of_Nat
import properties_of_Positive_Nat
import properties_of_order
import congruence     
import difference
import equivalence_of_equality

{-
recur : (n : Nat) -> {ty : Type} -> (a : ty) -> (f : ty -> ty) -> ty
recur Z a f = a
recur (S k) a f = f (recur k a f)

data Dif : Nat -> Nat -> Type where
     Zero : Dif n n
     PlusS : (k : Nat) -> Dif n (plus n (S k))
     MinusS : (k : Nat) -> Dif (plus n (S k)) n
     
dif : (a : Nat) -> (b : Nat) -> Dif a b
dif Z Z = Zero
dif (S x) Z = MinusS x
dif Z (S y) = PlusS y
dif (S x) (S y) = case dif (S x) (S y) of
                      Zero => Zero
                      MinusS k => MinusS k
                      PlusS k => PlusS k

dif : (a : Nat) -> (b : Nat) -> Nat
dif a Z = a
dif Z a = a
dif (S a) (S b) = dif a b
-}

public export
totalGcd : (a : Nat) -> (b : Nat) -> (NotBothZero a b) -> (bound : Nat) -> (geq bound (plus a b)) -> Positive_Nat
totalGcd Z Z prfNBZ bound prfG impossible
totalGcd Z (S a) prfNBZ bound prfG = ((S a) ** (Z_is_not_Sn a))
totalGcd (S a) Z prfNBZ bound prfG = ((S a) ** (Z_is_not_Sn a))
totalGcd (S a) (S b) prfNBZ Z (k ** prfG) = void (order_property9 (plus a (S b)) (k ** prfG))
totalGcd (S a) (S b) prfNBZ (S bound) (k ** prfK) = case decOrder a b of
                                                     Eql Refl => ((S a) ** (Z_is_not_Sn a))
                                                     Grt ((l ** prfL), prfNEq) => totalGcd (S b) (difference a b) LeftIsNotZero bound 
                                                                                  (rewrite commutativePlus b (difference a b) in 
                                                                                  (rewrite diff_property8 a b (l ** prfL) in 
                                                                                  ((plus k b) ** 
                                                                                  (Sn_eq_Sm_implies_n_eq_m bound (plus (plus k b) (S a)) 
                                                                                  (rewrite (associativePlus k b (S a)) in 
                                                                                  (rewrite commutativePlus k (plus b (S a)) in 
                                                                                  (rewrite commutativePlus (S (plus b (S a))) k in 
                                                                                  (rewrite commutativePlus (S b) (S a) in prfK))))))))
                                                                                  
                                                     Lst ((l ** prfL), prfNEq) => totalGcd (S a) (difference b a) LeftIsNotZero bound 
                                                                                  (rewrite commutativePlus a (difference b a) in 
                                                                                  (rewrite diff_property8 b a (l ** prfL) in 
                                                                                  ((plus k a) ** (Sn_eq_Sm_implies_n_eq_m bound (plus (plus k a) (S b)) 
                                                                                  (rewrite (associativePlus k a (S b)) in 
                                                                                  (rewrite commutativePlus k (plus a (S b)) in 
                                                                                  (rewrite commutativePlus (S (plus a (S b))) k in prfK)))))))
                                                                                  
                                                     
{-
total_Gcd : (a : Nat) -> (b : Nat) -> (NotBothZero a b) -> Positive_Nat
total_Gcd Z a LeftIsNotZero impossible
total_Gcd a Z RightIsNotZero impossible 
total_Gcd Z (S a) RightIsNotZero = ((S a) ** (Z_is_not_Sn a))
total_Gcd (S a) Z LeftIsNotZero = ((S a) ** (Z_is_not_Sn a))
total_Gcd (S a) (S b) prfNBZ = ?rhs
-}

