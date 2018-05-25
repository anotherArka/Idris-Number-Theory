module properties_of_divisibility

import equivalence_of_equality
import associativePlus
import commutativePlus
import distributiveMultAdd
import associativeMult
import commutativeMult
import logical_implications
import properties_of_order
import properties_of_Nat
import properties_of_order
--import equivalence_of_two_defn_of_positive_Nat

public export

data Positive_Nat = Succ Nat

public export

toNatural : Positive_Nat -> Nat
toNatural (Succ n) = (S n)

public export

Divides : Positive_Nat -> Nat -> Type
Divides a b = (divisor ** ((mult divisor (toNatural a)) = b))

public export

addPos : Positive_Nat -> Positive_Nat -> Positive_Nat
addPos (Succ k) (Succ l) = Succ (S (plus k l))

public export

multPos : Positive_Nat -> Positive_Nat -> Positive_Nat
multPos (Succ k) (Succ l) = Succ ( plus (plus k l) (mult k l))

public export

Uninhabited ((Z = Z) -> Void) where
    uninhabited fun = fun Refl

||| Property 1 - All non zero natural numbers divides Z
public export

div_property1 : (n : Positive_Nat) -> (Divides n Z)
div_property1 n = (Z ** Refl)

||| Property 2 - All natural numbers can be divided by 1
public export

div_property2 : (a : Nat) -> Divides (Succ Z) a
div_property2 a = (a ** (rewrite mult_n_1_is_n a in Refl))

||| Property 3 - if a = 1 then a divides 1
public export

div_property3 : (a : Positive_Nat) -> ((toNatural a) = (S Z)) -> (Divides a (S Z))
div_property3 (Succ Z) Refl = (1 ** Refl)
div_property3 (Succ (S l)) Refl impossible

||| Property 4 - a divides 1 only if a = 1
public export

div_property4 : (a : Positive_Nat) -> (Divides a 1) -> ((toNatural a) = 1)
div_property4 (Succ Z) ((S Z) ** Refl) = Refl
div_property4 (Succ (S k)) (Z ** Refl) impossible
div_property4 (Succ (S k)) ((S l) ** Refl) impossible
div_property4 (Succ Z) (Z ** Refl) impossible
div_property4 (Succ Z) ((S (S k)) ** Refl) impossible

||| Property 5 - a divides 1 iff a = 1
public export

div_property5 : (a : Positive_Nat) -> ((Divides a 1) -> ((toNatural a) = 1), ((toNatural a) = 1) -> (Divides a 1))
div_property5 (Succ k) = (div_property4 (Succ k) , div_property3 (Succ k))

||| Property 6 - a|b and c|d implies ac|bd
public export

div_property6 : (a : Positive_Nat) -> (b : Nat) -> (c : Positive_Nat) -> (d : Nat) -> 
            (Divides a b, Divides c d) -> (Divides (multPos a c) (mult b d))

div_property6 (Succ a) b (Succ c) d ((x ** prf1) , (y ** prf2)) = ((mult x y) ** (rewrite commutativePlus a c in 
                                                                             (rewrite associativePlus c a (mult a c) in 
                                                                             (rewrite commutativeMult a c in 
                                                                             (rewrite commutativeMult (S c) a in 
                                                                             (rewrite multiplying_four_1 x y (S a) (S c) in 
                                                                             (rewrite symmetry (associativeMult y (S a) (S c)) in 
                                                                             (rewrite commutativeMult y (S a) in 
                                                                             (rewrite associativeMult (S a) y (S c) in 
                                                                             (rewrite symmetry (associativeMult x (S a) (mult y (S c))) in 
                                                                             (multiplying_equals (mult x (S a)) b (mult y (S c)) d prf1 prf2)))))))))))
                                                               
||| Property 7 - if a|b and b|c then a|c
public export

div_property7 : (a : Positive_Nat) -> (b : Positive_Nat) -> (c : Nat) -> (Divides a (toNatural b), Divides b c) -> Divides a c 
div_property7 (Succ a) (Succ b) c ((x ** prf1) , (y ** prf2)) = ((mult x y) ** rewrite (symmetry prf2) in 
                                                                          (rewrite (symmetry prf1) in
                                                                          (rewrite (commutativeMult x y) in  
                                                                          (rewrite (associativeMult y x (S a)) in Refl))))
                                                                          
||| Property 8 - if a|b and b /= Z then a <= b 

div_property8 : (a : Positive_Nat) -> (b : Nat) -> (((b = Z) -> Void), (Divides a b)) -> leq (toNatural a) b
div_property8 (Succ k) Z (prf1, prf2) = absurd prf1
div_property8 (Succ k) (S l) (prf1, (Z ** prf2)) = absurd prf2
div_property8 (Succ k) (S l) (prf1, ((S m) ** prf2)) = ((mult m (S k)) ** (rewrite (commutativePlus  (mult m (S k)) (S k)) in (symmetry prf2)))



                                                                

















