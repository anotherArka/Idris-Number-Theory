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
import properties_of_Positive_Nat
import difference
import coProductType
--import substractNat

public export

Divides : Positive_Nat -> Nat -> Type
Divides (a ** prf) b = (divisor ** ((mult divisor a = b)))

||| Property 1 - All non zero natural numbers divides Z
public export

div_property1 : (m : Positive_Nat) -> (Divides m Z)
div_property1 (n ** prf) = (Z ** Refl)  

||| Property 2 - All natural numbers can be divided by 1
public export

div_property2 : (a : Nat) -> Divides (1 ** (Z_is_not_Sn Z)) a
div_property2 a = (a ** (rewrite mult_n_1_is_n a in Refl))

||| Property 3 - if a = 1 then a divides 1
public export

div_property3 : (a : Positive_Nat) -> ((toNatural a) = (S Z)) -> (Divides a (S Z))
div_property3 ((S Z) ** prf) Refl = (1 ** Refl)
div_property3 ((S(S l)) ** prf) Refl impossible

||| Property 4 - a divides 1 only if a = 1
public export

div_property4 : (a : Positive_Nat) -> (Divides a 1) -> ((toNatural a) = 1)
div_property4 ((S Z) ** prf) ((S Z) ** Refl) = Refl
div_property4 ((S(S k)) ** prf) (Z ** Refl) impossible
div_property4 ((S(S k)) ** prf) ((S l) ** Refl) impossible
div_property4 ((S Z) ** prf) (Z ** Refl) impossible
div_property4 ((S Z) ** prf) ((S (S k)) ** Refl) impossible

||| Property 5 - a divides 1 iff a = 1
public export

div_property5 : (a : Positive_Nat) -> ((Divides a 1) -> ((toNatural a) = 1), ((toNatural a) = 1) -> (Divides a 1))
div_property5 k = (div_property4 k , div_property3 k)

||| Property 6 - a|b and c|d implies ac|bd
public export
-- use another defn of positive nat
div_property6 : (u : Positive_Nat) -> (v : Nat) -> (w : Positive_Nat) -> (t : Nat) -> 
            (Divides u v, Divides w t) -> (Divides (multPos u w) (mult v t))
            
            
div_property6 (a ** prf3) b (Z ** prf4) d ((x ** prf1) , (y ** prf2)) = absurd prf4
div_property6 (Z ** prf3) b (c ** prf4) d ((x ** prf1) , (y ** prf2)) = absurd prf3
div_property6 ((S a) ** prf3) b ((S c) ** prf4) d ((x ** prf1) , (y ** prf2)) = ((mult x y) ** (rewrite (commutativeMult x y) in 
                                                                                               (rewrite (multiplying_four_2 y x (S a) (S c)) in 
                                                                                               (rewrite symmetry (commutativeMult x (S a)) in 
                                                                                               (rewrite symmetry (commutativeMult y (S c)) in -- ?rhs)))))
                                                                                               (multiplying_equals (mult x (S a)) b (mult y (S c)) d prf1 prf2))))))                 
                                                               
||| Property 7 - if a|b and b|c then a|c
public export

div_property7 : (a : Positive_Nat) -> (b : Positive_Nat) -> (c : Nat) -> (Divides a (toNatural b), Divides b c) -> Divides a c 
div_property7 ((S a) ** prfa) ((S b) ** prfb) c ((x ** prf1) , (y ** prf2)) = ((mult x y) ** rewrite (symmetry prf2) in 
                                                                          (rewrite (symmetry prf1) in
                                                                          (rewrite (commutativeMult x y) in  
                                                                          (rewrite (associativeMult y x (S a)) in Refl))))
div_property7 (Z ** prfa) (b ** prfb) c ((x ** prf1) , (y ** prf2)) = absurd prfa
div_property7 (a ** prfa) (Z ** prfb) c ((x ** prf1) , (y ** prf2)) = absurd prfb                                                                           
                                                                          
                                                                          
||| Property 8 - if a|b and b /= Z then a <= b 
public export

div_property8 : (a : Positive_Nat) -> (b : Nat) -> (((b = Z) -> Void), (Divides a b)) -> leq (toNatural a) b
div_property8 ((S k) ** prfk) Z (prf1, prf2) = absurd prf1
div_property8 ((S k) ** prfk) (S l) (prf1, (Z ** prf2)) = absurd prf2
div_property8 ((S k) ** prfk) (S l) (prf1, ((S m) ** prf2)) = ((mult m (S k)) ** (rewrite (commutativePlus  (mult m (S k)) (S k)) in (symmetry prf2)))
div_property8 (Z ** prfk) l (prf1, (m ** prf2)) = absurd prfk
{- 
||| Property 9 - if g|a, b and a >= b then g|(a - b)

div_property9 : (g : Positive_Nat) -> (a : Nat) -> (b : Nat) -> (prfG : geq a b) -> 
                (Divides g a) -> (Divides g b) -> (Divides g (fst (substractNat a b prfG)))
                
div_property9 (Z ** prfP) a b prfG prfDa prfDb = absurd prfP
div_property9 ((S g) ** prfP) a b (k ** prfG) (da ** prfDa) (db ** prfDb) = ?rhs 
-}
||| Given a positive Natural number b, a Natural number a and a proof that b divides a it gives the result of dividing a by b and proves that it is the correct result
public export

complete_divide : (a : Nat) -> (b : Positive_Nat) -> (Divides b a) -> (ans ** (mult ans (toNatural b) = a))
complete_divide a (b ** prfP) (k ** prfD) = (k ** prfD)


||| Property 9 - Given two natural numbers a and b. If d divides a and b then d divides a - b
public export

div_property9 : (a : Nat) -> (b : Nat) -> (d : Positive_Nat) -> (Divides d a) -> (Divides d b) -> (Divides d (difference a b))
div_property9 a Z (d ** prfPos) (k ** prfDa) (l ** prfDb) = (rewrite diff_property1 a in (k ** prfDa))
div_property9 Z b (d ** prfPos) (k ** prfDa) (l ** prfDb) = (l ** prfDb)
div_property9 a b (d ** prfPos) (k ** prfDa) (l ** prfDb) = ((difference k l) ** (rewrite distributiveDiffMult k l d in 
                                                                                 (rewrite prfDa in 
                                                                                 (rewrite prfDb in Refl))))
                                                                                 
||| Property 10 - Given two natural numbers a and b. If d divides a and a - b then d divides a
public export

div_property10 : (a : Nat) -> (b : Nat) -> (d : Positive_Nat) -> (Divides d a) -> (Divides d (difference a b)) -> (Divides d b)
div_property10 a b (d ** prfPosD) (k ** divDA) (l ** divDdif) = case (diff_property2 a b) of 
                                                                     (True ** prfDif1) => ((plus l k) ** (rewrite distributiveAddMult l k d in 
                                                                                                         (rewrite divDA in 
                                                                                                         (rewrite divDdif in prfDif1))))
                                                                     (False ** prfDif2) => ((difference k l) ** (rewrite distributiveDiffMult k l d in
                                                                                                                (rewrite divDA in 
                                                                                                                (rewrite divDdif in 
                                                                                                                (rewrite diff_property7 a b prfDif2 in
                                                                                                                 Refl)))))



                                                                

















