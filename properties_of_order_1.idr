module properties_of_order_1 

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
import substractNat
import properties_of_divisibility
import congruence


{-
||| Property 1.1 - a = b, g|a, b implies (a/g) = (b/g)
public export

order_property_1_1 : (a : Nat) -> (b : Nat) -> (prfEq : (a = b)) -> (g : Positive_Nat) 
                   -> (prfa : Divides g a) -> (prfb : Divides g b) 
                   -> ((fst (complete_divide a g prfa)) = (fst (complete_divide b g prfb)))
                   
order_property_1_1 a a Refl (g ** prfG) (Z ** prfa) ((S l) ** prfb) = Z_is_not_Sn l 
                                                    
||| Property 1.2 - if c.a = c.b then a = b
public export

order_property_1_2 : (a : Nat) -> (b : Nat) -> (c : Positive_Nat) 
                -> (prfEq : ((mult (toNatural c) a) = (mult (toNatural c) b))) -> (a = b)

order_property_1_2 a b (Z ** prf) prfEq = absurd prf 
order_property_1_2 a b ((S c) ** prfPos) prfEq =    
-}   
   
   
   
   
   
   
   
