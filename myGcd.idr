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
import properties_of_divisibility
import properties_of_Positive_Nat
import substractNat
-- import trial_and_error


||| Condition 1 - Divisors of a and b divide g
public export
Gcd_Condition_1 : (a : Nat) -> (b : Nat) -> (c : Positive_Nat) -> Type
Gcd_Condition_1 a b (g ** prfg) = (d : Positive_Nat) -> (Divides d a) -> (Divides d b) -> (Divides d g)	

Conditions_for_Gcd : (a : Nat) -> (b : Nat) -> (gcd' : Positive_Nat) -> Type
Conditions_for_Gcd a b g =  (Divides g a, Divides g b, Gcd_Condition_1 a b g) 

MyGcd : (a : Nat) -> (b : Nat) -> (prfNBZ : NotBothZero a b) -> (g : Positive_Nat ** (Conditions_for_Gcd a b g))
MyGcd Z Z prfNBZ impossible
MyGcd (S a) Z RightIsNotZero impossible
MyGcd Z (S b) LeftIsNotZero impossible
MyGcd (S a) Z LefIsNotZero = (((S a) ** (Z_is_not_Sn a)) ** ((1 ** (rewrite commutativePlus a Z in Refl)), 
                                                             (Z ** Refl), proof_func)) where proof_func d d1 d2 = d1
                                                             
MyGcd Z (S a) RightIsNotZero = (((S a) ** (Z_is_not_Sn a)) ** ((Z ** Refl), 
                                          (1 ** (rewrite commutativePlus a Z in Refl)), proof_func)) where proof_func d d1 d2 = d2

MyGcd (S a) (S b) prfNBZ = case decGeq (S a) (S b) of
                               Geq (k ** prfGeq) => ?rhs'
                               Lt ((k ** prfLeq), prfNeq) => let (g ** (part_gk, part_gb, proof_func)) = MyGcd k (S b) RightIsNotZero
                                                             in (g ** (?cond1, part_gb, ?cond3)) 
                                                             
                                                                                                                            

                                                                

















