module substractNat

import equivalence_of_equality
import associativePlus
import commutativePlus
import distributiveMultAdd
import associativeMult
import commutativeMult
import properties_of_Nat
import properties_of_order

||| Given two natural numbers a, b along with a proof that a >= b, substracts b from a, gives the result along with the proof that it is correct
public export

substractNat : (a : Nat) -> (b : Nat) -> (geq a b) -> (k : Nat ** (plus k b = a))
substractNat a b (k ** prf) = (k ** (symmetry prf))
   
