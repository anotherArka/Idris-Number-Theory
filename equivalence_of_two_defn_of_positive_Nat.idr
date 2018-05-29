module properties_of_positive_Nat

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

public export

Positive_Nat : Type
Positive_Nat = (k : Nat ** ((k = Z) -> Void))

toNatural : Positive_Nat -> Nat
toNatural (k ** prf) = k

toPositive_Nat : (n : Nat ** ((k = Z) -> Void)) -> Positive_Nat
toPositive_Nat (Z, prf) = ?rhs

addPos : Positive_Nat -> Positive_Nat -> Positive_Nat
addPos (Succ k) (Succ l) = Succ (S (plus k l))

multPos : Positive_Nat -> Positive_Nat -> Positive_Nat
multPos (Succ k) (Succ l) = Succ ( plus (plus k l) (mult k l))
	
Uninhabited ((Z = Z) -> Void) where
    uninhabited fun = fun Refl

Positive_Nat_defn_2 : Type 
Positive_Nat_defn_2 = (k : Nat ** ((k = Z) -> Void))

Positive_Nat_from_1_to_2 : Positive_Nat -> Positive_Nat_defn_2
Positive_Nat_from_1_to_2 (Succ k) = ((S k) ** (Z_is_not_Sn k))
 
Positive_Nat_from_2_to_1 : Positive_Nat_defn_2 -> Positive_Nat
Positive_Nat_from_2_to_1 ((S k) ** fun) = Succ k
-- confusion Positive_Nat_from_2_to_1 (Z ** ?lhs) impossible
Positive_Nat_from_2_to_1 (Z ** fun) = absurd fun

Positive_Nat_from_1_to_2_to_1 : Positive_Nat -> Positive_Nat
Positive_Nat_from_1_to_2_to_1 k = Positive_Nat_from_2_to_1 (Positive_Nat_from_1_to_2 k)

Positive_Nat_from_2_to_1_to_2 : Positive_Nat_defn_2 -> Positive_Nat_defn_2
Positive_Nat_from_2_to_1_to_2 k = Positive_Nat_from_1_to_2 (Positive_Nat_from_2_to_1 k)







