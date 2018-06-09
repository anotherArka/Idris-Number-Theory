module properties_of_Positive_Nat

import equivalence_of_equality
import associativePlus
import commutativePlus
import distributiveMultAdd
import associativeMult
import commutativeMult
import logical_implications
import properties_of_Nat

public export

Positive_Nat : Type
Positive_Nat = (k : Nat ** ((k = Z) -> Void))

public export

Uninhabited ((Z = Z) -> Void) where
    uninhabited fun = fun Refl

public export

toNatural : Positive_Nat -> Nat
toNatural (k ** prf) = k

public export

toPositive_Nat : (k : Nat) -> ((k = Z) -> Void) -> Positive_Nat
toPositive_Nat Z fun = absurd fun
toPositive_Nat (S k) fun = ((S k) ** fun)

public export

addPos : (a : Positive_Nat) -> (b : Positive_Nat) -> Positive_Nat
addPos (Z ** prf1) (a ** prf2) = absurd prf1
addPos (a ** prf1) (Z ** prf2) = absurd prf2
addPos ((S k) ** prf1) ((S l) ** prf2) = ((plus (S k) (S l)) ** (Z_is_not_Sn (plus k (S l))))

public export

multPos :  (a : Positive_Nat) -> (b : Positive_Nat) -> Positive_Nat
multPos (Z ** prf1) (a ** prf2) = absurd prf1
multPos (a ** prf1) (Z ** prf2) = absurd prf2
multPos ((S k) ** prf1) ((S l) ** prf2) = ((mult (S k) (S l)) ** (Z_is_not_Sn (plus l (mult k (S l)))))


 


