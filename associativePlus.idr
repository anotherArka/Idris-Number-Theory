module associativePlus

import equivalence_of_equality

%default total

public export

associativePlus : (a : Nat) -> (b : Nat) -> (c : Nat) -> ((a + b) + c = a + (b + c))
associativePlus Z b c = Refl
associativePlus (S k) b c = rewrite (associativePlus k b c) in Refl

public export

oppAssociativePlus :  (a : Nat) -> (b : Nat) -> (c : Nat) -> (a + (b + c) = (a + b) + c)
oppAssociativePlus a b c = symmetry (associativePlus a b c) --rewrite (associativePlus a b c) in Refl

