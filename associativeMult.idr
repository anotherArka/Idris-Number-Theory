module associativeMult

import equivalence_of_equality
import associativePlus
import commutativePlus
import distributiveMultAdd

%default total

public export

associativeMult' : (a : Nat) -> (b : Nat) -> (c : Nat) -> (mult a (mult b c) = mult (mult a b) c)
associativeMult' Z b c = Refl
associativeMult' (S a) b c = rewrite (distributiveAddMult b (mult a b) c) in 
                           (rewrite (associativeMult' a b c) in Refl)
                           
public export
                          
associativeMult : (a : Nat) -> (b : Nat) -> (c : Nat) -> (mult (mult a b) c = mult a (mult b c))
associativeMult Z b c = Refl
associativeMult (S a) b c = rewrite (distributiveAddMult b (mult a b) c) in 
                           (rewrite (associativeMult a b c) in Refl)
                          
