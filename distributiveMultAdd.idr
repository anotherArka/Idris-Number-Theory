module distributiveMultAdd

import equivalence_of_equality
import associativePlus
import commutativePlus

%default total

public export

mult_n_Z_is_Z : (n : Nat) -> (mult n Z = Z)
mult_n_Z_is_Z Z = Refl
mult_n_Z_is_Z (S k) = mult_n_Z_is_Z k

public export

distributiveMultAdd : (a : Nat) -> (b : Nat) -> (c : Nat) -> (a * (b + c) = a*b	 + a*c)
distributiveMultAdd Z _ _ = Refl
distributiveMultAdd a Z c = rewrite (mult_n_Z_is_Z a) in Refl
distributiveMultAdd a b Z = rewrite (commutativePlus b Z) in 
                           (rewrite (mult_n_Z_is_Z a) in 
                           (rewrite commutativePlus (mult a b) Z in Refl))
distributiveMultAdd (S a) b c = rewrite (distributiveMultAdd a b c) in 
                               (rewrite (oppAssociativePlus (plus b c) (mult a b) (mult a c)) in 
                               (rewrite (commutativePlus b c) in 
                               (rewrite (associativePlus c b (mult a b)) in 
                               (rewrite (commutativePlus c (plus b (mult a b))) in 
                               (rewrite (associativePlus (plus b (mult a b)) c (mult a c)) in Refl)))))
                               
public export
                               
distributiveAddMult : (a : Nat) -> (b : Nat) -> (c : Nat) -> ((a + b) * c = a*c + b*c)
distributiveAddMult Z _ _ = Refl		
distributiveAddMult a Z c = rewrite (commutativePlus a Z) in 
                           (rewrite (commutativePlus (mult a c) Z ) in Refl)
distributiveAddMult a b Z = rewrite (mult_n_Z_is_Z b) in 
                           (rewrite (mult_n_Z_is_Z (plus a b)) in 
                           (rewrite (mult_n_Z_is_Z a) in Refl))
                           
distributiveAddMult (S a) b c = rewrite (distributiveAddMult a b c) in 
                               (rewrite associativePlus c (mult a c) (mult b c) in Refl)                            

