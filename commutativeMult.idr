module commutativeMult

import equivalence_of_equality
import associativePlus
import commutativePlus
import distributiveMultAdd
import associativeMult

public export

mult_n_1_is_n : (n : Nat) -> (mult n 1) = n
mult_n_1_is_n Z = Refl
mult_n_1_is_n (S n) = rewrite (mult_n_1_is_n n) in Refl

public export

commutativeMult : (a : Nat) -> (b : Nat) -> (mult a b) = (mult b a)
commutativeMult Z a = rewrite (mult_n_Z_is_Z a) in Refl	
commutativeMult (S a) b = rewrite (commutativeMult a b) in 
                         (rewrite (distributiveMultAdd b 1 a) in 
                         (rewrite (mult_n_1_is_n b) in Refl))
                         
