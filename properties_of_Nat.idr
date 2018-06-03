module properties_of_Nat

import logical_implications
import commutativePlus
import associativePlus
import associativeMult
import commutativeMult
import equivalence_of_equality

%default total


||| Property 1 - Z is not a successor of any natural number
public export

Z_is_not_Sn : (n : Nat) -> ((S n) = Z) -> Void
Z_is_not_Sn n Refl impossible


||| Property 2 - n = m implies (S n) = (S m)
public export

n_eq_m_implies_Sn_eq_Sm : (n : Nat) -> (m : Nat) -> (n = m) -> ((S n) = (S m))
n_eq_m_implies_Sn_eq_Sm n m prf = cong prf

||| Property 3 - (S n) = (S m) implies (n = m)
public export

Sn_eq_Sm_implies_n_eq_m : (n : Nat) -> (m : Nat) -> (S n) = (S m) -> (n = m)
Sn_eq_Sm_implies_n_eq_m n n Refl = Refl

public export

cancellation : (k : Nat) -> (a : Nat) -> (b : Nat) -> (plus k a = plus k b) -> (a = b)
cancellation Z a b prf = prf
cancellation (S k) a b prf = cancellation k a b (Sn_eq_Sm_implies_n_eq_m (plus k a) (plus k b) prf)	 

public export

adding_four_1 : (a : Nat) -> (b : Nat) -> (k : Nat) -> (l : Nat) -> plus (plus a b) (plus k l) = plus a (plus b (plus k l))
adding_four_1 a b k l = rewrite symmetry (associativePlus (plus a b) k l) in	
                       (rewrite (associativePlus a b k) in 
                       (rewrite (associativePlus a (plus b k) l) in 
                       (rewrite symmetry (associativePlus b k l) in Refl)))
                       
public export
                          
adding_four_2 : (a : Nat) -> (b : Nat) -> (k : Nat) -> (l : Nat) -> plus (plus a b) (plus k l) = plus (plus k b) (plus l a)
adding_four_2 a b k l = rewrite (adding_four_1 a b k l) in 
                       (rewrite (commutativePlus l a) in 
                       (rewrite (commutativePlus k b) in 
                       (rewrite (adding_four_1 b k a l) in 
                       (rewrite symmetry (associativePlus k a l) in 
                       (rewrite (commutativePlus k a) in 
                       (rewrite (associativePlus a k l) in 
                       (rewrite symmetry (adding_four_1 a b k l) in 
                       (rewrite symmetry (adding_four_1 b a k l) in 
                       (rewrite (commutativePlus a b) in Refl)))))))))          	 	

public export
 	
multiplying_four_1 : (a : Nat) -> (b : Nat) -> (k : Nat) -> (l : Nat) -> mult (mult a b) (mult k l) = mult a (mult b (mult k l))
multiplying_four_1 a b k l = rewrite symmetry (associativeMult (mult a b) k l) in 
                            (rewrite associativeMult a b k in 
                            (rewrite associativeMult a (mult b k) l in 
                            (rewrite symmetry (associativeMult b k l) in Refl)))
                            
public export
                            
multiplying_four_2 : (a : Nat) -> (b : Nat) -> (k : Nat) -> (l : Nat) -> mult (mult a b) (mult k l) = mult (mult k b) (mult l a)
multiplying_four_2 a b k l = rewrite (multiplying_four_1 a b k l) in 
                       (rewrite (commutativeMult l a) in 
                       (rewrite (commutativeMult k b) in 
                       (rewrite (multiplying_four_1 b k a l) in 
                       (rewrite symmetry (associativeMult k a l) in 
                       (rewrite (commutativeMult k a) in 
                       (rewrite (associativeMult a k l) in 
                       (rewrite symmetry (multiplying_four_1 a b k l) in 
                       (rewrite symmetry (multiplying_four_1 b a k l) in 
                       (rewrite (commutativeMult a b) in Refl)))))))))          	
                            
                            

                            
                            
                            
                            
                            
                            
                            
                            
                            
                            
                            
