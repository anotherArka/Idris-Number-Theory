module difference

import coProductType
import commutativePlus
import equivalence_of_equality
import commutativeMult
import distributiveMultAdd
import properties_of_Nat
import properties_of_order

public export

difference' : (a : Nat) -> (b : Nat) -> (k : Nat ** coProduct (plus k a = b) (plus k b = a))
difference' Z a = (a ** (True ** (rewrite commutativePlus a Z in Refl)))
difference' a Z = (a ** (False ** (rewrite commutativePlus a Z in Refl)))
difference' (S a) (S b) = case difference' a b of
                             (k ** (True ** prf)) => (k ** (True ** (rewrite commutativePlus k (S a) in 
                                                                    (rewrite commutativePlus a k in 
                                                                    (cong prf)))))
                             (k ** (False ** prf)) => (k ** (False ** (rewrite commutativePlus k (S b) in 
                                                                    (rewrite commutativePlus b k in 
                                                                    (cong prf)))))

public export

difference : (a : Nat) -> (b : Nat) -> Nat
difference Z a = a
difference a Z = a
difference (S a) (S b) = difference a b

||| Property 1 - difference a Z = a
public export

diff_property1 : (a : Nat) -> ((difference a Z) = a)
diff_property1 Z = Refl
diff_property1 (S a) = Refl

||| Property 2 - a + (difference a b) = b or b + (difference a b) = a
public export

diff_property2 : (a : Nat) -> (b : Nat) -> (let k = (difference a b) in coProduct (plus k a = b) (plus k b = a))
diff_property2 Z a = (True ** (rewrite commutativePlus a Z in Refl))
diff_property2 a Z = (False ** (rewrite diff_property1 a in (rewrite commutativePlus a Z in Refl)))
diff_property2 (S a) (S b) = case (diff_property2 a b) of 
                                 (True ** (prfDif)) => (True ** (rewrite commutativePlus (difference a b) (S a) in 
                                                                (rewrite commutativePlus a (difference a b) in 
                                                                (n_eq_m_implies_Sn_eq_Sm (plus (difference a b) a) b prfDif))))
                                 (False ** (prfDif)) => (False ** (rewrite commutativePlus (difference a b) (S b) in 
                                                                  (rewrite commutativePlus b (difference a b) in 
                                                                  (n_eq_m_implies_Sn_eq_Sm (plus (difference a b) b) a prfDif))))
                                 
||| Property 3 - difference (S a) (S b) = difference a b
public export

diff_property3 : (a : Nat) -> (b :Nat) -> (difference (S a) (S b) = difference a b)
diff_property3 a b = Refl


||| Property 4 - difference a a = Z
public export

diff_property4 : (a : Nat) -> ((difference a a) = Z)
diff_property4 Z = Refl
diff_property4 (S a) = diff_property4 a

||| Property 5 - difference of (a + b) and b is a
public export

diff_property5 : (a : Nat) -> (b : Nat) -> ((difference (plus a b) b) = a)
diff_property5 Z a = diff_property4 a
diff_property5 a Z = (rewrite commutativePlus a Z in (diff_property1 a))
diff_property5 a (S b) = (rewrite commutativePlus a (S b) in 
                         (rewrite commutativePlus b a in (diff_property5 a b)))
                         
||| Property 6 - difference b/w (k + a) and (k + b) is same as difference b/w a and b
public export

diff_property6 : (a : Nat) -> (b : Nat) -> (k : Nat) -> ((difference (plus k a) (plus k b)) = (difference a b))
diff_property6 a b Z = Refl
diff_property6 a b (S c) = diff_property6 a b c	 

public export                                                                                                                                        
distributiveMultDiff : (a : Nat) -> (b : Nat) -> (c : Nat) -> ((mult a (difference b c)) = (difference (mult a b) (mult a c)))
distributiveMultDiff Z b c = Refl
distributiveMultDiff a Z c = (rewrite commutativeMult a Z in Refl)
distributiveMultDiff a b Z = (rewrite commutativeMult a Z in 
                             (rewrite (diff_property1 b) in 
                             (rewrite (diff_property1 (mult a b)) in Refl)))
distributiveMultDiff a (S b) (S c) = (rewrite (commutativeMult a (S b)) in 
                                     (rewrite (commutativeMult a (S c)) in 
                                     (rewrite diff_property6 (mult b a) (mult c a) a in 
                                     (rewrite commutativeMult b a in 
                                     (rewrite commutativeMult c a in 
                                     (distributiveMultDiff a b c))))))  
                                     
public export
distributiveDiffMult : (a : Nat) -> (b : Nat) -> (c : Nat) -> ((mult (difference a b) c) = (difference (mult a c) (mult b c)))
distributiveDiffMult a b c = (rewrite commutativeMult (difference a b) c in 
                             (rewrite commutativeMult a c in 
                             (rewrite commutativeMult b c in 
                             (distributiveMultDiff c a b))))
                             
||| Property 7 - (difference a (difference a b)) = b when a > b
public export

diff_property7 : (a : Nat) -> (b : Nat) -> (plus (difference a b) b = a) -> ((difference a (difference a b)) = b)
diff_property7 a b prfDif = (rewrite symmetry (diff_property6 a (difference a b) b) in
                            (rewrite commutativePlus b (difference a b) in    
                            (rewrite prfDif in 
                            (rewrite diff_property5 b a in Refl))))
                            
||| Property 8 - a >= b implies b + difference a b = a
public export
diff_property8 : (a : Nat) -> (b : Nat) -> (geq a b) -> ((plus (difference a b) b) = a)
diff_property8 a b (k ** prfK) = case diff_property2 a b of
                                    (False ** prfDif) => prfDif 
                                    (True ** prfDif) => rewrite prfK in 
                                                       (rewrite diff_property5 k b in Refl)
                                    
||| Property 9 - (difference (S a) (S b)) <= a given a > b
public export
diff_property9 : (a : Nat) -> (b : Nat) -> (geq a b) -> (geq a (difference (S a) (S b)))
diff_property9 a b (k ** prfK) = (rewrite prfK in 
                                 (rewrite diff_property5 k b in 
                                 (rewrite commutativePlus k b in (b ** Refl))))
                                 
||| Property 10 - difference a b = difference b a
public export
diff_property10 : (a : Nat) -> (b : Nat) -> (difference a b) = (difference b a)
diff_property10 Z Z = Refl
diff_property10 (S a) Z = Refl
diff_property10 Z (S a) = Refl
diff_property10 (S a) (S b) = diff_property10 a b













