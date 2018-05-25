module properties_of_order

import equivalence_of_equality
import associativePlus
import commutativePlus
import distributiveMultAdd
import associativeMult
import commutativeMult
import properties_of_Nat

public export

geq : Nat -> Nat -> Type
geq a b = (k : Nat ** (a = k + b))

public export

leq : Nat -> Nat -> Type
leq a b = geq b a

||| Property 1 - if (a = b) then (a >= b)
public export

geq_if_eq : (a : Nat) -> (b : Nat) -> (a = b) -> geq a b
geq_if_eq a a Refl = (Z ** Refl)	

||| Property 2 - if (a = b) then (a <= b)
public export

leq_if_eq  : (a : Nat) -> (b : Nat) -> (a = b) -> leq a b
leq_if_eq a a Refl = (Z ** Refl)

||| Property 3 - (k + l) = 0 implies k is Zero
public export

plus_k_l_is_Z_implies_both_Z : (k : Nat) -> (l : Nat) -> (plus k l = Z) -> (k = Z)
plus_k_l_is_Z_implies_both_Z Z Z Refl = Refl
plus_k_l_is_Z_implies_both_Z Z (S k) Refl impossible
plus_k_l_is_Z_implies_both_Z (S k) Z Refl impossible
plus_k_l_is_Z_implies_both_Z (S k) (S l) Refl impossible

||| Property 4 - (k + a = a) implies k = Zero
public export

plus_k_a_eq_a_implies_k_is_Z : (k : Nat) -> (a : Nat) -> (plus k a = a) -> (k = Z)
plus_k_a_eq_a_implies_k_is_Z k a prf = cancellation a k Z (rewrite commutativePlus a Z in (rewrite (commutativePlus a k) in prf))

||| Property 5 - (a = b) -> (c = d) -> (a + c = b + d)
public export

adding_equals : (a : Nat) -> (b : Nat) -> (c : Nat) -> (d : Nat) -> (a = b) -> (c = d) -> (plus a c = plus b d)
adding_equals a a c c Refl Refl = Refl

||| Property 6 - (a = b) -> (c = d) -> (a * c = b * d)
public export

multiplying_equals : (a : Nat) -> (b : Nat) -> (c : Nat) -> (d : Nat) -> (a = b) -> (c = d) -> (mult a c = mult b d)
multiplying_equals a a c c Refl Refl = Refl

||| Property 7 - (a >= b) and (a <= b) implies (a = b)
public export

geq_and_leq_implies_eq : (a : Nat) -> (b : Nat) -> (geq a b,leq a b) -> (a = b)
geq_and_leq_implies_eq a b ((Z ** prf1), (l ** prf2)) = rewrite prf1 in Refl
geq_and_leq_implies_eq a b ((k ** prf1), (Z ** prf2)) = rewrite prf2 in Refl
geq_and_leq_implies_eq a b ((k ** prf1), (l ** prf2)) = rewrite prf1 in 
                                                       (rewrite (plus_k_l_is_Z_implies_both_Z k l 
                                                        (cancellation (plus a b) (plus k l) Z 
                                                        (part4 a b k l (adding_equals a (plus k b) b (plus l a) prf1 prf2)))) in Refl)
                                                         where part4 : (a : Nat) -> (b : Nat) -> (k : Nat) -> (l : Nat) -> 
                                                                       (plus a b = plus (plus k b) (plus l a)) -> 
                                                                       (plus (plus a b) (plus k l) = plus (plus a b) 0)
                                                                 
                                                               part4 a b k l prf =  rewrite (commutativePlus (plus a b) Z) in 
                                                                                   (rewrite (adding_four_2 a b k l) in (symmetry prf)) 
                                                                                   
                                                                                          
                                                                 
                                                                      
                                                               
                            








