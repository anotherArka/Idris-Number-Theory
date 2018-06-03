module properties_of_order

import equivalence_of_equality
import associativePlus
import commutativePlus
import distributiveMultAdd
import associativeMult
import commutativeMult
import properties_of_Nat
import properties_of_Positive_Nat
import congruence

%default total

public export

neq : Nat -> Nat -> Type
neq a b = ((a = b) -> Void)

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
                                                                                   
public export
                                                       
data DecGeq : (a : Nat) -> (b : Nat) -> Type where
    Geq : (prf : (geq a b)) -> DecGeq a b
    Lt : (prf : (leq a b, neq a b)) -> DecGeq a b

public export

decGeq : (a : Nat) -> (b : Nat) -> DecGeq a b
decGeq a Z = Geq (a ** rewrite commutativePlus a Z in Refl)
decGeq Z (S k) = Lt (((S k) ** (rewrite commutativePlus k Z in Refl)), (Z_is_not_Sn k). symmetry )
decGeq (S k) (S l) = case decGeq k l of
                         Geq prf => let m = (fst prf) in Geq (m ** rewrite commutativePlus m (S l) in 
                                                             (n_eq_m_implies_Sn_eq_Sm k (plus l m) 
                                                             (rewrite commutativePlus l m in (snd prf)))) 	                                      
                         Lt prf => let m = fst (fst prf)
                                       prf1 = snd (fst prf)  
                                   in Lt ((m ** (rewrite commutativePlus m (S k) in 
                                                                      (rewrite commutativePlus k m in 
                                                                      (n_eq_m_implies_Sn_eq_Sm l (plus m k) prf1)))), 
                                                                       ((snd prf) . (Sn_eq_Sm_implies_n_eq_m k l)))
||| Property 8 - (S n) >= (S m) implies n >= m
public export

order_property8 : (n : Nat) -> (m : Nat) -> (geq (S n) (S m)) -> (geq n m)
order_property8 n m (k ** prf) = (k ** (Sn_eq_Sm_implies_n_eq_m n (plus k m) (rewrite commutativePlus k m in 
                                                                             (rewrite commutativePlus (S m) k in prf))))
                                                                             
||| Property 9 - Z is not greater than equal to any (S n)
public export

order_property9 : (n : Nat) -> (geq Z (S n)) -> Void
order_property9 n (k ** prf) = Z_is_not_Sn (plus n k) (rewrite commutativePlus (S n) k in (symmetry prf))

||| Property 11 - a >= b implies c.a >= c.b
public export

order_property11 : (a : Nat) -> (b : Nat) -> (prfG : geq a b) -> (c : Nat) -> (geq (mult c a) (mult c b))
order_property11 a b (k ** prfG) c = ((mult c k) ** (rewrite symmetry (distributiveMultAdd c k b) in 
                                                    (multiplying_equals c c a (plus k b) Refl prfG)))
                                                    
||| Property 12 - a, b > 0 implies a.b > 0
public export

order_property12 : (a : Positive_Nat) -> (b : Positive_Nat) -> ((mult (toNatural a) (toNatural b) = Z) -> Void)

order_property12 (Z ** prf) b = absurd prf
order_property12 a (Z ** prf) = absurd prf
order_property12 ((S a) ** prfa) ((S b) ** prfb) = Z_is_not_Sn (plus b (mult a (S b)))

||| Property 13 - a.b = 0 and a > 0 implies b = 0
public export

order_property13 : (a : Positive_Nat) -> (b : Nat) -> ((mult (toNatural a) b) = Z) -> (b = Z) 
order_property13 (Z ** prf1) b prf2 = absurd prf1
order_property13 ((S a) ** prfPos) Z prfEq = Refl
order_property13 ((S a) ** prfPos) (S b) prfEq = void(Z_is_not_Sn (plus b (mult a (S b))) prfEq)  	

public export
data DecOrder : Nat -> Nat -> Type where
    Grt : (prf : (geq a b, neq a b)) -> DecOrder a b
    Lst : (prf : (leq a b, neq a b)) -> DecOrder a b
    Eql : (prf : a = b) -> DecOrder a b
    

public export
decOrder : (a : Nat) -> (b : Nat) -> DecOrder a b
decOrder Z Z = Eql Refl
decOrder Z (S a) = Lst (((S a) ** (rewrite commutativePlus a Z in Refl)), (Z_is_not_Sn a). symmetry)
decOrder (S a) Z = Grt (((S a) ** (rewrite commutativePlus a Z in Refl)), Z_is_not_Sn a)
decOrder (S a) (S b) = case (decOrder a b) of 
                            Eql prfEq => Eql (cong prfEq)
                            Grt ((k ** prfG), prfNq) => Grt ((k ** (rewrite commutativePlus k (S b) in 
                                                                   (rewrite commutativePlus b k in cong prfG))), 
                                                                   prfNq . (Sn_eq_Sm_implies_n_eq_m a b))
                            Lst ((k ** prfL), prfNq) => Lst ((k ** (rewrite commutativePlus k (S a) in 
                                                                   (rewrite commutativePlus a k in cong prfL))), 
                                                                   prfNq . (Sn_eq_Sm_implies_n_eq_m a b))
                            
                                                  
                                                               
                                                                      
                                                               
                            








