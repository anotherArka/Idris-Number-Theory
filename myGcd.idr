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
import properties_of_divisibility
import properties_of_Positive_Nat
import coProductType
import difference

------------------------------------------------------------------------------------------------------------------------------------------------

||| Condition 1 - Divisors of a and b divide g
public export
Gcd_Condition_1 : (a : Nat) -> (b : Nat) -> (c : Positive_Nat) -> Type
Gcd_Condition_1 a b (g ** prfg) = (d : Positive_Nat) -> (Divides d a) -> (Divides d b) -> (Divides d g)

------------------------------------------------------------------------------------------------------------------------------------------------

Conditions_for_Gcd : (a : Nat) -> (b : Nat) -> (gcd' : Positive_Nat) -> Type
Conditions_for_Gcd a b g =  (Divides g a, Divides g b, Gcd_Condition_1 a b g)

------------------------------------------------------------------------------------------------------------------------------------------------

public export
Gcd_helper : (a : Nat) -> (b : Nat) -> (c : Positive_Nat) -> (Gcd_Condition_1 (S b) (difference b a) c) -> (Gcd_Condition_1 (S a) (S b) c)
Gcd_helper a b (g ** prfPosG) cond1 (d ** prfPosD) (k ** divDA) (l ** divDB) = cond1 (d ** prfPosD) (l ** divDB)
                                                                                     (div_property9 (S b) (S a) (d ** prfPosD)
                                                                                                                (l ** divDB) (k ** divDA))

------------------------------------------------------------------------------------------------------------------------------------------------

MyGcd : (a : Nat) -> (b : Nat) -> (prfNBZ : NotBothZero a b) -> (g : Positive_Nat ** (Conditions_for_Gcd a b g))

MyGcd Z Z prfNBZ impossible 
MyGcd (S a) Z RightIsNotZero impossible
MyGcd Z (S b) LeftIsNotZero impossible
MyGcd (S a) Z LeftIsNotZero = (((S a) ** (Z_is_not_Sn a)) ** ((1 ** (rewrite commutativePlus a Z in Refl)),
                                                             (Z ** Refl), proof_func)) where proof_func d d1 d2 = d1

MyGcd Z (S a) RightIsNotZero = (((S a) ** (Z_is_not_Sn a)) ** ((Z ** Refl),
                                          (1 ** (rewrite commutativePlus a Z in Refl)), proof_func)) where proof_func d d1 d2 = d2


MyGcd (S a) (S b) prfNBZ = let (g ** (divGB, divGDif, cond)) = (MyGcd (S b) (difference (S b) (S a)) LeftIsNotZero)
                           in (g ** (div_property10 (S b) (S a) g divGB divGDif , divGB, (Gcd_helper a b g cond)))

------------------------------------------------------------------------------------------------------------------------------------------------

proof_func1 : (z : Nat) -> (d : Positive_Nat) -> Divides d (S z) -> Divides d (S z) -> Divides d (S z)
proof_func1 z d prf1 prf2 = prf1

------------------------------------------------------------------------------------------------------------------------------------------------

Gcd_helper2 : (a : Nat) -> (b : Nat) -> (c : Positive_Nat) -> (Gcd_Condition_1 (S a) (difference b a) c) -> (Gcd_Condition_1 (S a) (S b) c)
Gcd_helper2 a b (g ** prfPosG) cond1 (d ** prfPosD) (k ** divDA) (l ** divDB) = cond1 (d ** prfPosD) (k ** divDA)
                                                                                      (div_property9 (S b) (S a) (d ** prfPosD)
                                                                                                                 (l ** divDB) (k ** divDA))

------------------------------------------------------------------------------------------------------------------------------------------------

totalGcd : (a : Nat) -> (b : Nat) -> (NotBothZero a b) -> (bound : Nat) -> (geq bound (plus a b)) ->
           (g : Positive_Nat ** (Conditions_for_Gcd a b g))

totalGcd Z Z prfNBZ bound prfG impossible

totalGcd Z (S a) prfNBZ bound prfG = (((S a) ** (Z_is_not_Sn a)) ** ((Z ** Refl),
                                          (1 ** (rewrite commutativePlus a Z in Refl)), proof_func)) where proof_func d d1 d2 = d2

totalGcd (S a) Z prfNBZ bound prfG = (((S a) ** (Z_is_not_Sn a)) ** ((1 ** (rewrite commutativePlus a Z in Refl)),
                                                             (Z ** Refl), proof_func)) where proof_func d d1 d2 = d1

totalGcd (S a) (S b) prfNBZ Z (k ** prfG) = void (order_property9 (plus a (S b)) (k ** prfG))
totalGcd (S a) (S b) prfNBZ (S bound) (k ** prfK) = case decOrder a b of
                                                         Eql Refl => (((S a) ** (Z_is_not_Sn a)) ** ((1 ** (rewrite commutativePlus a Z in Refl)),
                                                                                                 (1 ** (rewrite commutativePlus a Z in Refl)),
                                                                                                 proof_func1 a))

                                                         Grt ((l ** prfL), prfNEq) => let (g ** (divGB, divGDif, cond)) =
                                                                                      totalGcd (S b) (difference a b) LeftIsNotZero bound (rewrite commutativePlus b (difference a b) in
                                                                                                                                          (rewrite diff_property8 a b (l ** prfL) in
                                                                                                                                          ((plus k b) **
                                                                                                                                          (Sn_eq_Sm_implies_n_eq_m bound (plus (plus k b) (S a))
                                                                                                                                          (rewrite (associativePlus k b (S a)) in
                                                                                                                                          (rewrite commutativePlus k (plus b (S a)) in
                                                                                                                                          (rewrite commutativePlus (S (plus b (S a))) k in
                                                                                                                                          (rewrite commutativePlus (S b) (S a) in prfK))))))))
                                                                                      in (g ** (div_property10 (S b) (S a) g divGB
                                                                                               (rewrite diff_property10 b a in divGDif) ,
                                                                                               divGB, Gcd_helper a b g
                                                                                               (rewrite diff_property10 b a in cond)))


                                                         Lst ((l ** prfL), prfNEq) => let (g ** (divGA, divGDif, cond)) =
                                                                                      totalGcd (S a) (difference b a) LeftIsNotZero bound (rewrite commutativePlus a (difference b a) in
                                                                                                                                          (rewrite diff_property8 b a (l ** prfL) in
                                                                                                                                          ((plus k a) ** (Sn_eq_Sm_implies_n_eq_m bound (plus (plus k a) (S b))
                                                                                                                                          (rewrite (associativePlus k a (S b)) in
                                                                                                                                          (rewrite commutativePlus k (plus a (S b)) in
                                                                                                                                          (rewrite commutativePlus (S (plus a (S b))) k in prfK)))))))
                                                                                      in (g ** (divGA, div_property10 (S a) (S b) g divGA
                                                                                               (rewrite diff_property10 a b in divGDif)
                                                                                              , Gcd_helper2 a b g cond))
