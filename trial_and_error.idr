module division_algo


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
import properties_of_Positive_Nat
import properties_of_divisibility
import substractNat

||| Division algorithm
public export

division_algo : (a : Nat) -> (b : Positive_Nat) -> (q : Nat ** (r : Nat ** ((plus (mult (toNatural b) q) r = a, 
                                                                geq (toNatural b) r, neq (toNatural b) r))))
division_algo a (Z ** prf) = absurd prf

division_algo Z ((S b) ** prf) = (Z ** (Z ** ((rewrite commutativeMult b Z in Refl),
                                             ((S b) ** (rewrite commutativePlus b Z in Refl)), Z_is_not_Sn b)))

division_algo (S a) ((S b) ** prf) = case (decGeq (S a) (S b)) of
                                         Lt prfL => (Z ** ((S a) ** ((rewrite commutativeMult b Z in Refl), fst prfL, (snd prfL) . symmetry)))
                                         Geq prfG =>let (c ** prfA) = (substractNat (S a) (S b) prfG)
                                                        (q1 ** (r ** (prf1, prf2, prf3))) = division_algo c ((S b) ** prf)
                                                        q = (S q1)
                                                    in (q ** (r ** ((rewrite commutativeMult b (S q1) in 
                                                                    (rewrite commutativeMult q1 b in 
                                                                    (rewrite symmetry (associativePlus q1 b (mult b q1)) in 
                                                                    (rewrite commutativePlus q1 b in 
                                                                    (rewrite associativePlus b q1 (mult b q1) in 
                                                                    (rewrite associativePlus b (plus q1 (mult b q1)) r in ?rhs)))))), prf2, prf3))) 
                                                                    -- (rewrite (symmetry prfA) ?rhs))))))), prf2, prf3)))
