module commutativePlus

import associativePlus

public export

plus_n_Z_is_n : (n : Nat) -> (n + 0) = (0 + n)
plus_n_Z_is_n Z = Refl
plus_n_Z_is_n (S k) = rewrite (plus_n_Z_is_n k) in Refl

public export

plus_n_1_is_Sn : (n : Nat) -> (n + 1) = (S n)
plus_n_1_is_Sn Z = Refl
plus_n_1_is_Sn (S k) = rewrite (plus_n_1_is_Sn k) in Refl

public export

Sn_is_plus_n_1 : (n : Nat) -> (S n) = (n + 1)
Sn_is_plus_n_1 n = rewrite (plus_n_1_is_Sn n) in Refl

public export

commutativePlus : (a : Nat) -> (b : Nat) -> (a + b) = (b + a)
commutativePlus Z n = rewrite (plus_n_Z_is_n n) in Refl
commutativePlus (S k) n = (rewrite (Sn_is_plus_n_1 k) in 
                          (rewrite (commutativePlus k n) in 
                          (rewrite (oppAssociativePlus n k 1) in
                          (rewrite (Sn_is_plus_n_1 (n+k)) in Refl)))) 

