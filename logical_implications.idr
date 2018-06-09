module logical_implications

import coProductType

public export

contrapositive : (prop1 -> prop2) -> (prop2 -> Void) -> (prop1 -> Void)
contrapositive prf1 prf2 prf3 = prf2 (prf1 prf3)

public export

prop_does_not_imply_not_prop : prop -> (prop -> Void) -> Void
prop_does_not_imply_not_prop prf1 prf2 = prf2 prf1

public export

prop_implies_not_not_prop : prop -> (prop -> Void) -> Void
prop_implies_not_not_prop prf1 prf2 = prf2 prf1

--not_not_prop_implies_prop : ((prop -> Void) -> Void) -> Void 
