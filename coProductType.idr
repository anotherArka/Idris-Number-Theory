module coProductType

public export

coProduct : (a : Type) -> (b : Type) -> Type
coProduct a b = (p : Bool ** (AorB a b p)) where
                                            AorB : Type -> Type -> Bool -> Type
                                            AorB a b True = a
                                            AorB a b False = b
