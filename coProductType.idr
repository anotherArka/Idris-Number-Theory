module coProductType

%default total

public export

coProduct : (A : Type) -> (B : Type) -> Type
coProduct A B = (p : Bool ** (AorB A B p)) where 
                                            AorB : Type -> Type -> Bool -> Type
                                            AorB A B True = A
                                            AorB A B False = B
