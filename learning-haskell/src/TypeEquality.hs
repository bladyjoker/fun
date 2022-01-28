{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeOperators #-}

module TypeEquality where

import Data.Kind (Type)

type (:~:) :: Type -> Type -> Type
data a :~: b where
    Refl :: a :~: a

comm :: forall a b. a :~: b -> b :~: a
comm Refl = Refl

cong :: forall a b. (a -> b) -> a :~: a -> b :~: b
cong _ _ = Refl

trans :: forall a b c. a :~: b -> b :~: c -> a :~: c
trans (Refl :: a :~: b) (Refl :: b :~: c) = Refl :: a :~: c
