namespace Ex

universe u v

class Inhabited (a : Type u) where
  default : a

opaque default [Inhabited a] : a :=
  Inhabited.default

instance [Inhabited a] [Inhabited b] : Inhabited (a × b) where
  default := (default, default)

--  default instances for other types, such as List and Sum types
instance [Inhabited a] : Inhabited (List a) where
  default := []

instance [Inhabited a] : Inhabited (Sum a b) where
  default := Sum.inl default

instance [Inhabited b] : Inhabited (Sum a b) where
  default := Sum.inr default

instance : Inhabited (Option a) where
  default := none

#eval (default : Option Bool)

end Ex
