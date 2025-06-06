import Mathlib

open CategoryTheory

universe v v' u w

/-!
Base space:
locally compact space of finite cohomological dim
-/
variable (X : TopCat.{u})
variable (Y : TopCat.{u})

/-!
Base ring:
notherian, commutative and of finite cohomological dim
-/
variable (R : Type w) [CommRing R] [IsNoetherianRing R]

/-!
Sheaves considered:
sheaves of modules over R,
forming abelian category
Sh(X)
-/

-- TODO: Is this the right way to define sheaf of R-modules?
abbrev Sh (base : TopCat.{u}) := TopCat.Sheaf (ModuleCat.{v} R) base

/-!
Pass to complexes of sheaves,
bounded from below,
still an abelian category
C⁺(X)
-/

instance (base : TopCat) : Preadditive (Sh R base) := instPreadditiveSheaf
instance (base : TopCat) : Abelian (Sh R base) := sorry

abbrev C (base : TopCat.{u}) := CochainComplex (Sh.{v} R base) ℤ

instance (base : TopCat) : Abelian (C R base) := sorry
instance (base : TopCat) : HasDerivedCategory (C R base) := sorry

/-!
Pass to derived category
of complexes of sheaves,
becoming triangulated (optional)
D⁺(X)
-/

abbrev D (base : TopCat.{u}) := DerivedCategory.{v'} (C R base)

/-!
Continuous map f : X → Y : TopCat
induces direct image with proper support f_! : Sh(X) ⥤ Sh(Y),
induces functor on cochain complexes f_! : C⁺(X) ⥤ C⁺(Y),
induces right derived functor R f_! : D⁺(X) ⥤ D⁺(Y)

This sums up to the "m aking derivation" map
R(-) : (Sh(X) ⥤ Sh(Y)) → (D⁺(X) ⥤ D⁺(Y))
-/

def direct_image_proper_support (f : X → Y) (p_cont : Continuous f) : Sh.{v, u} R X ⥤ Sh.{v, u} R Y := sorry

-- We need a function that makes f_! a functor on chain complexes.
-- : whaaat type??? Think it through
def functor_to_chain_map (F : Sh R X ⥤ Sh R Y) : C.{v, u} R X ⥤ C.{v, u} R Y := sorry

def derived (F : C R X ⥤ C R Y) : D.{v', u} R X ⥤ D.{v', u} R Y := sorry

#check derived X Y R (functor_to_chain_map X Y R sorry)

example : derived X Y R sorry = sorry := sorry
example : derived X Y R (functor_to_chain_map X Y R sorry) = sorry := sorry
example : derived X Y R (functor_to_chain_map X Y R (direct_image_proper_support X Y R sorry sorry)) = sorry := sorry

-- why does this work???
-- how is the order of XXX.{u, v} matched to the variables in the function definition?
abbrev R! (f : X -> Y) (p_cont : Continuous f) := derived.{v', u} X Y R (functor_to_chain_map.{v, u} X Y R (direct_image_proper_support.{v, u} X Y R f p_cont))

/-!
Define/search for HomSheafComplex
and then define its right derived functor
-/

/-
Statement of the main theorem
-/



section SheafExperiment
-- Abelian sheaf
abbrev AbSheaf (base  : TopCat) := TopCat.Sheaf Ab base

instance : Preadditive (AbSheaf X) := instPreadditiveSheaf

def K (X : TopCat) := ChainComplex (AbSheaf X) ℤ

variable (F : AbSheaf X)

example : TopCat.Presheaf.IsSheaf F.presheaf := F.cond

end SheafExperiment
