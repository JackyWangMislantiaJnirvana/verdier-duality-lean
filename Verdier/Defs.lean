import Mathlib

open CategoryTheory

universe v v' u w

/-!
Base space:
locally compact space of finite cohomological dim
-/
variable (X : TopCat.{u})

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

-- TODO: How should I properly handle the `R`?
instance (base : TopCat) : Preadditive (Sh R base) := instPreadditiveSheaf

abbrev C (base : TopCat.{u}) := CochainComplex (Sh.{v} R base) ℤ

instance (base : TopCat) : Abelian (C R base) := sorry
instance (base : TopCat) : HasDerivedCategory (C R base) := sorry

/-!
Pass to derived category
of complexes of sheaves,
becoming triangulated (optional)
D⁺(X)
-/

-- TODO: Stuck with whether or not should I
-- wrap Sh/C/D in `Category`.
abbrev D (base : TopCat.{u}) := DerivedCategory.{v'} (C R base)

/-!
Continuous map f : X → Y : TopCat
induces direct image f_* : Sh(X) ⥤ Sh(Y),
induces functor on cochain complexes f_* : C⁺(X) ⥤ C⁺(Y),
induces right derived functor R f_* : D⁺(X) ⥤ D⁺(Y)

This sums up to the "m aking derivation" map
R(-) : (Sh(X) ⥤ Sh(Y )) → (D⁺(X) → D⁺(Y))
-/


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
