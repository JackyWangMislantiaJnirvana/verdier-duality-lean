import Mathlib

open CategoryTheory

universe v v' u w

/-!
Base space:
locally compact space of finite cohomological dim
-/
variable (X : TopCat.{u}) [LocallyCompactSpace X] [T2Space X]
variable (Y : TopCat.{u}) [LocallyCompactSpace Y] [T2Space Y]

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
instance (base : TopCat) : HasDerivedCategory (Sh R base) := sorry

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

def direct_image_proper_support (f : X → Y) (p_cont : Continuous f) :
  Sh.{v, u} R X ⥤ Sh.{v, u} R Y where
    obj ℱ := {
      val := {
        obj := sorry
        map := sorry
      }
      cond := sorry
    }
    map g := sorry

def direct_image (f : X → Y) (p_cont : Continuous f) :
  Sh.{v, u} R X ⥤ Sh.{v, u} R Y where
    obj ℱ := {
      val := {
        obj := sorry
        map := sorry
      }
      cond := sorry
    }
    map g := sorry

instance (f : X → Y) (p_cont : Continuous f) :
  -- Functor.Additive (direct_image_proper_support.{v, u} X Y R f p_cont) := sorry
  Functor.Additive (direct_image_proper_support.{v, u} X Y R f p_cont) := sorry

def functor_to_chain_map (F : Sh R X ⥤ Sh R Y) :
  C.{v, u} R X ⥤ C.{v, u} R Y where
    obj A := sorry
    map g := sorry

def derived (F : C R X ⥤ C R Y) : D.{v', u} R X ⥤ D.{v', u} R Y := sorry

#check derived X Y R (functor_to_chain_map X Y R sorry)

-- why does this universe assignment work???
-- how is the order of XXX.{u, v} matched to the variables in the function definition?
set_option pp.universes true
abbrev R! (f : X → Y) (p_cont : Continuous f): D.{v', u} R X ⥤ D.{v', u} R Y :=
  derived.{v', u} X Y R (
    functor_to_chain_map.{v, u} X Y R (
      direct_image_proper_support.{v, u} X Y R f p_cont))

abbrev Rstar (f : X → Y) (p_cont : Continuous f): D.{v', u} R X ⥤ D.{v', u} R Y :=
  derived.{v', u} X Y R (
    functor_to_chain_map.{v, u} X Y R (
      direct_image.{v, u} X Y R f p_cont))

-- Maybe a better way to define R!
-- noncomputable def CategoryTheory.Functor.mapDerivedCategory
--   {C₁ : Type u₁} [Category.{v₁, u₁} C₁] [Abelian C₁] [HasDerivedCategory C₁]
--   {C₂ : Type u₂} [Category.{v₂, u₂} C₂] [Abelian C₂] [HasDerivedCategory C₂]
--   (F : Functor C₁ C₂) [F.Additive]
--   [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F] :
--   Functor (DerivedCategory C₁) (DerivedCategory C₂)
-- set_option trace.Meta.synthInstance true
abbrev R!' (f : X → Y) (p_cont : Continuous f) :=
  -- Functor.mapDerivedCategory (direct_image_proper_support.{v, u} X Y R f p_cont)
  Functor.mapDerivedCategory (direct_image_proper_support.{v, u} X Y R f p_cont)


/-!
Define/search for HomSheafComplex
and then define its right derived functor
-/

def sheaf_hom (F G : Sh R X) : Sh R X := sorry

def sheaf_hom_complex (F G : C R X) : C R X := sorry

def derived_sheaf_hom_complex (F G : D R X) : D R X := sorry

/-
Statement of the main theorem
-/
#check D.{v, v', u, w} R X
variable (f : X → Y) (p_cont : Continuous f) (F : D R X) (G : D R Y)
theorem local_verdier_duality :
  ∃ g : D R Y ⥤ D R X,
  Iso
    (derived_sheaf_hom_complex Y R ((R! X Y R f p_cont).obj F) G)
    ((Rstar X Y R f p_cont).obj (derived_sheaf_hom_complex X R F (g.obj G)))
  := sorry

section SheafExperiment
-- Abelian sheaf
abbrev AbSheaf (base  : TopCat) := TopCat.Sheaf Ab base

instance : Preadditive (AbSheaf X) := instPreadditiveSheaf

def K (X : TopCat) := ChainComplex (AbSheaf X) ℤ

variable (F : AbSheaf X)

example : TopCat.Presheaf.IsSheaf F.presheaf := F.cond

end SheafExperiment
