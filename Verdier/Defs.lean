import Mathlib

open CategoryTheory

set_option pp.universes true
universe v v' u w

/-!
Base space:
locally compact space of finite cohomological dim
-/
variable (X : TopCat.{u}) [LocallyCompactSpace.{u} X] [T2Space.{u} X]
variable (Y : TopCat.{u}) [LocallyCompactSpace.{u} Y] [T2Space.{u} Y]

/-!
Base ring:
notherian, commutative and of finite cohomological dim
-/
variable (R : Type w) [CommRing.{w} R] [IsNoetherianRing.{w} R]

/-!
Sheaves considered:
sheaves of modules over R,
forming abelian category
Sh(X)
-/

abbrev Sh (base : TopCat.{u}) : Type (max u (v + 1) w)
  := TopCat.Sheaf.{u, v, (max w (v + 1))} (ModuleCat.{v, w} R) base

/-!
Pass to complexes of sheaves,
bounded from below,
still an abelian category
C⁺(X)
-/

instance (base : TopCat) : Preadditive (Sh R base) := instPreadditiveSheaf
instance (base : TopCat) : Abelian (Sh R base) := sorry
instance (base : TopCat) : HasDerivedCategory (Sh R base) := sorry

abbrev C (base : TopCat.{u}) : Type (max u (v + 1) w)
  := CochainComplex (Sh.{v} R base) ℤ

instance (base : TopCat) : Abelian (C R base) := sorry
instance (base : TopCat) : HasDerivedCategory (C R base) := sorry

/-!
Pass to derived category
of complexes of sheaves,
becoming triangulated (optional)
D⁺(X)
-/

abbrev D (base : TopCat.{u}) : Type (max u (v + 1) w)
  := DerivedCategory.{v'} (C.{v} R base)

/-!
Continuous map f : X → Y : TopCat
induces direct image with proper support f_! : Sh(X) ⥤ Sh(Y),
induces functor on cochain complexes f_! : C⁺(X) ⥤ C⁺(Y),
induces right derived functor R f_! : D⁺(X) ⥤ D⁺(Y)

This sums up to the "m aking derivation" map
R(-) : (Sh(X) ⥤ Sh(Y)) → (D⁺(X) ⥤ D⁺(Y))
-/

def direct_image (f : X → Y) (p_cont : Continuous f) :
  Sh.{v, u} R X ⥤ Sh.{v, u} R Y where
    obj F := {
      val := {
        -- obj := fun U => F.val.obj ((TopologicalSpace.Opens.map f).map U)
        obj :=
          -- fun U =>
            -- let presh := F.val
            -- let shmap : (TopologicalSpace.Opens X)ᵒᵖ → ModuleCat R := presh.obj
            -- let preimg := TopologicalSpace.Opens.map f
            -- let V := preimg.obj U
            -- presh.obj V
            sorry
        map ι := sorry
        map_comp := sorry
        map_id := sorry
      }
      cond := sorry
    }
    map g := sorry
    map_comp := sorry
    map_id := sorry

def direct_image_proper_support (f : X → Y) (p_cont : Continuous f) :
  Sh.{v, u} R X ⥤ Sh.{v, u} R Y where
    obj F := {
      val := {
        obj := sorry
        map := sorry
      }
      cond := sorry
    }
    map σ := sorry


instance (f : X → Y) (p_cont : Continuous f) :
  Functor.Additive (direct_image_proper_support.{v, u} X Y R f p_cont) := sorry

def functor_to_chain_map (F : Sh R X ⥤ Sh R Y) :
  C.{v, u, w} R X ⥤ C.{v, u, w} R Y where
    obj A := sorry
    map g := sorry

def derived (F : C.{v, u, w} R X ⥤ C.{v, u, w} R Y) :
  D.{v, v', u, w} R X ⥤ D.{v, v', u, w} R Y := sorry

abbrev R! (f : X → Y) (p_cont : Continuous f) :
  D.{v, v', u, w} R X ⥤ D.{v, v', u, w} R Y :=
    derived.{v, v', u, w} X Y R (
      functor_to_chain_map.{v, u, w, v, v} X Y R (
        direct_image_proper_support.{v, u} X Y R f p_cont))

abbrev Rstar (f : X → Y) (p_cont : Continuous f) :
  D.{v, v', u, w} R X ⥤ D.{v, v', u, w} R Y :=
    derived.{v, v', u, w} X Y R (
      functor_to_chain_map.{v, u} X Y R (
        direct_image.{v, u} X Y R f p_cont))

-- Maybe a better way to define R!
-- noncomputable def CategoryTheory.Functor.mapDerivedCategory
--   {C₁ : Type u₁} [Category.{v₁, u₁} C₁] [Abelian C₁] [HasDerivedCategory C₁]
--   {C₂ : Type u₂} [Category.{v₂, u₂} C₂] [Abelian C₂] [HasDerivedCategory C₂]
--   (F : Functor C₁ C₂) [F.Additive]
--   [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F] :
--   Functor (DerivedCategory C₁) (DerivedCategory C₂)
abbrev R!' (f : X → Y) (p_cont : Continuous f) :=
  -- Functor.mapDerivedCategory (direct_image_proper_support.{v, u} X Y R f p_cont)
  Functor.mapDerivedCategory (direct_image_proper_support.{v, u} X Y R f p_cont)


/-!
Define sheaf internal hom complex
and then define its right derived functor
-/

def sheaf_hom (F G : Sh.{v, u, w} R X) : Sh.{v, u, w} R X := sorry

def sheaf_hom_complex (F G : C.{v, u, w} R X) : C.{v, u, w} R X := sorry

def derived_sheaf_hom_complex (F G : D.{v, v', u, w} R X) : D.{v, v', u, w} R X := sorry

/-
Statement of the main theorem
-/

variable
  (f : X → Y)(p_cont : Continuous f)
  (F : D.{v, v', u, w} R X) (G : D.{v, v', u, w} R Y)

theorem local_verdier_duality :
  ∃ g : D.{v, v', u, w} R Y ⥤ D.{v, v', u, w} R X,
  Iso
    (derived_sheaf_hom_complex.{v, v', u, w} Y R ((R!.{v, v', u, w} X Y R f p_cont).obj F) G)
    ((Rstar.{v, v', u, w} X Y R f p_cont).obj (derived_sheaf_hom_complex.{v, v', u, w} X R F (g.obj G)))
  := sorry
