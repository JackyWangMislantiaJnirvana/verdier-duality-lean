import Mathlib

open CategoryTheory

universe v v' u w

attribute [pp_with_univ] TopCat ModuleCat

variable (X : TopCat.{u})
variable (R : Type w) [CommRing R] [IsNoetherianRing R]

/--
In `Sh.{v}`, `v` is the universe level for the category of modules.
-/
@[pp_with_univ]
abbrev Sh (base : TopCat.{u}) : Type (max u (v + 1) w) :=
  TopCat.Sheaf (ModuleCat.{v} R) base
-- Mathlib's `TopCat.Sheaf` is a `def` instead of an `abbrev`,
-- so we need to restate this instance:
instance (base : TopCat) : Preadditive (Sh R base) := instPreadditiveSheaf

abbrev C (base : TopCat.{u}) : Type (max u (v + 1) w):=
  CochainComplex (Sh.{v} R base) ℤ

instance (base : TopCat) : Abelian (C R base) := sorry
instance (base : TopCat) : HasDerivedCategory (C R base) := sorry

/--
In `D.{v,v'}`, `v` is the universe level for the category of modules,
and `v'` is the universe level for the morphisms in the localization category.
-/
abbrev D (base : TopCat.{u}) : Type (max u (v + 1) w) :=
  DerivedCategory.{v'} (C.{v} R base)

inductive BoolExpr where
  | var (name : String)
  | val (b : Bool)
  | or (p q : BoolExpr)
  | not (p : BoolExpr)

def simplify : BoolExpr → BoolExpr
  | BoolExpr.or p q => mkOr (simplify p) (simplify q)
  | BoolExpr.not p => mkNot (simplify p)
  | e => e
where
  mkOr : BoolExpr → BoolExpr → BoolExpr
  | p, BoolExpr.val true => BoolExpr.val true
  | p, BoolExpr.val false => p
  | BoolExpr.val true, p => BoolExpr.val true
  | p, q => BoolExpr.or p q
  mkNot : BoolExpr → BoolExpr
  | BoolExpr.val b => BoolExpr.val (not b)
  | p => BoolExpr.not p

#eval simplify (BoolExpr.or (BoolExpr.or (BoolExpr.val true) (BoolExpr.val true)) (BoolExpr.not (BoolExpr.val false)))

def f (Y : TopCat): TopCat := TopCat.of ℝ

instance (Y : TopCat) : T2Space (f Y) := sorry

def g (Y : TopCat) [T2Space Y] : TopCat := Y

abbrev fg := g (f (TopCat.of ℝ))

section SheafExperiment
-- Abelian sheaf
abbrev AbSheaf (base  : TopCat) := TopCat.Sheaf Ab base

instance : Preadditive (AbSheaf X) := instPreadditiveSheaf

def K (X : TopCat) := ChainComplex (AbSheaf X) ℤ

variable (F : AbSheaf X)

example : TopCat.Presheaf.IsSheaf F.presheaf := F.cond

end SheafExperiment

example (R : Type w) [Ring.{w} R] (M N : ModuleCat.{v, w} R) : (M ≅ N) → M ≅ N := by {
  intro hmn
  exact hmn
}
