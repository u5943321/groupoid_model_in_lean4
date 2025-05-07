import GroupoidModel.Groupoids.Sigma
import GroupoidModel.Russell_PER_MS.NaturalModel

universe v u v₁ u₁ v₂ u₂

noncomputable section
-- NOTE temporary section for stuff to be moved elsewhere
section ForOther
namespace CategoryTheory

-- NOTE is there a better way of doing this?
-- NOTE associativity of functors is definitional, so we can always use `rfl`
lemma func_middle_assoc {A B C D E: Type*} [Category A][Category B][Category C][Category D][Category E]
 (f1: A ⥤ B) (f2: B ⥤ C) (f3: C ⥤ D)(f4: D⥤ E):
 f1 ⋙ f2 ⋙ f3 ⋙ f4 = f1 ⋙ (f2 ⋙ f3) ⋙ f4 := rfl

lemma func_split_assoc {A B C D E: Type*} [Category A][Category B][Category C][Category D][Category E]
 (f1: A ⥤ B) (f2: B ⥤ C) (f3: C ⥤ D)(f4: D⥤ E):
 f1 ⋙ (f2 ⋙ f3) ⋙ f4 = (f1 ⋙ f2) ⋙ (f3 ⋙ f4) := rfl

lemma whiskeringLeft_Right_comm {A B C D: Type*} [Category A] [Category B]
    [Category C] [Category D] (F: A⥤ B)  (H: C ⥤ D):
    (whiskeringRight _ _ _).obj H ⋙ (whiskeringLeft  _ _ _ ).obj F =
    (whiskeringLeft _ _ _).obj F ⋙ (whiskeringRight _ _ _).obj H := by
  fapply CategoryTheory.Functor.ext
  · simp only [Functor.comp_obj, whiskeringRight_obj_obj,
      whiskeringLeft_obj_obj, Functor.assoc, implies_true]
  · intro F1 F2 η
    simp only [Functor.comp_obj, whiskeringRight_obj_obj, whiskeringLeft_obj_obj,
      Functor.comp_map, whiskeringRight_obj_map, whiskeringLeft_obj_map,
      eqToHom_refl, Category.comp_id, Category.id_comp,whiskerRight_left]

section
variable {A : Type u} [Category.{v} A] {B: Type u₁} [Groupoid.{v₁} B]
    {F G : A ⥤ B} (h : NatTrans F G)

-- NOTE not sure if this is the best way to organize this
@[simps] def NatTrans.iso : F ≅ G where
  hom := h
  inv := {app a := Groupoid.inv (h.app a)}

def NatTrans.inv : G ⟶ F := h.iso.inv

@[simp] lemma NatTrans.inv_vcomp : h.inv.vcomp h = NatTrans.id G := by
  ext a
  simp [NatTrans.inv]

@[simp] lemma NatTrans.vcomp_inv : h.vcomp h.inv = NatTrans.id F := by
  ext a
  simp [NatTrans.inv]

end
end CategoryTheory

end ForOther

-- NOTE content for this doc starts here
namespace GroupoidModel

open CategoryTheory NaturalModelBase Opposite Grothendieck.Groupoidal Groupoid PGrpd


/-
   Uncomment this to see the the flow of organizing Conjugation into the Conjugating functor.
   def Conjugating0 {Γ : Grpd.{v,u}} (A B : Γ ⥤ Grpd.{u₁,u₁})
    {x y: Γ } (f: x ⟶ y) : (A.obj x⥤ B.obj x) ⥤ (A.obj y⥤ B.obj y) :=
     let wr : B.obj x ⥤ B.obj y := B.map f
     let wl : A.obj y ⥤ A.obj x := A.map (Groupoid.inv f)
     let f1_ty : (A.obj y ⥤ A.obj x) ⥤ ((A.obj x) ⥤ (B.obj x)) ⥤ (A.obj y) ⥤  (B.obj x) :=
       whiskeringLeft (A.obj y) (A.obj x) (B.obj x)
     let f1 : ((A.obj x) ⥤ (B.obj x)) ⥤ (A.obj y) ⥤  (B.obj x) :=
       (whiskeringLeft (A.obj y) (A.obj x) (B.obj x)).obj (A.map (Groupoid.inv f))
     let f2_ty :  ((B.obj x) ⥤ (B.obj y)) ⥤ (A.obj y ⥤ B.obj x) ⥤ (A.obj y) ⥤  (B.obj y) :=
       whiskeringRight (A.obj y) (B.obj x) (B.obj y)
     let f2 : (A.obj y ⥤ B.obj x) ⥤ (A.obj y) ⥤  (B.obj y) :=
       (whiskeringRight (A.obj y) (B.obj x) (B.obj y)).obj (B.map f)
     let f3 := f1 ⋙ f2
     f3
-/

-- NOTE Use {Γ : Type u} [Groupoid.{v} Γ] instead of (Γ : Grpd)
/--
The functor that, on objects `G : A.obj x ⥤ B.obj x` acts by
creating the map on the right
         A f
  A x --------> A y
   |             .
   |             |
   |             .
G  |             | conjugating A B f G
   |             .
   V             V
  B x --------> B y
         B f
-/
def conjugating {Γ : Type u} [Groupoid.{v} Γ] (A B : Γ ⥤ Cat)
    {x y : Γ} (f : x ⟶ y) : (A.obj x ⥤ B.obj x) ⥤ (A.obj y ⥤ B.obj y) :=
  (whiskeringLeft (A.obj y) (A.obj x) (B.obj x)).obj (A.map (Groupoid.inv f)) ⋙
  (whiskeringRight (A.obj y) (B.obj x) (B.obj y)).obj (B.map f)

def conjugating_id {Γ : Type u} [Groupoid.{v} Γ] (A B : Γ ⥤ Cat)
    (x : Γ ) : conjugating A B (𝟙 x) = Functor.id _ := by
     simp only [conjugating, inv_eq_inv, IsIso.inv_id, CategoryTheory.Functor.map_id]
     have e: (𝟙 (B.obj x)) = (𝟭 (B.obj x)) := rfl
     simp only [e,CategoryTheory.whiskeringRight_obj_id,Functor.comp_id]
     have e': (𝟙 (A.obj x)) = (𝟭 (A.obj x)) := rfl
     simp only[e',CategoryTheory.whiskeringLeft_obj_id]

def conjugating_comp {Γ : Grpd.{v,u}} (A B : Γ ⥤ Cat)
    (x y z : Γ ) (f:x⟶ y) (g:y⟶ z) :
    conjugating A B (f ≫ g) = conjugating A B f ⋙ conjugating A B g := by
    simp only [conjugating, inv_eq_inv, IsIso.inv_comp, Functor.map_comp, Functor.map_inv]
    have e : (whiskeringRight (A.obj y) (B.obj x) (B.obj y)).obj (B.map f) ⋙
    (whiskeringLeft (A.obj z) (A.obj y) (B.obj y)).obj (CategoryTheory.inv (A.map g)) =
    (whiskeringLeft _ _ _).obj (CategoryTheory.inv (A.map g)) ⋙
    (whiskeringRight _ _ _).obj (B.map f) := by
      apply whiskeringLeft_Right_comm
    rw [Functor.assoc,func_middle_assoc,e,
      func_split_assoc,whiskeringRight_obj_comp,← whiskeringLeft_obj_comp]
    rfl

instance functorToGroupoid_Groupoid {A : Type u} [Category.{v,u} A] {B : Type u₁} [Groupoid.{v₁} B] :
    Groupoid (A ⥤ B) where
  Hom := NatTrans
  id := NatTrans.id
  comp {X Y Z} nt1 nt2 := nt1 ≫ nt2
  inv {X Y} nt:= nt.inv
  inv_comp := NatTrans.inv_vcomp
  comp_inv := NatTrans.vcomp_inv

-- NOTE commented out until it is needed
-- def Funcgrpd {A : Type u} [Category.{v,u} A] {B : Type u₁} [Groupoid.{v₁} B]  : Grpd :=
--  Grpd.of (A ⥤ B)

-- NOTE to follow mathlib convention can use camelCase for definitions, and capitalised first letter when that definition is a Prop or Type
def IsSec {A B : Type*} [Category A] [Category B] (F : B ⥤ A) (s : A ⥤ B) :=
 s ⋙ F = Functor.id A

abbrev Section {A B : Type*} [Category A] [Category B] (F : B ⥤ A) :=
  FullSubcategory (IsSec F)

instance Section.category {A B : Type*} [Category A] [Category B] (F : B ⥤ A) :
  Category (Section F) := FullSubcategory.category (IsSec F)

abbrev Section.inc {A B:Type*} [Category A] [Category B] (F:B ⥤ A) :
  Section F ⥤ (A ⥤ B) := CategoryTheory.fullSubcategoryInclusion (IsSec F)

@[simp] lemma Section.inc_obj {A B:Type*} [Category A] [Category B] (F:B ⥤ A) (s: Section F):
  (Section.inc F).obj s = s.obj := rfl

@[simp] lemma Section.inc_map {A B:Type*} [Category A] [Category B] (F:B ⥤ A)
  (s1 s2: Section F) (η : s1 ⟶ s2):
  (Section.inc F).map η = η := rfl

-- TODO refactor using `CategoryTheory.Functor.FullyFaithful.map_injective`
lemma Section.inc_eq {A B:Type*} [Category A] [Category B] (F:B ⥤ A)
  (s1 s2: Section F) (η₁ η₂ : s1 ⟶ s2):
  (Section.inc F).map η₁ = (Section.inc F).map η₂ → η₁ = η₂ := by
   intro a
   simp only [fullSubcategoryInclusion.obj, fullSubcategoryInclusion.map] at a
   assumption

instance Section.groupoid {A:Type u} [Category.{v} A] {B : Type u₁}
    [Groupoid.{v₁} B] (F : B ⥤ A) : Groupoid (Section F) :=
  InducedCategory.groupoid (A ⥤ B) (fun (f: Section F) ↦ f.obj)

--Q:Should this be def or abbrev? JH: abbrev I think?
abbrev Section.grpd {A:Type u} [Category.{v ,u} A] {B : Type u₁}
    [Groupoid.{v₁} B] (F : B ⥤ A) : Grpd :=
  Grpd.of (Section F)

open FunctorOperation

-- TODO camelCase
def Fiber_Grpd {Γ : Grpd.{v₂,u₂}} (A : Γ ⥤ Grpd.{v₁,u₁})
    (B : ∫(A) ⥤ Grpd.{v₁,u₁}) (x : Γ) : Grpd :=
  Section.grpd ((fstAux B).app x)

-- TODO lower case (and so on)
lemma Fiber_Grpd.α {Γ : Grpd.{v₂,u₂}} (A : Γ ⥤ Grpd.{v₁,u₁})
    (B : ∫(A) ⥤ Grpd.{v₁,u₁}) (x : Γ) :
    (Fiber_Grpd A B x).α = Section ((fstAux B).app x) := rfl

def conjugate {D: Type*} (C: Grpd.{v₁,u₁}) [Category D] (A B : C ⥤ D)
    {x y: C} (f: x ⟶ y) (s: A.obj x ⟶  B.obj x) :
     A.obj y ⟶  B.obj y := A.map (Groupoid.inv f) ≫ s ≫ B.map f


lemma conjugate_id {D: Type*} (C: Grpd.{v₁,u₁}) [Category D] (A B : C ⥤ D)
    (x : C) (s: A.obj x ⟶  B.obj x)  : conjugate C A B (𝟙 x) s = s:= by
     simp only [conjugate, inv_eq_inv, IsIso.inv_id, CategoryTheory.Functor.map_id,
       Category.comp_id, Category.id_comp]

lemma conjugate_comp {D: Type*} (C: Grpd.{v₁,u₁}) [Category D] (A B : C ⥤ D)
    {x y z: C} (f: x ⟶ y) (g: y ⟶ z) (s: A.obj x ⟶  B.obj x):
     conjugate C A B (f ≫ g) s = conjugate C A B g (conjugate C A B f s) := by
      simp only [conjugate, inv_eq_inv, IsIso.inv_comp, Functor.map_comp, Functor.map_inv,
        Category.assoc]

/-only need naturality of η-/
/-therefore, the fact that the conjugation sends section to section is by naturality of
 the projection map from sigma, and the fact that some functor has sections as its codomain-/
lemma conjugate_PreserveSection {D: Type*} (C: Grpd.{v₁,u₁}) [Category D] (A B : C ⥤ D)
    (η: NatTrans B A)
    {x y: C} (f: x ⟶ y) (s: A.obj x ⟶  B.obj x):
    s ≫ η.app x = 𝟙 (A.obj x) → (conjugate C A B f s) ≫ η.app y = 𝟙 (A.obj y) :=
     by
     intro ieq
     simp only [conjugate, inv_eq_inv, Functor.map_inv, ← Category.assoc, NatTrans.naturality,
      IsIso.inv_comp_eq, Category.comp_id]
     simp only [Category.assoc, NatTrans.naturality, IsIso.inv_comp_eq, Category.comp_id]
     simp only [← Category.assoc,ieq,Category.id_comp]

def conjugate_Fiber {Γ : Grpd.{v,u}} (A : Γ ⥤ Grpd.{u₁,u₁})
    (B : ∫(A) ⥤ Grpd.{u₁,u₁})
    {x y: Γ} (f: x ⟶ y)
    (s: A.obj x ⥤ (GroupoidModel.FunctorOperation.sigma A B).obj x) :
    (A.obj y ⥤ (GroupoidModel.FunctorOperation.sigma A B).obj y) :=
    conjugate Γ A (GroupoidModel.FunctorOperation.sigma A B) f s

def conjugate_FiberFunc {Γ : Grpd.{v,u}} (A : Γ ⥤ Grpd.{u₁,u₁})
    (B : ∫(A) ⥤ Grpd.{u₁,u₁})
    {x y: Γ} (f: x ⟶ y):
    (A.obj x ⥤ (GroupoidModel.FunctorOperation.sigma A B).obj x) ⥤
    (A.obj y ⥤ (GroupoidModel.FunctorOperation.sigma A B).obj y) :=
     conjugating (A ⋙ Grpd.forgetToCat)
      (GroupoidModel.FunctorOperation.sigma A B ⋙ Grpd.forgetToCat) f

lemma conjugate_FiberFunc.obj {Γ : Grpd.{v,u}} (A : Γ ⥤ Grpd.{u₁,u₁})
    (B : ∫(A) ⥤ Grpd.{u₁,u₁})
    {x y: Γ} (f: x ⟶ y):
     (conjugate_FiberFunc A B f).obj = conjugate _ A (FunctorOperation.sigma A B) f
     := rfl

lemma conjugate_FiberFunc.map {Γ : Grpd.{v,u}} (A : Γ ⥤ Grpd.{u₁,u₁})
    (B : ∫(A) ⥤ Grpd.{u₁,u₁})
    {x y: Γ} (f: x ⟶ y)
    (s1 s2: A.obj x ⥤ (GroupoidModel.FunctorOperation.sigma A B).obj x)
    (η: s1 ⟶ s2):
     (conjugate_FiberFunc A B f).map η =
     CategoryTheory.whiskerLeft (A.map (Groupoid.inv f))
     (CategoryTheory.whiskerRight η
         ((GroupoidModel.FunctorOperation.sigma A B).map f))
     := rfl

def conjugateLiftCond {Γ : Grpd.{v,u}} (A : Γ ⥤ Grpd.{u₁,u₁})
    (B : ∫(A) ⥤ Grpd.{u₁,u₁})
    {x y: Γ} (f: x ⟶ y):
    ∀ (X : Section ((fstAux B).app x)),
    IsSec ((fstAux B).app y)
    ((Section.inc ((fstAux B).app x) ⋙ conjugate_FiberFunc A B f).obj X)
    := by
      intro s
      simp only [IsSec, FunctorOperation.sigma_obj, Grpd.coe_of, Functor.comp_obj,
        fullSubcategoryInclusion.obj,conjugate_FiberFunc.obj]
      have a:= s.property
      simp only [IsSec, FunctorOperation.sigma_obj, Grpd.coe_of] at a
      have a':= conjugate_PreserveSection Γ A (FunctorOperation.sigma A B)
                (fstAux B) f _ a
      assumption


def conjugateLiftFunc {Γ : Grpd.{v,u}} (A : Γ ⥤ Grpd.{u₁,u₁})
    (B : ∫(A) ⥤ Grpd.{u₁,u₁})
    {x y: Γ} (f: x ⟶ y):
     Section ((fstAux B).app x) ⥤ Section ((fstAux B).app y) :=
     CategoryTheory.FullSubcategory.lift (IsSec ((fstAux B).app y))
            ((Section.inc ((fstAux B).app x) ⋙ conjugate_FiberFunc A B f))
     (conjugateLiftCond A B f)


lemma conjugateLiftFunc.obj {Γ : Grpd.{v,u}} (A : Γ ⥤ Grpd.{u₁,u₁})
    (B : ∫(A) ⥤ Grpd.{u₁,u₁})
    {x y: Γ} (f: x ⟶ y) (s: Section ((fstAux B).app x)):
    ((conjugateLiftFunc A B f).obj s).obj =
    (conjugate_FiberFunc A B f).obj s.obj := rfl



lemma conjugateLiftFunc.map {Γ : Grpd.{v,u}} (A : Γ ⥤ Grpd.{u₁,u₁})
    (B : ∫(A) ⥤ Grpd.{u₁,u₁})
    {x y: Γ} (f: x ⟶ y) (s1 s2: Section ((fstAux B).app x))
    (η: s1 ⟶ s2):
    (Section.inc ((fstAux B).app y)).map
     ((conjugateLiftFunc A B f).map η) =
    (conjugate_FiberFunc A B f).map η := rfl


lemma conjugateLiftFunc_Inc {Γ : Grpd.{v,u}} (A : Γ ⥤ Grpd.{u₁,u₁})
    (B : ∫(A) ⥤ Grpd.{u₁,u₁})
    {x y: Γ} (f: x ⟶ y):
    (conjugateLiftFunc A B f) ⋙ Section.inc ((fstAux B).app y)
    = ((Section.inc ((fstAux B).app x) ⋙ conjugate_FiberFunc A B f))
    := by
     simp only [FunctorOperation.sigma_obj, Grpd.coe_of, conjugateLiftFunc, Section.inc,
       FullSubcategory.lift_comp_inclusion_eq]

lemma idSection_Inc {Γ : Grpd.{v,u}} (A : Γ ⥤ Grpd.{u₁,u₁})
    (B : ∫(A) ⥤ Grpd.{u₁,u₁})
    (x : Γ) :
    𝟙 (Fiber_Grpd A B x) ⋙ Section.inc ((fstAux B).app x)
    = ((Section.inc ((fstAux B).app x) ⋙ conjugate_FiberFunc A B (𝟙 x))) :=
     by
     simp only [FunctorOperation.sigma_obj, Grpd.coe_of]
     rw[conjugate_FiberFunc,conjugating_id]
     rfl


lemma fullSubcategoryInclusion_Mono_lemma {T C:Type u}
   [Category.{v} C] [Category.{v} T]  (Z: C → Prop)
 (f g: T ⥤ FullSubcategory Z)
 (e: f ⋙ (fullSubcategoryInclusion Z) = g ⋙ (fullSubcategoryInclusion Z)) : f = g := by
  let iso:= eqToIso e
  let fgiso := CategoryTheory.Functor.fullyFaithfulCancelRight (fullSubcategoryInclusion Z) iso
  have p : ∀ (X : T), f.obj X = g.obj X := by
    intro X
    have e1: (f ⋙ fullSubcategoryInclusion Z).obj X = (g ⋙ fullSubcategoryInclusion Z).obj X
     := Functor.congr_obj e X
    simp only [Functor.comp_obj, fullSubcategoryInclusion.obj] at e1
    ext
    exact e1
  fapply CategoryTheory.Functor.ext_of_iso fgiso
  · exact p
  intro X
  simp only [Functor.fullyFaithfulCancelRight, NatIso.ofComponents_hom_app, Functor.preimageIso_hom,
    fullSubcategoryInclusion.obj, Iso.app_hom, fgiso]
  have e2: (fullSubcategoryInclusion Z).map (eqToHom (p X)) = (iso.hom.app X) := by
    simp only [fullSubcategoryInclusion, inducedFunctor_obj, inducedFunctor_map, eqToIso.hom,
      eqToHom_app, Functor.comp_obj, iso, fgiso]
    rfl
  simp only[← e2,Functor.preimage, fullSubcategoryInclusion.obj, fullSubcategoryInclusion.map,
    Classical.choose_eq, fgiso, iso]

lemma conjugateLiftFunc_id
    {Γ : Grpd.{v,u}} (A : Γ ⥤ Grpd.{u₁,u₁})
    (B : ∫(A) ⥤ Grpd.{u₁,u₁})
    (x: Γ) : conjugateLiftFunc A B (𝟙 x) = 𝟙 (Fiber_Grpd A B x) :=
     by
      fapply fullSubcategoryInclusion_Mono_lemma
      simp only [FunctorOperation.sigma_obj, Grpd.coe_of, conjugateLiftFunc_Inc A B (𝟙 x),
        idSection_Inc A B x]

lemma conjugateLiftFunc_comp
    {Γ : Grpd.{v,u}} (A : Γ ⥤ Grpd.{u₁,u₁})
    (B : ∫(A) ⥤ Grpd.{u₁,u₁})
    {x y z: Γ} (f : x ⟶ y) (g : y ⟶ z):
    conjugateLiftFunc A B (f ≫ g) =  (conjugateLiftFunc A B f) ⋙ (conjugateLiftFunc A B g) := by
    fapply fullSubcategoryInclusion_Mono_lemma
    simp only [FunctorOperation.sigma_obj, Grpd.coe_of, Functor.assoc]
    have e: conjugateLiftFunc A B (f ≫ g) ⋙ Section.inc ((fstAux B).app z) =
  conjugateLiftFunc A B f ⋙ conjugateLiftFunc A B g ⋙  Section.inc ((fstAux B).app z) :=
    by
     simp only [FunctorOperation.sigma_obj, Grpd.coe_of, conjugateLiftFunc_Inc A B g,
                ← Functor.assoc,conjugateLiftFunc_Inc A B f, FunctorOperation.sigma_obj,
                Grpd.coe_of, conjugate_FiberFunc]
     simp only [Functor.assoc, ← conjugating_comp (A ⋙ Grpd.forgetToCat),
                conjugateLiftFunc_Inc A B (f ≫ g),conjugate_FiberFunc]
    refine e

/-- The formation rule for Σ-types for the ambient natural model `base`
  unfolded into operations between functors -/

def pi {Γ : Grpd.{v,u}} {A : Γ ⥤ Grpd.{u₁,u₁}}
    (B : ∫(A) ⥤ Grpd.{u₁,u₁})
    : Γ ⥤ Grpd.{u₁,u₁} where
      obj x := Fiber_Grpd A B x
      map f := conjugateLiftFunc A B f
      map_id x:= conjugateLiftFunc_id A B x
      map_comp := conjugateLiftFunc_comp A B


def smallUPi_app {Γ : Ctx.{max u (v+1)}}
    (AB : y(Γ) ⟶ smallU.{v, max u (v+1)}.Ptp.obj smallU.{v, max u (v+1)}.Ty) :
    y(Γ) ⟶ smallU.{v, max u (v+1)}.Ty :=
  yonedaCategoryEquiv.symm (pi (smallUPTpEquiv AB).2)



/-- The formation rule for Π-types for the ambient natural model `smallU` -/
def smallUPi.Pi : smallU.{v}.Ptp.obj smallU.{v}.Ty ⟶ smallU.{v}.Ty :=
  NatTrans.yonedaMk (fun AB =>
    yonedaCategoryEquiv.symm (pi (smallUPTpEquiv AB).2))
    sorry




def lamAbeta.pt0  {Γ : Grpd.{v,u}} {A : Γ ⥤ Grpd.{u₁,u₁}}
    (β  : ∫(A) ⥤ PGrpd.{u₁,u₁})
    (x: Γ ) (a: A.obj x)
    : (sigma A (β ⋙ forgetToGrpd)).obj x where
      base  := a
      fiber := (β.obj ((ι A x).obj a)).str.pt

def lamAbeta.ptFunc  {Γ : Grpd.{v,u}} {A : Γ ⥤ Grpd.{u₁,u₁}}
    (β : ∫(A) ⥤ PGrpd.{u₁,u₁}) (x : Γ) :
    (A.obj x) ⥤ ((sigma A (β ⋙ forgetToGrpd)).obj x) :=
  sec ((ι A x ⋙ β) ⋙ forgetToGrpd) (ι A x ⋙ β) rfl
    -- where
      -- obj := lamAbeta.pt0 β x
      -- map {a1 a2} f := {
      --   base := f
      --   fiber := by
      --    simp
      --    let a0 := ((Groupoidal.ι A x) ⋙ β).map f
      --    simp[pt0]
      --    have a0':= CategoryTheory.PointedFunctor.point a0
      --    simp[a0] at a0'
      --    exact a0'
      -- }
      --   -- by
      --   -- simp[pt0]
      --   -- have a0 := ((Groupoidal.ι A x) ⋙ β).map f
      --   -- exact a0
      --   -- sorry
      -- map_id := sorry
      -- map_comp := sorry

lemma lamAbeta.ptFunc_obj  {Γ : Grpd.{v,u}} {A : Γ ⥤ Grpd.{u₁,u₁}}
    (β : ∫(A) ⥤ PGrpd.{u₁,u₁}) (x : Γ) :
   (lamAbeta.ptFunc β x).obj = lamAbeta.pt0 β x := rfl


lemma sec_IsSec {Γ : Grpd.{v,u}} (A : Γ ⥤ Grpd.{u₁,u₁})
  (α : Γ ⥤ PGrpd) (h : α ⋙ forgetToGrpd = A) :
  IsSec (CategoryTheory.Grothendieck.Groupoidal.forget) (sec A α h) := by
  simp only [IsSec, sec_forget]



def lamAbeta.pt  {Γ : Grpd.{v,u}} {A : Γ ⥤ Grpd.{u₁,u₁}}
    (β  : ∫(A) ⥤ PGrpd.{u₁,u₁})
    (x: Γ )
    : Fiber_Grpd A (β ⋙ forgetToGrpd) x where
      obj :=  lamAbeta.ptFunc β x
      property := by
       simp only [sigma_obj, sigmaObj, Grpd.coe_of, fstAux_app, ptFunc]
       apply sec_IsSec


/-Maybe deserve to have a file addressing functors to a grpd or category-/
lemma inv_map {Γ : Grpd.{v,u}}  {A : Γ ⥤ Grpd.{u₁,u₁}} {x y: Γ } (f: x ⟶ y):
CategoryTheory.inv (A.map f) = A.map (Groupoid.inv f):= by
 simp_all only [inv_eq_inv, Functor.map_inv]

-- lemma toGrpd_comp_obj {Γ : Grpd.{v,u}} {A : Γ ⥤ Grpd.{u₁,u₁}}
--  {x y z: Γ } (f: x ⟶ y) (g: y ⟶ z):
--   (A.map f).obj ((A.map (Groupoid.inv f)).obj ay)
#check  Cat.comp_obj
lemma toGrpd_map_inv_comp
{Γ : Grpd.{v,u}}  {A : Γ ⥤ Grpd.{u₁,u₁}} {x y: Γ } (f: x ⟶ y):
 (A.map (Groupoid.inv f) ≫  A.map f) = Functor.id _ := by
   have e := A.map_comp (Groupoid.inv f) f
   rw[← e]
   simp


lemma toGrpd_map_inv_comp'
{Γ : Grpd.{v,u}}  {A : Γ ⥤ Grpd.{u₁,u₁}} {x y: Γ } (f: x ⟶ y):
 (A.map (Groupoid.inv f) ⋙ A.map f) = Functor.id _ := by
  apply toGrpd_map_inv_comp

lemma toGrpd_map_comp
{Γ : Grpd.{v,u}}  {A : Γ ⥤ Grpd.{u₁,u₁}}
(β  : ∫(A) ⥤ PGrpd.{u₁,u₁})
{x y z: ∫(A) } (f: x ⟶ y) (g: y ⟶ z) (a: β.obj x):
 (β.map g).obj ((β.map f).obj a) = (β.map (f ≫ g)).obj a :=  by
  simp_all only [Functor.map_comp, comp_toFunctor, Functor.comp_obj]

/-Γ : Grpd
A : ↑Γ ⥤ Grpd
β : ∫(A) ⥤ PGrpd
x y : ↑Γ
f : x ⟶ y
ay : ↑(A.obj y)
e : ∀
  (f_1 :
    (ι A x).obj ((CategoryTheory.inv (A.map f)).obj ay) ⟶ (A.map f ⋙ ι A y).obj ((CategoryTheory.inv (A.map f)).obj ay))
  (g : (A.map f ⋙ ι A y).obj ((CategoryTheory.inv (A.map f)).obj ay) ⟶ (ι A y).obj ay)
  (a : ↑(β.obj ((ι A x).obj ((CategoryTheory.inv (A.map f)).obj ay)))),
  (β.map g).obj ((β.map f_1).obj a) = (β.map (f_1 ≫ g)).obj a


⊢ (β.map ((ιNatTrans f).app ((CategoryTheory.inv (A.map f)).obj ay) ≫ (ι A y).map (cast ⋯ (𝟙 ay)))).obj
    PointedGroupoid.pt ⟶
  PointedGroupoid.pt

  -/

lemma foo {Γ : Type u} [Groupoid Γ]  {A : Γ ⥤ Grpd.{u₁,u₁}} {x y:Γ } (f: x ⟶ y)  :
    (CategoryTheory.inv (A.map f))= A.map (Groupoid.inv f) := by
  simp_all only [inv_eq_inv, Functor.map_inv]

-- lemma foo1  {Γ : Type u} [Groupoid Γ]  {A : Γ ⥤ Grpd.{u₁,u₁}}
--  {x y:Γ } (f: x ⟶ y):
-- (CategoryTheory.inv (A.map f)).obj = (ιNatTrans (Groupoid.inv f)).app := sorry
lemma foo2  {Γ : Type u} [Groupoid Γ]  {A : Γ ⥤ Grpd.{u₁,u₁}}
 {x y:Γ } (f: x ⟶ y) (ay ay': A.obj y) :
 (whiskerLeft (A.map (Groupoid.inv f)) (ιNatTrans f)).app ay  =
 eqToHom sorry := by
  simp[ιNatTrans,Grothendieck.ιNatTrans]
  apply  Grothendieck.ext
  simp
  congr
  simp

  #check (whiskerLeft (A.map (Groupoid.inv f)) (ιNatTrans f)).app ay
  sorry


lemma foo' {Γ : Type u} [Groupoid Γ]  {A : Γ ⥤ Grpd.{u₁,u₁}}
 {x y:Γ } (f: x ⟶ y) (ay : A.obj y) :
 ((ιNatTrans f).app ((CategoryTheory.inv (A.map f)).obj ay)) =
 (ι A y).obj ay := by
  rw![foo]
  have e:= CategoryTheory.NatTrans.naturality (ιNatTrans f) (A.map (Groupoid.inv f))
  sorry



def lamAbeta {Γ : Grpd.{v,u}} {A : Γ ⥤ Grpd.{u₁,u₁}}
    (β  : ∫(A) ⥤ PGrpd.{u₁,u₁}) : Γ ⥤  PGrpd.{u₁,u₁} where
      obj x:= {
        α := (pi (β ⋙ forgetToGrpd)).obj x
        str := {
          pt := lamAbeta.pt β x
        }
      }
      --CategoryTheory.PointedFunctor
      map {x y} f :=
       PointedFunctor.mk ((pi (β ⋙ forgetToGrpd)).map f) {
         app ay:= by
          simp[pi]
          simp[conjugateLiftFunc,conjugate_FiberFunc,conjugating]
          simp[PointedCategory.pt,PointedGroupoid.pt,lamAbeta.pt,
              lamAbeta.ptFunc_obj]

          exact ⟨by
           simp[CategoryTheory.Grpd.forgetToCat];
           simp[lamAbeta.pt0,sigmaMap,sigmaMap];
           rw![inv_map]
           have e0: (A.map f).obj ((A.map (Groupoid.inv f)).obj ay) =
                     ((A.map (Groupoid.inv f)) ⋙ (A.map f)).obj ay := by
                     symm
                     --apply Cat.comp_obj
                     simp_all only [inv_eq_inv, Functor.map_inv, Functor.comp_obj]

           have e : (A.map f).obj ((A.map (Groupoid.inv f)).obj ay) = ay := by
            simp only[e0]
            simp only[toGrpd_map_inv_comp' ] --Q:Ask about things like this
            simp
            --#check CategoryTheory.Functor.map_comp
           simp only[e]
           exact (𝟙 ay)
           , by
            simp only [Functor.map_id]
            simp only[lamAbeta.ptFunc_obj,lamAbeta.pt0]
            simp only[Functor.comp_obj, forgetToGrpd_obj,id_eq
              Functor.comp_map, forgetToGrpd_map]
            rw![forgetToGrpd_map]
            simp only[id]
            --simp[sigmaMap]
            simp[sigmaMap,CategoryTheory.Grpd.forgetToCat]
            have e := @toGrpd_map_comp Γ A β   ((ι A x).obj ((CategoryTheory.inv (A.map f)).obj ay))
                    ((A.map f ⋙ ι A y).obj ((CategoryTheory.inv (A.map f)).obj ay))
                    ((ι A y).obj ay)
            simp only[e]
            simp only[CategoryTheory.Grothendieck.Groupoidal.ιNatTrans_comp_app]
            have e' :=
             CategoryTheory.Grothendieck.Groupoidal.ιNatTrans_comp_app
            have e' :
             ((ιNatTrans f).app ((CategoryTheory.inv (A.map f)).obj ay) ≫
              (ι A y).map (cast _ (𝟙 ay))) = Functor.id _ := sorry
            simp [toGrpd_map_comp]
            simp[← Functor.comp_map]
            have e1 := CategoryTheory.NatTrans.naturality (ιNatTrans f) f
            simp[← Functor.comp_map]
            #check (id (id (⋯.mpr (⋯.mpr (𝟙 ay)))))
            have e := (ι A y).map_id

            -- simp only [Functor.comp_obj, forgetToGrpd_obj, eq_mpr_eq_cast, cast_cast, id_eq,
            --   Functor.comp_map, forgetToGrpd_map]
            simp only [Functor.map_id]

            simp[CategoryTheory.Grpd.forgetToCat];
            simp[lamAbeta.pt0,sigmaMap,sigmaMap];
            rw[PointedGroupoid.pt]

            sorry⟩


        --  {
        --    base := sorry
        --    fiber := sorry
        --  }
        --  naturality := sorry
       }
      map_id := sorry
      map_comp := sorry

def smallUPi.lam : smallU.{v}.Ptp.obj smallU.{v}.Tm ⟶ smallU.{v}.Tm :=
  NatTrans.yonedaMk sorry sorry


def smallUPi : NaturalModelPi smallU.{v} where
  Pi := smallUPi.Pi.{v}
  lam := smallUPi.lam.{v}
  Pi_pullback := sorry

def uHomSeqPis' (i : ℕ) (ilen : i < 4) :
  NaturalModelPi (uHomSeqObjs i ilen) :=
  match i with
  | 0 => smallUPi.{0,4}
  | 1 => smallUPi.{1,4}
  | 2 => smallUPi.{2,4}
  | 3 => smallUPi.{3,4}
  | (n+4) => by omega

def uHomSeqPis : UHomSeqPiSigma Ctx := { uHomSeq with
  nmPi := uHomSeqPis'
  nmSigma := uHomSeqSigmas' }

end GroupoidModel

end
