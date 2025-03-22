import GroupoidModel.Groupoids.NaturalModelBase
import GroupoidModel.Russell_PER_MS.NaturalModelSigma

set_option maxHeartbeats 300000

universe v u v₁ u₁ v₂ u₂ v₃ u₃

noncomputable section
-- NOTE temporary section for stuff to be moved elsewhere
section ForOther



end ForOther


-- NOTE content for this doc starts here
namespace GroupoidModel

open CategoryTheory NaturalModelBase Opposite Grothendieck.Groupoidal

namespace FunctorOperation

-- TODO: Fix performance issue.
set_option maxHeartbeats 0 in
/-- The formation rule for Σ-types for the ambient natural model `base`
  unfolded into operations between functors.

  For a point `x : Γ`, `(sigma A B).obj x` is the groupoidal Grothendieck
  construction on the composition
  `ι _ x ⋙ B : A.obj x ⥤ Groupoidal A ⥤ Grpd` -/
@[simps] def sigma {Γ : Grpd.{v₂,u₂}} (A : Γ ⥤ Grpd.{v₁,u₁})
    (B : Grothendieck.Groupoidal A ⥤ Grpd.{v₁,u₁})
    : Γ ⥤ Grpd.{v₁,u₁} where
  obj x := Grpd.of (Grothendieck.Groupoidal ((ι _ x) ⋙ B))
  map {x y} f := map (whiskerRight (Grothendieck.ιNatTrans f) B)
    ⋙ pre (ι A y ⋙ B) (A.map f)
  map_id x := by
    let t := @Grothendieck.ιNatTrans _ _
        (A ⋙ Grpd.forgetToCat) _ _ (CategoryStruct.id x)
    have h (a : A.obj x) : B.map (t.app a) =
        eqToHom (by simp [Functor.map_id]) :=
      calc
        B.map (t.app a)
        _ = B.map (eqToHom (by simp [Functor.map_id])) := by
          rw [Grothendieck.ιNatTrans_id_app]
        _ = eqToHom (by simp [Functor.map_id]) := by
          simp [eqToHom_map]
    simp only [map, Grothendieck.Groupoidal.pre, Grpd.id_eq_id, Grothendieck.pre]
    apply CategoryTheory.Functor.ext
    · intro p1 p2 f
      simp only [Grpd.coe_of, Functor.comp_obj, Functor.comp_map, whiskerRight_twice,
        Grothendieck.map_obj_base, Grothendieck.map_obj_fiber, whiskerRight_app,
        Grothendieck.ι_obj, Grothendieck.map_map_base,
        Grothendieck.map_map_fiber, Functor.id_obj, Functor.id_map]
      congr 1
      · simp only [Grpd.map_id_map, Grothendieck.base_eqToHom,
          Grothendieck.comp_base]
      · simp only [Grpd.forgetToCat, id_eq, Functor.comp_map, whiskerRight_twice,
          Grothendieck.map_obj_base, Grothendieck.map_obj_fiber, whiskerRight_app,
          Grothendieck.ι_obj, Grothendieck.fiber_eqToHom, Grothendieck.comp_fiber]
        rw [Functor.congr_hom (h p2.base) f.fiber]
        simp only [Grpd.eqToHom_hom, eqToHom_map, heq_eqToHom_comp_iff,
          eqToHom_comp_heq_iff, comp_eqToHom_heq_iff, heq_comp_eqToHom_iff]
        generalize_proofs _ _ h1
        have h2 : B.map ((ι A x).map (eqToHom h1).base) =
            eqToHom (by simp only [CategoryTheory.Functor.map_id]; rfl) := by
          rw [Grothendieck.eqToHom_base, eqToHom_map, eqToHom_map]
        rw [Functor.congr_hom h2, heq_eqToHom_comp_iff, heq_comp_eqToHom_iff]
        simp only [heq_eq_eq, Grpd.eqToHom_hom]
    · intro p
      simp only [Functor.comp_obj, Grothendieck.map_obj]
      congr 1
      · exact Grpd.map_id_obj
      · simp only [Grpd.forgetToCat, id_eq, whiskerRight_app,
          Functor.comp_map]
        rw [Functor.congr_obj (h p.base) p.fiber]
        simp [Grpd.eqToHom_obj]
  map_comp := by
    intro x y z f g
    have h (a : A.obj x) : B.map ((Grothendieck.ιNatTrans (f ≫ g)).app a)
        = B.map ((Grothendieck.ιNatTrans f).app a)
        ⋙ B.map (eqToHom (by
          simp [Grpd.forgetToCat]))
        ⋙ B.map ((Grothendieck.ιNatTrans g).app ((A.map f).obj a))
        ⋙ B.map (eqToHom (by
          simp [Grpd.forgetToCat, Grpd.comp_eq_comp])) := by
      simp only [Grothendieck.ιNatTrans_comp_app, Functor.map_comp,
        eqToHom_map, CategoryTheory.Functor.map_id]
      rfl
    simp only [Grothendieck.Groupoidal.pre, Grothendieck.pre]
    apply CategoryTheory.Functor.ext
    · sorry
    · intro p
      simp only [Grpd.coe_of, Functor.comp_obj, Functor.comp_map]
      congr 1
      · rw [Grpd.map_comp_obj]
        rfl
      · simp [map, Grpd.forgetToCat, Functor.congr_obj (h p.base) p.fiber,
        eqToHom_refl, eqToHom_map, Grpd.eqToHom_obj, Grpd.id_eq_id, Functor.id_obj]

section

variable {Δ Γ: Grpd.{v₂,u₂}} (σ : Δ ⥤ Γ) (A : Γ ⥤ Grpd.{v₁,u₁})


theorem sigmaBeckChevalley (B : (Grothendieck.Groupoidal A) ⥤ Grpd.{v₁,u₁})
    : σ ⋙ sigma A B = sigma (σ ⋙ A) (pre A σ ⋙ B) := by
  refine CategoryTheory.Functor.ext ?_ ?_
  . intros x
    dsimp only [Functor.comp_obj, sigma_obj]
    rw [← Grothendieck.Groupoidal.ιCompPre σ A x]
    rfl
  . intros x y f
    sorry -- this goal might be improved by adding API for Groupoidal.ι and Groupoidal.pre
end

def eqToHomGrdik {C : Type u} [Category.{v} C] {F : C ⥤ Cat.{v₁,v₂}} {X Y : Grothendieck F} {h : X = Y} :
  eqToHom h = {base := eqToHom (congrArg (fun(x) => x.base) h), fiber := (eqToHom (by cases h; simp) )} := by
  rcases h
  simp[CategoryStruct.id,Grothendieck.id]

def pairSection {Γ : Grpd.{v₂,u₂}} (α β : Γ ⥤ PGrpd.{v₁,u₁})
    (B : Grothendieck.Groupoidal (α ⋙ PGrpd.forgetToGrpd) ⥤ Grpd.{v₁,u₁})
    (h : β ⋙ PGrpd.forgetToGrpd = Grothendieck.Groupoidal.sec α ⋙ B)
    : Γ ⥤ (Grothendieck.Groupoidal (sigma (α ⋙ PGrpd.forgetToGrpd) B)) where
    obj x := by
      fconstructor
      . exact x
      . fconstructor
        . exact (α.obj x).str.pt
        . exact (eqToHom (Functor.congr_obj h x)).obj ((β.obj x).str.pt)
    map {x y} f := by
      refine {base := f, fiber := {base := (α.map f).point, fiber := ?_}}
      dsimp[Grpd.forgetToCat,Grothendieck.Groupoidal.pre,ι,map,Grothendieck.ιNatTrans,Grpd.forgetToCat]

      have eq1 : (eqToHom (Functor.congr_obj h y)).obj (@PointedGroupoid.pt ((β.obj y)) (β.obj y).str) = (Functor.id _).obj ((eqToHom (Functor.congr_obj h y)).obj (@PointedGroupoid.pt ((β.obj y)) (β.obj y).str)) := by simp
      have eq2 : ((Groupoid.compForgetToCat (α ⋙ PGrpd.forgetToGrpd)).map (f ≫ 𝟙 y)).obj ((Grothendieck.Groupoidal.sec α).obj x).fiber = (α.map f).obj PointedCategory.pt := by
        simp[Grothendieck.Groupoidal.sec,Grpd.forgetToCat]
        apply congrArg
        exact rfl

      set outer : B.obj { base := y, fiber := (α.map f).obj (@PointedGroupoid.pt (↑(α.obj x)) (α.obj x).str)} ⟶ B.obj {base := y, fiber := (@PointedGroupoid.pt (↑(α.obj y)) (α.obj y).str)}
       := (B.map { base := 𝟙 y, fiber := eqToHom (Grothendieck.ι.proof_1 ((α ⋙ PGrpd.forgetToGrpd) ⋙ Grpd.forgetToCat) y) ≫ (α.map f).point })
      set inner :(B.obj { base := x, fiber := (@PointedGroupoid.pt (↑(α.obj x)) (α.obj x).str ) }) ⟶ (B.obj { base := y, fiber := (α.map f).obj (@PointedGroupoid.pt (↑(α.obj x)) (α.obj x).str)})
        := (B.map { base := f, fiber := 𝟙 ((α.map f).obj _)})
      set pg : (β.obj x) := @PointedGroupoid.pt (↑(β.obj x)) (β.obj x).str

      have eq5 : outer.obj (inner.obj ((eqToHom (Functor.congr_obj h x)).obj pg)) = (((eqToHom (Functor.congr_obj h x )⋙ eqToHom (Functor.congr_obj (Eq.symm h) x)) ⋙ PGrpd.forgetToGrpd.map (β.map f)) ⋙ eqToHom (Eq.symm (Functor.congr_obj (Eq.symm h) y))).obj (@PointedGroupoid.pt (↑(β.obj x)) (β.obj x).str) := by
        simp [outer,inner,pg,<- Grpd.map_comp_obj, CategoryStruct.comp,Grothendieck.comp,Grpd.forgetToCat]

        have rwn := Eq.trans (Prefunctor.congr_map (Grothendieck.Groupoidal.sec α ⋙ B).toPrefunctor (Category.comp_id f)) (Functor.congr_hom h.symm f)

        simp only [Functor.comp_map] at rwn

        unfold Grothendieck.Groupoidal.sec at rwn

        unfold IsMegaPullback.lift at rwn

        unfold Grothendieck.IsMegaPullback.lift at rwn

        unfold Grothendieck.IsMegaPullback.lift_obj at rwn

        unfold Grothendieck.IsMegaPullback.lift_obj at rwn




        simp only [Functor.comp_map, Grothendieck.Groupoidal.sec] at rwn
        rw [<-(PointedFunctor.congr_point (congrArg α.map (id (Category.comp_id f)))),rwn]
        simp [CategoryStruct.comp,<- Functor.assoc]
        sorry

      refine eqToHom eq5 ≫ ?_

      let m1 {a1 a2 a3 a4 a5: Grpd} {o1 : a1 = a2} {o2 : a2 = a3} {F : a3 ⥤ a4} {G : a4 ⥤ a5} {x : a1} : (((eqToHom o1) ⋙ (eqToHom o2)) ⋙ F ⋙ G).obj x ⟶ (eqToHom (Eq.trans o1 o2) ⋙ F ⋙ G).obj x := by
        refine eqToHom ?_
        cases o1
        cases o2
        simp[Functor.comp,CategoryStruct.id,Functor.id]

      exact m1 ≫ (eqToHom (Functor.congr_obj h y)).map (β.map f).point

    map_id x := by
      simp[CategoryStruct.id,Grothendieck.id]
      fapply Grothendieck.ext
      . exact rfl
      . simp
        rw [eqToHomGrdik]
        fapply Grothendieck.ext
        . refine Eq.trans (PointedFunctor.congr_point (α.map_id x)) ?_
          simp [CategoryStruct.id]
        . simp [PointedFunctor.congr_point (β.map_id x),eqToHom_map]
    map_comp := by
      intros x y z f g
      sorry

theorem pairSection_isSection {Γ : Grpd.{v₂,u₂}} (α β : Γ ⥤ PGrpd.{v₁,u₁})
    (B : Grothendieck.Groupoidal (α ⋙ PGrpd.forgetToGrpd) ⥤ Grpd.{v₁,u₁})
    (h : β ⋙ PGrpd.forgetToGrpd = Grothendieck.Groupoidal.sec α ⋙ B) :
     (pairSection α β B h) ⋙ Grothendieck.forget _ = Functor.id Γ := rfl

def pair {Γ : Grpd.{v₂,u₂}} (α β : Γ ⥤ PGrpd.{v₁,u₁})
    (B : Grothendieck.Groupoidal (α ⋙ PGrpd.forgetToGrpd) ⥤ Grpd.{v₁,u₁})
    (h : β ⋙ PGrpd.forgetToGrpd = Grothendieck.Groupoidal.sec α ⋙ B)
    : Γ ⥤ PGrpd.{v₁,u₁} := pairSection α β B h ⋙ Grothendieck.Groupoidal.toPGrpd _

def sigma_is_forgetToGrpd_after_pair {Γ : Grpd.{v₂,u₂}} (α β : Γ ⥤ PGrpd.{v₁,u₁})
    (B : Grothendieck.Groupoidal (α ⋙ PGrpd.forgetToGrpd) ⥤ Grpd.{v₁,u₁})
    (h : β ⋙ PGrpd.forgetToGrpd = Grothendieck.Groupoidal.sec α ⋙ B) :
    pair α β B h ⋙ PGrpd.forgetToGrpd = sigma (α ⋙ PGrpd.forgetToGrpd) B := by
  unfold pair
  rw [Functor.assoc]
  exact rfl

end FunctorOperation

open FunctorOperation

/-- The formation rule for Σ-types for the ambient natural model `base` -/
def baseSig : base.Ptp.obj base.{u}.Ty ⟶ base.Ty where
  app Γ := fun p =>
    let ⟨A,B⟩ := baseUvPolyTpEquiv p
    yonedaEquiv (yonedaCatEquiv.symm (sigma A B))
  naturality := sorry -- do not attempt

def basePair : base.uvPolyTp.compDom base.uvPolyTp ⟶ base.Tm where
  app Γ := fun ε =>
    let ⟨α,B,β,h⟩ := baseUvPolyTpCompDomEquiv ε
    yonedaEquiv (yonedaCatEquiv.symm (pair α β B h))
  naturality := by sorry

def ExtFunctorial {Γ : Ctx} {F G : (yoneda.obj Γ) ⟶  base.Ty} (n : (yonedaCatEquiv.toFun F) ⟶ (yonedaCatEquiv.toFun G)) : base.ext F ⟶ base.ext G := by
  dsimp [NaturalModelBase.ext, ext,Grpd.of,Grothendieck.Groupoidal]
  refine AsSmall.up.map ?_
  exact map n

def Sigma_UP_Elim (Γ : Ctx) (F : yoneda.obj Γ ⟶ base.Ptp.obj base.{u}.Ty) : (α : yoneda.obj Γ ⟶ base.Ty) × (yoneda.obj (base.ext α) ⟶ base.Ty) := by
  unfold Ptp at F
  have r := base.uvPolyTp.polyPair F
  rcases r with ⟨α, B⟩
  refine ⟨α,?_⟩
  let B' : y(base.ext α) ⟶ base.Ty := by
    refine ?_ ≫ B
    have iso :y(base.ext α) ≅ (Limits.pullback α base.uvPolyTp.p) := by
      exact (base.pullbackIsoExt α).symm
    exact (id iso.symm).inv
  exact B'

def Sigma_UP_Intro (Γ : Ctx) (α : yoneda.obj Γ ⟶ base.Ty) (B : yoneda.obj (base.ext α) ⟶ base.Ty) :  yoneda.obj Γ ⟶ base.Ptp.obj base.{u}.Ty
 := base.uvPolyTp.pairPoly α ( (Iso.hom (base.pullbackIsoExt α)) ≫ B)


-- def pair_UP_Elim (Γ : Ctx.{u}) (F : yoneda.obj Γ ⟶ base.{u}.uvPolyTp.compDom base.{u}.uvPolyTp) : (α : yoneda.obj Γ ⟶ base.{u}.Tm) × (β : yoneda.obj Γ ⟶ base.{u}.Tm) × (B : yoneda.obj (base.{u}.ext (α ≫ base.{u}.tp)) ⟶ base.{u}.Ty) ×' (β ≫ base.{u}.tp = (yoneda.map (base.{u}.sec α)) ≫ B ) := by
--   unfold UvPoly.compDom at F
--   let F.fst := F ≫ Limits.pullback.fst _ _
--   let F.snd := F ≫ Limits.pullback.snd _ _
--   have F.h := Limits.pullback.condition (f := base.uvPolyTp.p) (g := (UvPoly.genPb.u₂ base.uvPolyTp base.Ty))
--   have sigma : (α : yoneda.obj Γ ⟶ base.Ty) × (yoneda.obj (base.ext α) ⟶ base.Ty) := by
--     refine Sigma_UP_Elim Γ ?_
--     refine F.snd ≫ ?_
--     exact
--       UvPoly.genPb.fst base.uvPolyTp
--         ((AsSmall.down ⋙ Grpd.forgetToCat ⋙ catLift).op ⋙ yoneda.obj (Cat.of Grpd))
--   refine ⟨?_ , F.fst , ?_, ?_⟩




--   refine ⟨?_ , F.fst , ?_ , ?_ ⟩
--   . refine F.snd ≫ ?_
--     unfold UvPoly.genPb
--     refine Limits.pullback.snd _ _
--   . refine (base.var _) ≫ base.tp
--   . unfold F.fst
--     have help : base.tp = base.uvPolyTp.p := by rfl
--     have help2 : Limits.pullback.fst base.uvPolyTp.p (UvPoly.genPb.u₂ base.uvPolyTp base.Ty) = Limits.pullback.fst base.tp (UvPoly.genPb.u₂ base.uvPolyTp base.Ty) := by
--       simp [help]
--       exact rfl
--     rewrite [<- help] at F.h
--     rw [Category.assoc,help2, F.h]
--     simp [base.var]
--     have help3 : base.var ((F.snd ≫ id (Limits.pullback.snd (base.uvPolyTp.proj base.Ty) base.uvPolyTp.p)) ≫ base.tp) ≫ base.tp =




-- def pair_UP_Intro (Γ : Ctx) (α β : yoneda.obj Γ ⟶ base.Tm) (B : yoneda.obj (base.ext (α ≫ base.tp)) ⟶ base.Ty) (h : β ≫ base.tp = (yoneda.map (base.sec α)) ≫ B ) :  yoneda.obj Γ ⟶ base.uvPolyTp.compDom base.uvPolyTp := by


#check baseUvPolyTpCompDomEquiv
#check yonedaEquiv
def PairSigmaUP {Γ : Ctx} (β : yoneda.obj Γ ⟶ base.Tm) (AB : yoneda.obj Γ ⟶  base.Ptp.obj base.{u}.Ty) (h : Top ≫ base.tp = Left ≫ baseSig) : yoneda.obj Γ ⟶ base.uvPolyTp.compDom base.uvPolyTp := by
  refine yonedaEquiv.invFun ?_
  refine baseUvPolyTpCompDomEquiv.invFun ?_
  -- let sig := baseUvPolyTpEquiv.toFun (yonedaEquiv.toFun Left)
  -- rcases sig with ⟨A,B⟩
  refine ⟨?α,?B,(yonedaCatEquiv.toFun β),?h⟩
  . sorry
  .















def baseSigma : NaturalModelSigma base where
  Sig := baseSig
  pair := basePair
  Sig_pullback := sorry -- should prove using the `IsMegaPullback` strategy

def smallUSigma : NaturalModelSigma smallU := sorry

def uHomSeqSigmas' (i : ℕ) (ilen : i < 4) :
  NaturalModelSigma (uHomSeqObjs i ilen) :=
  match i with
  | 0 => smallUSigma
  | 1 => smallUSigma
  | 2 => smallUSigma
  | 3 => baseSigma
  | (n+4) => by omega

end GroupoidModel

end
