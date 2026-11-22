import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2210
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2775
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2621
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2774
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2677
import Development.AbelianVarietyTheory.Counterexamples.UniformisationSurvey.NeTopOfAdmissibleBase
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformizationEndomorphismCalculus
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2776
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedEighthPowerEndomorphismActsByIntMatri
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep.EndCompat

def preH {S : Scheme.{0}} {T T' G : Over S} [GrpObj G] (w : T' ⟶ T) : (T ⟶ G) →* (T' ⟶ G) :=
  MonoidHom.mk' (w ≫ ·) fun a b => MonObj.comp_mul w a b

def postH {S : Scheme.{0}} {T G H : Over S} [GrpObj G] [GrpObj H] (f : G ⟶ H) (hf : IsMonHom f) :
    (T ⟶ G) →* (T ⟶ H) :=
  haveI := hf
  MonoidHom.mk' (· ≫ f) fun a b => MonObj.mul_comp a b f

def pullH {S S' : Scheme.{0}} (f : S' ⟶ S) (T G : Over S) [GrpObj G] :
    (T ⟶ G) →* ((Over.pullback f).obj T ⟶ (Over.pullback f).obj G) where
  toFun := (Over.pullback f).map
  map_one' := by simp
  map_mul' a b := Functor.map_mul _ a b

theorem map_ofFn_prod {M N : Type} [Group M] [Group N] (f : M →* N) (x : Fin 8 → M) (k : Fin 8 → ℤ) :
    f (List.ofFn fun v => x v ^ k v).prod = (List.ofFn fun v => f (x v) ^ k v).prod := by
  rw [map_list_prod, List.map_ofFn]
  simp [Function.comp_def, map_zpow]

theorem aG_comp_eq_prod : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (y : Sp (FractionRing V₁) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left), IsSemiAbelian G₀ → IsGrpPullback A₀.A F.univ.A y α → ∀ (P : PolAV (Sp (FractionRing V₁))) (c : SiegPre g n ζ (y ≫ F.s)) (φc : c.A.left ⟶ F.univ.A.left), IsGrpPullback c.A F.univ.A y φc → ∀ pr : Fin 8 → (P.A ⟶ c.A), (∀ a, IsMonHom (pr a)) → ∀ (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V₁ (maximalIdeal V₁)) (U : Unif (maximalIdeal V₁) D P G) (q : Fin 8 → (G ⟶ G₀)), (∀ u, IsMonHom (q u)) → (∀ u, ((Over.pullback (jK V₁)).map (q u) ≫ U₀.gen.hom).left ≫ α = (U.gen.hom ≫ pr u).left ≫ φc) → ∀ (a : Matrix (Fin 8) (Fin 8) ℤ) (E : EndU U.toUnifPre), (∀ u, E.aA ≫ pr u = (List.ofFn fun v => pr v ^ a u v).prod) → ∀ u, E.aG ≫ q u = (List.ofFn fun v => q v ^ a u v).prod := by
  intro g n o _ ζ F V₁ _ _ _ hCN D₀ G₀ _ _ A₀ U₀ y α hG₀ hα P c φc hφc pr hpr G _ _ hG D U q hq hqc a E hE u
  haveI : IsNoetherianRing V₁ := hCN.1
  haveI : IsIntegrallyClosed V₁ := hCN.2.1
  haveI := E.homG
  haveI := hq u
  haveI := U₀.gen_hom
  have hR : IsMonHom (List.ofFn fun v => q v ^ a u v).prod := by
    refine isMonHom_of_mul _ fun T x z => ?_
    have key : ∀ w : T ⟶ G, w ≫ (List.ofFn fun v => q v ^ a u v).prod = ∏ v, (w ≫ q v) ^ a u v := fun w => by
      rw [← List.prod_ofFn]
      exact map_ofFn_prod (preH w) q (a u)
    rw [key, key, key, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    haveI := hq v
    rw [MonObj.mul_comp, mul_zpow]
  obtain ⟨F0, -, huniq⟩ := GlobalTheory.semiAbelianHomExtension_holds.fractionField V₁ (FractionRing V₁) G G₀ hG hG₀
    ((Over.pullback (jK V₁)).map (E.aG ≫ q u))
  refine (huniq _ ⟨inferInstance, rfl⟩).trans (huniq _ ⟨hR, ?_⟩).symm
  rw [← cancel_mono U₀.gen.hom]
  apply Over.OverMorphism.ext
  refine hα.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm)
  have hv : ∀ v, pushHom hα ((Over.pullback (jK V₁)).obj G) ((Over.pullback (jK V₁)).map (q v) ≫ U₀.gen.hom) =
      pushHom hφc ((Over.pullback (jK V₁)).obj G) (U.gen.hom ≫ pr v) :=
    fun v => Over.OverMorphism.ext (hqc v)
  have e₁ : ((Over.pullback (jK V₁)).map (List.ofFn fun v => q v ^ a u v).prod ≫ U₀.gen.hom).left ≫ α =
      (List.ofFn fun v => pushHom hφc ((Over.pullback (jK V₁)).obj G) (U.gen.hom ≫ pr v) ^ a u v).prod.left := by
    have := map_ofFn_prod ((pushHom hα ((Over.pullback (jK V₁)).obj G)).comp
      ((postH U₀.gen.hom U₀.gen_hom).comp (pullH (jK V₁) G G₀))) q (a u)
    refine (congrArg (fun z => z.left) this).trans ?_
    refine congrArg (fun z => Over.Hom.left (List.ofFn z).prod) (funext fun v => ?_)
    rw [← hv v]
    rfl
  have e₂ : ((Over.pullback (jK V₁)).map (E.aG ≫ q u) ≫ U₀.gen.hom).left ≫ α =
      (List.ofFn fun v => pushHom hφc ((Over.pullback (jK V₁)).obj G) (U.gen.hom ≫ pr v) ^ a u v).prod.left := by
    have h1 : ((Over.pullback (jK V₁)).map (E.aG ≫ q u) ≫ U₀.gen.hom).left ≫ α =
        (U.gen.hom ≫ (List.ofFn fun v => pr v ^ a u v).prod).left ≫ φc := by
      rw [Functor.map_comp, Category.assoc, Over.comp_left, Category.assoc, hqc u, ← Category.assoc,
        ← Over.comp_left, ← Category.assoc, E.ext, Category.assoc, hE u]
    have h2 := map_ofFn_prod ((pushHom hφc ((Over.pullback (jK V₁)).obj G)).comp (preH U.gen.hom)) pr (a u)
    exact h1.trans (congrArg (fun z => z.left) h2)
  exact e₁.trans e₂.symm

end GlobalTheory.Poinc.Sep.EndCompat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupGaloisMapMulStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedGroup_galoisMap_mul : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (σ τ : Gal ρ) (a b : G'.left ⟶ G'.left), GalMap hD U' σ a → GalMap hD U' τ b → GalMap hD U' (σ * τ) (a ≫ b) := by
  first | exact @GlobalTheory.Mum.galMap_mul | exact GlobalTheory.Mum.galMap_mul | (intros; apply GlobalTheory.Mum.galMap_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupGaloisMapOneStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedGroup_galoisMap_one : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), GalMap hD U' 1 (𝟙 _) := by
  first | exact @GlobalTheory.Mum.galMap_one | exact GlobalTheory.Mum.galMap_one | (intros; apply GlobalTheory.Mum.galMap_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupHomCharacterMapConstant
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.Mum.Two.HomConst

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ : DegPre R} {e : ℕ}
  {G₁ G₂ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂]

theorem torusHomOf_iff_appTop {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X']
    (h : X' → X) (t : splitTorus S X ⟶ splitTorus S X') : TorusHomOf h t ↔
      ∀ χ, t.left.appTop.hom (charUnit S X' χ).val = (charUnit S X (h χ)).val := by
  refine forall_congr' fun χ => ?_
  have : (res (fun x _ => show t.left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial)
      (pullU t.left ⊤ (charUnit S X' χ)) : Γ((splitTorus S X).left, ⊤)ˣ).val =
      t.left.appTop.hom (charUnit S X' χ).val := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [← this, Units.ext_iff]

def Acts (g₁ : GtCoord I D₁ e G₁) (g₂ : GtCoord I D₂ e G₂)
    (a : (thickObj R I e G₁).left ⟶ (thickObj R I e G₂).left) (f : D₂.X → D₁.X) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G₁).left) (z : Z) (J₁ : (Z ⟶ D₁.P.A.left) → D₁.P.L.ι)
    (J₂ : (Z ⟶ D₂.P.A.left) → D₂.P.L.ι), Good D₁.P.L z J₁ → Good D₂.P.L z J₂ →
    r ≫ g₁.pG.left = r ≫ (fstG I e G₁).left ≫ G₁.hom ≫ eSec D₁.P.A →
    ∀ x, val (g₂.t x) (r ≫ a) z J₂ = val (g₁.t (f x)) r z J₁

theorem acts_of_torusHomOf (g₁ : GtCoord I D₁ e G₁) (g₂ : GtCoord I D₂ e G₂)
    (a : thickObj R I e G₁ ⟶ thickObj R I e G₂) {f : D₂.X → D₁.X}
    {t : splitTorus _ D₁.X ⟶ splitTorus _ D₂.X} (ht : TorusHomOf f t)
    (hi : g₁.i ≫ a = t ≫ g₂.i) : Acts g₁ g₂ a.left f := by
  intro Z r z J₁ J₂ hJ₁ hJ₂ h x
  let FinalForm : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) :=
    Over.mk (r ≫ (thickObj R I e G₁).hom)
  let b : FinalForm ⟶ thickObj R I e G₁ := Over.homMk r rfl
  let τ := g₁.isKernel.lift b (toUnit _) ((CharAgree.comp_q_eq_one_iff g₁ b).2 h)
  have hτ : τ ≫ g₁.i = b := g₁.isKernel.lift_fst _ _ _
  have hτ' : (τ ≫ t) ≫ g₂.i = b ≫ a := by rw [Category.assoc, ← hi, ← Category.assoc, hτ]
  have k := (TorusCoord.val_torus_point_and_translate R I D₂ e G₂ g₂ FinalForm (τ ≫ t) 1 z J₂ hJ₂ x).1
  have k' := (TorusCoord.val_torus_point_and_translate R I D₁ e G₁ g₁ FinalForm τ 1 z J₁ hJ₁ (f x)).1
  rw [hτ'] at k
  rw [hτ] at k'
  refine k.trans (Eq.trans (Units.ext ?_) k'.symm)
  rw [gm_val _ _ ⊤ trivial, gm_val _ _ ⊤ trivial]
  refine congrArg (FinalForm.left.presheaf.germ ⊤ z trivial).hom ?_
  exact (SplitTorusHom.appTop_comp τ t _).trans
    (congrArg τ.left.appTop.hom ((torusHomOf_iff_appTop _ _).1 ht x))

theorem acts_unique [IsAdicComplete I R] (g₁ : GtCoord I D₁ e G₁) (g₂ : GtCoord I D₂ e G₂)
    {a : (thickObj R I e G₁).left ⟶ (thickObj R I e G₂).left} {f f' : D₂.X → D₁.X}
    (h : Acts g₁ g₂ a f) (h' : Acts g₁ g₂ a f') : f = f' := by
  funext x
  have := EndTorus.connectedSpace_thickening I e
  refine SplitTorusHom.charUnit_injective (S := Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))
    (congrArg Units.val (unit_ext fun z _ => ?_))
  choose J₁ hJ₁ using fun ψ : (splitTorus _ D₁.X).left ⟶ D₁.P.A.left => exists_chart D₁.P.isLB (ψ z)
  choose J₂ hJ₂ using fun ψ : (splitTorus _ D₁.X).left ⟶ D₂.P.A.left => exists_chart D₂.P.isLB (ψ z)
  have c := (CharAgree.comp_q_eq_one_iff g₁ g₁.i).1 g₁.isKernel.w
  have k := fun χ =>
    (TorusCoord.val_torus_point_and_translate R I D₁ e G₁ g₁ _ (𝟙 _) 1 z J₁ hJ₁ χ).1
  simp only [Category.id_comp] at k
  exact (k _).symm.trans (((h _ _ z J₁ J₂ hJ₁ hJ₂ c x).symm.trans (h' _ _ z J₁ J₂ hJ₁ hJ₂ c x)).trans (k _))

omit [IsDomain R] [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] in

theorem thickMap_comm (aG : G₁ ⟶ G₂) (e : ℕ) :
    thickMap R I e G₁ ≫ ((Over.pullback (thick R I (e + 1))).map aG).left =
      ((Over.pullback (thick R I e)).map aG).left ≫ thickMap R I e G₂ := by
  apply pullback.hom_ext <;>
    simp [thickMap, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
      pullback.lift_snd_assoc]

theorem acts_down {D₁ D₂ : DegData R I} {A₁ A₂ : PolAV (Sp (FractionRing R))}
    (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (aG : G₁ ⟶ G₂)
    {f : D₂.toPre.X → D₁.toPre.X}
    (h : Acts (U₁.gt (e + 1)) (U₂.gt (e + 1)) ((Over.pullback (thick R I (e + 1))).map aG).left f) :
    Acts (U₁.gt e) (U₂.gt e) ((Over.pullback (thick R I e)).map aG).left f := by
  intro Z r z J₁ J₂ hJ₁ hJ₂ c x
  have t : thickMap R I e G₁ ≫ (fstG I (e + 1) G₁).left = (fstG I e G₁).left :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have up : (r ≫ thickMap R I e G₁) ≫ (U₁.gt (e + 1)).pG.left =
      (r ≫ thickMap R I e G₁) ≫ (fstG I (e + 1) G₁).left ≫ G₁.hom ≫ eSec D₁.toPre.P.A := by
    refine (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) (U₁.gt_q e)).trans (c.trans ?_))
    refine Eq.trans (congrArg (r ≫ ·) ?_) (Category.assoc _ _ _).symm
    exact (congrArg (· ≫ G₁.hom ≫ eSec D₁.toPre.P.A) t.symm).trans (Category.assoc _ _ _)
  have k := h Z (r ≫ thickMap R I e G₁) z J₁ J₂ hJ₁ hJ₂ up x
  have sq : (r ≫ thickMap R I e G₁) ≫ ((Over.pullback (thick R I (e + 1))).map aG).left =
      (r ≫ ((Over.pullback (thick R I e)).map aG).left) ≫ thickMap R I e G₂ := by
    rw [Category.assoc, Category.assoc, thickMap_comm]
  rw [sq] at k
  exact (val_corr hJ₂ (U₂.gt_t e x) _).symm.trans ((val_pull hJ₂ _ _ _).trans (k.trans
    ((val_pull hJ₁ _ _ _).symm.trans (val_corr hJ₁ (U₁.gt_t e (f x)) r))))

theorem exists_torus_hom (hR : AdmBase R I) (g₁ : GtCoord I D₁ e G₁) (g₂ : GtCoord I D₂ e G₂)
    (a : thickObj R I e G₁ ⟶ thickObj R I e G₂) [IsMonHom a] :
    ∃ h : D₂.X →+ D₁.X, ∃ t, TorusHomOf h t ∧ g₁.i ≫ a = t ≫ g₂.i := by
  obtain ⟨hN, -, -, hC⟩ := hR
  have := EndTorus.connectedSpace_thickening I e
  have := g₂.q_hom
  have := g₁.i_hom
  have := g₂.i_hom
  have hk := g₂.isKernel
  have : IsProper D₂.P.A.hom := D₂.P.isAb.proper
  have hB : IsAbelianScheme (thickObj R I e D₂.P.A) :=
    { comm := inferInstance
      smooth := by have := D₂.P.isAb.smooth; show Smooth (pullback.snd _ _); infer_instance
      proper := by show IsProper (pullback.snd _ _); infer_instance
      geomConnected := by
        have := D₂.P.isAb.geomConnected
        show GeometricallyConnected (pullback.snd _ _)
        infer_instance }
  have h1 : g₁.i ≫ a ≫ g₂.q = toUnit _ ≫ η[thickObj R I e D₂.P.A] :=
    (splitTorus_hom_abelian_eq_one _ D₁.X _ hB (g₁.i ≫ a ≫ g₂.q) inferInstance).trans (Hom.one_def)
  have : Mono g₂.i := by
    have : Mono (η[thickObj R I e D₂.P.A]) := ⟨fun _ _ _ => toUnit_unique _ _⟩
    exact (MorphismProperty.monomorphisms _).of_isPullback hk.flip (.infer_property _)
  let t := hk.lift (g₁.i ≫ a) (toUnit _) (by rw [Category.assoc, h1])
  have ht : t ≫ g₂.i = g₁.i ≫ a := hk.lift_fst _ _ _
  have : IsMonHom (t ≫ g₂.i) := ht ▸ inferInstance
  have : IsMonHom t := EndTorus.isMonHom_of_mono t g₂.i
  obtain ⟨h, hh⟩ := SplitTorusHom.exists_addMonoidHom t
  exact ⟨h, t, (torusHomOf_iff_appTop _ _).2 hh, ht.symm⟩

end GlobalTheory.Mum.Two.HomConst

open GlobalTheory.Mum.Two.HomConst in

theorem GlobalTheory.Mum.Two.unifPre_hom_character_const : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂), IsMonHom a → ∃ h : D₂.toPre.X →+ D₁.toPre.X, OnTorus U₁ U₂ a h := by
  intro R _ _ I hR D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ U₁ U₂ a ha
  have ex := fun e => exists_torus_hom hR (U₁.gt e) (U₂.gt e) ((Over.pullback (thick R I e)).map a)
  choose h t ht hi using ex
  obtain ⟨-, -, -, hC⟩ := hR
  have down : ∀ (e : ℕ) (f : D₂.toPre.X → D₁.toPre.X),
      Acts (U₁.gt e) (U₂.gt e) ((Over.pullback (thick R I e)).map a).left f →
      Acts (U₁.gt 0) (U₂.gt 0) ((Over.pullback (thick R I 0)).map a).left f := by
    intro e f
    induction e with
    | zero => exact id
    | succ e ih => exact fun k => ih (acts_down U₁ U₂ a k)
  refine ⟨h 0, fun e => ⟨t e, ?_, hi e⟩⟩
  rw [← acts_unique _ _ (down e _ (acts_of_torusHomOf _ _ _ (ht e) (hi e)))
    (acts_of_torusHomOf _ _ _ (ht 0) (hi 0))]
  exact ht e
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupHomExtOfInducedMaps
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

namespace GlobalTheory.Mum.Two

theorem torusHomOf_iff_appTop {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X'] (h : X' → X)
    (t : splitTorus S X ⟶ splitTorus S X') : TorusHomOf h t ↔
      ∀ χ, t.left.appTop.hom (charUnit S X' χ).val = (charUnit S X (h χ)).val := by
  refine forall_congr' fun χ => ?_
  have : (res (fun x _ => show t.left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial)
      (pullU t.left ⊤ (charUnit S X' χ)) : Γ((splitTorus S X).left, ⊤)ˣ).val =
      t.left.appTop.hom (charUnit S X' χ).val := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [← this, Units.ext_iff]

theorem torusHomOf_unique {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X'] {h : X' → X}
    {t t' : splitTorus S X ⟶ splitTorus S X'} (ht : TorusHomOf h t) (ht' : TorusHomOf h t') : t = t' := by
  refine (splitTorusPointsEquiv S X' _).injective (MonoidHom.ext fun χ => Units.ext ?_)
  obtain ⟨χ, rfl⟩ := Multiplicative.ofAdd.surjective χ
  rw [splitTorusPointsEquiv_val, splitTorusPointsEquiv_val, (torusHomOf_iff_appTop _ _).1 ht,
    (torusHomOf_iff_appTop _ _).1 ht']

theorem hom_eq_of_over₀_onTorus : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G), ∀ (g g' : G ⟶ G) (b : D'.toPre.P.A ⟶ D.toPre.P.A) (h : D.toPre.X → D'.toPre.X), IsMonHom g → IsMonHom g' → Over₀ U'.toUnifPre U.toUnifPre g b → Over₀ U'.toUnifPre U.toUnifPre g' b → OnTorus U'.toUnifPre U.toUnifPre g h → OnTorus U'.toUnifPre U.toUnifPre g' h → g = g' := by
  intro R _ _ _ hR D A G _ _ hG U D' A' U' g g' b h hg hg' q₁ q₂ i₁ i₂
  have : IsNoetherianRing R := hR.1.1
  have : Smooth G.hom := hG.smooth
  have : GeometricallyConnected G.hom := hG.geomConnected
  have : IsSeparated G.hom := hG.separated
  refine GlobalTheory.AbelianPartIso.hom_eq_of_map_eq (IsLocalRing.maximalIdeal_le_jacobson _) G g g' fun e => ?_
  obtain ⟨t, ht, j₁⟩ := i₁ e
  obtain ⟨t', ht', j₂⟩ := i₂ e
  have htt : t = t' := torusHomOf_unique ht ht'
  have := (U.gt e).i_hom
  exact GlobalTheory.LinearUnifIso.hom_ext_torus (U.gt e) (U'.gt e) GlobalTheory.globalFns_holds _ _
    ((q₁ e).trans (q₂ e).symm) (j₁.trans (htt ▸ j₂.symm))

end GlobalTheory.Mum.Two
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupHomInducedMapsUnique
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.Mum.Two

theorem over₀_onTorus_unique : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂), (∀ b b' : D₁.toPre.P.A ⟶ D₂.toPre.P.A, Over₀ U₁ U₂ a b → Over₀ U₁ U₂ a b' → b = b') ∧ ∀ h h' : D₂.toPre.X → D₁.toPre.X, OnTorus U₁ U₂ a h → OnTorus U₁ U₂ a h' → h = h' := by
  intro R _ _ I hR D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ U₁ U₂ a
  refine ⟨fun b b' hb hb' => ?_, fun h h' hh hh' => ?_⟩
  · obtain ⟨_, -, -, _⟩ := hR
    have := D₁.toPre.P.isAb.smooth
    have := D₁.toPre.P.isAb.geomConnected
    have := D₁.toPre.P.isAb.proper
    have := D₂.toPre.P.isAb.proper
    refine (sec_eq_zero_and_hom_eq_of_thickenings R I (IsAdicComplete.le_jacobson_bot I) D₁.toPre.P.A).2 _ b b'
      fun e => ?_
    have := (U₁.gt e).q_flat
    have := (U₁.gt e).q_surj
    have := (U₁.gt e).q_affine
    have := FlatQuotient.epi_of_flat_surjective (U₁.gt e).q
    have k := congrArg (fun q => q.left ≫ pullback.fst D₂.toPre.P.A.hom (thick R I e))
      ((cancel_epi _).1 ((hb e).symm.trans (hb' e)))
    exact (pullback.lift_fst _ _ _).symm.trans (k.trans (pullback.lift_fst _ _ _))
  · have := hR.2.2.2
    have := EndTorus.connectedSpace_thickening I 0
    have : Mono (U₂.gt 0).i := by
      have : Mono (η[thickObj R I 0 D₂.toPre.P.A]) := ⟨fun _ _ _ => toUnit_unique _ _⟩
      exact (MorphismProperty.monomorphisms _).of_isPullback (U₂.gt 0).isKernel.flip (.infer_property _)
    obtain ⟨t, ht, e⟩ := hh 0
    obtain ⟨t', ht', e'⟩ := hh' 0
    obtain rfl : t = t' := (cancel_mono _).1 (e.symm.trans e')
    funext χ
    exact SplitTorusHom.charUnit_injective (S := Sp (R ⧸ I ^ (0 + 1)))
      (congrArg Units.val ((ht χ).symm.trans (ht' χ)))

end GlobalTheory.Mum.Two
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupHomPullbackMaps
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.Mum.Two.PullLin

open GlobalTheory.ArcPull GlobalTheory.PullLinear
open GlobalTheory.PsiEvenPull (proj)

theorem act_proj₂ {S S' : Scheme.{0}} (f : S' ⟶ S) {A B : Over S} {A' B' : Over S'}
    (e : A' ⟶ (Over.pullback f).obj A) (e₂ : B' ⟶ (Over.pullback f).obj B) {u : A ⟶ B} {u' : A' ⟶ B'}
    (h : u' ≫ e₂ = e ≫ (Over.pullback f).map u) :
    u'.left ≫ e₂.left ≫ pullback.fst B.hom f = (e.left ≫ pullback.fst A.hom f) ≫ u.left := by
  have h1 : u'.left ≫ e₂.left = e.left ≫ ((Over.pullback f).map u).left := congrArg (·.left) h
  rw [← Category.assoc, h1, Category.assoc, map_left_fst, Category.assoc]

theorem torusHomOf_iff' {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X'] (h : X' → X)
    (t : splitTorus S X ⟶ splitTorus S X') :
    TorusHomOf h t ↔ ∀ (Z : Scheme.{0}) (r : Z ⟶ (splitTorus S X).left) (z : Z) (χ : X'),
      gm (r ≫ t.left) z ⊤ (charUnit S X' χ) = gm r z ⊤ (charUnit S X (h χ)) := by
  constructor
  · intro H Z r z χ
    rw [← H χ]
    exact ((gm_res r z (V := ⊤) _ trivial _).trans (gm_pull r t.left z ⊤ trivial _)).symm
  · intro H χ
    refine unit_ext fun z _ => ?_
    rw [← H]
    exact (gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _) t.left z ⊤ trivial _)

set_option maxHeartbeats 800000 in

theorem linPull : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R') (φ : R →+* R') (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : Unif I D₁ A₁ G₁) (U₂ : Unif I D₂ A₂ G₂) (D₁' D₂' : DegData R' I') (A₁' A₂' : PolAV (Sp (FractionRing R'))) (hD₁ : IsPullDeg φ D₁.toPre D₁'.toPre) (hD₂ : IsPullDeg φ D₂.toPre D₂'.toPre) (U₁' : Unif I' D₁' A₁' ((Over.pullback (specOf φ)).obj G₁)) (U₂' : Unif I' D₂' A₂' ((Over.pullback (specOf φ)).obj G₂)), IsPullUnif φ hD₁ (Iso.refl _) U₁ U₁' → IsPullUnif φ hD₂ (Iso.refl _) U₂ U₂' → ∀ (a : G₁ ⟶ G₂) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (h : D₂.toPre.X →+ D₁.toPre.X), Lin U₁.toUnifPre U₂.toUnifPre a b h → ∃ (b' : D₁'.toPre.P.A ⟶ D₂'.toPre.P.A) (h' : D₂'.toPre.X →+ D₁'.toPre.X), Lin U₁'.toUnifPre U₂'.toUnifPre ((Over.pullback (specOf φ)).map a) b' h' ∧ b' ≫ hD₂.e.hom = hD₁.e.hom ≫ (Over.pullback (specOf φ)).map b ∧ ∀ χ, hD₁.xe (h' χ) = h (hD₂.xe χ) := by
  intro R R' _ _ _ _ I I' φ D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ U₁ U₂ D₁' D₂' A₁' A₂' hD₁ hD₂ U₁' U₂' hU₁ hU₂ a b h hL
  obtain ⟨homA, homB, hq0, hi0⟩ := hL
  obtain ⟨_wL₁, -, _he₁, -, H₁⟩ := (isPullUnif_iff_stalks R R' I I' φ D₁ D₁' hD₁ A₁ A₁' G₁ _ (Iso.refl _) U₁ U₁').1 hU₁
  obtain ⟨_wL₂, -, _he₂, -, H₂⟩ := (isPullUnif_iff_stalks R R' I I' φ D₂ D₂' hD₂ A₂ A₂' G₂ _ (Iso.refl _) U₂ U₂').1 hU₂
  choose h₁ hf₁ hpt₁ _hw₁ using H₁
  choose h₂ hf₂ hpt₂ _hw₂ using H₂
  have := hD₁.e_hom
  have := hD₂.e_hom
  obtain ⟨b', homB', hB⟩ : ∃ b' : D₁'.toPre.P.A ⟶ D₂'.toPre.P.A, IsMonHom b' ∧
      b' ≫ hD₂.e.hom = hD₁.e.hom ≫ (Over.pullback (specOf φ)).map b :=
    ⟨hD₁.e.hom ≫ (Over.pullback (specOf φ)).map b ≫ hD₂.e.inv, inferInstance, by simp⟩
  obtain ⟨h', hx⟩ : ∃ h' : D₂'.toPre.X →+ D₁'.toPre.X, ∀ χ, hD₁.xe (h' χ) = h (hD₂.xe χ) :=
    ⟨hD₁.xe.symm.toAddMonoidHom.comp (h.comp hD₂.xe.toAddMonoidHom), fun χ => hD₁.xe.apply_symm_apply _⟩
  have hG : (Over.pullback (specOf φ)).map a ≫ (Iso.refl ((Over.pullback (specOf φ)).obj G₂)).hom =
      (Iso.refl ((Over.pullback (specOf φ)).obj G₁)).hom ≫ (Over.pullback (specOf φ)).map a := by simp
  have hact : ∀ e : ℕ, ((Over.pullback (thick R' I' e)).map ((Over.pullback (specOf φ)).map a)).left ≫ h₂ e =
      h₁ e ≫ ((Over.pullback (thick R I e)).map a).left := by
    intro e
    have hf' : h₂ e ≫ pullback.fst G₂.hom (thick R I e) =
        pullback.fst ((Over.pullback (specOf φ)).obj G₂).hom (thick R' I' e) ≫
          (Iso.refl ((Over.pullback (specOf φ)).obj G₂)).hom.left ≫ pullback.fst G₂.hom (specOf φ) := hf₂ e
    have hf₁' : h₁ e ≫ pullback.fst G₁.hom (thick R I e) =
        pullback.fst ((Over.pullback (specOf φ)).obj G₁).hom (thick R' I' e) ≫
          (Iso.refl ((Over.pullback (specOf φ)).obj G₁)).hom.left ≫ pullback.fst G₁.hom (specOf φ) := hf₁ e
    have : IsClosedImmersion (thick R I e) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    have hmono : Mono (pullback.fst G₂.hom (thick R I e)) := inferInstance
    rw [← cancel_mono (pullback.fst G₂.hom (thick R I e)), Category.assoc, hf', Category.assoc, map_left_fst,
      ← Category.assoc (h₁ e), hf₁',
      ← Category.assoc (((Over.pullback (thick R' I' e)).map ((Over.pullback (specOf φ)).map a)).left), map_left_fst,
      Category.assoc, act_proj₂ _ (Iso.refl _).hom (Iso.refl _).hom hG]
    simp only [Category.assoc]
  have k : ∀ {S : Type} [CommRing S] [IsDomain S] {J : Ideal S} {E : DegPre S} {e : ℕ}
      {K : Over (Spec (CommRingCat.of S))} [GrpObj K] [IsCommMonObj K] (g : GtCoord J E e K)
      {B : Over (Spec (CommRingCat.of S))} (u : E.P.A ⟶ B), (g.q ≫ (Over.pullback (thick S J e)).map u).left ≫
        pullback.fst B.hom (thick S J e) = g.pG.left ≫ u.left := by
    intro S _ _ J E e K _ _ g B u
    rw [Over.comp_left, Category.assoc, map_left_fst, pG_left, Category.assoc]
  have hB' := act_proj₂ (specOf φ) hD₁.e.hom hD₂.e.hom hB
  have k₂ : ∀ e, (Over.map (thick R' I' e)).map ((Over.pullback (thick R' I' e)).map ((Over.pullback (specOf φ)).map a)) ≫
      (U₂'.gt e).pG = (U₁'.gt e).pG ≫ b' := by
    intro e
    have k₁ : ((Over.pullback (thick R I e)).map a).left ≫ (U₂.gt e).pG.left =
        (U₁.gt e).pG.left ≫ b.left := by
      rw [← k, ← hq0 e]
      exact (Category.assoc _ _ _).symm
    refine ext_of_iso_pullback _ hD₂.e ?_
    change (((Over.pullback (thick R' I' e)).map ((Over.pullback (specOf φ)).map a)).left ≫ (U₂'.gt e).pG.left) ≫ _ =
      ((U₁'.gt e).pG.left ≫ b'.left) ≫ _
    rw [Category.assoc, Category.assoc, hB', (hpt₂ e).1,
      ← Category.assoc (U₁'.gt e).pG.left, (hpt₁ e).1, ← Category.assoc, hact, Category.assoc,
      Category.assoc, k₁]
  have hq : ∀ e : ℕ, (Over.pullback (thick R' I' e)).map ((Over.pullback (specOf φ)).map a) ≫ (U₂'.gt e).q =
      (U₁'.gt e).q ≫ (Over.pullback (thick R' I' e)).map b' := by
    intro e
    refine ext_of_pullback _ ?_
    rw [k, Over.comp_left, Category.assoc]
    exact congrArg (·.left) (k₂ e)
  refine ⟨b', h', ⟨inferInstance, homB', hq, fun e => ?_⟩, hB, hx⟩
  obtain ⟨t, ht, hi⟩ := hi0 e
  have hk : ((U₁'.gt e).i ≫ (Over.pullback (thick R' I' e)).map ((Over.pullback (specOf φ)).map a)) ≫ (U₂'.gt e).q =
      toUnit _ ≫ η[thickObj R' I' e D₂'.toPre.P.A] := by
    rw [Category.assoc, hq, ← Category.assoc, (U₁'.gt e).isKernel.w, Category.assoc,
      IsMonHom.one_hom]
  have hi' := (U₂'.gt e).isKernel.lift_fst _ _ hk
  generalize (U₂'.gt e).isKernel.lift _ _ hk = t' at hi'
  refine ⟨t', ?_, hi'.symm⟩
  obtain ⟨s, τ, hτ⟩ := exists_point (U₁.gt e) (U₁'.gt e) (hpt₁ e).1 ((hpt₁ e).2 0).1 (𝟙 _)
  have hτ' : ((τ ≫ t) ≫ (U₂.gt e).i).left = (t' ≫ (U₂'.gt e).i).left ≫ h₂ e := by
    rw [Category.assoc, ← hi, ← Category.assoc, Over.comp_left, hτ, hi', Category.id_comp,
      Over.comp_left, Category.assoc, Category.assoc, hact]
  intro χ
  refine unit_ext fun z _ => ?_
  have e₁ := char_eq (U₂.gt e) (U₂'.gt e) hD₂.w ((hpt₂ e).2 χ).1 ((hpt₂ e).2 χ).2 t' (τ ≫ t) hτ' z
  have e₂ := char_eq (U₁.gt e) (U₁'.gt e) hD₁.w ((hpt₁ e).2 (h' χ)).1 ((hpt₁ e).2 (h' χ)).2 (𝟙 _) τ hτ z
  have e₃ := (torusHomOf_iff' _ t).1 ht _ τ.left z (hD₂.xe χ)
  rw [hx] at e₂
  refine ((gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _) t'.left z ⊤ trivial _)).trans ?_
  rw [Category.id_comp]
  exact e₁.symm.trans (e₃.trans e₂)

end GlobalTheory.Mum.Two.PullLin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformiserOrderEqOfAssociatedStalkImageStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformiserOrder_eq_of_associated_stalkImage : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] (M : RatModel o' Ω) (x : M.Z) (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z), ξ (IsLocalRing.closedPoint T.V) ⤳ x → ∀ (R : Type) [CommRing R] (j : M.Z.presheaf.stalk x →+* R) (V' : Type) [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] (h : T.V →+* V') (g' : R →+* V'), Function.Injective h → Irreducible (h T.ϖ) → spMap g' ≫ (spMap j ≫ M.Z.fromSpecStalk x) = spMap h ≫ ξ → ∀ (a : M.Z.presheaf.stalk x) (k : ℕ), Associated (g' (j a)) (h T.ϖ ^ k) → UOrdEq M T ξ (M.stalkHom x a) k := by
  first | exact @GlobalTheory.UPoinc.uOrdEq_stalkHom_of_associated | exact GlobalTheory.UPoinc.uOrdEq_stalkHom_of_associated | (intros; apply GlobalTheory.UPoinc.uOrdEq_stalkHom_of_associated <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversalFirstOrderDeformationStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.universal_first_order_deformation : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), 1 ≤ Dw.p + Dw.q → ∃ X : Sp (TrivSqZeroExt K (GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K)) ⟶ Xo.X, X ≫ Xo.s = sOf c _ ∧ spMap (TrivSqZeroExt.fstHom c.F K (GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K)).toRingHom ≫ X = y.x ∧ ∀ M : GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K, GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y (spMap (GlobalTheory.FlagTan.dir c M).toRingHom ≫ X) M := by
  first | exact @GlobalTheory.FlagTan.KSUniv.ksUniv | exact GlobalTheory.FlagTan.KSUniv.ksUniv | (intros; apply GlobalTheory.FlagTan.KSUniv.ksUniv <;> assumption)
end

