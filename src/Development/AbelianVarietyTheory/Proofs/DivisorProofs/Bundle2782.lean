import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2773
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2631
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1255
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CrossRelationGivesConvolutionRelation
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0048
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2764
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2721
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2464
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionCellFl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1117
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1207
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2683
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2344
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartIsOpenImmersionOverBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2569
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2684
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2511
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2651
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2685

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CarriedFlagTriangularFrame
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical
open GlobalTheory.FlagCell GlobalTheory.FlagConnect

namespace GlobalTheory.FlagCell

theorem pullbackComp_congr_app_pullbackSections {B Y T : Scheme.{0}} (π : Y ⟶ B) (g' : T ⟶ Y) (g : T ⟶ B)
    (w : g' ≫ π = g) (E : B.Modules) {U : B.Opens} {V : Y.Opens} {V' : T.Opens} (hV : V ≤ π ⁻¹ᵁ U)
    (h : V' ≤ g' ⁻¹ᵁ V) (h' : V' ≤ g ⁻¹ᵁ U) (t : Γ(E, U)) :
    ((Scheme.Modules.pullbackComp g' π).hom.app E ≫ (Scheme.Modules.pullbackCongr w).hom.app E).app V'
      (QCoh.pullbackSections g' _ h (QCoh.pullbackSections π E hV t)) = QCoh.pullbackSections g E h' t := by
  subst w
  rw [← Vert.DivPull.pullbackComp_inv_app g' π E hV h h' t, QCoh.app_app, Iso.inv_hom_id_app_assoc]
  rfl

theorem spans_pullCol_of_carries : ∀ (B Y T : Scheme.{0}) (π : Y ⟶ B) (ι : Type) (r : ι → ℕ) (E : ι → B.Modules) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)) (g' : T ⟶ Y) (g : T ⟶ B) (w : g' ≫ π = g) (fl' : ∀ a, Vert.Flag ((Scheme.Modules.pullback g).obj (E a)) (r a)), Carries π E r fl g' g w fl' → ∀ (U : B.Opens) (a : ι) (e : Fin (r a) → Γ(E a, U)) (V : Y.Opens) (hV : V ≤ π ⁻¹ᵁ U) (M : Matrix (Fin (r a)) (Fin (r a)) Γ(Y, V)) (V' : T.Opens) (h : V' ≤ g' ⁻¹ᵁ V) (h' : V' ≤ g ⁻¹ᵁ U), Spans (fl a) V (pullCol π e hV M) → Spans (fl' a) V' (pullCol g e h' (M.map (g'.appLE V V' h).hom)) := by
  intro B Y T π ι r E fl g' g w fl' hC U a e V hV M V' h h' hS l
  obtain ⟨s, hs, hsι⟩ := hS l
  obtain ⟨φ, hφ⟩ := hC a l
  haveI := ((fl a).isVB l).isQuasicoherent
  refine ⟨fun j => φ.hom.app V' (QCoh.pullbackSections g' _ h (s j)), ?_, fun j => ?_⟩
  · have h1 := (hs.pullback g').res h
    simp only [Twist.resM, QCoh.res_pullbackSections] at h1
    exact h1.map_iso φ.hom
  · dsimp only
    rw [QCoh.app_app, hφ, ← QCoh.app_app, QCoh.pullback_map_app_pullbackSections, hsι j]
    simp only [pullCol, map_sum, QCoh.pullbackSections_smul, Scheme.Modules.Hom.app_smul, Matrix.map_apply,
      pullbackComp_congr_app_pullbackSections π g' g w (E a) hV h h']

end GlobalTheory.FlagCell
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CarriedSectionsCrossRelationOfHom
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.FieldBaseChange

noncomputable section
namespace GlobalTheory.Mum.Two

theorem whisker_comm₂ {C : Type*} [Category C] [CartesianMonoidalCategory C] (T : C) {X₁ X₂ Y₁ Y₂ : C}
    (g₁ : X₁ ⟶ Y₁) (g₂ : X₂ ⟶ Y₂) (a : X₁ ⟶ X₂) (b : Y₁ ⟶ Y₂) (h : a ≫ g₂ = g₁ ≫ b) :
    T ◁ a ≫ lift (fst _ _) (snd _ _ ≫ g₂) = lift (fst _ _) (snd _ _ ≫ g₁) ≫ T ◁ b := by
  ext <;> simp [h]

theorem crossH_at {R : Type} [CommRing R] [IsDomain R] {A₁ A₂ : PolAV (Sp (FractionRing R))} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {c : A₁.A ⟶ A₂.A} {j j' : ℕ} {t₁ t₂ : SecA A₂ F j} {t₁' t₂' : SecA A₁ F j'}
    (h : CrossH c t₁ t₂ t₁' t₂') {Z : Scheme.{0}} (r : Z ⟶ (TFK (R := R) F ⊗ A₁.A).left) (z : Z) {J₁ J₂}
    (hJ₁ : Good A₁.L z J₁) (hJ₂ : Good A₂.L z J₂) :
    sA t₁ (r ≫ (TFK (R := R) F ◁ c).left) z J₂ * sA t₂' r z J₁ =
      sA t₂ (r ≫ (TFK (R := R) F ◁ c).left) z J₂ * sA t₁' r z J₁ := by
  have e : ∀ t : SecA A₁ F j', sA t r z J₁ = (r.stalkMap z).hom (sA t (𝟙 _) (r z) (fun ψ => J₁ (r ≫ ψ))) :=
    fun t => by
      have := GlobalTheory.UU.IntExp.sval_comp (L := A₁.L) (φ := fun _ : Fin 1 => (snd (TFK (R := R) F) A₁.A).left)
        (ε := fun _ => ((j' : ℕ) : ℤ)) t (𝟙 _) r z J₁ hJ₁
      rw [Category.comp_id] at this
      exact this
  have e' : ∀ t : SecA A₂ F j, sA t (r ≫ (TFK (R := R) F ◁ c).left) z J₂ =
      (r.stalkMap z).hom (sA t (TFK (R := R) F ◁ c).left (r z) (fun ψ => J₂ (r ≫ ψ))) :=
    fun t => GlobalTheory.UU.IntExp.sval_comp (L := A₂.L) (φ := fun _ : Fin 1 => (snd (TFK (R := R) F) A₂.A).left)
        (ε := fun _ => ((j : ℕ) : ℤ)) t _ r z J₂ hJ₂
  rw [e, e, e', e', ← map_mul, ← map_mul, h (r z) _ _ (fun ψ => hJ₁ (r ≫ ψ)) (fun ψ => hJ₂ (r ≫ ψ))]

theorem carried_cross_of_hom : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂) (c : A₁.A ⟶ A₂.A), Gen₀ U₁ U₂ a c → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (w₁ : W0 U₁) (w₂ : W0 U₂), w₁.IsGen → w₂.IsGen → ∀ (j j' : ℕ) (t₁ t₂ : SecA A₂ F j) (t₁' t₂' : SecA A₁ F j') (σ₁ σ₂ : U₂.SecGF F j) (σ₁' σ₂' : U₁.SecGF F j'), MixedConv.Carried w₂ j t₁ σ₁ → MixedConv.Carried w₂ j t₂ σ₂ → MixedConv.Carried w₁ j' t₁' σ₁' → MixedConv.Carried w₁ j' t₂' σ₂' → CrossH c t₁ t₂ t₁' t₂' → ∀ (y : (UnifPre.GF (G := G₁) F).left) (J₁ J₂), Good U₁.LG.L y J₁ → Good U₂.LG.L y J₂ → sval σ₁ (TFK (R := R) F ◁ (Over.pullback (jK R)).map a).left y J₂ * sval σ₂' (𝟙 _) y J₁ = sval σ₂ (TFK (R := R) F ◁ (Over.pullback (jK R)).map a).left y J₂ * sval σ₁' (𝟙 _) y J₁ := by
  intro R _ _ I D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ U₁ U₂ a c hc F _ _ w₁ w₂ _ _ j j' t₁ t₂ t₁' t₂' σ₁ σ₂ σ₁' σ₂'
    h₁ h₂ h₁' h₂' h y J₁ J₂ hJ₁ hJ₂
  have hm : (TFK (R := R) F ◁ (Over.pullback (jK R)).map a).left ≫ (U₂.genF F).left =
      (U₁.genF F).left ≫ (TFK (R := R) F ◁ c).left :=
    congrArg (fun q => q.left) (whisker_comm₂ (TFK (R := R) F) U₁.gen.hom U₂.gen.hom _ _ hc)
  obtain ⟨J'₁, hJ'₁⟩ := GlobalTheory.UT.CoefBasic.exists_good' A₁.isLB y
  obtain ⟨J'₂, hJ'₂⟩ := GlobalTheory.UT.CoefBasic.exists_good' A₂.isLB y
  have a₁ := GlobalTheory.BoxExpansion.isoRel_val h₁ (TFK (R := R) F ◁ (Over.pullback (jK R)).map a).left y hJ'₂ hJ₂
  have a₂ := GlobalTheory.BoxExpansion.isoRel_val h₂ (TFK (R := R) F ◁ (Over.pullback (jK R)).map a).left y hJ'₂ hJ₂
  have a₃ := GlobalTheory.BoxExpansion.isoRel_val h₁' (𝟙 _) y hJ'₁ hJ₁
  have a₄ := GlobalTheory.BoxExpansion.isoRel_val h₂' (𝟙 _) y hJ'₁ hJ₁
  have a₅ := crossH_at h (U₁.genF F).left y hJ'₁ hJ'₂
  rw [Category.comp_id, hm] at a₁ a₂
  rw [Category.comp_id, Category.id_comp (U₁.genF F).left] at a₃ a₄
  rw [a₁, a₂, a₃, a₄]
  exact (_root_.mul_mul_mul_comm _ _ _ _).trans ((congrArg (_ * ·) a₅).trans (_root_.mul_mul_mul_comm _ _ _ _))

end GlobalTheory.Mum.Two
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CarriesUnitSectionRigidificationUnit
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum

theorem stalkOf_cpt_bijective (W : Type) [CommRing W] [IsLocalRing W] : Function.Bijective (stalkOf (cpt W)) := by
  have e : stalkOf (cpt W) = (stalkClosedPointIso (.of W)).inv.hom := by
    have h := ΓSpecIso_hom_stalkClosedPointIso_inv (CommRingCat.of W)
    have h' : (stalkClosedPointIso (.of W)).inv = (Scheme.ΓSpecIso (CommRingCat.of W)).inv ≫
        (Sp W).presheaf.germ ⊤ (cpt W) trivial := by
      rw [Iso.eq_inv_comp]; exact h
    rw [h']; rfl
  rw [e]
  exact (stalkClosedPointIso (.of W)).symm.commRingCatIsoToRingEquiv.bijective

theorem exists_unit_stalkOf (W : Type) [CommRing W] [IsLocalRing W] (x : ((Sp W).presheaf.stalk (cpt W))ˣ) :
    ∃ ε : Wˣ, stalkOf (cpt W) (ε : W) = x.val := by
  let e := RingEquiv.ofBijective _ (stalkOf_cpt_bijective W)
  exact ⟨Units.map e.symm.toMonoidHom x, e.apply_symm_apply x.val⟩

theorem gs_scal_section {W : Type} [CommRing W] {Y : Scheme.{0}} (p : Y ⟶ Sp W) (e : Sp W ⟶ Y) (he : e ≫ p = 𝟙 _)
    (z : Sp W) (u : W) : gs e z ⊤ (scal p u) = stalkOf z u := by
  have h := gs_pull e p z ⊤ trivial ((Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom u)
  rw [he] at h
  exact h.trans (gs_eq (𝟙 _) z ⊤ trivial _)

theorem gw_val_indep {X X' Y Y' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F))
    (hw : w.IsGen) {s : Y ⟶ X} {s' : Y' ⟶ X'} (t : LB.Gen (L.pull s)) (ht : t.IsGen) (t' : LB.Gen (L'.pull s'))
    (ht' : t'.IsGen) (r : Z ⟶ Y) (r' : Z ⟶ Y') (e : Z ⟶ X') (he' : r' ≫ s' = e) (he : r ≫ s = e ≫ F) (z : Z)
    {I J : (Z ⟶ X) → L.ι} {I' J' : (Z ⟶ X') → L'.ι} (hI : Good L z I) (hJ : Good L z J) (hI' : Good L' z I')
    (hJ' : Good L' z J') :
    gw w e z (J (e ≫ F)) (J' e) * val t' r' z J' * (val t r z J)⁻¹ =
      gw w e z (I (e ≫ F)) (I' e) * val t' r' z I' * (val t r z I)⁻¹ := by
  have a := (isGen_iff w).1 hw Z e z (J (e ≫ F)) (I (e ≫ F)) (J' e) (I' e) (hJ (e ≫ F)) (hI (e ≫ F)) (hJ' e) (hI' e)
  have b : val t r z J = _ * val t r z I := gen_trans ht r z (hJ.mem _ r) (hI.mem _ r)
  have c : val t' r' z J' = _ * val t' r' z I' := gen_trans ht' r' z (hJ'.mem _ r') (hI'.mem _ r')
  rw [trF, Fintype.prod_unique, zpow_one] at b c
  subst he'
  rw [he] at b
  rw [a, b, c]
  generalize gm ((r' ≫ s') ≫ F) z _ _ = A
  generalize gm (r' ≫ s') z _ _ = B
  rw [mul_inv]
  generalize gw w _ _ _ _ = C
  generalize val t' r' z I' = D
  generalize (val t r z I)⁻¹ = E
  have : A * B⁻¹ * C * (B * D) * (A⁻¹ * E) = (A * A⁻¹) * (B * B⁻¹) * (C * D * E) := by ac_rfl
  rw [this]; simp

theorem Trait.carries_unit : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ) (u : W) (σ' : H0 T.U.LG.L k) (σ : SecK C.P.L.L T.β k), T.Carries u σ' σ → ∃ ε : Wˣ, ∀ J J', Good C.P.L.L (cpt W) J → Good T.U.LG.L (cpt W) J' → sval σ (unitW T.G) (cpt W) J * (val T.U.LG.rig (idW W) (cpt W) J').val ^ k = stalkOf (cpt W) (u * ε) * sval σ' (unitW T.G) (cpt W) J' * (val C.P.L.rig T.ξ (cpt W) J).val ^ k := by
  intro R _ _ _ D C W _ _ _ T k u σ' σ h
  obtain ⟨I, hI, -⟩ := exists_good C.P.L.L C.P.L.isLB (cpt W) (K := PEmpty.{1}) PEmpty.elim PEmpty.elim
    (fun a => a.elim) (fun a => a.elim)
  obtain ⟨I', hI', -⟩ := exists_good T.U.LG.L T.U.LG.isLB (cpt W) (K := PEmpty.{1}) PEmpty.elim PEmpty.elim
    (fun a => a.elim) (fun a => a.elim)
  have he : T.ξ ≫ eSec C.G = unitW T.G ≫ T.β := (PullGtPf.IsGrpPullback.one_left T.cart).symm
  obtain ⟨ε, hε⟩ := exists_unit_stalkOf W ((gw T.ℓ (unitW T.G) (cpt W) (I (unitW T.G ≫ T.β)) (I' (unitW T.G)) *
    val T.U.LG.rig (idW W) (cpt W) I' * (val C.P.L.rig T.ξ (cpt W) I)⁻¹) ^ k)
  refine ⟨ε, fun J J' hJ hJ' => ?_⟩
  have key := gw_val_indep T.ℓ T.ℓ_gen C.P.L.rig C.P.L.rigGen T.U.LG.rig T.U.LG.rigGen T.ξ (idW W) (unitW T.G)
    (Category.id_comp _) he (cpt W) hI hJ hI' hJ'
  rw [← key] at hε
  rw [h _ (unitW T.G) (cpt W) J J' hJ hJ', gs_scal_section T.G.hom (unitW T.G) (Over.w η[T.G]), map_mul, hε]
  generalize gw T.ℓ _ _ _ _ = A
  generalize val T.U.LG.rig _ _ _ = B
  generalize val C.P.L.rig _ _ _ = E
  have : (A * B * E⁻¹) ^ k * E ^ k = A ^ k * B ^ k := by rw [← mul_pow, ← mul_pow, inv_mul_cancel_right]
  have := congrArg Units.val this
  simp only [Units.val_mul, Units.val_pow_eq_pow_val] at this ⊢
  linear_combination (-(stalkOf (cpt W) u * sval σ' (unitW T.G) (cpt W) J')) * this

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechLineBundlePullTrivialOfPointwiseGenerator
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PtExt

theorem triv_pull_of_isPtGen : ∀ (R : Type) [CommRing R] (X Y : Over (Sp R)) (L : LB X.left), L.IsLB →
    ∀ (q : Y ⟶ X) (t : ∀ (E : Type) [CommRing E] [Algebra R E], Pt Y E → L.ι → E), IsPtGen L q t →
    GlobalTheory.AbLaw.Triv (L.pull q.left) := by
  intro R _ X Y L _ q t ht
  obtain ⟨hu, hn, hg⟩ := ht
  have hmul : ∀ {D : Type} [CommRing D] (x : Sp D ⟶ Y.left) (U : Y.left.Opens), ⊤ ≤ x ⁻¹ᵁ U →
      ∀ a b : Γ(Y.left, U), evU x U (a * b) = evU x U a * evU x U b := by
    intro D _ x U h a b; unfold evU; rw [dif_pos h, dif_pos h, dif_pos h, map_mul]
  have hone : ∀ {D : Type} [CommRing D] (x : Sp D ⟶ Y.left) (U : Y.left.Opens), ⊤ ≤ x ⁻¹ᵁ U →
      evU x U (1 : Γ(Y.left, U)) = 1 := by
    intro D _ x U h; unfold evU; rw [dif_pos h, map_one]
  have hch : ∀ (j : PUnit → L.ι) {E : Type} [CommRing E] [Algebra R E] (z : Pt Y E),
      ⊤ ≤ z.left ⁻¹ᵁ (L.pull q.left).U j → ⊤ ≤ (z ≫ q).left ⁻¹ᵁ L.U (j PUnit.unit) :=
    fun j E _ _ z h p hp ↦ LB.wchart_le L (K := PUnit) (fun _ ↦ q.left) j PUnit.unit (h hp)
  have huniq : ∀ (U : Y.left.Opens) (f : Fn0 Y), (∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E']
      [Algebra R E'] (ψ : E →ₐ[R] E') (z : Pt Y E), ⊤ ≤ z.left ⁻¹ᵁ U → f E' (spOver ψ ≫ z) = ψ (f E z)) →
      ∀ c c' : Γ(Y.left, U), (∀ (E : Type) [CommRing E] [Algebra R E] (z : Pt Y E), ⊤ ≤ z.left ⁻¹ᵁ U →
        evU z.left U c = f E z) → (∀ (E : Type) [CommRing E] [Algebra R E] (z : Pt Y E), ⊤ ≤ z.left ⁻¹ᵁ U →
        evU z.left U c' = f E z) → c = c' :=
    fun U f hf c c' hc hc' ↦ (GlobalTheory.T.exists_unique_section_of_natural_pointwise_function R Y U f hf).unique hc hc'
  have hnat : ∀ j : PUnit → L.ι, ∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E']
      (ψ : E →ₐ[R] E') (z : Pt Y E), ⊤ ≤ z.left ⁻¹ᵁ (L.pull q.left).U j →
      t E' (spOver ψ ≫ z) (j PUnit.unit) = ψ (t E z (j PUnit.unit)) :=
    fun j E _ _ E' _ _ ψ z h ↦ hn E E' ψ z _ (hch j z h)
  have hnatI : ∀ j : PUnit → L.ι, ∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E']
      (ψ : E →ₐ[R] E') (z : Pt Y E), ⊤ ≤ z.left ⁻¹ᵁ (L.pull q.left).U j →
      Ring.inverse (t E' (spOver ψ ≫ z) (j PUnit.unit)) = ψ (Ring.inverse (t E z (j PUnit.unit))) := by
    intro j E _ _ E' _ _ ψ z h
    rw [hnat j E E' ψ z h]
    obtain ⟨u, hu'⟩ := hu E z _ (hch j z h)
    rw [← hu', Ring.inverse_unit]
    have e : ψ (u : E) = ((Units.map (ψ : E →* E') u : E'ˣ) : E') := rfl
    rw [e, Ring.inverse_unit]
    rfl
  have ex := fun j : PUnit → L.ι ↦
    (GlobalTheory.T.exists_unique_section_of_natural_pointwise_function R Y ((L.pull q.left).U j) (fun E _ _ z ↦ t E z (j PUnit.unit)) (hnat j)).exists
  have exI := fun j : PUnit → L.ι ↦
    (GlobalTheory.T.exists_unique_section_of_natural_pointwise_function R Y ((L.pull q.left).U j) (fun E _ _ z ↦ Ring.inverse (t E z (j PUnit.unit))) (hnatI j)).exists
  choose a ha using ex
  choose b hb using exI
  have hab : ∀ j, a j * b j = 1 := by
    intro j
    refine huniq _ (fun _ _ _ _ ↦ 1) (fun E _ _ E' _ _ ψ z _ ↦ (map_one ψ).symm) _ _ ?_ ?_
    · intro E _ _ z h
      rw [hmul _ _ h, ha j E z h, hb j E z h]
      exact Ring.mul_inverse_cancel _ (hu E z _ (hch j z h))
    · intro E _ _ z h
      exact hone _ _ h
  refine ⟨⟨fun j ↦ ⟨a j, b j, hab j, by rw [mul_comm]; exact hab j⟩⟩, ?_⟩
  intro i j
  apply Units.ext
  have hVi : (L.pull q.left).U i ⊓ (L.pull q.left).U j ≤ (L.pull q.left).U i := inf_le_left
  have hVj : (L.pull q.left).U i ⊓ (L.pull q.left).U j ≤ (L.pull q.left).U j := inf_le_right
  refine huniq ((L.pull q.left).U i ⊓ (L.pull q.left).U j) (fun E _ _ z ↦ t E z (i PUnit.unit))
    (fun E _ _ E' _ _ ψ z h ↦ hnat i E E' ψ z (fun p hp ↦ hVi (h hp))) _ _ ?_ ?_
  · intro E _ _ z h
    have e1 := evalSectionAtPointOrZero_restriction Y.left E z.left _ _ hVi (a i) h
    refine Eq.trans ?_ ((e1.trans (ha i E z (fun p hp ↦ hVi (h hp)))))
    rfl
  · intro E _ _ z h
    have hzi : ⊤ ≤ z.left ⁻¹ᵁ (L.pull q.left).U i := fun p hp ↦ hVi (h hp)
    have hzj : ⊤ ≤ z.left ⁻¹ᵁ (L.pull q.left).U j := fun p hp ↦ hVj (h hp)
    have hij : ⊤ ≤ (z.left ≫ q.left) ⁻¹ᵁ (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) :=
      fun p hp ↦ ⟨hch i z hzi hp, hch j z hzj hp⟩
    rw [Units.val_mul, hmul _ _ h]
    have e2 := evalSectionAtPointOrZero_restriction Y.left E z.left _ _ hVj (a j) h
    have e2' : evU z.left _ (ReciprocityTheory.ChartRestriction.G.Semi.res hVj (⟨a j, b j, hab j, by rw [mul_comm]; exact hab j⟩ :
        Γ(Y.left, (L.pull q.left).U j)ˣ)).val = t E z (j PUnit.unit) :=
      e2.trans (ha j E z hzj)
    have e3 : evU z.left _ ((L.pull q.left).g i j).val =
        evU (z ≫ q).left (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) (L.g (i PUnit.unit) (j PUnit.unit)).val := by
      unfold evU
      rw [dif_pos h]
      have hij' : ⊤ ≤ (z ≫ q).left ⁻¹ᵁ (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) := hij
      rw [dif_pos hij']
      exact (evalAt_pull_g L q.left z.left i j hij h).symm
    rw [e3, e2']
    exact (hg E z (i PUnit.unit) (j PUnit.unit) (hch i z hzi) (hch j z hzj)).symm

end GlobalTheory.PtExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellColumnsFrame
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.FlagZ GlobalTheory.FlagZ.Univ
open GlobalTheory.QCoh (freeModule)
open GlobalTheory.Twist (resM)

namespace GlobalTheory.FlagZ.Univ

theorem isFrame_sum_smul_of_isUnit {X : Scheme.{0}} {F : X.Modules} {U : X.Opens} {n : Type} [Fintype n]
    [DecidableEq n] {e : n → Γ(F, U)} (he : VB.IsFrame e) (M : Matrix n n Γ(X, U)) (hM : IsUnit M) :
    VB.IsFrame fun j => ∑ i, M i j • e i := by
  intro V h
  have hM' : IsUnit ((resG X h).mapMatrix M) := hM.map _
  have hb : Function.Bijective ((resG X h).mapMatrix M).mulVec :=
    ⟨Matrix.mulVec_injective_of_isUnit hM', Matrix.mulVec_surjective_iff_isUnit.2 hM'⟩
  have key : ⇑(Fintype.linearCombination Γ(X, V) fun j => resM F h (∑ i, M i j • e i)) =
      (Fintype.linearCombination Γ(X, V) fun i => resM F h (e i)) ∘
        ((resG X h).mapMatrix M).mulVec := by
    funext a
    simp only [Function.comp_apply, Fintype.linearCombination_apply, map_sum, GlobalTheory.Twist.resM_smul,
      Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.smul_sum, smul_smul,
      RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  rw [key]
  exact (he V h).comp hb

theorem isFrame_cellCol : ∀ (ι : Type) [Fintype ι] (N : ℕ) (w : ι → Equiv.Perm (Fin N)) (τ : ι),
    VB.IsFrame (cellCol ι N w τ) := by
  intro ι _ N w τ
  exact isFrame_sum_smul_of_isUnit ((VB.isFrame_freeFrame (Fl ι N) (Fin N)).res le_top)
    ((cellRing ι N w).mapMatrix (cellGL Prod.fst Prod.snd w τ).1)
    ((cellGL Prod.fst Prod.snd w τ).isUnit.map _)

end GlobalTheory.FlagZ.Univ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellFlagPointStalk
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.FlagZ GlobalTheory.FlagZ.Univ
open GlobalTheory.QCoh (freeModule)
open GlobalTheory.Twist (resM)

namespace GlobalTheory.FlagZ.Univ

theorem flagPt_germ_cellGL_eq_fromSpecStalk (ι : Type) [Fintype ι] (N : ℕ) (w : ι → Equiv.Perm (Fin N)) (y : Fl ι N)
    (hy : y ∈ cellOpen ι N w) :
    flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd (fun τ => Matrix.GeneralLinearGroup.map
      (((Fl ι N).presheaf.germ (cellOpen ι N w) y hy).hom.comp (cellRing ι N w)) (cellGL Prod.fst Prod.snd w τ)) =
      (Fl ι N).fromSpecStalk y := by
  have hU : IsAffineOpen (cellOpen ι N w) :=
    (isAffineOpen_top (Sp (CellRing (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd))).image_of_isOpenImmersion _
  have key : spMap (cellRing ι N w) ≫ cell (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd w = hU.fromSpec := by
    have h := IsAffineOpen.SpecMap_appLE_fromSpec (cell (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd w) hU
      (isAffineOpen_top _) (Scheme.Hom.preimage_image_eq _ ⊤).ge
    have e₀ : ((cell (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd w).appIso ⊤).hom =
        (cell (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd w).appLE (cellOpen ι N w) ⊤
          (Scheme.Hom.preimage_image_eq _ ⊤).ge :=
      Scheme.Hom.appIso_hom' _ _
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← e₀] at h
    have e : spMap (cellRing ι N w) = Spec.map ((cell (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd w).appIso ⊤).inv ≫
        Spec.map (Scheme.ΓSpecIso (CommRingCat.of (CellRing (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd))).inv := by
      exact Spec.map_comp _ _
    rw [e]
    erw [Category.assoc, ← h]
    erw [← Spec.map_comp_assoc, Iso.hom_inv_id, Spec.map_id, Category.id_comp]
  rw [← spMap_flagPt, ← cell, ← hU.fromSpecStalk_eq_fromSpecStalk hy, IsAffineOpen.fromSpecStalk, ← key]
  rw [spMap, spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  rfl

end GlobalTheory.FlagZ.Univ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterLineBundleAdditiveOfEquivariantGeneratoStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.characterLineBundle_additive_of_equivariantGenerator : ∀ (K : Type) [Field K] [IsAlgClosed K] (A A' N T : Over (Sp K)) [GrpObj A] [GrpObj A'] [GrpObj N] (i : N ⟶ A) (q : A ⟶ A') (χ : Γ((N ⊗ T).left, ⊤)ˣ) (M : LB (A' ⊗ T).left) (e : ∀ k, Γ((A ⊗ T).left, (pmap q T).left ⁻¹ᵁ M.U k)ˣ), IsAbelianScheme A → IsAbelianScheme A' → IsMonHom i → IsMonHom q → IsFinite q.left → Flat q.left → Surjective q.left → IsPullback i (toUnit N) q η[A'] → IsCharacter χ → M.IsLB → IsEquivGen i q χ M e → IsAdditive M := by
  first | exact @GlobalTheory.CharKer.isAdditive_of_isEquivGen | exact GlobalTheory.CharKer.isAdditive_of_isEquivGen | (intros; apply GlobalTheory.CharKer.isAdditive_of_isEquivGen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartIsOpenImmersionOverBaseStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_isOpenImmersion_over_base : ∀ {R : Type} [CommRing R] [IsLocalRing R] (S : Scheme.{0}) (π : S ⟶ Sp R) (G' : Over S) [GrpObj G'] (N : Near π G') (n : ℕ) (x : Fin n → (Over.mk (𝟙 S) ⟶ G')) (j : Option (Fin n)), IsOpenImmersion (N.chart x j) ∧ N.chart x j ≫ G'.hom = pullback.snd N.U.hom π := by
  first | exact @GlobalTheory.Mum.Near.chart_isOpenImmersion_over | exact GlobalTheory.Mum.Near.chart_isOpenImmersion_over | (intros; apply GlobalTheory.Mum.Near.chart_isOpenImmersion_over <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartOverlapEqPreimageOpenOfFibreStableStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartOverlap_eq_preimage_open_of_fibre_stable : ∀ (B S X : Scheme.{0}) (π : S ⟶ B) (U : Over B) (J : Type) (e : J → (pullback U.hom π ⟶ X)), IsProper π → Surjective π → (∀ j, IsOpenImmersion (e j)) → (∀ (i j : J) (T : Scheme.{0}) (w₁ w₂ h₁ : T ⟶ pullback U.hom π), w₁ ≫ pullback.fst _ _ = w₂ ≫ pullback.fst _ _ → h₁ ≫ e j = w₁ ≫ e i → ∃ h₂ : T ⟶ pullback U.hom π, h₂ ≫ e j = w₂ ≫ e i ∧ h₂ ≫ pullback.fst _ _ = h₁ ≫ pullback.fst _ _) → ∀ i j : J, ∃ V : U.left.Opens, ∀ a : ↥(pullback U.hom π), pullback.fst U.hom π a ∈ V ↔ e i a ∈ Set.range (e j) := by
  first | exact @GlobalTheory.Div.DescendOpens.overlap_preimage_open | exact GlobalTheory.Div.DescendOpens.overlap_preimage_open | (intros; apply GlobalTheory.Div.DescendOpens.overlap_preimage_open <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernClassContractionTangentEqTorsorCocycle
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem contr_chern_eq_tanCoc : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left), P.IsLB → ∀ v : epsR R ⟶ B, IsTangent v → ∀ (j : ∀ (D : Type) [CommRing D] [Algebra R D], Pt A D → P.ι), IsChoice P j → ∀ w : Z2 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)), IsChern (dp0 R) _ P (CatCoh.H2.mk _ w) → (∀ (T T' T'' : Thick (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)) (a : T ⟶ T') (b : T' ⟶ T''), T.J = ⊥ → T'.J = ⊥ → T''.J = ⊥ → w.1 T T' T'' a b = 0) → ∀ κ : Fn1 A, IsContr w.1 v κ → ∃ u : Fn1 (A ⊗ B), IsCoc P.U u ∧ Cohom (chartsA P) κ ((tanCoc P j v).add (sndPull u v)) := by
  intro R _ A B _ _ P hP v hv j hj w hch hw κ hκ
  obtain ⟨i, hi, U, ℓ, hU, hℓ, hcl⟩ := hch
  rw [CoefMap.pullCohomologyTwo_class, H2.mk_eq_mk] at hcl
  obtain ⟨n, hn⟩ := hcl
  refine ⟨cocOf P.U n, isCoc_cocOf P.U n ?_, GlobalTheory.T.chernCocycle_tangentContraction_cohomologous_torsor R A B P hP v hv j hj w hw i hi U ℓ hU hℓ n hn κ hκ⟩
  intro T T' T'' a b h h' h''
  have e := congrFun (congrFun (congrFun (congrFun (congrFun hn T) T') T'') a) b
  rw [e]
  have h0 : ℓ.1 T T' T'' a b = 0 := by
    have := (hℓ T T' T'' a b).1
    rw [h''] at this
    exact (Ideal.mem_bot).1 this
  change w.1 _ _ _ _ _ - ℓ.1 T T' T'' a b = 0
  rw [h0, sub_zero]
  exact hw _ _ _ _ _ h h' h''

end GlobalTheory.PtExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernDensityPullbackWeightInLiftedChartStatement
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open MeasureTheory GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.Points
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernDensity_pullbackWeight_in_liftedChart : ∀ {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} (π : Y ⟶ X) (hπ : π ≫ p = q) {B : LB X} (φ : Weight p σ B), φ.IsCInf → ∀ (c : AlgChart p σ D) (c' : AlgChart q σ D), (∀ w ∈ c'.e.source, PtsOver.map π hπ (spMap σ) w ∈ c.e.source ∧ c'.e w = c.e (PtsOver.map π hπ (spMap σ) w)) → ∀ w ∈ c'.e.source, c'.chernDens (φ.pull π hπ) w = c.chernDens φ (PtsOver.map π hπ (spMap σ) w) := by
  first | exact @GlobalTheory.PullChartDens.chernDens_pull_of_chart | exact GlobalTheory.PullChartDens.chernDens_pull_of_chart | (intros; apply GlobalTheory.PullChartDens.chernDens_pull_of_chart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMeasurePartPreimageCoveringField
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverChernField

theorem chernPart_preimage_of_cover : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ), IsProjOver p → IsProjOver q → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (B : LB X) (φ : Weight p σ B), φ.IsCInf → ∀ (ε : ℤˣ) (U : Set (CxPts p σ)), IsOpen U → ∀ n : ℕ, (∀ y ∈ U, (PtsOver.map π hπ (spMap σ) ⁻¹' {y}).encard = (n : ℕ∞)) → (∀ y ∈ U, ∃ c : AlgChart p σ D, y ∈ c.e.source) → (∀ z : CxPts q σ, PtsOver.map π hπ (spMap σ) z ∈ U → ∀ c : AlgChart p σ D, PtsOver.map π hπ (spMap σ) z ∈ c.e.source → ∃ c' : AlgChart q σ D, z ∈ c'.e.source ∧ ∀ w ∈ c'.e.source, PtsOver.map π hπ (spMap σ) w ∈ c.e.source ∧ c'.e w = c.e (PtsOver.map π hπ (spMap σ) w)) → (φ.pull π hπ).chernPart D ε (PtsOver.map π hπ (spMap σ) ⁻¹' U) = (n : ENNReal) * φ.chernPart D ε U := by
  intro k _ X Y _ _ p q σ D hp hq π hπ B φ hφ ε U hU n hfib hchart hlift
  have := CxPts.t2Space_cxPts_of_isProjOver σ hq
  have := CxPts.secondCountableTopology_of_isProjOver (σ := σ) hp
  have := CxPts.secondCountableTopology_of_isProjOver (σ := σ) hq
  have hφ' := hφ.pull π hπ
  unfold Weight.chernPart
  refine GlobalTheory.CoverChern.glueMeas_preimage_of_cover_on (fun c c' => c.holo_trans c')
    (fun c c' y hy hy' => ?_)
    (fun c c' => c.holo_trans c') (fun c c' y hy hy' => ?_)
    (PtsOver.continuous_map π hπ _) hU hfib (fun z hz => ?_) hU.measurableSet subset_rfl
  · rw [c.chernDens_trans c' hφ hy hy', mul_left_comm, ENNReal.ofReal_mul (sq_nonneg _)]
  · rw [c.chernDens_trans c' hφ' hy hy', mul_left_comm, ENNReal.ofReal_mul (sq_nonneg _)]
  · obtain ⟨c, hc⟩ := hchart _ hz
    obtain ⟨c', hz', hc'⟩ := hlift z hz c hc
    exact ⟨c, c', hz', hc, fun w hw _ => ⟨(hc' w hw).2, by
      rw [GlobalTheory.PullChartDens.chernDens_pull_of_chart π hπ φ hφ c c' hc' w hw]⟩⟩

end GlobalTheory.CoverChernField
end
end

