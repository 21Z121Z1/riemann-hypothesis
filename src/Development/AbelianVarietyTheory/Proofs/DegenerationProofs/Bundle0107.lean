import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsOpensEtaleOfUniqueClassicalPoints
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0092
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0099
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0062
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLevelPoint
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsGTransport
import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0044
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0059
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.AppCompatGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAbelianSchemeThick
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0102
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0082
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0004

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SmoothOfRelativeDimensionGroupSchemeOfTests
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory

theorem isStandardSmoothOfRelativeDimension_mvPolynomial_fin (R : Type) [CommRing R] (n : ℕ) :
    Algebra.IsStandardSmoothOfRelativeDimension n R (MvPolynomial (Fin n) R) := by
  let P₀ : Algebra.Presentation R (MvPolynomial (Fin n) R) (Fin n) Empty :=
    { __ := Algebra.Generators.mvPolynomial R (Fin n)
      relation := Empty.elim
      span_range_relation_eq_ker := by
        rw [Algebra.Generators.ker_mvPolynomial]
        simp }
  let P₁ : Algebra.PreSubmersivePresentation R (MvPolynomial (Fin n) R) (Fin n) Empty :=
    { __ := P₀
      map := Empty.elim
      map_inj := fun a => a.elim }
  let P₂ : Algebra.SubmersivePresentation R (MvPolynomial (Fin n) R) (Fin n) Empty :=
    { __ := P₁
      jacobian_isUnit := by
        rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
        simp }
  exact P₂.isStandardSmoothOfRelativeDimension (by simp [Algebra.Presentation.dimension])

theorem smoothOfRelativeDimension_affineSpace_fin (S : Scheme.{0}) (n : ℕ) :
    SmoothOfRelativeDimension n (𝔸(Fin n; S) ↘ S) := by
  have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} n
  refine MorphismProperty.pullback_fst (P := @SmoothOfRelativeDimension n) _ _ ?_
  have := isIso_of_isTerminal specULiftZIsTerminal.{0} terminalIsTerminal (terminal.from _)
  rw [← terminal.comp_from (Spec.map (CommRingCat.ofHom MvPolynomial.C)),
    MorphismProperty.cancel_right_of_respectsIso (P := @SmoothOfRelativeDimension n),
    HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)]
  refine RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_
  exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap n).2
    (isStandardSmoothOfRelativeDimension_mvPolynomial_fin (ULift ℤ) n)

namespace ZJ

theorem Core.exists_opens_smoothOfRelativeDimension (C : Core) (hT : C.HasTests) (hF : C.Fib)
    (w : C.G.toScheme) (hc : IsClosed ({w} : Set C.G.toScheme)) :
    ∃ V : C.G.toScheme.Opens, w ∈ V ∧ SmoothOfRelativeDimension C.g (V.ι ≫ C.GG.hom) := by
  obtain ⟨hsep, hlft, -, hint, -, -, ha, hcart, -, -, -, hdom, -⟩ := GlobalTheory.T.abelianSchemeProperClosureData_basic_properties C
  obtain ⟨W, hw, u, -, hu⟩ := GlobalTheory.T.exists_coord_reducedFibre_closedPoint C hT hF w hc
  have hqf := GlobalTheory.T.quasiFiniteAt_affineSpace_homOfVector_of_coord C w W hw u hc hu
  have huniq := GlobalTheory.T.classical_point_eq_of_reduction_coords C hT hF w W hw u hu
  have hint' : IsIntegral C.G.toScheme := hint
  have : Nonempty W.toScheme := ⟨⟨w, hw⟩⟩
  have : IsIntegral W.toScheme := isIntegral_of_isOpenImmersion W.ι
  let t : W.toScheme ⟶ C.Z := W.ι ≫ C.GG.hom
  let u' : Fin C.g → Γ(W.toScheme, ⊤) := fun i => W.topIso.inv.hom (u i)
  let v : W.toScheme ⟶ 𝔸(Fin C.g; C.Z) := AffineSpace.homOfVector t u'
  have hv : v ≫ 𝔸(Fin C.g; C.Z) ↘ C.Z = t := AffineSpace.homOfVector_over _ _
  have : LocallyOfFiniteType t := inferInstanceAs (LocallyOfFiniteType (W.ι ≫ C.GG.hom))
  have : IsSeparated t := inferInstanceAs (IsSeparated (W.ι ≫ C.GG.hom))
  have : IsDominant W.ι := ⟨by
    rw [DenseRange, Scheme.Opens.range_ι]
    exact W.isOpen.dense ⟨w, hw⟩⟩
  have : IsDominant t := inferInstanceAs (IsDominant (W.ι ≫ C.GG.hom))
  have hA := smoothOfRelativeDimension_affineSpace_fin C.Z C.g
  have : Smooth (𝔸(Fin C.g; C.Z) ↘ C.Z) := SmoothOfRelativeDimension.smooth C.g _
  have : LocallyOfFiniteType v := by
    have : LocallyOfFiniteType (v ≫ 𝔸(Fin C.g; C.Z) ↘ C.Z) := by rw [hv]; infer_instance
    exact locallyOfFiniteType_of_comp v (𝔸(Fin C.g; C.Z) ↘ C.Z)
  have : IsSeparated v := by
    have : IsSeparated (v ≫ 𝔸(Fin C.g; C.Z) ↘ C.Z) := by rw [hv]; infer_instance
    exact IsSeparated.of_comp v (𝔸(Fin C.g; C.Z) ↘ C.Z)
  let U' : W.toScheme.Opens := t ⁻¹ᵁ C.U
  have hU' : (U' : Set W.toScheme).Nonempty := by
    obtain ⟨x, hx⟩ := t.denseRange.exists_mem_open C.U.isOpen C.ne
    exact ⟨x, hx⟩
  have hsm : SmoothOfRelativeDimension C.g (U'.ι ≫ t) := by
    let l : U'.toScheme ⟶ C.A.left := hcart.lift (U'.ι ≫ W.ι) (t ∣_ C.U)
      (by rw [morphismRestrict_ι, Category.assoc])
    have h1 : l ≫ C.a = U'.ι ≫ W.ι := hcart.lift_fst _ _ _
    have h2 : l ≫ C.A.hom = t ∣_ C.U := hcart.lift_snd _ _ _
    have : IsOpenImmersion (l ≫ C.a) := by rw [h1]; infer_instance
    have : IsOpenImmersion l := IsOpenImmersion.of_comp l C.a
    have h3 : U'.ι ≫ t = l ≫ C.A.hom ≫ C.U.ι := by
      rw [reassoc_of% h2, morphismRestrict_ι]
    have := C.dim
    have h4 : SmoothOfRelativeDimension (0 + (C.g + 0)) (l ≫ C.A.hom ≫ C.U.ι) := inferInstance
    rw [h3]
    simpa using h4
  have : IsDominant v := GlobalTheory.T.isDominant_homOfVector_of_quasiFiniteAt' W.toScheme C.Z t C.g U' hU' hsm u' ⟨w, hw⟩ hqf
  have := C.flat
  have := C.lft
  have hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme 𝔸(Fin C.g; C.Z) :=
    forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth (𝔸(Fin C.g; C.Z) ↘ C.Z) C.normal
  have hc' : IsClosed ({⟨w, hw⟩} : Set W.toScheme) := by
    have := hc.preimage W.ι.continuous
    convert this using 1
    ext z
    exact Subtype.ext_iff
  obtain ⟨V, hV, hE⟩ := exists_opens_etale_of_unique_classical_points 𝔸(Fin C.g; C.Z)
    (𝔸(Fin C.g; C.Z) ↘ C.Z ≫ C.π) hN W.toScheme v ⟨w, hw⟩ U' hc' hqf hU' (by
      intro p _ a a' h hp hr hg _
      refine huniq p a a' ?_ ?_ hp hr fun i => ?_
      · rintro _ ⟨z, rfl⟩
        exact hg ⟨z, rfl⟩
      · change a ≫ t = a' ≫ t
        rw [← hv, reassoc_of% h]
      · have e : ∀ b : Sp (OO p) ⟶ W.toScheme,
            b.appTop.hom (u' i) = (b ≫ v).appTop.hom (AffineSpace.coord C.Z i) := fun b => by
          rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
          exact congrArg _ (AffineSpace.homOfVector_appTop_coord t u' i).symm
        exact (e a).trans ((congrArg (fun c : Sp (OO p) ⟶ 𝔸(Fin C.g; C.Z) =>
          c.appTop.hom (AffineSpace.coord C.Z i)) h).trans (e a').symm))
  have h5 : SmoothOfRelativeDimension (0 + C.g) ((V.ι ≫ v) ≫ 𝔸(Fin C.g; C.Z) ↘ C.Z) :=
    inferInstance
  rw [Category.assoc, hv, zero_add] at h5
  refine ⟨(V.ι ≫ W.ι).opensRange, ⟨⟨⟨w, hw⟩, hV⟩, rfl⟩, ?_⟩
  have h6 : SmoothOfRelativeDimension (0 + C.g)
      ((V.ι ≫ W.ι).isoOpensRange.inv ≫ V.ι ≫ t) := inferInstance
  rw [zero_add] at h6
  convert h6 using 1
  rw [← (V.ι ≫ W.ι).isoOpensRange_inv_comp]
  simp only [Category.assoc, t]

theorem Core.smoothOfRelativeDimension_of_hasTests :
    ∀ C : Core, C.HasTests → C.Fib → SmoothOfRelativeDimension C.g C.GG.hom := by
  intro C hT hF
  obtain ⟨-, hlft, -⟩ := GlobalTheory.T.abelianSchemeProperClosureData_basic_properties C
  have := C.lft
  choose V hV hs using C.exists_opens_smoothOfRelativeDimension hT hF
  let V' : {w : C.G.toScheme // IsClosed ({w} : Set C.G.toScheme)} → C.G.toScheme.Opens :=
    fun w => V w.1 w.2
  have htop : iSup V' = ⊤ :=
    (jacobson_closedPoints_tools_int C.G.toScheme (C.GG.hom ≫ C.π)).2.2.1 _ _ fun x hx =>
      ⟨fun _ => trivial, fun _ => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hx⟩, hV x hx⟩⟩
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{0} C.g) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  exact IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension.{0} C.g) V' htop
    fun w => hs w.1 w.2

end ZJ
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusCoordUnitAndSectionEqExpansion
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.IntegralSum
open GlobalTheory.FormalValue Filter Topology ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω}
variable {ρ : S.Real} {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀)

theorem gPt_cancel {ψ ψ' : Sp (OO p) ⟶ u.D.toPre.P.A.left} (h : gPt p ≫ ψ = gPt p ≫ ψ') : ψ = ψ' := by
  have : IsProper u.D.toPre.P.A.hom := u.D.toPre.P.isAb.proper
  have := GlobalTheory.ZJ.AddExt.isDominant_gPt p
  exact ext_of_isDominant_of_isSeparated u.D.toPre.P.A.hom
    (ext_of_isDominant (gPt p) (by rw [← Category.assoc, h, Category.assoc])) (gPt p) h

theorem gtN_zero (c : Sp (OO p) ⟶ u.G.left) (g : GtPtF u.D.toPre (PadicAlgCl p)) (hc : c ≫ u.G.hom = spMap u.j)
    (h : u.Lev c g) : u.GtN g 0 := by
  obtain ⟨b₀, hb, H⟩ := h
  intro J hJ χ
  obtain ⟨ce, hce⟩ := exists_level_point u c hc 0
  obtain ⟨hbe, H⟩ := H 0 ce hce
  have := GlobalTheory.ZJ.AddExt.isDominant_gPt p
  have hb₀ : b₀ ≫ u.D.toPre.P.A.hom = spMap u.j := by
    refine ext_of_isDominant (gPt p) ?_
    rw [← Category.assoc, hb]
    refine (Over.w g.b).trans ?_
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl
  have ht : ⊤ ≤ ce ⁻¹ᵁ LB.wchart u.D.toPre.P.L (u.D.toPre.Oφ (u.U.gt 0).pG χ)
      (fun k => J (DegPre.gtφ u.D.toPre (PadicAlgCl p) g.b χ k)) := fun y _ => Set.mem_iInter.2 fun i => by
    have h1 := hJ (b₀ ≫ u.D.toPre.Oφ (𝟙 _) χ i) (by rw [Category.assoc, Oφ_over, hb₀])
    rw [← Category.assoc, hb, ← gtφ_eq] at h1
    exact (congrArg (fun q => q y ∈ u.D.toPre.P.L.U _) (level_Oφ u b₀ ce hbe χ i)).mpr (top_le_comp h1 _ trivial)
  obtain ⟨x, hx, hx'⟩ := H χ _ ht
  rw [← hx, norm_eq_one_of_isUnit u (e := 0) (by rw [hx']; exact isUnit_valR _ _ ht _)]
  simp

theorem parAt [ArithBase o Ω] (c : Sp (OO p) ⟶ u.G.left) (g : GtPtF u.D.toPre (PadicAlgCl p)) (a : u.PtC)
    (hc : c ≫ u.G.hom = spMap u.j) (ha : gPt p ≫ c = u.toG a) (h : u.Lev c g) (k : ℕ) : u.ParAt k a g := by
  obtain ⟨b₀, hb, H⟩ := h
  intro w hw l hl
  choose ce hce using exists_level_point u c hc
  have hbe := fun e => (H e (ce e) (hce e)).1
  choose d hd using fun y => exists_chart u.D.toPre.P.isLB y
  obtain ⟨jL, hjL⟩ := exists_chart u.U.LG.isLB (c (cpt _))
  have hL : ⊤ ≤ c ⁻¹ᵁ u.U.LG.L.U jL := (top_le_iff_cpt _ _).2 hjL
  have hM : ⊤ ≤ b₀ ⁻¹ᵁ u.D.toPre.P.L.U (d (b₀ (cpt _))) := (top_le_iff_cpt _ _).2 (hd _)
  obtain ⟨ω, ωe, hω0, hω, hωe⟩ := exists_omega u c b₀ ce hce hbe hL hM hc
  have hθ : ∀ θ : u.D.toPre.P.A.left ⟶ u.D.toPre.P.A.left,
      ⊤ ≤ (b₀ ≫ θ) ⁻¹ᵁ u.D.toPre.P.L.U (d ((b₀ ≫ θ) (cpt _))) := fun θ => (top_le_iff_cpt _ _).2 (hd _)
  choose x hx hx' using fun e χ => (H e (ce e) (hce e)).2 χ (fun i => d ((b₀ ≫ u.D.toPre.Oφ (𝟙 _) χ i) (cpt _)))
    (fun y _ => Set.mem_iInter.2 fun i => (congrArg (fun q => q y ∈ u.D.toPre.P.L.U _)
      (level_Oφ u b₀ (ce e) (hbe e) χ i)).mpr (top_le_comp (hθ _) _ trivial))
  have hx0 : ∀ e χ, x 0 χ = x e χ := fun e χ => Subtype.ext ((hx 0 χ).trans (hx e χ).symm)
  have HS := fun σ f hE => hasSum_integral u c b₀ ce hce hbe hL d hd (x 0) (fun e χ => by rw [hx0 e, hx']) ω ωe hω hωe
    (k := k) σ f hE
  let z : Sp (PadicAlgCl p) := cpt _
  obtain ⟨J, hJ, eJ⟩ := exists_good u.D.toPre.P.L u.D.toPre.P.isLB z
    (fun θ : u.D.toPre.P.A.left ⟶ u.D.toPre.P.A.left => gPt p ≫ b₀ ≫ θ) (fun θ => d ((b₀ ≫ θ) (cpt _)))
    (fun θ θ' e => by rw [gPt_cancel u e]) (fun θ => top_le_comp (hθ θ) _ trivial)
  let r : Sp (PadicAlgCl p) ⟶ (UnifPre.GF (G := u.G) (PadicAlgCl p)).left :=
    (lift (𝟙 (TFK (R := u.V) (PadicAlgCl p))) a).left
  have hr : r ≫ UnifPre.gFK (G := u.G) (PadicAlgCl p) = gPt p ≫ c := by
    rw [ha, ← Category.assoc]
    exact congrArg (fun t : u.PtC => t.left ≫ _) (lift_snd _ _)
  have hr' : r ≫ (fst (TFK (R := u.V) (PadicAlgCl p)) ((Over.pullback (jK u.V)).obj u.G)).left = 𝟙 _ :=
    congrArg (fun t => t.left) (lift_fst (𝟙 (TFK (R := u.V) (PadicAlgCl p))) a)
  obtain ⟨τ, τ0, hτ⟩ := exists_valF_secLin u.U.LG.isLB _ _ r hr' (gPt p ≫ c) hr k (l := l) (l' := jL)
    (by rw [ha]; exact hl) (top_le_comp hL _)
  obtain ⟨κ, κ0, hκ⟩ := exists_coef_secLin u.D.toPre (PadicAlgCl p) k g w hw z J hJ
  refine ⟨κ * ω ^ k * τ⁻¹, by simp [τ0, κ0, hω0], ?_⟩
  rintro σ' s ⟨n, cc, σ, f, hE, hσ, hs⟩
  have e₁ : valF r _ (σ'.f (fun _ => l)) =
      τ * ∑ i, cc i * ((secVal u.U.toUnifPre (σ i) c jL : OO p) : PadicAlgCl p) :=
    (hτ σ' n cc σ hσ).trans (congrArg (τ * ·) (Finset.sum_congr rfl fun i _ => congrArg (cc i * ·)
      (valR_spMap (OO p).subtype c _ (top_le_secChart hL) _)))
  have e₂ : ∀ χ, coef s g w χ = κ * ∑ i, cc i *
      ((valR b₀ _ ((f i χ).f (fun j => d ((b₀ ≫ u.D.toPre.famφB χ j) (cpt _)))) * x 0 χ : OO p) : PadicAlgCl p) := by
    intro χ
    refine (hκ s χ n cc (fun i => f i χ) (hs χ) (gPt p ≫ b₀) (fun j => d ((b₀ ≫ u.D.toPre.famφB χ j) (cpt _)))
      (fun i => d ((b₀ ≫ u.D.toPre.Oφ (𝟙 _) χ i) (cpt _))) hb (fun i => by rw [Category.assoc, eJ])
      (fun i => by rw [Category.assoc, eJ])).trans (congrArg (κ * ·) (Finset.sum_congr rfl fun i _ =>
        congrArg (cc i * ·) ?_))
    rw [MulMemClass.coe_mul]
    exact congrArg₂ (· * ·) (valR_spMap (OO p).subtype b₀ _
      ((top_le_iff_cpt _ _).2 (Set.mem_iInter.2 fun j => hd ((b₀ ≫ u.D.toPre.famφB χ j) (cpt _)))) _) (hx 0 χ).symm
  have hs' := (hasSum_sum (s := Finset.univ) fun i _ => (HS (σ i) (f i) (hE i)).mul_left (cc i)).mul_left κ
  show HasSum _ (_ * valF r _ (σ'.f (fun _ => l)))
  rw [e₁, funext e₂]
  refine (congrArg (HasSum _ ·) ?_).mp hs'
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp

theorem gtN_zero_and_parAt : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (c : Sp (OO p) ⟶ u.G.left) (g : GtPtF u.D.toPre (PadicAlgCl p)) (a : u.PtC), c ≫ u.G.hom = spMap u.j → gPt p ≫ c = u.toG a → u.Lev c g → u.GtN g 0 ∧ ∀ k, 1 ≤ k → u.ParAt k a g :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ u c g a hc ha h => ⟨gtN_zero u c g hc h, fun k _ => parAt u c g a hc ha h k⟩

end GlobalTheory.ZH.IntegralSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UnifPullbackOfUnifRing
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ZH

theorem exists_sec_pull_of_comp {X Y Z : Scheme.{0}} (L : LB X) (j : Y ⟶ X) (n : Z ⟶ Y) (φ : Z ⟶ X) (e : n ≫ j = φ)
    (σ : LB.Sec (L.pull j)) : ∃ θ : LB.Sec (L.pull φ), ∀ y, n y ∈ nonzeroLocus σ → y ∈ nonzeroLocus θ := by
  subst e
  refine ⟨DVR.pullSec L (fun _ : PUnit => j) (fun _ => 1) σ n, fun y hy => ?_⟩
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨k, ?_⟩
  have h₁ : y ∈ Z.basicOpen ((n.app _).hom (σ.f k)) := by
    rw [← Scheme.preimage_basicOpen]; exact hk
  have h₂ : y ∈ (L.pull (n ≫ j)).U k := mem_pull.2 ((mem_pull (F := j)).1 (Y.basicOpen_le _ hk))
  exact (Z.basicOpen_res _ _).ge ⟨h₂, h₁⟩

theorem unif_pullback_of_unif_ring : (∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R], IsNoetherianRing R → IsIntegrallyClosed R → IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (_ : CubicalStr G L) (W : (Sp R).Opens), IsSemiAbelian G → L.IsSymmetric → HypS G L.L → (∃ E : SplitExt (Sp (IsLocalRing.ResidueField R)), E.IsGt ((Over.pullback (spMap (IsLocalRing.residue R))).obj G)) → (∃ θ : LB.Sec L.L, ∃ x ∈ nonzeroLocus θ, G.hom x = IsLocalRing.closedPoint R) → (W : Set (Sp R)).Nonempty → (W : Set (Sp R)) = abLocus G → IsProper (pullback.snd G.hom W.ι) → RelAmple ((Over.pullback W.ι).obj G) (L.L.pull (pullback.fst G.hom W.ι)) → KTriv ((Over.pullback W.ι).obj G) (L.L.pull (pullback.fst G.hom W.ι)) → ∃ (D : DegData R (IsLocalRing.maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (IsLocalRing.maximalIdeal R) D A G), U.LG = L ∧ ∀ y, PsiUnitOn D.toPre y W) → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Over₀ M U₀ → IsOpen (abLocus Q.G) → Q.Ab → Q.LocTheta → HypS Q.G Q.L.L → (∀ W : M.Z.Opens, (W : Set M.Z) ⊆ abLocus Q.G → RelAmple ((Over.pullback W.ι).obj Q.G) (Q.L.L.pull (pullback.fst Q.G.hom W.ι)) ∧ KTriv ((Over.pullback W.ι).obj Q.G) (Q.L.L.pull (pullback.fst Q.G.hom W.ι))) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R], IsNoetherianRing R → IsIntegrallyClosed R → IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (ξ : Sp R ⟶ M.Z), (ξ ⁻¹' abLocus Q.G).Nonempty → ∀ [IsCommMonObj ((Over.pullback ξ).obj Q.G)], ∃ (D : DegData R (IsLocalRing.maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (IsLocalRing.maximalIdeal R) D A ((Over.pullback ξ).obj Q.G)), LBIso U.LG.L (Q.L.L.pull (pullback.fst Q.G.hom ξ)) ∧ ∀ y, PsiUnitOn D.toPre y (ξ ⁻¹' abLocus Q.G) := by
  intro H o Ω _ _ _ _ S ρ M U₀ Q _ hop hab hth hS hpol R _ _ _ _ hN hI hC ξ hne _
  have h := isGrpPullback_pullback Q.G ξ
  obtain ⟨hL, hr, ⟨c', -⟩, hs⟩ := CubePf.cubePull _ _ Q.G _ (cubeMapOf h) Q.L Q.cub
  have hrefl : LBIso (Q.L.L.pull (pullback.fst Q.G.hom ξ)) (Q.L.L.pull (pullback.fst Q.G.hom ξ)) :=
    ⟨_, CubePf.idIsoL_isGen hL⟩
  let W₀ : M.Z.Opens := ⟨abLocus Q.G, hop⟩
  let W : (Sp R).Opens := ξ ⁻¹ᵁ W₀
  let G' := (Over.pullback ξ).obj Q.G
  have h₀ := isGrpPullback_pullback Q.G W₀.ι
  have h₁ := isGrpPullback_pullback G' W.ι
  have sq : (ξ ∣_ W₀) ≫ W₀.ι = W.ι ≫ ξ := morphismRestrict_ι ξ W₀
  have h₂ := (h₁.comp h).congr sq.symm rfl
  let ψ : ((Over.pullback W.ι).obj G').left ⟶ ((Over.pullback W₀.ι).obj Q.G).left :=
    h₀.1.lift _ _ (h₂.1.w.trans (Category.assoc _ _ _).symm)
  have hψ : ψ ≫ pullback.fst Q.G.hom W₀.ι = pullback.fst G'.hom W.ι ≫ pullback.fst Q.G.hom ξ := h₀.1.lift_fst _ _ _
  have h₃ : IsGrpPullback ((Over.pullback W.ι).obj G') ((Over.pullback W₀.ι).obj Q.G) (ξ ∣_ W₀) ψ :=
    h₀.cancel (h₂.congr rfl hψ.symm) (h₀.1.lift_snd _ _ _)
  have hsa := IsSemiAbelian.pullback W₀.ι Q.G Q.semi
  have hA : IsAbelianScheme ((Over.pullback W₀.ι).obj Q.G) :=
    { comm := hsa.comm, smooth := hsa.smooth, proper := hab.2 W₀ subset_rfl, geomConnected := hsa.geomConnected }
  have hiso : LBIso ((Q.L.L.pull (pullback.fst Q.G.hom ξ)).pull (pullback.fst G'.hom W.ι))
      ((Q.L.L.pull (pullback.fst Q.G.hom W₀.ι)).pull ψ) :=
    LBIso.chartPull
      (chartPullLinComb Q.L.L _ (fun _ : PUnit => pullback.fst G'.hom W.ι) (fun _ => 𝟙 _) (fun _ => 1) _
        fun _ => (Category.comp_id _).symm)
      (chartPullLinComb Q.L.L _ (fun _ : PUnit => ψ) (fun _ => 𝟙 _) (fun _ => 1) _
        fun _ => hψ.trans (Category.comp_id _).symm)
      ⟨_, CubePf.idIsoL_isGen (pull_isLB Q.L.isLB (𝟙 _))⟩
  obtain ⟨hA', ha, hk⟩ := GlobalTheory.pol_pull _ _ _ _ _ ψ _ _ (pull_isLB Q.L.isLB _) (pull_isLB hL _) hA h₃ hiso
  obtain ⟨ha₀, hk₀⟩ := hpol W₀ subset_rfl
  have hsp : ∃ E : SplitExt (Sp (IsLocalRing.ResidueField R)),
      E.IsGt ((Over.pullback (spMap (IsLocalRing.residue R))).obj G') := by
    obtain ⟨E, hE⟩ := GlobalTheory.ZJ.SplitAll.fieldPoint (G := Q.G) Q.split _ (spMap (IsLocalRing.residue R) ≫ ξ)
    exact ⟨E, isGt_of_iso (pullCompIso _ ξ Q.G) hE⟩
  have hθ' : ∃ θ : LB.Sec (Q.L.L.pull (pullback.fst Q.G.hom ξ)), ∃ x ∈ nonzeroLocus θ,
      G'.hom x = IsLocalRing.closedPoint R := by
    obtain ⟨N, σ, hz, hσ⟩ := hth (ξ (IsLocalRing.closedPoint R))
    have hξ : ξ ⁻¹ᵁ N = ⊤ := Scheme.preimage_eq_top_of_closedPoint_mem ξ hz
    obtain ⟨n, hn⟩ : ∃ n : G'.left ⟶ (Q.G.hom ⁻¹ᵁ N).toScheme, n ≫ (Q.G.hom ⁻¹ᵁ N).ι = pullback.fst Q.G.hom ξ :=
      ⟨IsOpenImmersion.lift _ (pullback.fst Q.G.hom ξ) (by
        rintro _ ⟨y, rfl⟩
        rw [Scheme.Opens.range_ι]
        exact (congrArg (fun q => q y ∈ N) h.1.w).mpr (hξ.ge (Set.mem_univ (G'.hom y)))),
        IsOpenImmersion.lift_fac _ _ _⟩
    obtain ⟨θ, hθ⟩ := exists_sec_pull_of_comp Q.L.L _ n _ hn σ
    obtain ⟨x, hx, hx'⟩ := hσ _ hz
    obtain ⟨y, hy, hy'⟩ := Scheme.exists_preimage_of_isPullback h.1 _ _ hx'
    refine ⟨θ, y, hθ y ?_, hy'⟩
    have e : n y = x := (Q.G.hom ⁻¹ᵁ N).ι.isOpenEmbedding.injective
      ((congrArg (fun q => q y) hn).trans hy)
    rwa [e]
  obtain ⟨D, A, U, hU, hP⟩ := H R hN hI hC G' ((cubeMapOf h).rigLB Q.L hL hr) c' W
    (IsSemiAbelian.pullback ξ Q.G Q.semi) (hs Q.sym)
    (GlobalTheory.SymBaseChange.hypS_baseChange _ _ Q.G G' ξ _ Q.L.L _ Q.L.isLB hL h hrefl hS) hsp hθ' hne
    (Set.ext fun x => abLocus_pullback abLocusOne Q.semi h.1 x) hA'.proper
    (ha ha₀) (hk hk₀)
  exact ⟨D, A, U, by rw [hU]; exact hrefl, hP⟩

end GlobalTheory.ZH

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedTestDimensionsAndSplitFibre
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH

theorem exists_isGt_specialFibre (hB : GtBaseChangeSt) {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V]
    (D : DegPre V) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (g : GtCoord (IsLocalRing.maximalIdeal V) D 0 G) :
    ∃ E : SplitExt (Sp (IsLocalRing.ResidueField V)),
      E.IsGt ((Over.pullback (spMap (IsLocalRing.residue V))).obj G) := by
  obtain ⟨E₀, -, -, -, -, hE⟩ := GlobalTheory.gtCoord_isGt V (IsLocalRing.maximalIdeal V) D 0 G ⟨g⟩
  have hle : IsLocalRing.maximalIdeal V ^ (0 + 1) ≤ RingHom.ker (IsLocalRing.residue V) := by
    rw [zero_add, pow_one, IsLocalRing.ker_residue]
  let c : V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1) →+* IsLocalRing.ResidueField V :=
    Ideal.Quotient.lift _ (IsLocalRing.residue V) fun a ha => (RingHom.mem_ker).1 (hle ha)
  obtain ⟨E₁, -, -, -, -, hE₁⟩ := hB _ _ (spMap c) E₀ _ hE
  have hc : spMap c ≫ thick V (IsLocalRing.maximalIdeal V) 0 = spMap (IsLocalRing.residue V) := by
    rw [show thick V (IsLocalRing.maximalIdeal V) 0 = spMap (Ideal.Quotient.mk _) from rfl, ← spMap_comp]
    congr 1
  have gp := ((isGrpPullback_pullback (thickObj V (IsLocalRing.maximalIdeal V) 0 G) (spMap c)).comp
    (isGrpPullback_pullback G (thick V (IsLocalRing.maximalIdeal V) 0))).congr hc rfl
  obtain ⟨e, he, -⟩ := grpPullback_iso gp (isGrpPullback_pullback G (spMap (IsLocalRing.residue V)))
  exact ⟨E₁, isGt_of_iso e hE₁⟩

theorem utest_dim_and_split : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀), u.A.g = S.g ∧ u.D.toPre.P.g + Module.finrank ℤ u.D.toPre.X = S.g ∧ SmoothOfRelativeDimension S.g u.G.hom ∧ 4 ≤ S.N ∧ ∃ E : SplitExt (Sp (IsLocalRing.ResidueField u.V)), E.IsGt ((Over.pullback (spMap (IsLocalRing.residue u.V))).obj u.G) := by
  intro hL o Ω _ _ _ _ S ρ p _ y₀ u
  have : CharZero u.V :=
    ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V))).charZero
  have hA : AdmBase u.V (IsLocalRing.maximalIdeal u.V) := ⟨inferInstance, inferInstance, inferInstance, u.complete⟩
  have hsm : SmoothOfRelativeDimension S.g u.A.A.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback u.cart.1 (ρ.g_eq ▸ ρ.P.smoothDim)
  have hg : u.A.g = S.g :=
    H1.dim_unique u.A.A.hom u.A.smoothDim hsm (eSec u.A.A (IsLocalRing.closedPoint (FractionRing u.V)))
  refine ⟨hg, ?_, ?_, ?_, exists_isGt_specialFibre hL.2.2.1.gtBaseChange _ _ (u.U.gt 0)⟩
  · have h := GlobalTheory.UT.dim_eq_rank_add_dim hL u.V _ hA u.D u.A u.G u.semi u.U
    rw [← hg, add_comm]
    exact h.symm
  · have := u.semi.smooth
    have := u.semi.geomConnected
    refine GlobalTheory.GenericDim.smoothOfRelativeDimension_of_generic u.V u.G S.g ?_
    have w : u.U.gen.hom.left ≫ u.A.A.hom = pullback.snd u.G.hom (jK u.V) := Over.w u.U.gen.hom
    have : IsIso u.U.gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map u.U.gen.hom))
    exact (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
      (IsPullback.of_horiz_isIso (g := 𝟙 _) ⟨w.trans (Category.comp_id _).symm⟩) hsm
  · rw [ρ.N_eq]
    have h₁ : 2 ≤ ρ.n ^ ρ.k := ρ.n_prime.two_le.trans (Nat.le_self_pow (by have := ρ.two_le; omega) _)
    exact Nat.pow_le_pow_left h₁ 2

end GlobalTheory.ZH
end

