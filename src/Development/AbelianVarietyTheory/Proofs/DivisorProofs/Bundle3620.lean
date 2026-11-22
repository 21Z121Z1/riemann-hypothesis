import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0600
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2332
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3614
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0694
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0037
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0029
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0007
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0005
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0684
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0663
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0825
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0828
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0817
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0827
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2811
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3326
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3616
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3615
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistAtEach
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3562
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2956
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TxFrameTranslate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2552
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3541

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularOfFiniteOfFormallyUnramified
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj

namespace GlobalTheory.InteriorChart

theorem bijective_stalkSpecializes {X : Scheme.{0}} {x y : X} (e : x = y) (h : x ⤳ y) :
    Function.Bijective (X.presheaf.stalkSpecializes h).hom := by
  subst e
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  exact Function.bijective_id

theorem isEtaleCompletion_comp {A B C : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] [CommRing C]
    [IsLocalRing C] (φ : A →+* B) (ρ : B →+* C) [IsLocalHom ρ] (hφ : IsEtaleCompletion φ) (hf : ρ.Flat)
    (hm : (maximalIdeal B).map ρ = maximalIdeal C) (hfin : ρ.Finite) : IsEtaleCompletion (ρ.comp φ) := by
  obtain ⟨h1, h2, h3⟩ := hφ
  refine ⟨RingHom.Flat.comp h1 hf, ?_, ?_⟩
  · rw [← Ideal.map_map, h2, hm]
  · have e : (residue C).comp (ρ.comp φ) = (ResidueField.map ρ).comp ((residue B).comp φ) := by
      rw [← RingHom.comp_assoc, ← ResidueField.map_comp_residue, RingHom.comp_assoc]
    rw [e]
    have hm' : (ResidueField.map ρ).Finite := by
      have h := RingHom.Finite.comp (RingHom.Finite.of_surjective (residue C) residue_surjective) hfin
      rw [← ResidueField.map_comp_residue] at h
      exact RingHom.Finite.of_comp_finite h
    exact RingHom.Finite.comp hm' h3

theorem regular_of_finite_of_formallyUnramified {A B : Type} [CommRing A] [CommRing B] [IsRegularLocalRing A]
    [IsLocalRing B] (ρ : A →+* B) [IsLocalHom ρ] (hi : Function.Injective ρ) (hfin : ρ.Finite)
    (hu : ρ.FormallyUnramified) :
    (maximalIdeal A).map ρ = maximalIdeal B ∧ IsRegularLocalRing B ∧ ρ.Flat := by
  algebraize [ρ]
  haveI : IsLocalHom (algebraMap A B) := ‹IsLocalHom ρ›
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  have hm : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B := Algebra.FormallyUnramified.map_maximalIdeal
  have hd : ringKrullDim B = ringKrullDim A := ReciprocityTheory.CA.ringKrullDim_eq_of_isIntegral_of_injective hi
  haveI hreg : IsRegularLocalRing B := by
    apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
    have h1 := Ideal.spanFinrank_map_le_of_fg (algebraMap A B) (maximalIdeal A).fg_of_isNoetherianRing
    rw [hm] at h1
    rw [hd, ← IsRegularLocalRing.spanFinrank_maximalIdeal]
    exact_mod_cast h1
  refine ⟨hm, hreg, ?_⟩
  haveI : Module.Free A B := GlobalTheory.free_of_isRegularLocalRing_of_finite hd.symm
  exact (inferInstance : Module.Flat A B)

theorem completedStalk_chart (X : Scheme.{0}) (x : X) [IsNoetherianRing (X.presheaf.stalk x)] :
    IsEtaleCompletion (Scheme.stalkClosedPointTo (GlobalTheory.fromSpecCompletedStalk X x)).hom ∧
      Function.Surjective ((residue (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))).comp
        (Scheme.stalkClosedPointTo (GlobalTheory.fromSpecCompletedStalk X x)).hom) := by
  have fg : (maximalIdeal (X.presheaf.stalk x)).FG := IsNoetherian.noetherian _
  have hm := AdicCompletion.maximalIdeal_eq_map_of_fg fg
  let φ := algebraMap (X.presheaf.stalk x) (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))
  haveI : IsLocalHom φ := ((IsLocalRing.local_hom_TFAE φ).out 0 2).mpr hm.symm.le
  have hres : Function.Surjective ((residue _).comp φ) := by
    intro r
    obtain ⟨a, ha⟩ := (AdicCompletion.residueField_map_bijective (X.presheaf.stalk x)).2 r
    obtain ⟨b, rfl⟩ := residue_surjective a
    refine ⟨b, ?_⟩
    rw [← ha, RingHom.comp_apply, ResidueField.map_residue]
  have hx : GlobalTheory.fromSpecCompletedStalk X x (closedPoint _) = x := by
    rw [GlobalTheory.fromSpecCompletedStalk]
    erw [Scheme.Hom.comp_apply]
    have hc : Spec.map (CommRingCat.ofHom φ) (closedPoint _) = closedPoint (X.presheaf.stalk x) :=
      IsLocalRing.comap_closedPoint φ
    erw [hc]
    exact Scheme.fromSpecStalk_closedPoint
  obtain ⟨e, he, hψ⟩ := GlobalTheory.GenFan.stalk_factor_eq hx (CommRingCat.ofHom φ)
    (Scheme.stalkClosedPointTo (GlobalTheory.fromSpecCompletedStalk X x))
    (Scheme.Spec_stalkClosedPointTo_fromSpecStalk _)
  refine ⟨?_, ?_⟩
  · rw [hψ]
    exact isEtaleCompletion_comp_bij e he φ ⟨RingHom.flat_algebraMap_iff.2 (AdicCompletion.flat_of_isNoetherian _),
      hm.symm, RingHom.Finite.of_surjective _ hres⟩
  · rw [hψ, ← RingHom.comp_assoc]
    exact hres.comp he.2

end GlobalTheory.InteriorChart

namespace GlobalTheory.InteriorChart

theorem chart : ∀ (g n : ℕ), 3 ≤ n → ∀ (F : SFam g n (zetaAway n)) (x₀ : F.X), ∃ (R : Type) (_ : CommRing R) (_ : IsRegularLocalRing R) (_ : IsDomain R) (ξ₀ : Sp R ⟶ F.X), IsAdicComplete (maximalIdeal R) R ∧ CharZero R ∧ ξ₀ (closedPoint R) = x₀ ∧ IsEtaleCompletion (Scheme.stalkClosedPointTo ξ₀).hom ∧ ((residue R).comp (Scheme.stalkClosedPointTo ξ₀).hom).FormallyUnramified ∧ ∃ (B : Over (Sp R)) (_ : GrpObj B) (_ : IsCommMonObj B) (β : B.left ⟶ F.univ.A.left) (β₂ : (G2 B).left ⟶ (G2 F.univ.A).left) (M : RigLB B) (_ : CubicalStr B M), IsGrpPullback B F.univ.A ξ₀ β ∧ IsSquare β β₂ ∧ RelAmple B M.L ∧ KTriv B M.L ∧ LBIso (abelian₂ B M.L) (F.univ.P.pull β₂) := by
  intro g n _ F x₀

  haveI : IsRegularLocalRing (GlobalTheory.LowChart.W F (r := 0) x₀) := GlobalTheory.LowChart.isRegularLocalRing_W_of_isRegularRing F (r := 0) x₀
  haveI hc₀ : IsAdicComplete (maximalIdeal (GlobalTheory.LowChart.W F (r := 0) x₀)) (GlobalTheory.LowChart.W F (r := 0) x₀) :=
    GlobalTheory.LowChart.isAdicComplete_completedStalkSiegelFibrePower F (r := 0) x₀
  haveI : CharZero (GlobalTheory.LowChart.W F (r := 0) x₀) := GlobalTheory.LowChart.charZero_W_of_charZero F (r := 0) x₀
  haveI : IsRegularLocalRing (F.X.presheaf.stalk x₀) := GlobalTheory.LowChart.isRegularLocalRing_stalk F (r := 0) x₀
  let y₀ : Sp (GlobalTheory.LowChart.W F (r := 0) x₀) ⟶ F.X := GlobalTheory.LowChart.toPow F (r := 0) x₀
  have hx : y₀ (closedPoint (GlobalTheory.LowChart.W F (r := 0) x₀)) = x₀ := GlobalTheory.LowChart.toPow_closedPoint F (r := 0) x₀
  obtain ⟨hEt₀, hres₀⟩ := completedStalk_chart F.X x₀
  change IsEtaleCompletion (Scheme.stalkClosedPointTo y₀).hom at hEt₀
  change Function.Surjective ((residue (GlobalTheory.LowChart.W F (r := 0) x₀)).comp (Scheme.stalkClosedPointTo y₀).hom) at hres₀

  obtain ⟨R', _, _, ρ, hc', hloc, hinj, hfin, hfu, B, _, _, β, β₂, M, hcub, hpb, hsq, hamp, hk, hiso⟩ :=
    GlobalTheory.T.finite_unramified_extension_group_lift F (GlobalTheory.LowChart.W F (r := 0) x₀) hc₀ y₀
  obtain ⟨hm', hreg', hflat⟩ := regular_of_finite_of_formallyUnramified ρ hinj hfin hfu
  have hdom : IsDomain R' := (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing R').1
  have hcz : CharZero R' := charZero_of_injective_ringHom hinj
  let ξ₀ : Sp R' ⟶ F.X := spMap ρ ≫ y₀
  have hcp : ξ₀ (closedPoint R') = y₀ (closedPoint (GlobalTheory.LowChart.W F (r := 0) x₀)) := by
    show y₀ (spMap ρ (closedPoint R')) = _
    rw [show spMap ρ (closedPoint R') = closedPoint (GlobalTheory.LowChart.W F (r := 0) x₀) from IsLocalRing.comap_closedPoint ρ]
  have hs : ξ₀ (closedPoint R') ⤳ y₀ (closedPoint (GlobalTheory.LowChart.W F (r := 0) x₀)) := specializes_of_eq hcp
  have key := GlobalTheory.TorRef.stalkClosedPointTo_comp_spMap_specializes F.X y₀ ρ hs
  let E := RingEquiv.ofBijective (F.X.presheaf.stalkSpecializes hs).hom (bijective_stalkSpecializes hcp hs)
  have hξ : (Scheme.stalkClosedPointTo ξ₀).hom =
      (ρ.comp (Scheme.stalkClosedPointTo y₀).hom).comp E.symm.toRingHom := by
    ext b
    obtain ⟨a, rfl⟩ := E.surjective b
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.symm_apply_apply]
    exact key a
  refine ⟨R', inferInstance, hreg', hdom, ξ₀, hc', hcz, hcp.trans hx, ?_, ?_, B, inferInstance, inferInstance, β, β₂, M,
    hcub, hpb, hsq, hamp, hk, hiso⟩
  · rw [hξ]
    exact isEtaleCompletion_comp_bij _ E.symm.bijective _ (isEtaleCompletion_comp _ ρ hEt₀ hflat hm' hfin)
  · have hmap : (ResidueField.map ρ).FormallyUnramified := by
      apply RingHom.FormallyUnramified.of_comp (f := residue (GlobalTheory.LowChart.W F (r := 0) x₀))
      rw [ResidueField.map_comp_residue]
      exact RingHom.FormallyUnramified.comp hfu (RingHom.FormallyUnramified.of_surjective residue_surjective)
    have e2 : (residue R').comp (Scheme.stalkClosedPointTo ξ₀).hom = (ResidueField.map ρ).comp
        (((residue (GlobalTheory.LowChart.W F (r := 0) x₀)).comp (Scheme.stalkClosedPointTo y₀).hom).comp E.symm.toRingHom) := by
      rw [hξ, ← RingHom.comp_assoc, ← RingHom.comp_assoc, ← ResidueField.map_comp_residue]
      rfl
    rw [e2]
    exact RingHom.FormallyUnramified.comp
      (RingHom.FormallyUnramified.of_surjective (hres₀.comp E.symm.surjective)) hmap

end GlobalTheory.InteriorChart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareCommutationIntegralIdentity
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

namespace GlobalTheory.ThetaAgreeConv

theorem map_finRel_eq_zero {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {W W₁ X : HSp D}
    {A : GlobalTheory.ChainFr.Fr W} {A₁ : GlobalTheory.ChainFr.Fr W₁} {B : GlobalTheory.ChainFr.Fr X} {α β : (AE D)ˣ →* Circle} {ωA ωB Pi rf rl p p'}
    (hM : GlobalTheory.SquareComm.IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p') {Ψ}
    (hΨ : Ψ ∈ GlobalTheory.SquareComm.finRel ωB (GlobalTheory.SquareComm.algF ψ θ false A₁ B)) : p' Ψ = 0 := by
  have hle : GlobalTheory.SquareComm.finRel ωB (GlobalTheory.SquareComm.algF ψ θ false A₁ B) ≤ LinearMap.ker p' := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, hu, Ψ, hΨ, rfl⟩
    show p' (ωB (u, 1) Ψ - Ψ) = 0
    rw [map_sub, hM.mapB.invf u hu Ψ hΨ, sub_self]
  exact hle hΨ

section Reg

open MeasureTheory GlobalTheory.SquareComm GlobalTheory.RegCompare

variable {D : D7}

theorem intg_right {M X : HSp D} {ω : GlobalTheory.Grid.WRep M X} {ν : Measure (GA D M)} {𝓕 : Set (GA D M)}
    (hν : IsHaarFD M ν 𝓕) {Φ : WO M X → ℂ} (hL : ∀ γ ∈ GQ M, ∀ g h, thetaKO ω (γ * g) h Φ = thetaKO ω g h Φ)
    (hΦ : Intg ω ν 𝓕 Φ) (k : GA D M) :
    Intg ω ν 𝓕 (ω (k, 1) Φ) ∧ thetaInt ω ν 𝓕 (ω (k, 1) Φ) = thetaInt ω ν 𝓕 Φ := by
  haveI := hν.1
  have key := fun h => setIntegral_mul_right' M ν 𝓕 hν.2 (fun g => thetaKO ω g h Φ)
    (fun γ hγ u => hL γ hγ u h) (hΦ h) k
  refine ⟨fun h => ?_, ?_⟩
  · simpa only [thetaKO_right] using (key h).1
  · funext h
    simp only [thetaInt, thetaKO_right]
    exact (key h).2

theorem thetaInt_wop_of_intg {M X : HSp D} {ω : GlobalTheory.Grid.WRep M X} {ν : Measure (GA D M)} {𝓕 : Set (GA D M)}
    (hν : IsHaarFD M ν 𝓕) {Φ : WO M X → ℂ} (hL : ∀ γ ∈ GQ M, ∀ g h, thetaKO ω (γ * g) h Φ = thetaKO ω g h Φ)
    (hΦ : Intg ω ν 𝓕 Φ) (z : GA D M →₀ ℂ) :
    thetaInt ω ν 𝓕 (wop ω z Φ) = GlobalTheory.FunObj.zdeg z • thetaInt ω ν 𝓕 Φ := by
  have hk := fun k => intg_right hν hL hΦ k
  rw [wop_apply, thetaInt_sum _ fun k _ => ((hk k).1).smul _]
  simp only [thetaInt_smul, (hk _).2, GlobalTheory.FunObj.zdeg, Finsupp.sum, Finset.sum_smul]

theorem thetaInt_eq_zero_of_finRel (hP : GlobalTheory.FunPr.Hypotheses₂) (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree)
    {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) {W W₁ X : HSp D} {A₁ : GlobalTheory.ChainFr.Fr W₁}
    {B : GlobalTheory.ChainFr.Fr X} {α β : (AE D)ˣ →* Circle} (hT : IsTriple W W₁ X α β) {ν₁ : Measure (GA D W₁)}
    {𝓕₁ : Set (GA D W₁)} (hν₁ : IsHaarFD W₁ ν₁ 𝓕₁) {ωB : GlobalTheory.Grid.WRep W₁ X}
    (hw : GlobalTheory.Grid.IsWeil ψ false W₁ X α (α / β) ωB)
    (hstab : ∀ g ∈ GfC W₁, ∀ Φ ∈ algF ψ θ false A₁ B, ωB (g, 1) Φ ∈ algF ψ θ false A₁ B)
    {Ψ : WO W₁ X → ℂ} (hΨ : Ψ ∈ finRel ωB (algF ψ θ false A₁ B)) (hint : Intg ωB ν₁ 𝓕₁ Ψ) :
    thetaInt ωB ν₁ 𝓕₁ Ψ = 0 := by
  set S := algF ψ θ false A₁ B with hSdef
  have hL : ∀ Φ ∈ S, ∀ γ ∈ GQ W₁, ∀ g h, thetaKO ωB (γ * g) h Φ = thetaKO ωB g h Φ :=
    GlobalTheory.T.thetaKernel_leftInvariant_rational_unitary D ψ θ hθ W₁ X A₁ B α (α / β) ωB hw
  have hle : finRel ωB S ≤ S := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, hu, Φ, hΦ, rfl⟩
    exact S.sub_mem (hstab u hu Φ hΦ) hΦ
  have hΨS : Ψ ∈ S := hle hΨ
  have hrel := hΨ
  rw [finRel, Submodule.mem_span_set'] at hrel
  obtain ⟨n, c, g, hsum⟩ := hrel
  choose u hu Ψi hΨi hg using fun i => (g i).2
  obtain ⟨z, hzG, hz0, hz⟩ := GlobalTheory.T.seesaw_identity_weil_triple hP hK D ψ θ hθ W W₁ X A₁ B α β hT ν₁ 𝓕₁ hν₁ ωB hw n Ψi u hΨi hu
  have hX : ∀ i, ModInt θ ωB ν₁ 𝓕₁ (wop ωB z (Ψi i)) ∧
      ∃ u' ∈ GfC W₁, wop ωB z (ωB (u i, 1) (Ψi i)) = ωB (u', 1) (wop ωB z (Ψi i)) := fun i => hz i
  choose u' hu' hcomm using fun i => (hX i).2
  have hXS : ∀ i, wop ωB z (Ψi i) ∈ S := fun i => wop_mem hstab hzG (hΨi i)
  have hXr := fun i => modInt_right hν₁ (hL _ (hXS i)) (hX i).1 (u' i)
  have eΨ : Ψ = ∑ i, c i • (ωB (u i, 1) (Ψi i) - Ψi i) := by
    have e : ∑ i, c i • (g i : WO W₁ X → ℂ) = ∑ i, c i • (ωB (u i, 1) (Ψi i) - Ψi i) := by simp only [hg]
    rw [← e, hsum]
  have eW : wop ωB z Ψ = ∑ i, c i • (ωB (u' i, 1) (wop ωB z (Ψi i)) - wop ωB z (Ψi i)) := by
    rw [eΨ, map_sum]
    simp only [map_smul, map_sub, hcomm]
  have hJ : thetaInt ωB ν₁ 𝓕₁ (wop ωB z Ψ) = 0 := by
    have hi : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        Intg ωB ν₁ 𝓕₁ (c i • (ωB (u' i, 1) (wop ωB z (Ψi i)) - wop ωB z (Ψi i))) := fun i _ =>
      ((intg_of_modInt (hXr i).1).sub (intg_of_modInt (hX i).1)).smul _
    rw [eW, thetaInt_sum _ hi]
    simp only [thetaInt_smul, thetaInt_sub (intg_of_modInt (hXr _).1) (intg_of_modInt (hX _).1), (hXr _).2, sub_self,
      smul_zero, Finset.sum_const_zero]
  rw [thetaInt_wop_of_intg hν₁ (hL Ψ hΨS) hint z] at hJ
  exact (smul_eq_zero.1 hJ).resolve_left hz0

end Reg

theorem thetaIntegralsAgree_of_integrable : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : GlobalTheory.ChainFr.Fr W) (A₁ : GlobalTheory.ChainFr.Fr W₁) (B : GlobalTheory.ChainFr.Fr X) (α β : (AE D)ˣ →* Circle),
    GlobalTheory.SquareComm.IsTriple W W₁ X α β →
    ∀ (ν : MeasureTheory.Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : MeasureTheory.Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁)),
    GlobalTheory.SquareComm.IsHaarFD W ν 𝓕 → GlobalTheory.SquareComm.IsHaarFD W₁ ν₁ 𝓕₁ →
    ∀ ωA ωB Pi rf rl p p', GlobalTheory.SquareComm.IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∃ c : ℂ, c ≠ 0 ∧ ∀ Φ ∈ GlobalTheory.SquareComm.algF ψ θ true A B, ∀ Φ' ∈ GlobalTheory.SquareComm.algF ψ θ false A₁ B,
      (∀ h, MeasureTheory.IntegrableOn (fun g => thetaKO ωB g h Φ') 𝓕₁ ν₁) → p Φ = p' Φ' →
      GlobalTheory.SquareComm.thetaInt ωA ν 𝓕 Φ = c • GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Φ' := by
  intro hP hK hL D ψ θ hψ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB Pi rf rl p p' hM
  obtain ⟨c, hc0, hc⟩ := GlobalTheory.T.theta_integrals_of_minguez hP.minguezThetaGL hP hK hL D ψ θ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ hν hν₁
    ωA ωB Pi rf rl p p' hM
  refine ⟨c, hc0, fun Φ hΦ Φ' hΦ' hint hp => ?_⟩
  obtain ⟨Φ₀, -, hrel, ⟨N, C, hmod⟩, hI⟩ := hc Φ' hΦ'
  have hp0 : p' Φ' = p' Φ₀ := by
    have := map_finRel_eq_zero hM hrel
    rwa [map_sub, sub_eq_zero] at this
  rw [hI Φ hΦ (hp.trans hp0)]
  congr 1
  have hlin : ∀ g h, thetaKO ωB g h (Φ' - Φ₀) = thetaKO ωB g h Φ' - thetaKO ωB g h Φ₀ := fun g h => by
    simp only [thetaKO, map_sub, _root_.Pi.sub_apply]
  have hint' : ∀ h, MeasureTheory.IntegrableOn (fun g => thetaKO ωB g h (Φ' - Φ₀)) 𝓕₁ ν₁ := fun h => by
    simp only [hlin]; exact (hint h).sub (hmod h).1
  have h0 := GlobalTheory.ThetaAgreeConv.thetaInt_eq_zero_of_finRel hP hK hθ hT hν₁ hM.weilB hM.mapB.stabM.1 hrel hint'
  funext h
  have e := congrFun h0 h
  simp only [GlobalTheory.SquareComm.thetaInt, hlin, _root_.Pi.zero_apply] at e ⊢
  rw [MeasureTheory.integral_sub (hint h) (hmod h).1] at e
  exact (sub_eq_zero.1 e).symm

end GlobalTheory.ThetaAgreeConv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsTorusTranslatesTwistedSums
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

noncomputable section

theorem GlobalTheory.Poinc.Sep.twistSum_translate : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∃ (sg : ℤˣ) (eps : X₁.S.Gam → X₁.S.Gam → ℕ), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : (Fin 8 → X) → C → V, 𝔪.Terms x₀ lab T → ∀ (c : C), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∀ zt h : X₁.M.Z.presheaf.stalk z₁, X₁.M.stalkHom z₁ zt = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) → X₁.M.stalkHom z₁ h = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ eps (lab c) τ) * X₁.S.th (lab c + τ) / X₁.S.th x₀ → ∀ wt : (Fin 8 → X) → ZMod (X₁.S.r * X₁.S.N), (∀ a mu, 𝔪.YY a mu → wt mu = (sg : ℤ) • eStd X₁.S.g _ τ a) → SumI (maximalIdeal V) (fun mu => ev zt ^ (wt mu).val * T mu c) (ev h) := by
  intro g n F W Z i X₁ z₁ act x₀ hdiv
  obtain ⟨sg, hsg, hweil⟩ := GlobalTheory.T.exists_thetaTwistedSum_sign_everyMember g n F W Z i X₁ z₁ act x₀ hdiv
  classical
  let Wit : X₁.S.Gam → X₁.S.Gam → ℕ → Prop := fun a τ e =>
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (ev : X₁.M.Z.presheaf.stalk z₁ →+* V)
      (X : Type) (_ : AddCommGroup X) (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X)
      (𝔪 : UMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam) (_ : ∀ c, lab c ∈ X₁.S.HH X₁.M z₁)
      (T : (Fin 8 → X) → C → V) (_ : 𝔪.Terms x₀ lab T) (c : C), lab c = a ∧
      TwistSum X₁ z₁ act x₀ 𝔪 lab T sg c τ e ∧
      ∃ r : X₁.M.Z.presheaf.stalk z₁, X₁.M.stalkHom z₁ r = X₁.S.th (lab c + τ) / X₁.S.th x₀ ∧ ev r ≠ 0
  refine ⟨sg, fun a τ => if h : ∃ e, Wit a τ e then h.choose else 0, ?_⟩
  intro V _ _ _ ev X _ m t δ 𝔪 C lab hlab T hT c τ hτ zt h hzt hh wt hwt
  obtain ⟨e₂, he₂⟩ := hsg V ev X m t δ 𝔪 C lab hlab T hT c τ hτ
  by_cases hW : ∃ e, Wit (lab c) τ e
  · beta_reduce at hh
    rw [dif_pos hW] at hh
    obtain ⟨V₁, _, _, _, ev₁, Y₁, _, m₁, t₁, δ₁, 𝔪₁, C₁, lab₁, hlab₁, T₁, hT₁, c₁, hc₁, hts, r, hr, hr0⟩ := hW.choose_spec
    have key := GlobalTheory.T.twistedThetaSum_zeta_exponent_independent_member g n F W Z i X₁ z₁ act x₀ hdiv sg hsg hweil V₁ ev₁ Y₁ m₁ t₁ δ₁ 𝔪₁ C₁ lab₁ hlab₁ T₁ hT₁ c₁
      V ev X m t δ 𝔪 C lab hlab T hT c hc₁ τ hτ _ e₂ hts he₂ ⟨r, hr, hr0⟩
    exact key zt h hzt hh wt hwt
  · beta_reduce at hh
    rw [dif_neg hW] at hh
    have hh' : X₁.M.stalkHom z₁ h = X₁.S.th (lab c + τ) / X₁.S.th x₀ := by rw [hh]; simp
    have hev : ev h = 0 := by
      by_contra hne
      exact hW ⟨e₂, V, inferInstance, inferInstance, inferInstance, ev, X, inferInstance, m, t, δ, 𝔪, C, lab, hlab, T, hT, c,
        rfl, he₂, h, hh', hne⟩
    obtain ⟨s, hs⟩ := exists_stalk_zeta X₁ z₁ (X₁.S.ζ ^ e₂)
    have := he₂ zt (s * h) hzt (by rw [map_mul, hs, hh', mul_div_assoc]) wt hwt
    rw [map_mul, hev, mul_zero] at this
    rwa [hev]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberExistsTermsDividingGroupLabel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

noncomputable section

namespace GlobalTheory.GSep

theorem exists_terms_single : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (t1 : Y1 → V1) (δ1 : I → Y1 → Y1) (𝔪1 : GlobalTheory.GSep.GMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (a : X₁.S.Gam), a ∈ X₁.S.HH X₁.M z₁ → ∃ T : Y1 → Unit → V1, 𝔪1.Terms x₀ (fun _ : Unit => a) T := by
  intro I X₁ z₁ act x₀ hdiv V _ _ _ ev Y _ t δ 𝔪 a ha
  obtain ⟨u, ⟨x, fr, th, w₀, s, g', w, hx, hfr, hth, hw₀, hs, hc, hT⟩, -, -⟩ :=
    GlobalTheory.T.thetaMember_exists_integral_terms_unit_shift I X₁ z₁ act x₀ hdiv V ev Y t δ 𝔪 (X₁.S.HH X₁.M z₁) Subtype.val Subtype.range_coe
  exact ⟨fun mu _ => u mu ⟨a, ha⟩ * t mu, x, fr, th, w₀, s, fun _ => g' ⟨a, ha⟩, fun _ => w ⟨a, ha⟩, hx, hfr, hth,
    hw₀, hs, fun _ => hc ⟨a, ha⟩, fun mu _ => hT mu ⟨a, ha⟩⟩

end GlobalTheory.GSep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberExistsTermsTorusTranslate
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

noncomputable section
namespace GlobalTheory.GSep.TermsExt
open GlobalTheory.UT.CoefBasic GlobalTheory.UT.TorsionValue

theorem exists_frAt_ratio {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {K : Type} [Field K] [Algebra (FractionRing R) K] {x : TFK (R := R) K ⟶ A.A} {e e' : FrAt x} (he : e.IsGen)
    (he' : e'.IsGen) : ∃ c : K, c ≠ 0 ∧ ∀ z J, Good A.L z J → (val e' (𝟙 _) z J).val =
      @id ((TFK (R := R) K).left.presheaf.stalk z) (cstH (R := R) z c) * (val e (𝟙 _) z J).val := by
  obtain ⟨z⟩ : Nonempty (TFK (R := R) K).left := exists_pt (R := R) (F := K)
  obtain ⟨J', hJ'⟩ := exists_good' A.isLB z
  obtain ⟨c, hc⟩ := cstH_surj (R := R) (F := K) z (val e' (𝟙 _) z J' * (val e (𝟙 _) z J')⁻¹).val
  refine ⟨c, fun h => ?_, fun z' J hJ => ?_⟩
  · rw [h, map_zero] at hc
    exact Units.ne_zero _ hc.symm
  · obtain rfl : z = z' := pt_eq (R := R) (F := K) z z'
    rw [hc, val_tr he (𝟙 _) hJ hJ', val_tr he' (𝟙 _) hJ hJ']
    refine Eq.trans ?_ (Units.val_mul _ _)
    congr 1
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

theorem over_scale {I : Type} {X₁ : GlobalTheory.GSep.GSet} {z₁ : X₁.M.Z} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
    {X : Type} [AddCommGroup X] {t : X → V} {δ : I → X → X}
    (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) {w₀ : W0 𝔪.U.toUnifPre} {g' : GtPtF 𝔪.D.toPre (FractionRing V)}
    {w w' : Frm 𝔪.D.toPre (FractionRing V) 1 g'.b} (hw : w.IsGen) {x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A}
    {e e' : FrAt x} {c : FractionRing V} (hc : c ≠ 0)
    (he : ∀ z J, Good 𝔪.A.L z J → (val e' (𝟙 _) z J).val =
      @id ((TFK (R := V) (FractionRing V)).left.presheaf.stalk z) (cstH (R := V) z c) * (val e (𝟙 _) z J).val)
    (hv : ∀ z J, Good 𝔪.D.toPre.P.L z J → (val w' (𝟙 _) z J).val = cst (FractionRing V) z c⁻¹ * (val w (𝟙 _) z J).val)
    (h : 𝔪.Over' w₀ g' w x e) : 𝔪.Over' w₀ g' w' x e' := by
  intro k hk wk' hwk' _ s s' v hs hval
  obtain ⟨wk, hwk, hwkv⟩ := exists_frm_pow w hw k
  have pf : ∀ (e : FrAt x) z J, val (powFrame 𝔪.A.A 𝔪.A.L x e (k : ℤ)) (𝟙 _) z J = val e (𝟙 _) z J ^ k :=
    fun e z J => (map_zpow _ _ _).trans (zpow_natCast _ _)
  have hval' : ValAt s x e (c ^ k * v) := fun z J hJ => by
    have cm : @id ((TFK (R := V) (FractionRing V)).left.presheaf.stalk z) (cst (R := V) (FractionRing V) z (c ^ k * v)) =
        @id ((TFK (R := V) (FractionRing V)).left.presheaf.stalk z) (cstH (R := V) z c) ^ k *
          @id ((TFK (R := V) (FractionRing V)).left.presheaf.stalk z) (cst (R := V) (FractionRing V) z v) :=
      (cst_eq (R := V) z _).trans ((map_mul _ _ _).trans
        (congrArg₂ (· * ·) (map_pow _ _ _) (cst_eq (R := V) z _).symm))
    rw [hval z J hJ, pf, pf, cm, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, he z J hJ]
    ring
  have S := sumF_const_mul (c⁻¹ ^ k) (h k hk wk hwkv hwk s s' _ hs hval')
  have sc := coef_scale (w' := wk') hwk (c := c⁻¹ ^ k) (fun z J hJ => by
    rw [hwk' z J hJ, hwkv z J hJ, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hv z J hJ, mul_pow,
      cst_eq, cst_eq, map_pow]) s'
  rw [← _root_.mul_assoc, ← mul_pow, inv_mul_cancel₀ hc, one_pow, _root_.one_mul] at S
  simpa only [← sc] using S

attribute [local instance] GlobalTheory.TorusExt.gtGroup in

theorem exists_terms_translate : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : X → C → V, 𝔪.Terms x₀ lab T → ∀ (c : C), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ T' : X → Unit → V, 𝔪.Terms x₀ (fun _ : Unit => lab c + τ) T' := by
  intro I X₁ z₁ act x₀ _ V _ _ _ ev X _ t δ 𝔪 C lab _ T hT c τ hτ
  obtain ⟨χ, hχ, hyp⟩ := GlobalTheory.T.exists_torus_char_of_label_orthogonal_dividing I X₁ z₁ act V ev X t δ 𝔪 τ hτ
  obtain ⟨x, fr, th, w₀, s, g', w, hx, hfr, hth, hw₀, hs, hc, hTc⟩ := hT
  obtain ⟨ρA, hρA, htors⟩ := GlobalTheory.GSep.TwistTranslate.exists_rig_torsFrame 𝔪 x fr hx hfr
  have hg₀ : IsTor χ (GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)) :=
    (isTor_iff _ _).2 (GlobalTheory.TorusExt.isTorusPtF_torusPt χ)
  obtain ⟨p, xτ, hpy, hpg, hq, hxτ⟩ := hyp _ hg₀
  have hadd := (GlobalTheory.TorusExt.isAdd_iff_eq (g' c) (GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)) _).2 rfl
  have hb := (GlobalTheory.UT.ThetaAverage.val_translate hg₀ hadd).1
  obtain ⟨w'', hw''g, hw''v⟩ : ∃ w'' : Frm 𝔪.D.toPre (FractionRing V) 1 (g' c + GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)).b,
      w''.IsGen ∧ ∀ z J, val w'' (𝟙 _) z J = val (w c) (𝟙 _) z J := by
    revert hb
    generalize (g' c + GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)).b = b
    rintro rfl
    exact ⟨w c, (hc c).2.1, fun _ _ => rfl⟩
  obtain ⟨e₂, he₂, hov⟩ := GlobalTheory.GSep.TwistTranslate.over_translate 𝔪 w₀ hw₀ ρA hρA (x (lab c)) (fr (lab c)) (htors _)
    (g' c) (w c) (hc c).1 (hc c).2.1 (hc c).2.2 χ hχ _ hg₀ p xτ hpy hpg hq _ hadd w'' (fun z J _ => hw''v z J)
    (x (lab c + τ)) (GlobalTheory.GSep.TwistTranslate.x_add 𝔪 x hx (lab c) τ xτ hxτ)
  obtain ⟨u, hu, huv⟩ := exists_frAt_ratio he₂.2.1 (htors (lab c + τ)).2.1
  have hk : 0 < X₁.S.r * X₁.S.N := Nat.mul_pos X₁.S.r_pos (by have := X₁.S.N_ge; omega)
  have hu1 : u ^ ((X₁.S.r * X₁.S.N) ^ 2 * (X₁.S.r * X₁.S.N) ^ 2) = 1 := by
    obtain ⟨z⟩ : Nonempty (TFK (R := V) (FractionRing V)).left := exists_pt (R := V) (F := FractionRing V)
    obtain ⟨J, hJ⟩ := exists_good' 𝔪.A.isLB z
    have q := GlobalTheory.Poinc.DivDeep.torsFrame_two_levels 𝔪.A (htors (lab c + τ)) he₂ hJ
    rw [div_self', one_pow] at q
    have q' := congrArg Units.val q
    have e : (val (fr (lab c + τ)) (𝟙 _) z J / val e₂ (𝟙 _) z J).val =
        @id ((TFK (R := V) (FractionRing V)).left.presheaf.stalk z) (cstH (R := V) z u) := by
      rw [div_eq_mul_inv, Units.val_mul, huv z J hJ, Units.mul_inv_cancel_right]
    rw [Units.val_pow_eq_pow_val, e] at q'
    exact cstH_inj (R := V) z ((map_pow _ _ _).trans (q'.trans (map_one _).symm))
  obtain ⟨w₃, hw₃, hw₃v⟩ := exists_frm_scale w'' hw''g (inv_ne_zero hu)
  have hov' := over_scale 𝔪 hw''g hu huv hw₃v hov
  have hco : ∀ χ', coef s (g' c + GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)) w₃ χ' =
      u⁻¹ * ((χ (Multiplicative.ofAdd χ') : (FractionRing V)ˣ) : FractionRing V) * coef s (g' c) (w c) χ' := fun χ' =>
    GlobalTheory.UT.ThetaAverage.coef_translate hg₀ hadd (hc c).2.1 (fun z J hJ => by rw [hw₃v z J hJ, hw''v, cst_eq]) s χ'
  haveI : IsIntegrallyClosed V := 𝔪.cn.2.1
  have hint : ∀ mu : X, ∃ a : V, algebraMap V (FractionRing V) a =
      u⁻¹ * ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) := fun mu => by
    refine IsIntegrallyClosed.isIntegral_iff.1 (IsIntegral.mul ?_ ?_)
    · refine IsIntegral.of_pow (n := (X₁.S.r * X₁.S.N) ^ 2 * (X₁.S.r * X₁.S.N) ^ 2) (by positivity) ?_
      rw [inv_pow, hu1, inv_one]
      exact isIntegral_one
    · refine IsIntegral.of_pow hk ?_
      rw [← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, hχ, MonoidHom.one_apply, Units.val_one]
      exact isIntegral_one
  choose a ha using hint
  refine ⟨fun mu _ => a mu * T mu c, x, fr, th, w₀, s, fun _ => _, fun _ => w₃, hx, hfr, hth, hw₀, hs,
    fun _ => ⟨⟨0, (GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).2 ?_, (GlobalTheory.TorusExt.isZero_iff_eq _).2 rfl⟩, hw₃, hov'⟩,
    fun mu _ => ?_⟩
  · obtain ⟨o, ho, ho'⟩ := (hc c).1
    rw [smul_add, ← (GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).1 ho, (GlobalTheory.TorusExt.isZero_iff_eq _).1 ho', ← map_nsmul,
      ← ofMul_pow, hχ, ofMul_one, map_zero, add_zero]
  · rw [hco, map_mul, ha, ← hTc, _root_.mul_assoc]

end GlobalTheory.GSep.TermsExt
end
end

