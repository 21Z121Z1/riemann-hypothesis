import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0873
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteTorusExtensionOfModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2471
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PullQkSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0796
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PsiGenOnInteriorOfPsiUnitOn
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2380
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2478
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0066
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinExtTqClosedFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem exists_cover_step (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hR : GlobalTheory.TorRef.IsCN R)
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] (e₀ : ResidueField R →+* Ω) (t : Ω) (q : Polynomial (ResidueField R))
    (hq : q.Monic) (hqt : q.eval₂ e₀ t = 0) :
    ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (_ : IsLocalHom ρ)
      (β : ResidueField R' →+* Ω), GlobalTheory.TorRef.IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧
      β.comp (ResidueField.map ρ) = e₀ ∧ t ∈ Set.range β := by
  letI : Algebra (ResidueField R) Ω := e₀.toAlgebra
  have hint : IsIntegral (ResidueField R) t := ⟨q, hq, hqt⟩
  set p := minpoly (ResidueField R) t with hpdef
  have hpm : p.Monic := minpoly.monic hint
  have hirr : Irreducible p := minpoly.irreducible hint
  have hdeg : 0 < p.degree := minpoly.degree_pos hint
  have hpt : p.eval₂ e₀ t = 0 := minpoly.aeval _ t
  have hlift : p ∈ Polynomial.lifts (residue R) :=
    (Polynomial.lifts_iff_set_range p).2 (Polynomial.map_surjective _ IsLocalRing.residue_surjective p)
  obtain ⟨P, hPmap, hPdeg, hPm⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hpm
  let C := AdjoinRoot P
  have hfinC : (AdjoinRoot.of P).Finite := by
    have : Module.Finite R (AdjoinRoot P) := (AdjoinRoot.powerBasis' hPm).finite
    exact RingHom.finite_algebraMap.2 this
  have hinjC : Function.Injective (AdjoinRoot.of P) := by
    refine (injective_iff_map_eq_zero _).2 fun r hr => ?_
    rw [AdjoinRoot.of, RingHom.comp_apply, AdjoinRoot.mk_eq_zero] at hr
    have h0 := Polynomial.eq_zero_of_dvd_of_degree_lt hr
      (lt_of_le_of_lt Polynomial.degree_C_le (hPdeg ▸ hdeg))
    simpa using h0
  obtain ⟨R', i1, i2, i3, ρ, σ, hcn', hinj', hfin', hloc, hσ⟩ :=
    GlobalTheory.LocExt.exists_isCN_cover_of_finite R C (AdjoinRoot.of P) hR hinjC hfinC
  let r : ResidueField R' := residue R' (σ (AdjoinRoot.root P))
  have hres : (ResidueField.map ρ).comp (residue R) = (residue R').comp ρ := ResidueField.map_comp_residue ρ
  have hr : p.eval₂ (ResidueField.map ρ) r = 0 := by
    rw [← hPmap, Polynomial.eval₂_map, hres, ← hσ]
    show Polynomial.eval₂ (((residue R').comp σ).comp (AdjoinRoot.of P)) (((residue R').comp σ) (AdjoinRoot.root P)) P = 0
    rw [← Polynomial.hom_eval₂, AdjoinRoot.eval₂_root, map_zero]
  haveI : Fact (Irreducible p) := ⟨hirr⟩
  let gam : AdjoinRoot p →+* ResidueField R' := AdjoinRoot.lift (ResidueField.map ρ) r hr
  let del : AdjoinRoot p →+* Ω := AdjoinRoot.lift e₀ t hpt
  letI : Algebra (AdjoinRoot p) (ResidueField R') := gam.toAlgebra
  letI : Algebra (AdjoinRoot p) Ω := del.toAlgebra
  have hintR : ρ.IsIntegral := hfin'.to_isIntegral
  haveI : Algebra.IsIntegral (AdjoinRoot p) (ResidueField R') := by
    constructor
    intro y
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨m, hm, hmx⟩ := hintR x
    refine ⟨(m.map (residue R)).map (AdjoinRoot.of p), (hm.map _).map _, ?_⟩
    show Polynomial.eval₂ gam (residue R' x) ((m.map (residue R)).map (AdjoinRoot.of p)) = 0
    rw [Polynomial.eval₂_map, Polynomial.eval₂_map]
    have hgam : (gam.comp (AdjoinRoot.of p)).comp (residue R) = (residue R').comp ρ := by
      rw [← hres]; congr 1; ext a; exact AdjoinRoot.lift_of hr
    rw [hgam, ← Polynomial.hom_eval₂, hmx, map_zero]
  let β₀ : ResidueField R' →ₐ[AdjoinRoot p] Ω := IsAlgClosed.lift
  have hβ : ∀ a, β₀ (gam a) = del a := fun a => β₀.commutes a
  refine ⟨R', i1, i2, i3, ρ, hloc, β₀.toRingHom, hcn', hinj', hfin', ?_, ⟨gam (AdjoinRoot.root p), ?_⟩⟩
  · ext a
    have h1 : ResidueField.map ρ a = gam (AdjoinRoot.of p a) := (AdjoinRoot.lift_of hr).symm
    show β₀ (ResidueField.map ρ a) = e₀ a
    rw [h1, hβ]
    exact AdjoinRoot.lift_of hpt
  · show β₀ (gam (AdjoinRoot.root p)) = t
    rw [hβ]
    exact AdjoinRoot.lift_root hpt

theorem exists_cover_residue (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hR : GlobalTheory.TorRef.IsCN R)
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] (e₀ : ResidueField R →+* Ω) (s : Finset Ω)
    (hs : ∀ t ∈ s, ∃ q : Polynomial (ResidueField R), q.Monic ∧ q.eval₂ e₀ t = 0) :
    ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (_ : IsLocalHom ρ)
      (β : ResidueField R' →+* Ω), GlobalTheory.TorRef.IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧
      β.comp (ResidueField.map ρ) = e₀ ∧ (s : Set Ω) ⊆ Set.range β := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨R, inferInstance, inferInstance, inferInstance, RingHom.id R, inferInstance, e₀, hR, Function.injective_id,
      RingHom.Finite.id R, by rw [ResidueField.map_id]; rfl, by simp⟩
  | insert t s ht ih =>
    obtain ⟨R₁, i1, i2, i3, ρ₁, hl₁, β₁, hcn₁, hinj₁, hfin₁, hβ₁, hs₁⟩ :=
      ih fun u hu => hs u (Finset.mem_insert_of_mem hu)
    obtain ⟨q, hq, hqt⟩ := hs t (Finset.mem_insert_self t s)
    have hqt' : (q.map (ResidueField.map ρ₁)).eval₂ β₁ t = 0 := by rw [Polynomial.eval₂_map, hβ₁, hqt]
    obtain ⟨R₂, j1, j2, j3, ρ₂, hl₂, β₂, hcn₂, hinj₂, hfin₂, hβ₂, ht₂⟩ :=
      exists_cover_step R₁ hcn₁ β₁ t _ (hq.map _) hqt'
    refine ⟨R₂, j1, j2, j3, ρ₂.comp ρ₁, inferInstance, β₂, hcn₂, hinj₂.comp hinj₁, hfin₂.comp hfin₁, ?_, ?_⟩
    · rw [ResidueField.map_comp, ← RingHom.comp_assoc, hβ₂, hβ₁]
    · rw [Finset.coe_insert]
      refine Set.insert_subset ht₂ (hs₁.trans ?_)
      rintro _ ⟨a, rfl⟩
      exact ⟨ResidueField.map ρ₂ a, by rw [← hβ₂]; rfl⟩

theorem exists_finExt_tq_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (G' : Over (Sp R')) (_ : GrpObj G') (_ : IsCommMonObj G') (β : G'.left ⟶ G.left) (X : Type) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X), FinExt ρ ∧ IsGrpPullback G' G (spMap ρ) β ∧ Nonempty (GlobalTheory.UU.TQ (thickObj R' (maximalIdeal R') 0 G') X) := by
  intro R _ _ _ hR G _ _ hG
  have hcn : GlobalTheory.TorRef.IsCN R := ⟨hR.1.1, hR.1.2.2.1, hR.1.2.2.2, hR.2⟩
  have h₀ : IsSemiAbelian ((Over.pullback (spMap (residue R))).obj G) := IsSemiAbelian.pullback _ G hG
  haveI := h₀.smooth
  haveI := h₀.quasiCompact
  haveI := h₀.separated
  let k := ResidueField R
  let Ω := AlgebraicClosure k
  obtain ⟨T⟩ := h₀.fibres Ω (spMap (algebraMap k Ω))
  obtain ⟨s, hs, H⟩ := GlobalTheory.FieldModel.exists_finite_torusExtension_range (algebraMap k Ω) _ T
  obtain ⟨R', i1, i2, i3, ρ, hl, β, hcn', hinj, hfin, hβ, hr⟩ := exists_cover_residue R hcn (algebraMap k Ω) hs.toFinset
    (fun t _ => ⟨minpoly k t, minpoly.monic (Algebra.IsIntegral.isIntegral t), minpoly.aeval k t⟩)
  have hT := H (ResidueField R') (ResidueField.map ρ) β hβ (by simpa using hr)
  let G' := (Over.pullback (spMap ρ)).obj G
  have hT' : Nonempty (TorusExtension ((Over.pullback (spMap (residue R'))).obj G')) := by
    refine GlobalTheory.nonempty_torusExtension_of_comp_eq ?_ G hT
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      ResidueField.map_comp_residue]
  obtain ⟨X, _, _, _, ⟨Q⟩⟩ := GlobalTheory.Raynaud.exists_tq_level_zero_of_torusExtension R' G' hT'
  exact ⟨R', i1, i2, i3, ρ, G', inferInstance, inferInstance, _, X, inferInstance, inferInstance, inferInstance,
    ⟨⟨hcn'.1, inferInstance, hcn'.2.1, hcn'.2.2.1⟩, hinj, hfin⟩, isGrpPullback_pullback G (spMap ρ), ⟨Q⟩⟩

end GlobalTheory.Mum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteChartMapToNormalFiniteModel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.ModelAt

open GlobalTheory.Points GlobalTheory.ZH.RatModel

theorem isIntegral_valMap {C : Type} [CommRing C] {Z : Scheme.{0}} {V : Z.Opens} (hV : IsAffineOpen V)
    (f : Sp C ⟶ V) [IsFinite f] (h : ⊤ ≤ (f ≫ V.ι) ⁻¹ᵁ V) : (valMap (f ≫ V.ι) V h).hom.IsIntegral := by
  have e := specMap_valMap_fromSpec hV (f ≫ V.ι) h
  have e2 : Spec.map (valMap (f ≫ V.ι) V h) = f ≫ hV.isoSpec.hom := by
    rw [← cancel_mono hV.fromSpec, e, Category.assoc, ← hV.isoSpec_inv_ι, Iso.hom_inv_id_assoc]
  have : IsFinite (Spec.map (valMap (f ≫ V.ι) V h)) := by rw [e2]; infer_instance
  exact ((IsFinite.SpecMap_iff _).1 this).to_isIntegral

theorem mem_of_isIntegralElem {o Ω A : Type} [CommRing o] [Field Ω] [Algebra o Ω] [CommRing A]
    (S : Subalgebra o Ω) [IsFractionRing S Ω] [IsIntegrallyClosed S] (σ : A →+* Ω) (hσ : ∀ a, σ a ∈ S) {x : Ω}
    (hx : σ.IsIntegralElem x) : x ∈ S := by
  have h1 : (algebraMap S Ω).IsIntegralElem x := by
    obtain ⟨p, hp, h0⟩ := hx
    refine ⟨p.map (σ.codRestrict S hσ), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    exact h0
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 (show IsIntegral S x from h1)
  exact hy ▸ y.2

theorem exists_map_model : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (Z : Scheme.{0}) (π : M.Z ⟶ Z), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → IsFinite π → ∀ (R : Subalgebra o Ω), (∀ z : Ω, ∃ a ∈ R, ∃ c ∈ R, z = a / c) → IsIntegrallyClosed R → ∀ (V : Z.Opens) (f : Sp R ⟶ V), IsAffineOpen V → IsFinite f → M.pt ≫ π = spMap R.val.toRingHom ≫ f ≫ V.ι → ∃ φ : Sp R ⟶ M.Z, φ ≫ π = f ≫ V.ι ∧ ∀ (P : Sp R) (a b : R), b ∉ P.asIdeal → (a : Ω) / (b : Ω) ∈ M.O (φ P) := by
  intro o Ω _ _ _ M Z π hn hπ R hR hic V f hV hf hpt
  have hg : ⊤ ≤ (f ≫ V.ι) ⁻¹ᵁ V := fun w _ => (f w).2
  have hpV : ⊤ ≤ (M.pt ≫ π) ⁻¹ᵁ V := by
    rw [hpt]
    exact fun w _ => hg (x := _) trivial
  have hW : IsAffineOpen (π ⁻¹ᵁ V) := hV.preimage π
  have hne : ((π ⁻¹ᵁ V : M.Z.Opens) : Set M.Z).Nonempty :=
    ⟨M.pt (IsLocalRing.closedPoint Ω), hpV (x := IsLocalRing.closedPoint Ω) trivial⟩
  haveI : IsFractionRing R Ω := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨a, ha, c, hc, h⟩ := hR z
    exact ⟨⟨a, ha⟩, ⟨c, hc⟩, h⟩
  have hα := isIntegral_valMap hV f hg
  have hβ : (π.app V).hom.IsIntegral := (π.finite_app V hV).to_isIntegral
  have hcomm : ∀ a, M.res _ hne ((π.app V).hom a) = (((valMap (f ≫ V.ι) V hg).hom a : R) : Ω) := fun a => by
    rw [res_apply, valF_eq_valR, ← valR_comp, hpt, valR_spMap_comp _ _ _ hg, valR_eq _ _ hg]
    rfl
  have hσ : (M.res _ hne).comp (π.app V).hom = R.val.toRingHom.comp (valMap (f ≫ V.ι) V hg).hom :=
    RingHom.ext hcomm
  have h1 : ∀ c, M.res _ hne c ∈ R := fun c =>
    mem_of_isIntegralElem R ((M.res _ hne).comp (π.app V).hom) (fun a => by
      rw [RingHom.comp_apply, hcomm]; exact Subtype.prop _) (by
      obtain ⟨p, hp, h0⟩ := hβ c
      exact ⟨p, hp, by rw [← Polynomial.hom_eval₂, h0, map_zero]⟩)
  have h2 : ∀ r : R, ∃ c, M.res _ hne c = r := fun r => by
    have : (r : Ω) ∈ M.ringOn (π ⁻¹ᵁ V : M.Z.Opens) := mem_ringOn.2 fun z hz => by
      have := isIntegrallyClosed_O hn z
      refine mem_of_isIntegralElem (M.O z) ((M.res _ hne).comp (π.app V).hom) (fun a => by
        rw [RingHom.comp_apply, res_apply]; exact valF_mem_O hz _) ?_
      obtain ⟨p, hp, h0⟩ := hα r
      refine ⟨p, hp, ?_⟩
      rw [hσ]
      exact (Polynomial.hom_eval₂ p _ R.val.toRingHom r).symm.trans (by rw [h0, map_zero])
    obtain ⟨c, hc⟩ := (mem_ringOn_iff_exists hne).1 this
    exact ⟨c, (M.res_apply _ hne c).trans hc⟩
  let ψ : Γ(M.Z, π ⁻¹ᵁ V) ⟶ CommRingCat.of R := CommRingCat.ofHom ((M.res _ hne).codRestrict R h1)
  have hφ := le_preimage_specMap_fromSpec hW ψ
  refine ⟨Spec.map ψ ≫ hW.fromSpec, ?_, fun P a b hb => ?_⟩
  · refine ext_of_valR hV hφ hg fun a => ?_
    rw [valR_comp, valR_eq _ _ hφ, valMap_specMap_fromSpec, valR_eq _ _ hg]
    exact Subtype.ext (hcomm a)
  · have hz : (Spec.map ψ ≫ hW.fromSpec) P ∈ π ⁻¹ᵁ V := hφ (x := P) trivial
    obtain ⟨a', ha'⟩ := h2 a
    obtain ⟨b', hb'⟩ := h2 b
    have hbz : (Spec.map ψ ≫ hW.fromSpec) P ∈ M.Z.basicOpen b' := by
      change Spec.map ψ P ∈ hW.fromSpec ⁻¹ᵁ M.Z.basicOpen b'
      rw [hW.fromSpec_preimage_basicOpen]
      change ψ.hom b' ∉ P.asIdeal
      rwa [show ψ.hom b' = b from Subtype.ext hb']
    have hu := ((isUnit_O_iff _).1 ((isUnit_valF_iff hz b').2 hbz)).2
    rw [← ha', ← hb', res_apply, res_apply, div_eq_mul_inv]
    exact mul_mem (valF_mem_O hz a') hu

end GlobalTheory.Poinc.ModelAt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteCompleteTraitExtensionOfBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TraitExt

theorem exists_finite_trait_extension : ∀ (R W R₁ : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing W] [IsDomain W] [IsLocalRing W] [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (ρ : R →+* R₁), FinExt ρ → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra (FractionRing W) Ω] [Algebra.IsAlgebraic (FractionRing W) Ω] (e : FractionRing R₁ →+* Ω), (∀ r, e (algebraMap R₁ (FractionRing R₁) (ρ r)) = algebraMap (FractionRing W) Ω (algebraMap W (FractionRing W) (φ r))) → ∃ (W₁ : Type) (_ : CommRing W₁) (_ : IsDomain W₁) (_ : IsLocalRing W₁) (iw : W →+* W₁) (φ₁ : R₁ →+* W₁) (σ : Ω →+* AlgebraicClosure (FractionRing W₁)), GlobalTheory.LN.CDvr W₁ ∧ Function.Injective iw ∧ iw.Finite ∧ IsLocalHom iw ∧ Function.Injective φ₁ ∧ IsLocalHom φ₁ ∧ φ₁.comp ρ = iw.comp φ ∧ (∀ w, σ (algebraMap (FractionRing W) Ω (algebraMap W (FractionRing W) w)) = algebraMap (FractionRing W₁) (AlgebraicClosure (FractionRing W₁)) (algebraMap W₁ (FractionRing W₁) (iw w))) ∧ ∀ r, σ (e (algebraMap R₁ (FractionRing R₁) r)) = algebraMap (FractionRing W₁) (AlgebraicClosure (FractionRing W₁)) (algebraMap W₁ (FractionRing W₁) (φ₁ r)) := by
  intro R W R₁ _ _ _ _ _ _ _ _ _ hW φ hφ hφl ρ hρ Ω _ _ _ _ e he
  obtain ⟨hWd, hWc, hW0⟩ := hW
  obtain ⟨-, hρi, hρf⟩ := hρ

  letI : Algebra W Ω := ((algebraMap (FractionRing W) Ω).comp (algebraMap W (FractionRing W))).toAlgebra
  haveI : IsScalarTower W (FractionRing W) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hWΩ : Function.Injective (algebraMap W Ω) :=
    (algebraMap (FractionRing W) Ω).injective.comp (IsFractionRing.injective W (FractionRing W))
  haveI : FaithfulSMul W Ω := (faithfulSMul_iff_algebraMap_injective W Ω).2 hWΩ
  haveI : Algebra.IsAlgebraic W Ω :=
    (IsFractionRing.comap_isAlgebraic_iff (A := W) (K := FractionRing W) (C := Ω)).mpr inferInstance

  letI : Algebra R R₁ := ρ.toAlgebra
  haveI : Module.Finite R R₁ := hρf
  letI : Algebra R W := φ.toAlgebra
  letI : Algebra R Ω := ((algebraMap W Ω).comp φ).toAlgebra
  haveI : IsScalarTower R W Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let f₀ : R₁ →+* Ω := e.comp (algebraMap R₁ (FractionRing R₁))
  have hf₀ : ∀ r, f₀ (ρ r) = algebraMap W Ω (φ r) := he
  let f : R₁ →ₐ[R] Ω := { f₀ with commutes' := fun r => hf₀ r }
  have hint : ∀ x : R₁, IsIntegral W (f₀ x) := fun x =>
    IsIntegral.tower_top (A := W) (IsIntegral.map f (show IsIntegral R x from RingHom.Finite.to_isIntegral hρf x))
  obtain ⟨S, hS⟩ := (Module.Finite.fg_top : (⊤ : Submodule R R₁).FG)
  classical
  obtain ⟨W₁, hd, hc, -, hfin, -, hloc, -, hmem⟩ :=
    GlobalTheory.exists_complete_dvr_finite_subalgebra W Ω (S.image f₀)
  have hin : ∀ x : R₁, f₀ x ∈ W₁ := by
    intro x
    have hx : x ∈ Submodule.span R (S : Set R₁) := hS ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy => exact hmem _ (Finset.mem_image_of_mem _ hy) (hint y)
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact W₁.add_mem hy hz
    | smul a y _ hy =>
      rw [Algebra.smul_def, map_mul]
      refine W₁.mul_mem ?_ hy
      change f₀ (ρ a) ∈ W₁
      rw [hf₀]; exact W₁.algebraMap_mem _

  let iw : W →+* W₁ := algebraMap W W₁
  let φ₁ : R₁ →+* W₁ := f₀.codRestrict W₁ hin
  have hiwinj : Function.Injective iw := fun a b h => hWΩ (congrArg Subtype.val h)
  haveI : CharZero W₁ := charZero_of_injective_ringHom hiwinj
  have hcomp : φ₁.comp ρ = iw.comp φ := by
    ext r; exact hf₀ r
  have hφ₁inj : Function.Injective φ₁ := fun a b h => by
    have : f₀ a = f₀ b := congrArg Subtype.val h
    exact IsFractionRing.injective R₁ (FractionRing R₁) (e.injective this)
  have hφ₁l : IsLocalHom φ₁ := by
    have h1 : (maximalIdeal W₁).comap iw = maximalIdeal W := ((local_hom_TFAE iw).out 0 4).mp hloc
    have h2 : (maximalIdeal W).comap φ = maximalIdeal R := ((local_hom_TFAE φ).out 0 4).mp hφl
    have hP : ((maximalIdeal W₁).comap φ₁).comap ρ = maximalIdeal R := by
      rw [Ideal.comap_comap, hcomp, ← Ideal.comap_comap, h1, h2]
    have hmax : ((maximalIdeal W₁).comap φ₁).IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_comap' ρ (RingHom.Finite.to_isIntegral hρf) _
        (by rw [hP]; infer_instance)
    exact ((local_hom_TFAE φ₁).out 0 4).mpr (IsLocalRing.eq_maximalIdeal hmax)
  haveI : Algebra.IsAlgebraic W₁ Ω := Algebra.IsAlgebraic.extendScalars hiwinj
  haveI : Module.IsTorsionFree W₁ Ω :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr Subtype.val_injective
  haveI : Module.IsTorsionFree W₁ (AlgebraicClosure (FractionRing W₁)) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (by
      rw [IsScalarTower.algebraMap_eq W₁ (FractionRing W₁) (AlgebraicClosure (FractionRing W₁))]
      exact (algebraMap (FractionRing W₁) _).injective.comp (IsFractionRing.injective W₁ (FractionRing W₁)))
  let σ' : Ω →ₐ[W₁] AlgebraicClosure (FractionRing W₁) := IsAlgClosed.lift
  have hσ : ∀ x : W₁, σ' (x : Ω) = algebraMap (FractionRing W₁) (AlgebraicClosure (FractionRing W₁))
      (algebraMap W₁ (FractionRing W₁) x) := fun x => by
    rw [← IsScalarTower.algebraMap_apply]; exact σ'.commutes x
  refine ⟨W₁, inferInstance, inferInstance, inferInstance, iw, φ₁, σ'.toRingHom, ⟨hd, hc, inferInstance⟩,
    hiwinj, RingHom.finite_algebraMap.2 hfin, hloc, hφ₁inj, hφ₁l, hcomp, fun w => hσ (iw w), fun r => hσ (φ₁ r)⟩

end GlobalTheory.TraitExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleCoverChartAtFieldPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Poinc.ChartAt

theorem mem_genericPoints_of_forall_specializes {X : Scheme.{0}} (ε : X) (h : ∀ z, z ⤳ ε → z = ε) :
    ε ∈ genericPoints X := by
  have hc : irreducibleComponent ε ∈ irreducibleComponents X := irreducibleComponent_mem_irreducibleComponents ε
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober (isIrreducible_irreducibleComponent (x := ε)) isClosed_irreducibleComponent
  have e : ξ = ε := h ξ (hξ.specializes mem_irreducibleComponent)
  subst e
  change closure {ξ} ∈ irreducibleComponents X
  rw [hξ.def]
  exact hc

theorem forall_specializes_of_flat {X Y : Scheme.{0}} (g : Y ⟶ X) [Flat g] (ε : Y) (h : ∀ z, z ⤳ ε → z = ε) :
    ∀ z, z ⤳ g ε → z = g ε := by
  intro z hz
  obtain ⟨z', hz', e⟩ := Flat.generalizingMap g hz
  rw [← e, h z' hz']

theorem forall_specializes_fromSpec {Y : Scheme.{0}} {U : Y.Opens} (hU : IsAffineOpen U) (P : PrimeSpectrum Γ(Y, U))
    (hP : P.asIdeal ∈ minimalPrimes Γ(Y, U)) : ∀ z, z ⤳ hU.fromSpec P → z = hU.fromSpec P := by
  intro z hz
  have hr : z ∈ Set.range hU.fromSpec := hz.mem_open hU.fromSpec.isOpenEmbedding.isOpen_range ⟨P, rfl⟩
  obtain ⟨Q, rfl⟩ := hr
  have h1 : Q ⤳ P := hU.fromSpec.isOpenEmbedding.isInducing.specializes_iff.1 hz
  have h2 : (show PrimeSpectrum Γ(Y, U) from Q).asIdeal ≤ P.asIdeal := (PrimeSpectrum.le_iff_specializes _ _).2 h1
  have h3 := hP.2 ⟨PrimeSpectrum.isPrime Q, bot_le⟩ h2
  rw [show Q = P from PrimeSpectrum.ext (le_antisymm h2 h3)]

theorem exists_chart_at : ∀ (n N : ℕ) (X Y Z : Scheme.{0}) (sX : X ⟶ Sp (cycAway n)) (sY : Y ⟶ Sp (cycAway N)) (q : Y ⟶ X) (i : X ⟶ Z), IsOpenImmersion i → 0 < n → 0 < N → Smooth sX → Smooth sY → IsFinite q → Etale q → Surjective q → ∀ (K : Type) [Field K] (y' : Sp K ⟶ Y), ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra (cycAway N) Ω) (_ : ArithBase (cycAway N) Ω) (R : Subalgebra (cycAway N) Ω) (x : Sp R ⟶ Y) (yR : Sp K ⟶ Sp R) (V : Z.Opens) (f : Sp R ⟶ V), R.FG ∧ (∀ z : Ω, ∃ a ∈ R, ∃ c ∈ R, z = a / c) ∧ IsIntegrallyClosed R ∧ x ≫ sY = spMap (algebraMap (cycAway N) R) ∧ yR ≫ x = y' ∧ (∀ w, (spMap R.val.toRingHom ≫ x ≫ q) w ∈ genericPoints X) ∧ ((spMap R.val.toRingHom ≫ x ≫ q ≫ i).stalkMap (genericPoint (Sp Ω))).hom.Finite ∧ IsAffineOpen V ∧ IsFinite f ∧ f ≫ V.ι = x ≫ q ≫ i := by
  intro n N X Y Z sX sY q i hi hn hN hsX hsY hq he hs K _ y'
  let pt : Sp K := closedPoint (CommRingCat.of K)
  obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (q (y' pt))) isOpen_univ
  replace hV₀ : IsAffineOpen V₀ := hV₀
  have hU : IsAffineOpen (q ⁻¹ᵁ V₀) := hV₀.preimage q
  set U := q ⁻¹ᵁ V₀ with hUdef
  have hrange : Set.range y' ⊆ Set.range hU.fromSpec := by
    rintro _ ⟨w, rfl⟩
    rw [hU.range_fromSpec, Subsingleton.elim w pt]
    exact hxV
  let χ : Γ(Y, U) →+* K := (Spec.preimage (IsOpenImmersion.lift hU.fromSpec y' hrange)).hom
  have hχ : spMap χ ≫ hU.fromSpec = y' := by
    have : spMap χ = IsOpenImmersion.lift hU.fromSpec y' hrange := Spec.map_preimage _
    rw [this, IsOpenImmersion.lift_fac]
  haveI : (RingHom.ker χ).IsPrime := RingHom.ker_isPrime χ
  obtain ⟨P₀, hP₀, hPχ⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal Γ(Y, U))) (J := RingHom.ker χ) bot_le
  obtain ⟨P, rfl⟩ : ∃ P : PrimeSpectrum Γ(Y, U), P.asIdeal = P₀ := ⟨⟨P₀, hP₀.1.1⟩, rfl⟩
  have hmax := forall_specializes_fromSpec hU P hP₀
  have hgen : (sY (hU.fromSpec P)).asIdeal = ⊥ := by
    let b : Sp (cycAway N) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (cycAway N))
    have hb : b ⤳ sY (hU.fromSpec P) := (PrimeSpectrum.le_iff_specializes _ _).1 (show (⊥ : Ideal _) ≤ _ from bot_le)
    rw [← forall_specializes_of_flat sY _ hmax b hb]
  let ψ : cycAway N →+* Γ(Y, U) := (Spec.preimage (hU.fromSpec ≫ sY)).hom
  have hψ : spMap ψ = hU.fromSpec ≫ sY := Spec.map_preimage _
  have hft : ψ.FiniteType := by
    have : LocallyOfFiniteType (spMap ψ) := by rw [hψ]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this
  have hsm : ψ.Smooth := by
    have : Smooth (spMap ψ) := by rw [hψ]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @Smooth)).1 this
  have hker : Ideal.comap ψ P.asIdeal = ⊥ := by
    have h1 : spMap ψ P = sY (hU.fromSpec P) := by rw [hψ]; rfl
    change (spMap ψ P).asIdeal = ⊥
    rw [h1]; exact hgen
  letI : Algebra (cycAway N) Γ(Y, U) := ψ.toAlgebra
  haveI : Algebra.Smooth (cycAway N) Γ(Y, U) := hsm
  haveI : IsDedekindDomain (cycAway N) := GlobalTheory.CycAwayReg.isDedekindDomain_cycAway N
  have hic : IsIntegrallyClosed (Γ(Y, U) ⧸ P.asIdeal) := isIntegrallyClosed_quotient_of_mem_minimalPrimes
    (fun m _ => isDomain_and_isIntegrallyClosed_atPrime_of_smooth (cycAway N) m _) hP₀
  let Ω := FractionRing (Γ(Y, U) ⧸ P.asIdeal)
  let φ : Γ(Y, U) →+* Ω := (algebraMap (Γ(Y, U) ⧸ P.asIdeal) Ω).comp (Ideal.Quotient.mk P.asIdeal)
  have hφker : ∀ a, φ a = 0 ↔ a ∈ P.asIdeal := fun a => by
    simp only [φ, RingHom.comp_apply]
    rw [(IsFractionRing.injective (Γ(Y, U) ⧸ P.asIdeal) Ω).eq_iff' (map_zero _), Ideal.Quotient.eq_zero_iff_mem]
  letI : Algebra (cycAway N) Ω := (φ.comp ψ).toAlgebra
  let f : Γ(Y, U) →ₐ[cycAway N] Ω := { φ with commutes' := fun _ => rfl }
  have hinj : Function.Injective (algebraMap (cycAway N) Ω) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have : x ∈ Ideal.comap ψ P.asIdeal := (hφker (ψ x)).1 hx
    rwa [hker, Ideal.mem_bot] at this
  haveI : CharZero Ω := charZero_of_injective_algebraMap hinj
  haveI : ArithBase (cycAway N) Ω :=
    ⟨GlobalTheory.CycAwayReg.isDedekindDomain_cycAway N, finiteType_cycAway N, inferInstance, hinj⟩
  have hsurj : Function.Surjective f.rangeRestrict.toRingHom := f.rangeRestrict_surjective
  have hkerR : RingHom.ker f.rangeRestrict.toRingHom = P.asIdeal := by
    ext a
    rw [RingHom.mem_ker, ← hφker, Subtype.ext_iff]
    rfl
  let χR : f.range →+* K := RingHom.liftOfSurjective f.rangeRestrict.toRingHom hsurj ⟨χ, hkerR.le.trans hPχ⟩
  have hχR : χR.comp f.rangeRestrict.toRingHom = χ := RingHom.liftOfSurjective_comp _ _ _
  have hfin : IsFinite (spMap f.rangeRestrict.toRingHom) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.Finite.of_surjective _ hsurj)
  refine ⟨Ω, inferInstance, inferInstance, inferInstance, f.range, spMap f.rangeRestrict.toRingHom ≫ hU.fromSpec,
    spMap χR, i ''ᵁ V₀, spMap f.rangeRestrict.toRingHom ≫ hU.isoSpec.inv ≫ (q ∣_ V₀) ≫ (i.isoImage V₀).hom,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, hV₀.image_of_isOpenImmersion i, inferInstance, ?_⟩
  · rw [← Algebra.map_top]
    haveI : Algebra.FiniteType (cycAway N) Γ(Y, U) := hft
    exact Algebra.FiniteType.out.map f
  · intro z
    obtain ⟨x, s, -, rfl⟩ := IsFractionRing.div_surjective (A := Γ(Y, U) ⧸ P.asIdeal) z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective s
    exact ⟨f a, ⟨a, rfl⟩, f c, ⟨c, rfl⟩, rfl⟩
  · exact IsIntegrallyClosed.of_equiv
      ((Ideal.quotEquivOfEq hkerR.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj))
  · rw [Category.assoc, ← hψ, ← Spec.map_comp]
    rfl
  · rw [← Category.assoc, ← hχ, ← hχR, ← Spec.map_comp]
    rfl
  · intro w
    have hw : spMap f.rangeRestrict.toRingHom (spMap f.range.val.toRingHom w) = P := by
      refine PrimeSpectrum.ext ?_
      change Ideal.comap (f.rangeRestrict.toRingHom) (Ideal.comap f.range.val.toRingHom w.asIdeal) = P.asIdeal
      rw [@Ideal.eq_bot_of_prime _ _ w.asIdeal (PrimeSpectrum.isPrime (show PrimeSpectrum Ω from w))]
      ext a
      simp only [Ideal.mem_comap, Ideal.mem_bot]
      exact hφker a
    show q (hU.fromSpec (spMap f.rangeRestrict.toRingHom (spMap f.range.val.toRingHom w))) ∈ genericPoints X
    rw [hw]
    exact mem_genericPoints_of_forall_specializes _ (forall_specializes_of_flat q _ hmax)
  · have e : spMap f.range.val.toRingHom ≫ spMap f.rangeRestrict.toRingHom =
        spMap (f.range.val.toRingHom.comp f.rangeRestrict.toRingHom) := (Spec.map_comp _ _).symm
    have h1 := GlobalTheory.Poinc.Chart.stalkMap_finite_of_chart Ω Γ(Y, U) q hU.fromSpec
      (f.range.val.toRingHom.comp f.rangeRestrict.toRingHom) (fun z => by
        obtain ⟨x, s, -, rfl⟩ := IsFractionRing.div_surjective (A := Γ(Y, U) ⧸ P.asIdeal) z
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
        obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective s
        exact ⟨a, c, rfl⟩) _ rfl
    have e2 : spMap f.range.val.toRingHom ≫ (spMap f.rangeRestrict.toRingHom ≫ hU.fromSpec) ≫ q ≫ i =
        (spMap (f.range.val.toRingHom.comp f.rangeRestrict.toRingHom) ≫ hU.fromSpec ≫ q) ≫ i := by
      rw [← e]; simp only [Category.assoc]
    rw [e2, Scheme.Hom.stalkMap_comp]
    exact h1.comp (RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso (i.stalkMap _)).2)
  · simp only [Category.assoc]
    rw [Scheme.Hom.isoImage_hom_ι, ← Category.assoc (q ∣_ V₀), morphismRestrict_ι, Category.assoc,
      ← Category.assoc hU.isoSpec.inv, hU.isoSpec_inv_ι]

end GlobalTheory.Poinc.ChartAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFractionRingOnOfMemModelLocalRingStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Points RatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fraction_ringOn_of_mem_modelLocalRing : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U : M.Z.Opens), IsAffineOpen U → ∀ z ∈ U, ∀ x ∈ M.O z, ∃ a ∈ M.ringOn (U : Set M.Z), ∃ b ∈ M.ringOn (U : Set M.Z), b ≠ 0 ∧ b⁻¹ ∈ M.O z ∧ x = a / b := by
  first | exact @GlobalTheory.Poinc.exists_eq_div_of_mem_O_affine | exact GlobalTheory.Poinc.exists_eq_div_of_mem_O_affine | (intros; apply GlobalTheory.Poinc.exists_eq_div_of_mem_O_affine <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorLineBundlePullbackSpecLocalRing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.LocalPullGen

theorem main : ∀ (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0}) (L : LB X), L.IsLB →
    ∀ p : (𝟙_ (Over (Sp R))).left ⟶ X, ∃ ρ : LB.Gen (L.pull p), ρ.IsGen := by
  intro R _ _ X L hL p
  exact ReciprocityTheory.ChartRestriction.G.DVR.exists_gen_of_local (V := R) L hL (K := PUnit) (fun _ => p) (fun _ => 1)

end GlobalTheory.LocalPullGen
end

