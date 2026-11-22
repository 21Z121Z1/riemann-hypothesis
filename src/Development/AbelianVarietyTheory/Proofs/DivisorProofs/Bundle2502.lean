import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2404
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveSwapOfTrivAxes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2361
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2432
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2212
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2243
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1333
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2278
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2191
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2051
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2405
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0046
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisStatementOfSmall
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Definitions.Divisors.LiftFrameEmbeddingBase
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatOfFiniteRetractOfFiniteFlatStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.DualCon
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_of_finite_retract_of_finite_flat : ∀ (R : Type) [CommRing R] (H K : Over (Sp R)) (s : H ⟶ K) (r : K ⟶ H), s ≫ r = 𝟙 H → IsFinite H.hom → IsFinite K.hom → Flat K.hom → Flat H.hom := by
  first | exact @GlobalTheory.retract_flat_of_finite | exact GlobalTheory.retract_flat_of_finite | (intros; apply GlobalTheory.retract_flat_of_finite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FnOfPreimageMemSpanBy
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem fnOf_appLE_top (D : Type) [CommRing D] {X' : Scheme.{0}} [IsIntegral X'] (p' : X' ⟶ Sp D) (V : X'.Opens)
    (hV : genericPoint X' ∈ V) (h : V ≤ p' ⁻¹ᵁ ⊤) (z : Γ(Sp D, ⊤)) :
    fnOf V hV ((p'.appLE ⊤ V h) z) = fnOf ⊤ trivial (p'.appTop z) := by
  rw [← Scheme.Hom.appLE_map p' (U := ⊤) (V := ⊤) (by simp) (homOfLE (le_top : V ≤ ⊤)).op]
  rw [CommRingCat.comp_apply]
  refine (X'.presheaf.germ_res_apply (homOfLE (le_top : V ≤ ⊤)) _ hV ((p'.appLE ⊤ ⊤ (by simp)) z)).trans ?_
  have e : p'.appLE ⊤ ⊤ (by simp) = p'.appTop := (Scheme.Hom.app_eq_appLE p').symm
  rw [e]
  rfl

theorem fnOf_preimage_mem_spanBy : ∀ (T D : Type) [CommRing T] [CommRing D] (a : T →+* D) (X X' : Scheme.{0}) [IsIntegral X] [IsIntegral X'] (p : X ⟶ Sp T) (p' : X' ⟶ Sp D) (π : X' ⟶ X) (θ : X.functionField →+* X'.functionField), IsPullback π p' p (spMap a) → PFF (𝟙 _) π θ → ∀ (U : X.Opens) (hU : genericPoint X ∈ U) (hU' : genericPoint X' ∈ π ⁻¹ᵁ U), IsAffineOpen U → ∀ s : Γ(X', π ⁻¹ᵁ U), GlobalTheory.Cartier.fnOf (π ⁻¹ᵁ U) hU' s ∈ spanBy (GlobalTheory.Desc.cst p') (θ '' Set.range (GlobalTheory.Cartier.fnOf U hU)) := by
  intro T D _ _ a X X' _ _ p p' π θ H hθ U hU hU' hAff s
  letI : Algebra D X'.functionField := (GlobalTheory.Desc.cst p').toAlgebra
  set M : Submonoid X'.functionField := ((θ.comp (fnOf U hU)).rangeS).toSubmonoid with hM
  have hMset : (M : Set X'.functionField) = θ '' Set.range (fnOf U hU) := by
    ext v; simp [hM, Set.range_comp]
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := U) (UY := π ⁻¹ᵁ U) le_top le_top
    (by simp)).mp (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) (isAffineOpen_top _) hAff)
  have hcl := CommRingCat.closure_range_union_range_eq_top_of_isPushout po
  let S : Subring Γ(X', π ⁻¹ᵁ U) := (Algebra.adjoin D (M : Set X'.functionField)).toSubring.comap (fnOf (π ⁻¹ᵁ U) hU')
  have hle : (⊤ : Subring _) ≤ S := by
    rw [← hcl, Subring.closure_le]
    rintro _ (⟨y, rfl⟩ | ⟨z, rfl⟩)
    · show fnOf (π ⁻¹ᵁ U) hU' _ ∈ Algebra.adjoin D (M : Set X'.functionField)
      apply Algebra.subset_adjoin
      rw [hMset]
      refine ⟨fnOf U hU y, ⟨y, rfl⟩, ?_⟩
      rw [GaussPt.theta_fnOf hθ U hU hU', Scheme.Hom.app_eq_appLE]
    · show fnOf (π ⁻¹ᵁ U) hU' _ ∈ Algebra.adjoin D (M : Set X'.functionField)
      have e : fnOf (π ⁻¹ᵁ U) hU' ((p'.appLE ⊤ (π ⁻¹ᵁ U) (by simp)) z) = algebraMap D X'.functionField ((Scheme.ΓSpecIso (CommRingCat.of D)).hom z) := by
        rw [RingHom.algebraMap_toAlgebra]
        simp only [GlobalTheory.Desc.cst, RingHom.comp_apply]
        refine (fnOf_appLE_top D p' _ hU' _ z).trans ?_
        simp
      rw [e]
      exact Subalgebra.algebraMap_mem _ _
  have hs : fnOf (π ⁻¹ᵁ U) hU' s ∈ Algebra.adjoin D (M : Set X'.functionField) := hle (Subring.mem_top s)
  have hsp : fnOf (π ⁻¹ᵁ U) hU' s ∈ Submodule.span D (M : Set X'.functionField) := by
    have := Algebra.adjoin_eq_span D (M : Set X'.functionField)
    rw [Submonoid.closure_eq] at this
    rw [← this]; exact hs
  obtain ⟨n, f, g, hfg⟩ := Submodule.mem_span_set'.1 hsp
  refine ⟨n, f, fun i => g i, fun i => hMset ▸ (g i).2, ?_⟩
  rw [← hfg]
  simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra]

end GlobalTheory.Desc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOrdEqMultOfIsCartierDivisorOfRationalForm
section
set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

theorem DivOver.formOrd_eq_mult_of_isDivOfForm : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q] (η : RatForms q n), η ≠ 0 → ∀ K : CartierDiv Y, IsDivOfForm K η → ∀ (E : DivOver q) (w : Y), E.IsAt w → E.formOrd η = K.mult w := by
  intro k _ _ Y _ _ q n _ η hη K hK E w hE
  haveI := SmoothOfRelativeDimension.smooth n q
  have hn : topologicalKrullDim Y = n := GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth q n ‹_›
  obtain ⟨U, ω, hU, hω⟩ := exists_isFrame q n w
  have hgen := isFreeGen_formOf (gen_mem hU) hω
  have h0 : formOf U (gen_mem hU) ω ≠ 0 := fun h =>
    one_ne_zero (hgen.1 (a₁ := 1) (a₂ := 0) (by simp [h]))
  obtain ⟨c, hc⟩ := hgen.2 η
  have hc0 : c ≠ 0 := fun e => hη (by rw [← hc, e]; exact zero_smul _ _)
  have h1 := hK U ω hω w hU (Units.mk0 c hc0) hc.symm
  have h2 := E.formOrd_smul hn h0 (Units.mk0 c hc0)
  rw [DivOver.formOrd_formOf_eq_zero hU hE hω, add_zero] at h2
  replace h2 : E.formOrd η = E.ord (Units.mk0 c hc0) := hc ▸ h2
  rw [h2, h1.mult_eq, hE.ord_eq]

end GlobalTheory.Discrepancy
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOrderBirationalPullback
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.BirOrd

theorem formOrd_ratPull_of_over : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s], Function.Bijective (functionFieldMap s) → ∀ (E' : DivOver (s ≫ p)) (E : DivOver p), DivOver.Over s E' E → ∀ (n : ℕ) (η : RatForms p n), η ≠ 0 → E'.formOrd (EtaleKlt.ratPull p s n η) = E.formOrd η := by
  intro k _ X Y _ _ p s _ hbij E' E hO n η hη
  set φ := functionFieldMap s with hφdef
  let φe : X.functionField ≃+* Y.functionField := RingEquiv.ofBijective φ hbij
  have hpc : φ.comp (Cartier.constFn p) = Cartier.constFn (s ≫ p) :=
    EtaleKlt.functionFieldMap_comp_constFn p s
  have hcc : (φe.symm : Y.functionField →+* X.functionField).comp (Cartier.constFn (s ≫ p)) =
      Cartier.constFn p := by
    ext a
    rw [← hpc]
    exact φe.symm_apply_apply _

  let Φ' := TopForm.formMap n (φe.symm : Y.functionField →+* X.functionField) hcc
  have hinv : ∀ ξ : RatForms p n, Φ' (EtaleKlt.ratPull p s n ξ) = ξ := by
    intro ξ
    have e0 : (φe.symm : Y.functionField →+* X.functionField).comp φ = RingHom.id _ := by
      ext x
      exact φe.symm_apply_apply x
    refine (TopForm.formMap_formMap φ (φe.symm : Y.functionField →+* X.functionField)
      (RingHom.id _) e0 hpc hcc (RingHom.id_comp _) ξ).trans ?_
    exact TopForm.formMap_of_eq_id _ rfl _ ξ

  let ψ : E.ring →+* E'.ring := φ.restrict E.ring E'.ring fun x hx => (hO x).1 hx
  have hψv : ∀ a, (ψ a : Y.functionField) = φ a := fun _ => rfl
  have hψb : Function.Bijective ψ := by
    refine ⟨fun a b h => Subtype.ext (hbij.1 (by simpa [hψv] using congrArg Subtype.val h)), ?_⟩
    intro y
    obtain ⟨x, hx⟩ := hbij.2 (y : Y.functionField)
    have hxE : x ∈ E.ring := (hO x).2 (hx ▸ y.2)
    exact ⟨⟨x, hxE⟩, Subtype.ext hx⟩
  let eψ : E.ring ≃+* E'.ring := RingEquiv.ofBijective ψ hψb
  let χ : E'.ring →+* E.ring := eψ.symm
  have hc : ψ.comp E.const = E'.const := by
    ext a
    exact RingHom.congr_fun hpc a
  have hc' : χ.comp E'.const = E.const := by
    ext a
    rw [← hc]
    exact congrArg Subtype.val (eψ.symm_apply_apply (E.const a))
  have hχv : ∀ y, ((χ y : E.ring) : X.functionField) = φe.symm (y : Y.functionField) := by
    intro y
    obtain ⟨x, rfl⟩ := eψ.surjective y
    have h1 : χ (eψ x) = x := eψ.symm_apply_apply x
    rw [h1]
    exact (φe.symm_apply_apply (x : X.functionField)).symm

  have hord : ∀ g : X.functionFieldˣ, E'.ord (Units.map φ.toMonoidHom g) = E.ord g := by
    intro g
    obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible E.ring
    exact EtaleDiv.log_ordFrac_map E.ring E'.ring φ ψ hψv ht (ht.map eψ) g.ne_zero
  have hfe : ∀ ω : Forms E.const n, IsFreeGen E.ring ω →
      IsFreeGen E'.ring (TopForm.formMap n ψ hc ω) := fun ω hω =>
    EtaleDiv.isFreeGen_formMap (EtaleDiv.formallyEtale_of_bijective ψ hψb) hc hω
  have hfe' : ∀ ω : Forms E'.const n, IsFreeGen E'.ring ω →
      IsFreeGen E.ring (TopForm.formMap n χ hc' ω) := fun ω hω =>
    EtaleDiv.isFreeGen_formMap (EtaleDiv.formallyEtale_of_bijective χ eψ.symm.bijective) hc' hω
  have hτ : (E'.ring.subtype.comp ψ).comp E.const = Cartier.constFn (s ≫ p) := by
    rw [RingHom.comp_assoc, hc]
    rfl
  have key : ∀ ω : Forms E.const n,
      EtaleKlt.ratPull p s n (E.toRat n ω) = E'.toRat n (TopForm.formMap n ψ hc ω) := by
    intro ω
    have e : φ.comp E.ring.subtype = E'.ring.subtype.comp ψ := by
      ext x
      rfl
    have k1 := TopForm.formMap_formMap (D := n) E.ring.subtype φ _ e rfl hpc hτ ω
    have k2 := TopForm.formMap_formMap (D := n) ψ E'.ring.subtype _ rfl hc rfl hτ ω
    exact k1.trans k2.symm
  have hτ' : (E.ring.subtype.comp χ).comp E'.const = Cartier.constFn p := by
    rw [RingHom.comp_assoc, hc']
    rfl
  have key' : ∀ ω : Forms E'.const n,
      Φ' (E'.toRat n ω) = E.toRat n (TopForm.formMap n χ hc' ω) := by
    intro ω
    have e : (φe.symm : Y.functionField →+* X.functionField).comp E'.ring.subtype =
        E.ring.subtype.comp χ := by
      ext y
      exact (hχv y).symm
    have k1 := TopForm.formMap_formMap (D := n) E'.ring.subtype
      (φe.symm : Y.functionField →+* X.functionField) _ e rfl hcc hτ' ω
    have k2 := TopForm.formMap_formMap (D := n) χ E.ring.subtype _ rfl hc' rfl hτ' ω
    exact k1.trans k2.symm
  have fwd : ∀ a, E.IsFormOrd η a → E'.IsFormOrd (EtaleKlt.ratPull p s n η) a := by
    rintro a ⟨ω, hω, g, hη', hg⟩
    refine ⟨_, hfe ω hω, Units.map φ.toMonoidHom g, ?_, (hord g).trans hg⟩
    rw [hη', map_smulₛₗ, key]
    rfl
  have bwd : ∀ a, E'.IsFormOrd (EtaleKlt.ratPull p s n η) a → E.IsFormOrd η a := by
    rintro a ⟨ω, hω, f, hη', hf⟩
    let g : X.functionFieldˣ := Units.map (φe.symm : Y.functionField →+* X.functionField).toMonoidHom f
    have hgf : Units.map φ.toMonoidHom g = f := by
      ext
      exact φe.apply_symm_apply (f : Y.functionField)
    refine ⟨_, hfe' ω hω, g, ?_, ?_⟩
    · rw [← hinv η, hη', map_smulₛₗ, key']
      rfl
    · rw [← hord g, hgf, hf]
  have hne : EtaleKlt.ratPull p s n η ≠ 0 := by
    intro h0
    apply hη
    rw [← hinv η, h0, map_zero]
  by_cases h : ∃ a, E.IsFormOrd η a
  · obtain ⟨a, ha⟩ := h
    rw [ha.formOrd_eq hη, (fwd a ha).formOrd_eq hne]
  · have h' : ¬ ∃ a, E'.IsFormOrd (EtaleKlt.ratPull p s n η) a :=
      fun ⟨a, ha⟩ => h ⟨a, bwd a ha⟩
    rw [DivOver.formOrd, DivOver.formOrd, dif_neg h, dif_neg h']

end GlobalTheory.BirOrd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionRingEqUniformiserZpowMulUnit
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory

theorem DVR.fractionRing_eq_zpow_mul_unit : ∀ {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}, Irreducible ϖ → ∀ (y : FractionRing V), y ≠ 0 → ∃ (v : ℤ) (w : Vˣ), y = algebraMap V (FractionRing V) ϖ ^ v * algebraMap V (FractionRing V) (w : V) := by
  intro V _ _ _ ϖ hϖ y hy
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := V) y
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha : a ≠ 0 := by rintro rfl; simp at hy
  obtain ⟨n₁, u₁, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  obtain ⟨n₂, u₂, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  refine ⟨(n₁ : ℤ) - n₂, u₁ * u₂⁻¹, ?_⟩
  have hϖ0 : algebraMap V (FractionRing V) ϖ ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap V (FractionRing V)), (IsFractionRing.injective V (FractionRing V)).eq_iff]
    exact hϖ.ne_zero
  have hu : ∀ u : Vˣ, algebraMap V (FractionRing V) (u : V) ≠ 0 := fun u => by
    rw [Ne, ← map_zero (algebraMap V (FractionRing V)), (IsFractionRing.injective V (FractionRing V)).eq_iff]
    exact u.ne_zero
  have h2 := hu u₂
  have h1 := hu u₁
  have key : algebraMap V (FractionRing V) ((u₂⁻¹ : Vˣ) : V) = (algebraMap V (FractionRing V) (u₂ : V))⁻¹ := by
    exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
  simp only [Units.val_mul, map_mul, map_pow, key, zpow_sub₀ hϖ0, zpow_natCast]
  field_simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameFormsResidueIndependence
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.IndepDiscrep

theorem neg_one_lt_formOrd_sub_sum : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ) [SmoothOfRelativeDimension n q], topologicalKrullDim Y = n → ∀ (y : Y) (U : Y.Opens) (hy : y ∈ U) (ω : FormsOn q n U), IsFrame ω → ∀ (J : Type) [Fintype J] (a : J → Y.presheaf.stalk y) (ha : ∀ j, a j ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) (v : J → Y.functionFieldˣ) (c : J → ℚ), LinearIndependent (IsLocalRing.ResidueField (Y.presheaf.stalk y)) (fun j : J => ((IsLocalRing.maximalIdeal (Y.presheaf.stalk y)).toCotangent ⟨a j, ha j⟩ : IsLocalRing.CotangentSpace (Y.presheaf.stalk y))) → (∀ j, (v j : Y.functionField) = algebraMap (Y.presheaf.stalk y) Y.functionField (a j)) → (∀ j, c j < 1) → ∀ E : DivOver q, E.Through y → -1 < (E.formOrd (formOf U (gen_mem hy) ω) : ℚ) - ∑ j, c j * E.ord (v j) := by
  classical
  intro Y _ _ q n _ hn y U hy ω hω J _ a ha v c hind hv hc E hE
  haveI := SmoothOfRelativeDimension.smooth n q
  haveI : GlobalTheory.IsNormalScheme Y := GlobalTheory.ModifSections.isNormalScheme_of_smooth q
  obtain ⟨U', hy', z, e, he, hze, hz⟩ :=
    GlobalTheory.AdaptedFrame.exists_adapted_frame (p := q) (n := n) y a ha hind
  have h0 : formOf U (gen_mem hy) ω ≠ 0 := fun h =>
    one_ne_zero ((isFreeGen_formOf (gen_mem hy) hω).1 (a₁ := 1) (a₂ := 0) (by simp [h]))
  have h0' : formOf U' (gen_mem hy') (dOn q z) ≠ 0 := fun h =>
    one_ne_zero ((isFreeGen_formOf (gen_mem hy') hz).1 (a₁ := 1) (a₂ := 0) (by simp [h]))
  obtain ⟨f, hf⟩ := (isFreeGen_formOf (gen_mem hy') hz).2 (formOf U (gen_mem hy) ω)
  have hf0 : f ≠ 0 := fun h => h0 (by rw [← hf, h]; exact zero_smul _ _)
  set u : Y.functionFieldˣ := Units.mk0 f hf0 with hu
  have hfu : ((u : Y.functionField) • formOf U' (gen_mem hy') (dOn q z)) = formOf U (gen_mem hy) ω :=
    by rw [hu, Units.val_mk0]; exact hf
  have hF (Fd : DivOver q) : Fd.formOrd (formOf U (gen_mem hy) ω) =
      Fd.ord u + Fd.formOrd (formOf U' (gen_mem hy') (dOn q z)) := by
    rw [← Fd.formOrd_smul hn h0' u, hfu]
  have h0z : ∀ w, w ⤳ y → ∀ Fd : DivOver q, Fd.IsAt w → Fd.ord u = 0 := by
    intro w hw Fd hFd
    have h1 := hF Fd
    have a1 := DivOver.formOrd_formOf_eq_zero (hw.mem_open U.isOpen hy) hFd hω
    have a2 := DivOver.formOrd_formOf_eq_zero (hw.mem_open U'.isOpen hy') hFd hz
    rw [a1, a2] at h1
    omega
  have reg : ∀ w : Y.functionFieldˣ,
      (∀ x, x ⤳ y → ∀ Fd : DivOver q, Fd.IsAt x → 0 ≤ Fd.ord w) → 0 ≤ E.ord w := fun w hw =>
    (E.ord_nonneg_iff w).2 (hE _ (regAt_of_forall_coheight_eq_one fun x hx h1 =>
      have ⟨Fd, hFd⟩ := DivOver.exists_isAt_of_coheight_eq_one (p := q) h1
      (hFd _).1 ((Fd.ord_nonneg_iff w).1 (hw x hx Fd hFd))))
  have hu1 := reg u fun x hx Fd hFd => (h0z x hx Fd hFd).ge
  have hu2 := reg u⁻¹ fun x hx Fd hFd => by rw [Fd.ord_inv, h0z x hx Fd hFd, neg_zero]
  rw [E.ord_inv] at hu2
  have hu0 : E.ord u = 0 := by omega
  have hA := DivOver.sum_ord_sub_one_le_formOrd_dOn hn E hy' hE z h0' e he v fun j => by
    rw [hv, ← hze j, algebraMap_germ]
  have hN := DivOver.formOrd_formOf_nonneg hn hy' hE (dOn q z) h0'
  have hnn : ∀ j, 0 ≤ E.ord (v j) := fun j => (E.ord_nonneg_iff _).2 (hE _ ⟨a j, (hv j).symm⟩)
  rw [hF E, hu0, zero_add]
  have hAq : (∑ j, (E.ord (v j) : ℚ)) - 1 ≤ (E.formOrd (formOf U' (gen_mem hy') (dOn q z)) : ℚ) := by
    exact_mod_cast hA
  have hNq : (0 : ℚ) ≤ (E.formOrd (formOf U' (gen_mem hy') (dOn q z)) : ℚ) := by exact_mod_cast hN
  have hle : ∀ j, c j * (E.ord (v j) : ℚ) ≤ E.ord (v j) := fun j => by
    have : (0 : ℚ) ≤ E.ord (v j) := by exact_mod_cast hnn j
    nlinarith [hc j]
  by_cases h : ∃ j, 0 < E.ord (v j)
  · obtain ⟨j, hj⟩ := h
    have hlt : ∑ j, c j * (E.ord (v j) : ℚ) < ∑ j, (E.ord (v j) : ℚ) :=
      Finset.sum_lt_sum (fun j _ => hle j) ⟨j, Finset.mem_univ _, by
        have : (0 : ℚ) < E.ord (v j) := by exact_mod_cast hj
        nlinarith [hc j]⟩
    linarith
  · push_neg at h
    have h' : ∀ j, E.ord (v j) = 0 := fun j => le_antisymm (h j) (hnn j)
    simp only [h', Int.cast_zero, mul_zero, Finset.sum_const_zero, sub_zero]
    linarith

end GlobalTheory.IndepDiscrep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramePolynomialCoeffBoundedByDeterminantsStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LamT (CMPt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.framePolynomial_coeff_bounded_by_determinants : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La →
    ∀ (e : Formalism.L2.Pj.Ix Dw → ℤ) (k : (E →+* ℂ) → ℕ), e none = 0 →
    ∀ (p : IsDedekindDomain.HeightOneSpectrum (𝓞 z.K)) (T : CDVR) (iK : z.K →+* T.Fr), T.FinRes →
      (∀ y : z.K, iK y ∈ Set.range (algebraMap T.V T.Fr) ↔ p.valuation z.K y ≤ 1) → ∀ (M : GlobalTheory.LamT.LocMod z T iK),
      letI := (iK.comp (algebraMap c.F z.K)).toAlgebra
      ∀ (φ : z.K →ₐ[c.F] T.Fr) (yT y' : FrPt Xo c T.Fr)
        (g : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) T.Fr) (a : T.Fr),
        φ.toRingHom = iK → FrMap φ z.y yT → GlobalTheory.Frames.FrChg g a yT y' → a ≠ 0 → (∀ b, IsUnit (g b).det) →
        GlobalTheory.LamT.LieInt T (iK.comp (algebraMap c.F z.K)) M.m1 M.m2 y'.u → GlobalTheory.LamT.SecInt T M.m1 M.m2 y'.s →
        ∀ cl : ∀ b : E →+* ℂ, Fin (Dw.mult b) → T.Fr,
          (∀ b j i, cl b j * (g b)⁻¹ j i ∈ Set.range (algebraMap T.V T.Fr)) →
        ∀ F ∈ GlobalTheory.AllWt.secZ Xo c e, (∀ v, ∀ w ∈ valSet Xo c (algCls Xo c) v, 0 ≤ w F) →
        ∀ G : MvPolynomial (Formalism.L2.LamCM.FrVar Dw.mult) z.K, (∀ (y' : FrPt Xo c z.K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) z.K),
          (∀ b, (Y b).det ≠ 0) → GlobalTheory.Frames.FrChg (fun b => (Y b).transpose) 1 z.y y' →
          (∏ b, (Y b).det ^ k b) * evR Xo c F y' = Formalism.L2.LamCM.evalFr G Y) →
        ∀ μ, ∃ w : T.V, iK (MvPolynomial.coeff μ G) * ∏ v : Formalism.L2.LamCM.FrVar Dw.mult, cl v.1 v.2.2 ^ μ v =
          (∏ b, (g b).det ^ k b) * algebraMap T.V T.Fr w := by
  first | exact @GlobalTheory.FrameCoeffLoc.coeff_mul_prod_mem_det | exact GlobalTheory.FrameCoeffLoc.coeff_mul_prod_mem_det | (intros; apply GlobalTheory.FrameCoeffLoc.coeff_mul_prod_mem_det <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldMapBijectiveOfIsIsoRestrict
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

theorem functionFieldMap_bijective_of_isIso_restrict : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (s : Y ⟶ X) [IsDominant s] (U : X.Opens), (U : Set X).Nonempty → IsIso (s ∣_ U) → Function.Bijective (functionFieldMap s) := by
  intro X Y _ _ s _ U hU hiso
  have hg : s (genericPoint Y) = genericPoint X := by
    have h := (genericPoint_spec Y).image s.continuous
    rw [Set.image_univ, s.denseRange.closure_range] at h
    exact h.eq (genericPoint_spec X)
  have hmem : genericPoint Y ∈ s ⁻¹ᵁ U := by
    change s (genericPoint Y) ∈ U
    rw [hg]
    exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hU)
  have h1 : IsIso ((s ∣_ U).stalkMap ⟨genericPoint Y, hmem⟩) :=
    ((isIso_iff_isIso_stalkMap (s ∣_ U)).1 hiso).2 _
  have h2 : IsIso (s.stalkMap (genericPoint Y)) :=
    ((MorphismProperty.isomorphisms CommRingCat).arrow_mk_iso_iff
      (morphismRestrictStalkMap s U ⟨genericPoint Y, hmem⟩)).mp h1
  have h3 : ∀ (x y : X) (_ : x = y) (h : x ⤳ y), IsIso (X.presheaf.stalkSpecializes h) := by
    rintro x y rfl h
    rw [TopCat.Presheaf.stalkSpecializes_refl]
    infer_instance
  unfold functionFieldMap
  have h4 := h3 _ _ hg (hg ▸ specializes_rfl)
  exact ConcreteCategory.bijective_of_isIso _

end GlobalTheory.Discrepancy
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GalLab
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
  {X₁ : Setup F W i} {ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}

def Deep.GalLab (D : Deep X₁ ε₁) (σ : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁) (a : D.X.S.Gam ≃+ D.X.S.Gam) : Prop :=
  ∃ (P₀ : PolAV (Sp D.X.Ω₁)) (b : P₀.A.left ⟶ D.X.ρ.P.A.left) (t : P₀.A.left ⟶ P₀.A.left)
    (ε₀ : Matrix (Fin 8) (Fin 8) ℤ → (P₀.A ⟶ P₀.A)),
    IsGrpPullback P₀.A D.X.ρ.P.A (spMap D.X.S.R.val.toRingHom) b ∧
    IsGrpPullback P₀.A P₀.A (spMap (σ : D.X.Ω₁ →+* D.X.Ω₁)) t ∧
    LBIso P₀.L (D.X.ρ.P.L.pull b) ∧ LBIso P₀.L (P₀.L.pull t) ∧
    (∀ E, (ε₀ E).left ≫ b = b ≫ (D.ε E).left ∧ (ε₀ E).left ≫ t = t ≫ (ε₀ E).left) ∧
    ∀ x (w w' : Sp D.X.Ω₁ ⟶ P₀.A.left), w ≫ b = spMap D.X.S.R.val.toRingHom ≫ (D.X.ρ.pt x).left →
      w' ≫ t = spMap (σ : D.X.Ω₁ →+* D.X.Ω₁) ≫ w →
        w' ≫ b = spMap D.X.S.R.val.toRingHom ≫ (D.X.ρ.pt (a x)).left

end GlobalTheory.Poinc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisStatementOfSmallStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_statement_of_small : GlobalTheory.Published.ClozelCohomological → GlobalTheory.Published.CohomologicalCsdTempered → GlobalTheory.Published.HeckeLAdicCharacter → GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.DiscreteSpectrumGL → GlobalTheory.Published.GaloisRepOfPolarizedCuspidal → GlobalTheory.Published.BaseChangeDefiniteUnitary → GlobalTheory.Published.BhattScholzeCrystallineLattices → GlobalTheory.Published.HeckeLAdicCharacterAbove → GlobalTheory.Published.LocalLanglandsGL → SmallSt → GlobalTheory.ExpTie.GalSt := by
  first | exact @GlobalTheory.FrameGal.galSt | exact GlobalTheory.FrameGal.galSt | (intros; apply GlobalTheory.FrameGal.galSt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreComponentClosureOpenIsIntegralStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericFibre_componentClosure_open_isIntegral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : (Xo.XF c).Opens), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (gen Y) → IsClosed (U : Set (Xo.XF c)) → GeometricallyConnected (U.ι ≫ toF Xo c) → ∃ V : (gen Y).Opens, (V : Set (gen Y)) = compactOf Y U ∧ IsIntegral V.toScheme := by
  first | exact @GlobalTheory.DetLine.exists_open_compactOf_isIntegral | exact GlobalTheory.DetLine.exists_open_compactOf_isIntegral | (intros; apply GlobalTheory.DetLine.exists_open_compactOf_isIntegral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricallyConnectedSmoothProjModificationOffOStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompHS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometricallyConnected_smoothProjModification_offOpen : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] (sX : X ⟶ Sp F) (n : ℕ) [SmoothOfRelativeDimension n sX] (U : X.Opens) (M : Modif sX U n) [IsIntegral M.X] [GeometricallyConnected sX], (U : Set X).Nonempty → GeometricallyConnected M.str := by
  first | exact @GlobalTheory.ModifGeomConn.geometricallyConnected_modif | exact GlobalTheory.ModifGeomConn.geometricallyConnected_modif | (intros; apply GlobalTheory.ModifGeomConn.geometricallyConnected_modif <;> assumption)
end

