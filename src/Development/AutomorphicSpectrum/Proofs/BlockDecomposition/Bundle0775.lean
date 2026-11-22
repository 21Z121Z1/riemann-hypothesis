import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1870
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0771
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0772
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0480
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1842
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0770
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.DerivSub
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0757
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0769
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0767
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0768
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KvFintype
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantTermBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealModelExists
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0524
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeTransformInvariance
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Pointwise

namespace GlobalTheory.CompanionTheory.FJE.TransportInt

theorem isAddFundamentalDomain_prod {X : Type*} [AddCommGroup X] [MeasurableSpace X]
    (Γ : AddSubgroup X) {μ : Measure X} [SFinite μ] {F : Set X}
    (h : IsAddFundamentalDomain Γ F μ) :
    IsAddFundamentalDomain (Γ.prod Γ) (F ×ˢ F) (μ.prod μ) := by
  refine ⟨h.nullMeasurableSet.prod h.nullMeasurableSet, ?_, ?_⟩
  · have h1 : ∀ᵐ z ∂(μ.prod μ), ∃ g : Γ, g +ᵥ z.1 ∈ F :=
      Measure.quasiMeasurePreserving_fst.ae h.ae_covers
    have h2 : ∀ᵐ z ∂(μ.prod μ), ∃ g : Γ, g +ᵥ z.2 ∈ F :=
      Measure.quasiMeasurePreserving_snd.ae h.ae_covers
    filter_upwards [h1, h2] with z a b
    obtain ⟨g, hg⟩ := a
    obtain ⟨g', hg'⟩ := b
    exact ⟨⟨(g.1, g'.1), g.2, g'.2⟩, hg, hg'⟩
  · intro g g' hne
    have key : ∀ k : Γ.prod Γ, (k +ᵥ (F ×ˢ F)) =
        (((⟨k.1.1, k.2.1⟩ : Γ)) +ᵥ F) ×ˢ (((⟨k.1.2, k.2.2⟩ : Γ)) +ᵥ F) := by
      intro k
      ext z
      simp only [Set.mem_vadd_set_iff_neg_vadd_mem, Set.mem_prod]
      rfl
    show μ.prod μ ((g +ᵥ (F ×ˢ F)) ∩ (g' +ᵥ (F ×ˢ F))) = 0
    rw [key, key, Set.prod_inter_prod, Measure.prod_prod]
    by_cases h1 : g.1.1 = g'.1.1
    · have h2 : g.1.2 ≠ g'.1.2 := fun h2 => hne (Subtype.ext (Prod.ext h1 h2))
      have : ((⟨g.1.2, g.2.2⟩ : Γ)) ≠ ⟨g'.1.2, g'.2.2⟩ := fun h3 => h2 (congrArg Subtype.val h3)
      have h4 := h.aedisjoint this
      simp only [Function.onFun] at h4
      rw [show μ _ = 0 from h4, mul_zero]
    · have : ((⟨g.1.1, g.2.1⟩ : Γ)) ≠ ⟨g'.1.1, g'.2.1⟩ := fun h3 => h1 (congrArg Subtype.val h3)
      have h4 := h.aedisjoint this
      simp only [Function.onFun] at h4
      rw [show μ _ = 0 from h4, zero_mul]

section Generic

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem map_eq_of_fundamentalDomain (L : AddSubgroup G) [Countable L] (ν : Measure G)
    [ν.IsAddHaarMeasure] {F : Set G} (hF : IsAddFundamentalDomain L F ν) (h0 : ν F ≠ 0)
    (hT0 : ν F ≠ ∞) (T : G ≃ₜ+ G) (hr : ∀ x, T x ∈ L ↔ x ∈ L) :
    ν.map T = ν ∧ IsAddFundamentalDomain L (T '' F) ν := by
  have hemb : MeasurableEmbedding T := T.toHomeomorph.measurableEmbedding
  haveI hH : (ν.map T).IsAddHaarMeasure :=
    T.toAddEquiv.isAddHaarMeasure_map ν T.continuous T.symm.continuous
  have e := Measure.isAddLeftInvariant_eq_smul (ν.map T) ν
  have hF2 : IsAddFundamentalDomain L F (ν.map T) :=
    hF.mono (by rw [e]; exact Measure.smul_absolutelyContinuous)
  have hF3 : IsAddFundamentalDomain L (T '' F) (ν.map T) := by
    let g : L ≃ L :=
      { toFun := fun γ => ⟨T.symm γ, (hr _).1 (by rw [T.apply_symm_apply]; exact γ.2)⟩
        invFun := fun γ => ⟨T γ, (hr _).2 γ.2⟩
        left_inv := fun γ => Subtype.ext (T.apply_symm_apply _)
        right_inv := fun γ => Subtype.ext (T.symm_apply_apply _) }
    refine hF.image_of_equiv T.toEquiv ?_ g fun γ x => ?_
    · refine ⟨(T.symm.continuous.measurable : Measurable (T.symm : G → G)), ?_⟩
      have : (ν.map T).map T.symm = ν := by
        have hs : Measurable (T.symm : G → G) := T.symm.continuous.measurable
        have ht : Measurable (T : G → G) := T.continuous.measurable
        rw [Measure.map_map hs ht]
        have : (T.symm ∘ T : G → G) = id := funext T.symm_apply_apply
        rw [this, Measure.map_id]
      exact this.absolutelyContinuous
    · change T (T.symm γ + x) = γ + T x
      rw [map_add, T.apply_symm_apply]
  have h3 : ν.map T F = ν.map T (T '' F) := hF2.measure_eq hF3
  have h4 : ν.map T (T '' F) = ν F := by
    rw [hemb.map_apply, Set.preimage_image_eq _ T.injective]
  have hc : Measure.addHaarScalarFactor (ν.map T) ν = 1 := by
    have h5 : ν.map T F = ν F := h3.trans h4
    rw [e, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h5
    have h6 := (ENNReal.mul_eq_right h0 hT0).1 h5
    simpa using h6
  have hm : ν.map T = ν := by rw [e, hc, one_smul]
  refine ⟨hm, ?_⟩
  rwa [hm] at hF3

theorem setIntegral_comp_eq (L : AddSubgroup G) [Countable L] (ν : Measure G)
    [ν.IsAddHaarMeasure] {F : Set G} (hF : IsAddFundamentalDomain L F ν) (h0 : ν F ≠ 0)
    (hT0 : ν F ≠ ∞) (T : G ≃ₜ+ G) (hr : ∀ x, T x ∈ L ↔ x ∈ L) (A : G → ℂ)
    (hA : ∀ γ ∈ L, ∀ v, A (γ + v) = A v) :
    ∫ v in F, A (T v) ∂ν = ∫ v in F, A v ∂ν := by
  obtain ⟨hm, hF3⟩ := map_eq_of_fundamentalDomain L ν hF h0 hT0 T hr
  have hemb : MeasurableEmbedding T := T.toHomeomorph.measurableEmbedding
  have h1 : ∫ v in T '' F, A v ∂(ν.map T) = ∫ v in F, A (T v) ∂ν := by
    rw [hemb.setIntegral_map, Set.preimage_image_eq _ T.injective]
  rw [← h1, hm]
  exact hF3.setIntegral_eq hF fun γ a => hA γ γ.2 a

end Generic

end GlobalTheory.CompanionTheory.FJE.TransportInt

namespace GlobalTheory.CompanionTheory.FJE.TransportInt

theorem transport_int : ∀ {D : D7} {ρ p : ℕ} (m : Meas D ρ p) (T : (Mx D ρ p × Mx D ρ p) ≃ₜ+ (Mx D ρ p × Mx D ρ p)), (∀ ξ₁ ξ₂ : Matrix (Fin ρ) (Fin p) D.host.E, ∃ ξ₁' ξ₂' : Matrix (Fin ρ) (Fin p) D.host.E, T (GlobalTheory.CompanionTheory.FJE.rt ξ₁, GlobalTheory.CompanionTheory.FJE.rt ξ₂) = (GlobalTheory.CompanionTheory.FJE.rt ξ₁', GlobalTheory.CompanionTheory.FJE.rt ξ₂')) → (∀ ξ₁ ξ₂ : Matrix (Fin ρ) (Fin p) D.host.E, ∃ ξ₁' ξ₂' : Matrix (Fin ρ) (Fin p) D.host.E, T.symm (GlobalTheory.CompanionTheory.FJE.rt ξ₁, GlobalTheory.CompanionTheory.FJE.rt ξ₂) = (GlobalTheory.CompanionTheory.FJE.rt ξ₁', GlobalTheory.CompanionTheory.FJE.rt ξ₂')) → ∀ A : Mx D ρ p × Mx D ρ p → ℂ, (∀ (ξ₁ ξ₂ : Matrix (Fin ρ) (Fin p) D.host.E) v, A (v + (GlobalTheory.CompanionTheory.FJE.rt ξ₁, GlobalTheory.CompanionTheory.FJE.rt ξ₂)) = A v) → ∫ v in m.𝓕 ×ˢ m.𝓕, A (T v) ∂(m.μ.prod m.μ) = ∫ v in m.𝓕 ×ˢ m.𝓕, A v ∂(m.μ.prod m.μ) := by
  intro D ρ p m T h1 h2 A hA
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D ρ p
  haveI : BorelSpace (Mx D ρ p) := ⟨rfl⟩
  haveI : Countable (ratMx D ρ p) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨hμ, hF, hone⟩ := m.hμ
  haveI : Countable ((ratMx D ρ p).prod (ratMx D ρ p)) :=
    (Function.Injective.countable (f := fun g : (ratMx D ρ p).prod (ratMx D ρ p) =>
      ((⟨g.1.1, g.2.1⟩ : ratMx D ρ p), (⟨g.1.2, g.2.2⟩ : ratMx D ρ p))) fun a b h =>
        Subtype.ext (Prod.ext (congrArg (fun z => z.1.1) h) (congrArg (fun z => z.2.1) h)))
  have hv : m.μ.prod m.μ (m.𝓕 ×ˢ m.𝓕) = 1 := by rw [Measure.prod_prod, hone, one_mul]
  have mem : ∀ z : Mx D ρ p × Mx D ρ p, z ∈ (ratMx D ρ p).prod (ratMx D ρ p) ↔
      ∃ ξ₁ ξ₂ : Matrix (Fin ρ) (Fin p) D.host.E, z = (GlobalTheory.CompanionTheory.FJE.rt ξ₁, GlobalTheory.CompanionTheory.FJE.rt ξ₂) := by
    rintro ⟨a, b⟩
    constructor
    · rintro ⟨⟨ξ₁, h₁⟩, ⟨ξ₂, h₂⟩⟩
      exact ⟨ξ₁, ξ₂, Prod.ext h₁.symm h₂.symm⟩
    · rintro ⟨ξ₁, ξ₂, h⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact ⟨⟨ξ₁, rfl⟩, ⟨ξ₂, rfl⟩⟩
  have hr : ∀ x, T x ∈ (ratMx D ρ p).prod (ratMx D ρ p) ↔ x ∈ (ratMx D ρ p).prod (ratMx D ρ p) := by
    intro x
    constructor
    · intro h
      obtain ⟨ξ₁, ξ₂, e⟩ := (mem _).1 h
      obtain ⟨ξ₁', ξ₂', e'⟩ := h2 ξ₁ ξ₂
      refine (mem _).2 ⟨ξ₁', ξ₂', ?_⟩
      rw [← e', ← e, T.symm_apply_apply]
    · intro h
      obtain ⟨ξ₁, ξ₂, e⟩ := (mem _).1 h
      obtain ⟨ξ₁', ξ₂', e'⟩ := h1 ξ₁ ξ₂
      exact (mem _).2 ⟨ξ₁', ξ₂', by rw [e, e']⟩
  refine setIntegral_comp_eq _ (m.μ.prod m.μ) (isAddFundamentalDomain_prod _ hF)
    (by rw [hv]; exact one_ne_zero) (by rw [hv]; exact ENNReal.one_ne_top) T hr A ?_
  intro γ hγ v
  obtain ⟨ξ₁, ξ₂, e⟩ := (mem _).1 hγ
  rw [e, add_comm]
  exact hA ξ₁ ξ₂ v

end GlobalTheory.CompanionTheory.FJE.TransportInt
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftInvSubtypeSum
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.SplitGram

variable {D : D7}

abbrev sg (D : D7) : D.host.E →+* D.host.E := (D.sp.cm.sig : D.host.E →+* D.host.E)

theorem gramQ_eq (V : HSp D) {r : ℕ} (x : Matrix (Fin V.rank) (Fin r) D.host.E) :
    gramQ V x = Formalism.UG.cT (sg D) x * (HSpace.gram V * x) := rfl

theorem gramQ_mul (V : HSp D) {r : ℕ} {δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E}
    (hδ : Formalism.UG.cT (sg D) δ * HSpace.gram V * δ = HSpace.gram V)
    (x : Matrix (Fin V.rank) (Fin r) D.host.E) : gramQ V (δ * x) = gramQ V x := by
  rw [gramQ_eq, gramQ_eq, Formalism.UG.cT_mul]
  calc Formalism.UG.cT (sg D) x * Formalism.UG.cT (sg D) δ * (HSpace.gram V * (δ * x))
      = Formalism.UG.cT (sg D) x * ((Formalism.UG.cT (sg D) δ * HSpace.gram V * δ) * x) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hδ]

theorem gramQ_herm (V : HSp D) {r : ℕ} (x : Matrix (Fin V.rank) (Fin r) D.host.E) :
    ((gramQ V x).map (D.sp.cm.sig : D.host.E → D.host.E)).transpose = gramQ V x := by
  have hJ : Formalism.UG.cT (sg D) (HSpace.gram V) = HSpace.gram V := Matrix.ext fun i j => (GlobalTheory.Doubling.isHermND_gram V).1 i j
  have hx : Formalism.UG.cT (sg D) (Formalism.UG.cT (sg D) x) = x := Matrix.ext fun i j => star_star (x i j)
  change Formalism.UG.cT (sg D) (gramQ V x) = gramQ V x
  rw [gramQ_eq, Formalism.UG.cT_mul, Formalism.UG.cT_mul, hx, hJ, Matrix.mul_assoc]

theorem leftInv_subtypeSum {M : Type*} [AddCommMonoid M] [TopologicalSpace M] (V : HSp D) {n : ℕ}
    (f : Mx D V.rank n → M) (p : Matrix (Fin V.rank) (Fin n) D.host.E → Prop)
    (hp : ∀ δ : GL (Fin V.rank) D.host.E, Formalism.UG.cT (sg D) δ.1 * HSpace.gram V * δ.1 = HSpace.gram V →
      ∀ ξ, p ξ → p (δ.1 * ξ)) :
    LeftInv (GQ V) fun h => ∑' ξ : {ξ : Matrix (Fin V.rank) (Fin n) D.host.E // p ξ},
      f (GlobalTheory.SiegelFormula.invPt V h ξ.1) := by
  intro γ hγ h
  obtain ⟨δ, hU, hδ⟩ : ∃ δ : GL (Fin V.rank) D.host.E, _ ∧ Formalism.UG.bc (incA D) δ = Formalism.L2.Theta.matHom V γ⁻¹ := inv_mem hγ
  have hU' : Formalism.UG.cT (sg D) δ.1 * HSpace.gram V * δ.1 = HSpace.gram V := hU
  have hUi : Formalism.UG.cT (sg D) (δ⁻¹).1 * HSpace.gram V * (δ⁻¹).1 = HSpace.gram V :=
    (Formalism.UG.UJ (sg D) (HSpace.gram V)).inv_mem hU
  let e : {ξ : Matrix (Fin V.rank) (Fin n) D.host.E // p ξ} ≃ {ξ : Matrix (Fin V.rank) (Fin n) D.host.E // p ξ} :=
    ⟨fun ξ => ⟨δ.1 * ξ.1, hp δ hU' _ ξ.2⟩, fun ξ => ⟨(δ⁻¹).1 * ξ.1, hp δ⁻¹ hUi _ ξ.2⟩,
      fun ξ => Subtype.ext (by simp), fun ξ => Subtype.ext (by simp)⟩
  have h1 : Formalism.L2.Theta.mt V γ⁻¹ = δ.1.map (incA D) := (congrArg Units.val hδ).symm
  have h2 : Formalism.L2.Theta.mt V (γ * h)⁻¹ = Formalism.L2.Theta.mt V h⁻¹ * Formalism.L2.Theta.mt V γ⁻¹ := by rw [mul_inv_rev]; rfl
  refine (tsum_congr fun ξ => ?_).trans (e.tsum_eq fun ξ => f (GlobalTheory.SiegelFormula.invPt V h ξ.1))
  simp only [GlobalTheory.SiegelFormula.invPt, e, Equiv.coe_fn_mk, h2, h1, Matrix.mul_assoc, Matrix.map_mul]

def fibreEquiv (V : HSp D) (r : ℕ) :
    (Σ β : HermE D r, {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = β.1}) ≃
      {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r} where
  toFun p := ⟨p.2.1, p.2.2.1⟩
  invFun x := ⟨⟨gramQ V x.1, gramQ_herm V x.1⟩, ⟨x.1, x.2, rfl⟩⟩
  left_inv := by
    rintro ⟨⟨b, hb⟩, x, hx, hg⟩
    change gramQ V x = b at hg
    subst hg
    rfl
  right_inv _ := rfl

theorem hasSum_IfrB : ∀ (D : Formalism.BasicNotions.D7) (r : ℕ) (V : Formalism.BasicNotions.TH.HSp D) (θ : InfFam D), IsInfFam θ →
    ∀ (ν : Measure (GA D V)), ν.IsHaarMeasure → ∀ φ : Mx D V.rank r → ℂ, φ ∈ schwartzA θ V.rank r →
    GlobalTheory.SiegelFormula.absThetaInt V ν φ < ⊤ →
    HasSum (fun β : PositivityTheory.GramSchwartzFunctions.HermE D r => PositivityTheory.GramSchwartzFunctions.BC.IfrB V ν φ β) (PositivityTheory.GramSchwartzFunctions.Ifr V ν φ) := by
  intro D r V θ hθ ν hν φ hφ habs
  have : BorelSpace (GA D V) := ⟨rfl⟩
  haveI := hν
  haveI := GlobalTheory.ThetaTransformMeas.countable_field D.host.E
  haveI : Countable (Matrix (Fin V.rank) (Fin r) D.host.E) :=
    inferInstanceAs (Countable (Fin V.rank → Fin r → D.host.E))
  haveI : Countable (Matrix (Fin r) (Fin r) D.host.E) :=
    inferInstanceAs (Countable (Fin r → Fin r → D.host.E))
  haveI : Countable (HermE D r) :=
    inferInstanceAs (Countable {b : Matrix (Fin r) (Fin r) D.host.E // _})
  have hcont : Continuous φ :=
    (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ _ _ φ hφ).1
  have hrank : ∀ (δ : GL (Fin V.rank) D.host.E) (ξ : Matrix (Fin V.rank) (Fin r) D.host.E),
      (δ.1 * ξ).rank = ξ.rank := fun δ ξ =>
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).1 δ.isUnit)
  have hA := leftInv_subtypeSum V (fun y => ‖φ y‖ₑ)
    (fun x : Matrix (Fin V.rank) (Fin r) D.host.E => x.rank = r)
    (fun δ _ ξ h => (hrank δ ξ).trans h)
  have hfin : ∫⁻ q, descend (GQ V) (fun g => ∑' x : {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r},
      ‖φ (GlobalTheory.SiegelFormula.invPt V g x.1)‖ₑ) q ∂autMeasure V ν < ⊤ := by
    refine (lintegral_mono fun q => ?_).trans_lt habs
    exact ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective
      (fun ξ => ‖φ (GlobalTheory.SiegelFormula.invPt V q.out ξ)‖ₑ)
  have key := GlobalTheory.CompanionTheory.ThetaOrbit.hasSum_average_descend (Γ := GQ V) (μ := ν) (fibreEquiv V r)
    (fun h x => φ (GlobalTheory.SiegelFormula.invPt V h x.1))
    (fun x => (hcont.comp (GlobalTheory.AbsThetaSemi.continuous_invPt V x.1)).measurable)
    hA
    (fun β => leftInv_subtypeSum V φ
      (fun x : Matrix (Fin V.rank) (Fin r) D.host.E => x.rank = r ∧ gramQ V x = β.1)
      (fun δ hδ ξ h => ⟨(hrank δ ξ).trans h.1, (gramQ_mul V hδ ξ).trans h.2⟩))
    hfin
  exact key

end GlobalTheory.CompanionTheory.SplitGram

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NuPairOfDerivativesJacquetStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nu_pair_of_derivatives_jacquet : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → GlobalTheory.BZSeg.DerivJac k → GlobalTheory.BZSeg.JmTheta k → GlobalTheory.BZSeg.DerivSub k → GlobalTheory.BZSeg.NuPair k := by
  first | exact @GlobalTheory.CompanionTheory.BZNuPairAsm.nuPair | exact GlobalTheory.CompanionTheory.BZNuPairAsm.nuPair | (intros; apply GlobalTheory.CompanionTheory.BZNuPairAsm.nuPair <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantFourierCoefficient
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.PcFc

variable {D : D7} {n ρ p : ℕ}

theorem conj_psi {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (t : AF D.host.F) : conj (ψ t) = ψ (-t) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hψ.2.1 t)]

theorem chn_eq (ψ : AddChar (AF D.host.F) ℂ) (β : HermE D n) (b : hermA D n) :
    chn ψ β b = ψ (-GlobalTheory.CompanionTheory.FourierN.pr β.1 b.1) := rfl

theorem chn_cont {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (β : HermE D n) : Continuous (chn ψ β) :=
  hψ.1.comp ((GlobalTheory.CompanionTheory.FourierN.continuous_pr β.1).neg.comp continuous_subtype_val)

theorem chn_per {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (β : HermE D n) : IsPer (chn ψ β) := fun γ hγ x => by
  rw [chn_eq, chn_eq, show (γ + x).1 = γ.1 + x.1 from rfl, GlobalTheory.CompanionTheory.FourierN.pr_add_right, neg_add, AddChar.map_add_eq_mul,
    GlobalTheory.CompanionTheory.FourierN.ker_of_rat hψ γ hγ, one_mul]

theorem trace_bl_mul {R : Type} [CommRing R] (hn : ρ + p = n) (a z : Matrix (Fin ρ) (Fin ρ) R) (d y : Matrix (Fin p) (Fin p) R)
    (x : Matrix (Fin ρ) (Fin p) R) (c : Matrix (Fin p) (Fin ρ) R) :
    Matrix.trace (bl hn a 0 0 d * bl hn z x c y) = Matrix.trace (a * z) + Matrix.trace (d * y) := by
  unfold bl
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  have h : ∀ M : Matrix (Fin ρ ⊕ Fin p) (Fin ρ ⊕ Fin p) R,
      Matrix.trace (M.submatrix (finSumFinEquiv.trans (finCongr hn)).symm (finSumFinEquiv.trans (finCongr hn)).symm) = Matrix.trace M :=
    fun M => Equiv.sum_comp (finSumFinEquiv.trans (finCongr hn)).symm (fun j => M j j)
  rw [h]
  simp [Matrix.trace, Fintype.sum_sum_type]

theorem map_dsum (hn : ρ + p = n) (b₀ : HermE D ρ) (β' : HermE D p) :
    (dsum hn b₀ β').1.map (incA D) = bl hn (b₀.1.map (incA D)) 0 0 (β'.1.map (incA D)) := by
  refine Matrix.ext fun i j => ?_
  simp only [dsum, bl, Matrix.map_apply, Matrix.submatrix_apply]
  rcases (finSumFinEquiv.trans (finCongr hn)).symm i with i' | i' <;>
    rcases (finSumFinEquiv.trans (finCongr hn)).symm j with j' | j' <;> simp

theorem pr_split (hn : ρ + p = n) (b₀ : HermE D ρ) (β' : HermE D p) (z : hermA D ρ) (x : Mx D ρ p) (y : hermA D p) :
    GlobalTheory.CompanionTheory.FourierN.pr (dsum hn b₀ β').1 (bT hn z x y).1 = GlobalTheory.CompanionTheory.FourierN.pr b₀.1 z.1 + GlobalTheory.CompanionTheory.FourierN.pr β'.1 y.1 := by
  simp only [GlobalTheory.CompanionTheory.FourierN.pr, ← GlobalTheory.CompanionTheory.FourierN.halfTr_add]
  congr 1
  rw [map_dsum]
  exact trace_bl_mul hn _ _ _ _ _ _

theorem chn_split {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (hn : ρ + p = n) (b₀ : HermE D ρ) (β' : HermE D p)
    (z : hermA D ρ) (x : Mx D ρ p) (y : hermA D p) :
    chn ψ (dsum hn b₀ β') (bT hn z x y) = conj (chz ψ b₀ z) * chn ψ β' y := by
  rw [chn_eq, pr_split, neg_add, AddChar.map_add_eq_mul, chn_eq]
  congr 1
  exact (conj_psi hψ _).symm

theorem coef_pm (hn : ρ + p = n) (m : Meas D ρ p) {lam : Measure (hermA D n)} {𝓖 : Set (hermA D n)} (h : IsCovolOneH lam 𝓖)
    {lp : Measure (hermA D p)} {𝓖p : Set (hermA D p)} (hp : IsCovolOneH lp 𝓖p) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ)
    (b₀ : HermE D ρ) (β' : HermE D p) (Φ : hermA D n → ℂ) (hc : Continuous Φ) (hper : IsPer Φ) :
    ∫ b in 𝓖, Φ b * chn ψ (dsum hn b₀ β') b ∂lam = ∫ y in 𝓖p, pm hn m ψ b₀ Φ y * chn ψ β' y ∂lp := by
  have hd := GlobalTheory.T.hermitian_integral_block_fubini hn m h hp (fun b => Φ b * chn ψ (dsum hn b₀ β') b) (hc.mul (chn_cont hψ _))
    (fun γ hγ x => by
      show Φ (γ + x) * chn ψ (dsum hn b₀ β') (γ + x) = _
      rw [hper γ hγ x, chn_per hψ _ γ hγ x])
  rw [hd]
  refine integral_congr_ae (.of_forall fun y => ?_)
  show ∫ x in m.𝓕, ∫ z in m.𝓖, Φ (bT hn z x y) * chn ψ (dsum hn b₀ β') (bT hn z x y) ∂m.lz ∂m.μ = pm hn m ψ b₀ Φ y * chn ψ β' y
  simp only [chn_split hψ, ← mul_assoc]
  simp only [integral_mul_const, pm]

end GlobalTheory.CompanionTheory.PcFc

namespace GlobalTheory.CompanionTheory.PcFc

theorem per_nb {D : D7} {n : ℕ} {F : G D n → ℂ} (hinv : LeftInv (GF D n) F) {nb : hermA D n → G D n} (hnb : IsNMap nb) (g : G D n) :
    IsPer (fun b => F (nb b * g)) := fun γ hγ x => by
  show F (nb (γ + x) * g) = F (nb x * g)
  rw [GlobalTheory.CompanionTheory.FourierN.nb_add hnb, mul_assoc]
  exact hinv _ (GlobalTheory.CompanionTheory.FourierN.nb_rat hnb γ hγ) _

theorem cont_nb {D : D7} {n : ℕ} {F : G D n → ℂ} (hF : Continuous F) {nb : hermA D n → G D n} (hnb : IsNMap nb) (g : G D n) :
    Continuous (fun b => F (nb b * g)) :=
  hF.comp ((GlobalTheory.CompanionTheory.FourierN.continuous_nb hnb).mul continuous_const)

def zH (D : D7) (p : ℕ) : HermE D p := ⟨0, by
  rw [Matrix.map_zero _ (map_zero _), Matrix.transpose_zero]⟩

theorem chn_zero {D : D7} {p : ℕ} (ψ : AddChar (AF D.host.F) ℂ) (y : hermA D p) : chn ψ (zH D p) y = 1 := by
  have h := GlobalTheory.CompanionTheory.FourierN.pr_zero_left (D := D) (n := p) y.1
  simp only [GlobalTheory.CompanionTheory.FourierN.pr] at h
  simp only [chn, zH, h, neg_zero, AddChar.map_zero_eq_one]

theorem pcFc : PcFc := by
  intro D n ρ p hn M m ψ hψ F hF hinv
  obtain ⟨lp, 𝓖p, hp⟩ := GlobalTheory.CompanionTheory.HermVol.exists_isCovolOneH D p
  refine ⟨?_, ?_⟩
  · intro h nb lam 𝓖 hC β hr g
    obtain ⟨a, b₀, β', hd, he⟩ := GlobalTheory.T.hermitian_block_diagonal_normal_form hn β hr
    obtain ⟨q, hq⟩ := GlobalTheory.T.fourier_coefficient_conjugation hψ F hF hinv hC a β
    have h1 := hq (q⁻¹ * g)
    rw [mul_inv_cancel_left] at h1
    rw [h1, he]
    have h2 := coef_pm hn m hC.2 hp hψ b₀ β' _ (cont_nb hF hC.1 (q⁻¹ * g)) (per_nb hinv hC.1 (q⁻¹ * g))
    refine h2.trans ?_
    refine setIntegral_eq_zero_of_forall_eq_zero fun y _ => ?_
    rw [← GlobalTheory.T.partial_coefficient_unipotent_mean M m ψ b₀ F hC.1, h b₀ hd, zero_mul]
  · intro hR b₀ hb β hβ nb lam 𝓖 hC g
    have hc := cont_nb hF hC.1 g
    have hpr := per_nb hinv hC.1 g
    have key := GlobalTheory.T.eq_const_of_fourier_coefficients_zero hp hψ (pm hn m ψ b₀ (fun b => F (nb b * g))) (GlobalTheory.T.continuous_partial_fourier_mean hn m hψ b₀ _ hc hpr)
      (GlobalTheory.T.periodic_partial_fourier_mean hn m ψ b₀ _ hpr)
      (fun a ha => by
        rw [← coef_pm hn m hC.2 hp hψ b₀ a _ hc hpr]
        exact hR nb lam 𝓖 hC _ (GlobalTheory.T.rank_direct_sum_hermitian_lt hn b₀ hb a ha) g)
    have e0 : β = dsum hn b₀ (zH D p) := Subtype.ext hβ
    have e1 : fc ψ lam 𝓖 nb F β g = ∫ y in 𝓖p, pm hn m ψ b₀ (fun b => F (nb b * g)) y * chn ψ (zH D p) y ∂lp := by
      rw [e0]
      exact coef_pm hn m hC.2 hp hψ b₀ _ _ hc hpr
    have e2 : pc M m ψ b₀ F g = pm hn m ψ b₀ (fun b => F (nb b * g)) 0 := by
      have := GlobalTheory.T.partial_coefficient_unipotent_mean M m ψ b₀ F hC.1 g 0
      have hz : bT hn (0 : hermA D ρ) 0 (0 : hermA D p) = 0 := by
        apply Subtype.ext
        show (bl hn (0 : Mx D ρ ρ) 0 (adj (0 : Mx D ρ p)) 0 : Mx D n n) = 0
        rw [adj_zero, bl, Matrix.fromBlocks_zero]
        rfl
      rw [hz, GlobalTheory.CompanionTheory.FourierN.nb_zero hC.1, one_mul] at this
      exact this
    rw [e1, e2]
    simp only [chn_zero, mul_one]
    rw [show (fun y => pm hn m ψ b₀ (fun b => F (nb b * g)) y) = fun _ => pm hn m ψ b₀ (fun b => F (nb b * g)) 0 from funext key]
    rw [setIntegral_const, measureReal_def, hp.2.2]
    simp

theorem target : MapsExist → PositivityTheory.PfSWUS.FourierZero → PcFc := fun _ _ => pcFc

end GlobalTheory.CompanionTheory.PcFc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankResidueLeRankGenericStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_residue_le_rank_generic : ∀ (O L : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [Field L] [Algebra O L] [IsFractionRing O L] (n : ℕ) (T : Matrix (Fin n) (Fin n) O), (T.map (IsLocalRing.residue O)).rank ≤ (T.map (algebraMap O L)).rank := by
  first | exact @GlobalTheory.CompanionTheory.Jp.rank_residue_map_le_rank_fraction_map | exact GlobalTheory.CompanionTheory.Jp.rank_residue_map_le_rank_fraction_map | (intros; apply GlobalTheory.CompanionTheory.Jp.rank_residue_map_le_rank_fraction_map <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalPointsHeisenbergGroup
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

theorem rat_maps_mem_GF : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn),
    (∀ ξ : Matrix (Fin ρ) (Fin p) D.host.E, M.sh (GlobalTheory.CompanionTheory.FJE.rt ξ) ∈ GF D n) ∧
    (∀ ξ : Matrix (Fin ρ) (Fin p) D.host.E, M.nzx 0 (GlobalTheory.CompanionTheory.FJE.rt ξ) ∈ GF D n) ∧
    ∀ z ∈ ratHerm D ρ, M.nzx z 0 ∈ GF D n := by
  intro D n ρ p hn M
  refine ⟨fun ξ => GlobalTheory.CompanionTheory.PcB.sh_rat M ξ, fun ξ => GlobalTheory.CompanionTheory.PcB.nzx_rat M 0 (zero_mem _) ξ, fun z hz => ?_⟩
  have h := GlobalTheory.CompanionTheory.PcB.nzx_rat M z hz 0
  rwa [GlobalTheory.CompanionTheory.PcB.rat_zero'] at h

end GlobalTheory.CompanionTheory.FJE
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealModelExistsStatement
section
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_model_exists : PositivityTheory.RgBcC.RealD.ModelEx := by
  first | exact @GlobalTheory.CompanionTheory.ModelS.modelEx_main | exact GlobalTheory.CompanionTheory.ModelS.modelEx_main | (intros; apply GlobalTheory.CompanionTheory.ModelS.modelEx_main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueMeasureIdentityStatement
section
open PositivityTheory.Rg.Rsw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_measure_identity : MapsExist → HtExist → HeckeEta → FJEis → PcBound → RSec → EisHol → ThTotal → PcFc → SphBound → PositivityTheory.PfSWUS.FourierZero → PositivityTheory.PfSWUS.CoefDataExists → ResMu := by
  first | exact @GlobalTheory.CompanionTheory.ResMu.resMu_main | exact GlobalTheory.CompanionTheory.ResMu.resMu_main | (intros; apply GlobalTheory.CompanionTheory.ResMu.resMu_main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBruhatIntegrableAdelicStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_bruhat_integrable_adelic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ dx : Measure (Fin n → Fin M → AF F ⊗[F] E), SdW F E σ M J (AF F) ψ n dx → ∀ Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ, IsSchwartzBruhat Φ → Integrable Φ dx := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Coef.sb_integrable_selfDual | exact GlobalTheory.CompanionTheory.SiegelND.Coef.sb_integrable_selfDual | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Coef.sb_integrable_selfDual <;> assumption)
end

