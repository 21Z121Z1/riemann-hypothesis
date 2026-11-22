import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0271
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0327
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0277
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.OppositeColumnLifts
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0264
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0274
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnMulRight
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.IoLift.AvgLift

private theorem isFundamentalDomain_preimage_mul_right' {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (Γ : Subgroup G) (μ : Measure G) [μ.IsMulRightInvariant] {𝓕 : Set G}
    (h : IsFundamentalDomain Γ 𝓕 μ) (a : G) : IsFundamentalDomain Γ ((fun g => g * a) ⁻¹' 𝓕) μ :=
  h.preimage_of_equiv (measurePreserving_mul_right μ a).quasiMeasurePreserving Function.bijective_id
    (fun γ x => mul_assoc (γ : G) x a)

theorem integrableOn_mul_right {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (Γ : Subgroup G)
    [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {𝓕 : Set G}
    (h : IsFundamentalDomain Γ 𝓕 μ) {Φ : G → ℂ} (hΦ : ∀ γ ∈ Γ, ∀ g, Φ (γ * g) = Φ g) (hi : IntegrableOn Φ 𝓕 μ)
    (a : G) : IntegrableOn (fun g => Φ (g * a)) 𝓕 μ := by
  have hinv : ∀ (γ : Γ) (x : G), (fun g => Φ (g * a)) (γ • x) = (fun g => Φ (g * a)) x := by
    intro γ x
    show Φ ((γ : G) * x * a) = Φ (x * a)
    rw [mul_assoc]
    exact hΦ γ γ.2 (x * a)
  rw [h.integrableOn_iff (isFundamentalDomain_preimage_mul_right' Γ μ h a) hinv]
  exact ((measurePreserving_mul_right μ a).integrableOn_comp_preimage
    (MeasurableEquiv.mulRight a).measurableEmbedding).mpr hi

private theorem setIntegral_fd_comp_mul_right_of_invariant {G E : Type} [Group G] [MeasurableSpace G] [MeasurableMul G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (Γ : Subgroup G) [Countable Γ] (μ : Measure G)
    [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {𝓕 : Set G} (h : IsFundamentalDomain Γ 𝓕 μ)
    {Φ : G → E} (hΦ : ∀ γ ∈ Γ, ∀ g, Φ (γ * g) = Φ g) (a : G) :
    ∫ g in 𝓕, Φ (g * a) ∂μ = ∫ g in 𝓕, Φ g ∂μ := by
  have hinv : ∀ (γ : Γ) (x : G), (fun g => Φ (g * a)) (γ • x) = (fun g => Φ (g * a)) x := by
    intro γ x
    show Φ ((γ : G) * x * a) = Φ (x * a)
    rw [mul_assoc]
    exact hΦ γ γ.2 (x * a)
  rw [h.setIntegral_eq (isFundamentalDomain_preimage_mul_right' Γ μ h a) hinv]
  exact (measurePreserving_mul_right μ a).setIntegral_preimage_emb
    (MeasurableEquiv.mulRight a).measurableEmbedding Φ 𝓕

theorem setIntegral_average {G K : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [SecondCountableTopology G] (Γ : Subgroup G) [Countable Γ]
    (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {𝓕 : Set G}
    (h : IsFundamentalDomain Γ 𝓕 μ) [TopologicalSpace K] [MeasurableSpace K] [OpensMeasurableSpace K]
    (m : Measure K) [IsProbabilityMeasure m] {κ : K → G} (hκ : Continuous κ)
    {Φ : G → ℂ} (hΦ : ∀ γ ∈ Γ, ∀ g, Φ (γ * g) = Φ g) (hc : Continuous Φ) (hi : IntegrableOn Φ 𝓕 μ) :
    ∫ g in 𝓕, ∫ k, Φ (g * κ k) ∂m ∂μ = ∫ g in 𝓕, Φ g ∂μ := by
  have hjoint : Continuous fun p : G × K => Φ (p.1 * κ p.2) :=
    hc.comp (continuous_fst.mul (hκ.comp continuous_snd))
  have hint : Integrable (Function.uncurry fun g k => Φ (g * κ k)) ((μ.restrict 𝓕).prod m) := by
    refine (integrable_prod_iff' hjoint.aestronglyMeasurable).mpr ⟨?_, ?_⟩
    · exact Filter.Eventually.of_forall fun k => integrableOn_mul_right Γ μ h hΦ hi (κ k)
    · have hn : ∀ k, ∫ g in 𝓕, ‖Φ (g * κ k)‖ ∂μ = ∫ g in 𝓕, ‖Φ g‖ ∂μ := fun k =>
        setIntegral_fd_comp_mul_right_of_invariant Γ μ h (Φ := fun g => ‖Φ g‖)
          (fun γ hγ g => by simp only [hΦ γ hγ g]) (κ k)
      show Integrable (fun k => ∫ g in 𝓕, ‖Φ (g * κ k)‖ ∂μ) m
      simp only [hn]
      exact integrable_const _
  rw [integral_integral_swap hint]
  have hs : ∀ k, ∫ g in 𝓕, Φ (g * κ k) ∂μ = ∫ g in 𝓕, Φ g ∂μ := fun k =>
    setIntegral_fd_comp_mul_right_of_invariant Γ μ h hΦ (κ k)
  simp only [hs, integral_const, probReal_univ, one_smul]

variable {D : D7} {T : HSp D} {Sp : D.what₂.Tau → SPar}

theorem frame_mem (M : DSModel T Sp) (τ : D.what₂.Tau) {κ : Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (hκ : κ ∈ Formalism.REAL.Kset (M.ε τ)) : (M.fr τ)⁻¹ * κ * M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D T τ) := by
  obtain ⟨hu, hcomm⟩ := hκ
  have hdet : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ)
  have h1 : M.fr τ * (M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have h2 : ((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  have hκu : κᴴ * κ = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.mp hu
    rwa [Matrix.star_eq_conjTranspose] at this
  show ((M.fr τ)⁻¹ * κ * M.fr τ)ᴴ * gramAt D T τ * ((M.fr τ)⁻¹ * κ * M.fr τ) = gramAt D T τ
  rw [← M.fr_gram τ]
  simp only [Matrix.conjTranspose_mul, mul_assoc]
  rw [← mul_assoc ((M.fr τ)⁻¹)ᴴ, h2, one_mul, ← mul_assoc (M.fr τ) (M.fr τ)⁻¹, h1, one_mul,
    ← mul_assoc (Formalism.REAL.Jm (M.ε τ)) κ, ← hcomm, mul_assoc κ, ← mul_assoc κᴴ κ, hκu, one_mul]

theorem continuous_elt {θ : InfFam D} (hθ : IsInfFam θ) (M : DSModel T Sp) (τ : D.what₂.Tau) :
    Continuous fun k : Formalism.REAL.KG (M.ε τ) => GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt θ M τ (Formalism.REAL.toMK k) := by
  have hK : ∀ k : Formalism.REAL.KG (M.ε τ), Formalism.REAL.toMK k ∈ Formalism.REAL.Kset (M.ε τ) := fun k =>
    (Formalism.REAL.mem_KG (M.ε τ) k).mp k.2
  have hc : Continuous fun k : Formalism.REAL.KG (M.ε τ) => Formalism.REAL.toMK k :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  show Continuous fun k : Formalism.REAL.KG (M.ε τ) => atTau θ T τ ((M.fr τ)⁻¹ * Formalism.REAL.toMK k * M.fr τ)
  exact (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ T τ).comp_continuous
    ((continuous_const.matrix_mul hc).matrix_mul continuous_const)
    (fun k => frame_mem M τ (hK k))

theorem liftInt_eq_sum_average : ∀ (D : D7) (V W : HSp D) (S' : D.what₂.Tau → SPar) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)), IsInfFam θ → IsWeilDatumO ψ V W χS χT ω → ν.IsHaarMeasure → IsFundamentalDomain (GQ W) 𝓕 ν → ∀ (τ : D.what₂.Tau) (n : ℕ) (c : Fin n → Formalism.REAL.KG (M'.ε τ) → ℂ) (f : WO V W → ℂ) (fs : Fin n → WO V W → ℂ) (F : GA D W → ℂ) (Fs : Fin n → GA D W → ℂ), (∀ i, Continuous (c i)) → IsThetaFunO ψ V W f → (∀ k, ω (1, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt θ M' τ (Formalism.REAL.toMK k)) f = ∑ i, c i k • fs i) → IsAutFun W F → (∀ i h, Fs i h = ∫ k, c i k * F (h * GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt θ M' τ (Formalism.REAL.toMK k)) ∂(Formalism.REAL.muK (M'.ε τ))) → ∀ g, IntegrableOn (fun h => thetaKO ω g h f * F h) 𝓕 ν → (∀ i, IntegrableOn (fun h => thetaKO ω g h (fs i) * Fs i h) 𝓕 ν) → Lift.liftInt ν 𝓕 (thetaKO ω) f F g = ∑ i, Lift.liftInt ν 𝓕 (thetaKO ω) (fs i) (Fs i) g := by
  intro D V W S' M' θ ψ χS χT ω ν 𝓕 hθ hW hν h𝓕 τ n c f fs F Fs hc hf hω hF hFs g hi hii
  obtain ⟨hlc, hsc, ht2, hbor, htg, -, hcount⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  obtain ⟨hright, -⟩ := GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D W ν hν
  have hker := GlobalTheory.thetaKO_continuous_and_rat_invariant ψ V W χS χT ω hW f hf
  have hec : Continuous fun k : Formalism.REAL.KG (M'.ε τ) => GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt θ M' τ (Formalism.REAL.toMK k) :=
    continuous_elt hθ M' τ
  have hΦinv : ∀ γ ∈ GQ W, ∀ h, thetaKO ω g (γ * h) f * F (γ * h) = thetaKO ω g h f * F h := by
    intro γ hγ h
    have h1 := hker.2 1 (GQ V).one_mem γ hγ g h
    rw [one_mul] at h1
    rw [h1, hF.left γ hγ h]
  have hΦc : Continuous fun h => thetaKO ω g h f * F h :=
    (hker.1.comp (continuous_const.prodMk continuous_id)).mul hF.cont
  have hlin : ∀ (h k : GA D W) (u : WO V W → ℂ), thetaKO ω g (h * k) u = thetaKO ω g h (ω (1, k) u) := by
    intro h k u
    show ω (g, h * k) u 0 = ω (g, h) (ω (1, k) u) 0
    have hp : ((g, h * k) : GA D V × GA D W) = (g, h) * (1, k) := by simp
    rw [hp, map_mul]
    rfl
  have hsum : ∀ (h : GA D W) (k : Formalism.REAL.KG (M'.ε τ)),
      thetaKO ω g h (∑ i, c i k • fs i) = ∑ i, c i k * thetaKO ω g h (fs i) := by
    intro h k
    show ω (g, h) (∑ i, c i k • fs i) 0 = ∑ i, c i k * ω (g, h) (fs i) 0
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hpt : ∀ h, ∫ k, thetaKO ω g (h * GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt θ M' τ (Formalism.REAL.toMK k)) f *
      F (h * GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt θ M' τ (Formalism.REAL.toMK k)) ∂(Formalism.REAL.muK (M'.ε τ)) =
      ∑ i, thetaKO ω g h (fs i) * Fs i h := by
    intro h
    have hexp : ∀ k, thetaKO ω g (h * GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt θ M' τ (Formalism.REAL.toMK k)) f *
        F (h * GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt θ M' τ (Formalism.REAL.toMK k)) =
        ∑ i, thetaKO ω g h (fs i) * (c i k * F (h * GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt θ M' τ (Formalism.REAL.toMK k))) := by
      intro k
      rw [hlin, hω k, hsum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hFk : Continuous fun k : Formalism.REAL.KG (M'.ε τ) =>
        F (h * GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt θ M' τ (Formalism.REAL.toMK k)) :=
      hF.cont.comp (continuous_const.mul hec)
    have hint : ∀ i, Integrable (fun k => thetaKO ω g h (fs i) *
        (c i k * F (h * GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt θ M' τ (Formalism.REAL.toMK k)))) (Formalism.REAL.muK (M'.ε τ)) := fun i =>
      integrableOn_univ.mp
        ((continuous_const.mul ((hc i).mul hFk)).continuousOn.integrableOn_compact isCompact_univ)
    simp_rw [hexp]
    rw [integral_finsetSum _ fun i _ => hint i]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul, hFs i h]
  show ∫ h in 𝓕, thetaKO ω g h f * F h ∂ν = ∑ i, ∫ h in 𝓕, thetaKO ω g h (fs i) * Fs i h ∂ν
  refine (setIntegral_average (GQ W) ν h𝓕 (m := Formalism.REAL.muK (M'.ε τ))
    (Φ := fun h => thetaKO ω g h f * F h) hec hΦinv hΦc hi).symm.trans ?_
  rw [← integral_finsetSum _ fun i _ => hii i]
  exact integral_congr_ae (Filter.Eventually.of_forall hpt)

end GlobalTheory.Chain.IoLift.AvgLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralFundamentalDomainEqIteratedDecomp
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix

open scoped Pointwise

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoordUnfold

theorem isAddFundamentalDomain_prod {A B : Type} [AddGroup A] [AddGroup B] [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} [SFinite μ] [SigmaFinite ν]
    {Γ : AddSubgroup A} {Δ : AddSubgroup B} {s : Set A} {t : Set B}
    (hs : IsAddFundamentalDomain Γ s μ) (ht : IsAddFundamentalDomain Δ t ν) :
    IsAddFundamentalDomain (Γ.prod Δ) (s ×ˢ t) (μ.prod ν) where
  nullMeasurableSet := hs.nullMeasurableSet.prod ht.nullMeasurableSet
  ae_covers := by
    have h1 : ∀ᵐ p ∂(μ.prod ν), ∃ g : Γ, g +ᵥ p.1 ∈ s :=
      Measure.quasiMeasurePreserving_fst.ae hs.ae_covers
    have h2 : ∀ᵐ p ∂(μ.prod ν), ∃ d : Δ, d +ᵥ p.2 ∈ t :=
      Measure.quasiMeasurePreserving_snd.ae ht.ae_covers
    filter_upwards [h1, h2] with p hg hd
    obtain ⟨g, hg⟩ := hg
    obtain ⟨d, hd⟩ := hd
    exact ⟨⟨((g : A), (d : B)), g.2, d.2⟩, hg, hd⟩
  aedisjoint := by
    rintro ⟨⟨g, d⟩, hg, hd⟩ ⟨⟨g', d'⟩, hg', hd'⟩ hne
    have key : ((⟨(g, d), hg, hd⟩ : Γ.prod Δ) +ᵥ s ×ˢ t) ∩ ((⟨(g', d'), hg', hd'⟩ : Γ.prod Δ) +ᵥ s ×ˢ t) =
        (((⟨g, hg⟩ : Γ) +ᵥ s) ∩ ((⟨g', hg'⟩ : Γ) +ᵥ s)) ×ˢ (((⟨d, hd⟩ : Δ) +ᵥ t) ∩ ((⟨d', hd'⟩ : Δ) +ᵥ t)) := by
      ext ⟨x, y⟩
      simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_vadd_set_iff_neg_vadd_mem]
      exact ⟨fun ⟨⟨a1, a2⟩, a3, a4⟩ => ⟨⟨a1, a3⟩, a2, a4⟩, fun ⟨⟨a1, a3⟩, a2, a4⟩ => ⟨⟨a1, a2⟩, a3, a4⟩⟩
    show (μ.prod ν) (_ ∩ _) = 0
    rw [key, Measure.prod_prod]
    by_cases h : g = g'
    · subst h
      have hdd : (⟨d, hd⟩ : Δ) ≠ ⟨d', hd'⟩ := fun e => hne (by
        have := congrArg Subtype.val e
        simp only at this
        subst this; rfl)
      have := ht.aedisjoint hdd
      rw [show ν _ = 0 from this, mul_zero]
    · have hgg : (⟨g, hg⟩ : Γ) ≠ ⟨g', hg'⟩ := fun e => h (congrArg Subtype.val e)
      have := hs.aedisjoint hgg
      rw [show μ _ = 0 from this, zero_mul]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem integral_fundamentalDomain_eq_iterated : ∀ (D : D7) (V W : HSp D) (a b k : ℕ) (f₁ f₃ : Mx D a b → WO V W) (f₂ : Mx D 1 k → WO V W), Continuous f₁ → Continuous f₂ → Continuous f₃ → (∀ s s', f₁ (s + s') = f₁ s + f₁ s') → (∀ z z', f₂ (z + z') = f₂ z + f₂ z') → (∀ y y', f₃ (y + y') = f₃ y + f₃ y') → (∀ x : WO V W, ∃ s z y, x = f₁ s + f₂ z + f₃ y) → (∀ s z y, f₁ s + f₂ z + f₃ y = 0 → s = 0 ∧ z = 0 ∧ y = 0) → (∀ s z y, f₁ s + f₂ z + f₃ y ∈ ratL W V ↔ s ∈ GlobalTheory.MixModel.ratMx D a b ∧ z ∈ GlobalTheory.MixModel.ratMx D 1 k ∧ y ∈ GlobalTheory.MixModel.ratMx D a b) → ∀ (μ : Measure (Mx D a b)) (𝓨 : Set (Mx D a b)), IsCovolOne (GlobalTheory.MixModel.ratMx D a b) μ 𝓨 → ∀ (η : Measure (Mx D 1 k)) (𝓩 : Set (Mx D 1 k)), η.IsAddHaarMeasure → IsAddFundamentalDomain (GlobalTheory.MixModel.ratMx D 1 k) 𝓩 η → ∀ (ν : Measure (WO V W)) (𝓕 : Set (WO V W)), ν.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 ν → ∃ κ : ℝ, 0 < κ ∧ ∀ T : WO V W → ℂ, Continuous T → (∀ γ ∈ ratL W V, ∀ u, T (γ + u) = T u) → ∫ u in 𝓕, T u ∂ν = κ * ∫ s in 𝓨, (∫ z in 𝓩, (∫ y in 𝓨, T (f₁ s + f₂ z + f₃ y) ∂μ) ∂η) ∂μ := by
  intro D V W a b k f₁ f₃ f₂ hc₁ hc₂ hc₃ ha₁ ha₂ ha₃ hsurj hinj hrat μ 𝓨 hμ η 𝓩 hη h𝓩 ν 𝓕 hν h𝓕
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.MixModel.lattice_Mx D a b
  obtain ⟨j1, j2, j3, j4, j5, KZ, hKZ, hKZc⟩ := GlobalTheory.MixModel.lattice_Mx D 1 k
  obtain ⟨l1, l2, l3, l4, l5, K, hK, hKc⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank V.rank
  haveI : BorelSpace (Mx D a b) := ⟨rfl⟩
  haveI : BorelSpace (Mx D 1 k) := ⟨rfl⟩
  haveI : BorelSpace (WO V W) := ⟨rfl⟩
  haveI : Countable (GlobalTheory.MixModel.ratMx D a b) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI : Countable (GlobalTheory.MixModel.ratMx D 1 k) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI : IsTopologicalAddGroup (WO V W) := l1
  haveI : LocallyCompactSpace (WO V W) := l2
  haveI : SecondCountableTopology (WO V W) := l3
  haveI : T2Space (WO V W) := l4
  haveI : BaireSpace (WO V W) := BaireSpace.of_t2Space_locallyCompactSpace
  haveI : Countable (ratL W V) := by
    have : Countable (GlobalTheory.MixModel.ratMx D W.rank V.rank) :=
      TopologicalSpace.separableSpace_iff_countable.1 inferInstance
    exact this
  haveI := hμ.1

  have hZfin : η 𝓩 < ⊤ := by
    have hcov : 𝓩 ⊆ ⋃ γ : GlobalTheory.MixModel.ratMx D 1 k, ((γ +ᵥ KZ) ∩ 𝓩) := by
      intro x hx
      obtain ⟨γ, hγ, hγx⟩ := hKZc x
      refine Set.mem_iUnion.2 ⟨⟨-γ, neg_mem hγ⟩, Set.mem_vadd_set.2 ⟨γ + x, hγx, ?_⟩, hx⟩
      show -γ + (γ + x) = x
      abel
    calc η 𝓩 ≤ ∑' γ : GlobalTheory.MixModel.ratMx D 1 k, η ((γ +ᵥ KZ) ∩ 𝓩) :=
          (measure_mono hcov).trans (measure_iUnion_le _)
      _ = η KZ := (h𝓩.measure_eq_tsum KZ).symm
      _ < ⊤ := hKZ.measure_lt_top
  haveI : IsFiniteMeasure (μ.restrict 𝓨) := ⟨by rw [Measure.restrict_apply_univ, hμ.2.2]; exact ENNReal.one_lt_top⟩
  haveI : IsFiniteMeasure (η.restrict 𝓩) := ⟨by rw [Measure.restrict_apply_univ]; exact hZfin⟩

  let Ehom : (Mx D a b × (Mx D 1 k × Mx D a b)) →+ WO V W :=
    AddMonoidHom.mk' (fun p => f₁ p.1 + f₂ p.2.1 + f₃ p.2.2) (fun p q => by
      simp only [Prod.fst_add, Prod.snd_add, ha₁, ha₂, ha₃]; abel)
  have hEc : Continuous Ehom :=
    ((hc₁.comp continuous_fst).add (hc₂.comp (continuous_fst.comp continuous_snd))).add
      (hc₃.comp (continuous_snd.comp continuous_snd))
  have hEi : Function.Injective Ehom := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨s, z, y⟩ h
    obtain ⟨h1, h2, h3⟩ := hinj s z y h
    simp [h1, h2, h3]
  have hEs : Function.Surjective Ehom := fun x => by
    obtain ⟨s, z, y, rfl⟩ := hsurj x
    exact ⟨(s, z, y), rfl⟩
  have hEo : IsOpenMap Ehom := AddMonoidHom.isOpenMap_of_sigmaCompact Ehom hEs hEc
  let Eq : (Mx D a b × (Mx D 1 k × Mx D a b)) ≃+ WO V W := AddEquiv.ofBijective Ehom ⟨hEi, hEs⟩
  let H : (Mx D a b × (Mx D 1 k × Mx D a b)) ≃ₜ WO V W := Eq.toEquiv.toHomeomorphOfContinuousOpen hEc hEo
  let Ec : (Mx D a b × (Mx D 1 k × Mx D a b)) ≃ₜ+ WO V W :=
    { Eq with continuous_toFun := hEc, continuous_invFun := H.symm.continuous }
  have hEapp : ∀ s z y, Ec (s, z, y) = f₁ s + f₂ z + f₃ y := fun _ _ _ => rfl
  let Me : (Mx D a b × (Mx D 1 k × Mx D a b)) ≃ᵐ WO V W := H.toMeasurableEquiv
  have hMe : ∀ p, Me p = Ec p := fun _ => rfl

  set lam : Measure (Mx D a b × (Mx D 1 k × Mx D a b)) := μ.prod (η.prod μ) with hlam
  haveI : lam.IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  set m : Measure (WO V W) := lam.map Me with hm
  haveI : m.IsAddHaarMeasure := Ec.isAddHaarMeasure_map lam
  have hνm := Measure.isAddLeftInvariant_eq_smul ν m
  set c := Measure.addHaarScalarFactor ν m with hcdef
  have hc : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure ν m
  have hcne : (c : ENNReal) ≠ 0 := by exact_mod_cast hc.ne'

  set Γ : AddSubgroup (Mx D a b × (Mx D 1 k × Mx D a b)) :=
    (GlobalTheory.MixModel.ratMx D a b).prod ((GlobalTheory.MixModel.ratMx D 1 k).prod (GlobalTheory.MixModel.ratMx D a b)) with hΓ
  have hmemΓ : ∀ p, p ∈ Γ ↔ Ec p ∈ ratL W V := by
    rintro ⟨s, z, y⟩
    rw [hEapp, hrat]
    simp [Γ, AddSubgroup.mem_prod]
  have hFDP : IsAddFundamentalDomain Γ (𝓨 ×ˢ (𝓩 ×ˢ 𝓨)) lam :=
    isAddFundamentalDomain_prod hμ.2.1 (isAddFundamentalDomain_prod h𝓩 hμ.2.1)
  have hac : lam.map Me ≪ ν := by
    intro s hs
    rw [hνm, Measure.smul_apply] at hs
    exact (smul_eq_zero.1 hs).resolve_left hc.ne'
  have hqmp : Measure.QuasiMeasurePreserving Me lam ν := ⟨Me.measurable, hac⟩
  let eΓ : ratL W V → Γ := fun g => ⟨Ec.symm g, (hmemΓ _).2 (by simpa using g.2)⟩
  have heΓ : Function.Bijective eΓ := by
    refine ⟨fun g g' h => Subtype.ext ?_, fun p => ⟨⟨Ec p, (hmemΓ p).1 p.2⟩, Subtype.ext ?_⟩⟩
    · have := congrArg (fun q : Γ => Ec q.1) h
      simpa [eΓ] using this
    · simp [eΓ]
  haveI : Countable Γ := heΓ.2.countable
  have hFDE : IsAddFundamentalDomain Γ (Me ⁻¹' 𝓕) lam :=
    h𝓕.preimage_of_equiv hqmp heΓ (fun g p => by
      show Me ((Ec.symm g : _) + p) = (g : WO V W) + Me p
      rw [hMe, hMe, map_add, Ec.apply_symm_apply])
  refine ⟨(c : ℝ), by exact_mod_cast hc, fun T hT hper => ?_⟩
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hT.continuousOn
  have hbd : ∀ x, ‖T x‖ ≤ C := fun x => by
    obtain ⟨γ, hγ, hx⟩ := hKc x
    rw [← hper γ hγ x]
    exact hC _ hx
  have hTE : Continuous fun p => T (Me p) := hT.comp Ec.continuous
  have e1 : ∫ u in 𝓕, T u ∂ν = (c : ℝ) • ∫ u in 𝓕, T u ∂m := by
    rw [hνm, Measure.restrict_smul, integral_smul_nnreal_measure, NNReal.smul_def]
  have e2 : ∫ u in 𝓕, T u ∂m = ∫ p in Me ⁻¹' 𝓕, T (Me p) ∂lam := setIntegral_map_equiv Me T 𝓕
  have e3 : ∫ p in Me ⁻¹' 𝓕, T (Me p) ∂lam = ∫ p in 𝓨 ×ˢ (𝓩 ×ˢ 𝓨), T (Me p) ∂lam :=
    hFDE.setIntegral_eq hFDP (fun g p => by
      show T (Me ((g : _) + p)) = T (Me p)
      rw [hMe, hMe, map_add]
      exact hper _ ((hmemΓ _).1 g.2) _)
  have e4 : lam.restrict (𝓨 ×ˢ (𝓩 ×ˢ 𝓨)) = (μ.restrict 𝓨).prod ((η.restrict 𝓩).prod (μ.restrict 𝓨)) := by
    rw [Measure.prod_restrict, Measure.prod_restrict]
  rw [e1, e2, e3, e4, integral_prod _ (Integrable.of_bound hTE.aestronglyMeasurable C (ae_of_all _ fun p => hbd _)),
    Complex.real_smul]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun s => ?_)
  have hs : Continuous fun q : Mx D 1 k × Mx D a b => T (Me (s, q)) := hTE.comp (Continuous.prodMk_right s)
  dsimp only
  rw [integral_prod _ (Integrable.of_bound hs.aestronglyMeasurable C (ae_of_all _ fun p => hbd _))]
  rfl

end GlobalTheory.CoordUnfold

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCuspGrowOfMemSpan
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.CuspGrowSpace

variable {D : D7} {θ : InfFam D} {V : HSp D} {φ ψ : GA D V → ℂ}

theorem isCuspGrow_add (h : IsCuspGrow θ V φ) (h' : IsCuspGrow θ V ψ) : IsCuspGrow θ V (φ + ψ) := by
  obtain ⟨a, s, c, g⟩ := h
  obtain ⟨a', s', c', g'⟩ := h'
  refine ⟨⟨fun γ hγ g => by rw [Pi.add_apply, Pi.add_apply, a.left γ hγ, a'.left γ hγ], ?_, a.cont.add a'.cont⟩,
    add_mem s s', GlobalTheory.MultMem.isCuspFun_add a a' c c', ?_⟩
  · obtain ⟨U, hU, e⟩ := a.level
    obtain ⟨U', hU', e'⟩ := a'.level
    exact ⟨U ⊓ U', hU.inter hU', fun k hk hf g => by
      rw [Pi.add_apply, Pi.add_apply, e k hk.1 hf, e' k hk.2 hf]⟩
  · obtain ⟨N, hN⟩ := GlobalTheory.Size.unifModGrowth_iff.1 g
    obtain ⟨N', hN'⟩ := GlobalTheory.Size.unifModGrowth_iff.1 g'
    refine GlobalTheory.Size.unifModGrowth_iff.2 ⟨max N N', fun l hl => ?_⟩
    rw [(GlobalTheory.Size.linOnSm_rWord hl).add _ s _ s']
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2
      ⟨ne_top_of_le_ne_top (hN l hl) (GlobalTheory.Size.growthSize_anti (le_max_left _ _)),
        ne_top_of_le_ne_top (hN' l hl) (GlobalTheory.Size.growthSize_anti (le_max_right _ _))⟩) GlobalTheory.Size.growthSize_add_le

theorem isCuspGrow_smul (z : ℂ) (h : IsCuspGrow θ V φ) : IsCuspGrow θ V (z • φ) := by
  obtain ⟨a, s, c, g⟩ := h
  refine ⟨⟨fun γ hγ g => by rw [Pi.smul_apply, Pi.smul_apply, a.left γ hγ], ?_, a.cont.const_smul z⟩,
    Submodule.smul_mem _ z s, GlobalTheory.MultMem.isCuspFun_smul z c, ?_⟩
  · obtain ⟨U, hU, e⟩ := a.level
    exact ⟨U, hU, fun k hk hf g => by rw [Pi.smul_apply, Pi.smul_apply, e k hk hf]⟩
  · obtain ⟨N, hN⟩ := GlobalTheory.Size.unifModGrowth_iff.1 g
    refine GlobalTheory.Size.unifModGrowth_iff.2 ⟨N, fun l hl => ?_⟩
    rw [(GlobalTheory.Size.linOnSm_rWord hl).smul, GlobalTheory.Size.growthSize_smul]
    exact ENNReal.mul_ne_top enorm_ne_top (hN l hl)

theorem isCuspGrow_zero : IsCuspGrow θ V 0 := by
  refine ⟨(isAutFunSm_const θ V 0).toIsAutFun, zero_mem _, fun _ _ _ _ _ _ _ _ => by simp,
    GlobalTheory.Size.unifModGrowth_iff.2 ⟨0, fun l hl => ?_⟩⟩
  have := (GlobalTheory.Size.linOnSm_rWord (θ := θ) hl).smul 0 0
  rw [zero_smul, zero_smul] at this
  rw [this]
  exact (GlobalTheory.Size.growthSize_const (0 : ℂ)).trans_ne enorm_ne_top

theorem isCuspGrow_of_mem_span : ∀ (D : D7) (θ : InfFam D) (V : HSp D),
    ∀ φ ∈ Submodule.span ℂ {φ | IsCuspGrow θ V φ}, IsCuspGrow θ V φ := by
  intro D θ V φ h
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact isCuspGrow_zero
  | add x y _ _ hx hy => exact isCuspGrow_add hx hy
  | smul c x _ hx => exact isCuspGrow_smul c hx

end GlobalTheory.Chain.CuspGrowSpace

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFinVecOfDual
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.IwahoriMembership
open scoped Pointwise TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FlipPath

variable {D : D7}

section Local

variable (e : AE D) (I : Ideal (𝓞 D.host.E)) (ν : (AE D)ˣ →* Circle)

def IsPlaces : Prop := I ≠ ⊥ ∧ ∃ P : Finset (Pl D.host.E), IsIdemSum e P ∧ ∀ w ∈ P, I ≤ w.asIdeal

def TrivMod : Prop := ∀ z : (AE D)ˣ, e * ((z : AE D) - 1) = (z : AE D) - 1 → InI I (toEAf D ((z : AE D) - 1)) → ν z = 1

def OwnDepth {p q : ℕ} (φ : Matrix (Fin p) (Fin q) (Datum.EAf D) → ℂ) : Prop :=
  ∀ y, InHalf e y → (φ y ≠ 0 → IsIntM y) ∧ ∀ u, InHalf e u → (∀ i j, InI I (u i j)) → φ (y + u) = φ y

def DualDepth {p q : ℕ} (φ : Matrix (Fin p) (Fin q) (Datum.EAf D) → ℂ) : Prop :=
  ∀ y, InHalf e y → (φ y ≠ 0 → ∀ i j, InIinv I (y i j)) ∧ ∀ u, InHalf e u → IsIntM u → φ (y + u) = φ y

def ColDepth {a d₁ d₂ : ℕ} (Φ : Matrix (Fin d₁) (Fin a) (Datum.EAf D) → Matrix (Fin d₂) (Fin a) (Datum.EAf D) → ℂ) : Prop :=
  ∀ x₁ x₂, InHalf e x₁ → InHalf e x₂ →
    (Φ x₁ x₂ ≠ 0 → IsIntM x₁ ∧ ∀ i j, InIinv I (x₂ i j)) ∧
    ∀ u₁ u₂, InHalf e u₁ → InHalf e u₂ → (∀ i j, InI I (u₁ i j)) → IsIntM u₂ → Φ (x₁ + u₁) (x₂ + u₂) = Φ x₁ x₂

def IsCosetReps {n : ℕ} (Rp : Set (GL (Fin n) (AE D))) : Prop :=
  (∀ r ∈ Rp, AtE e r) ∧ ∀ g, AtE e g → ∃! r, r ∈ Rp ∧ InK e I (g * r⁻¹)

variable {e I}

end Local

theorem isSelfDualC_sgn (ε : Bool) {S : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} (h : IsSelfDualC S Λ) :
    IsSelfDualC (sgn ε S) Λ := by
  cases ε
  · exact h
  · refine ⟨h.1, fun y => (h.2 y).trans (forall₂_congr fun x _ => ?_)⟩
    have e : ∑ i, ∑ j, star (x i) * (neg S).gram i j * y j = -∑ i, ∑ j, star (x i) * S.gram i j * y j := by
      simp [neg_gram, Finset.sum_neg_distrib]
    refine ⟨fun ⟨b, hb⟩ => ⟨-b, ?_⟩, fun ⟨b, hb⟩ => ⟨-b, ?_⟩⟩
    · refine Eq.trans ?_ e.symm
      rw [← hb]; simp
    · have := hb.trans e
      rw [← neg_eq_iff_eq_neg] at this
      rw [← this]; simp

section Fin

variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : Node D} {e : AE D} {P : Finset (Pl D.host.E)} {f₀ f : WO S.V T.V → ℂ}

theorem isFinVec_of_own {ε : Bool} (hv : IsVac ψ θ ε S T f₀) (hS : IsSelfDualC S.V S.Λ) (hT : IsSelfDualC T.V T.Λ) (he : IsIdemSum e P)
    {φ : Matrix (Fin T.V.rank) (Fin S.V.rank) (Datum.EAf D) → ℂ} (h : IsDatOwn ψ ε S T e f₀ φ f) : IsFinVec ψ θ ε S T f := by
  obtain ⟨hSB, ⟨Tm, hTm⟩, hall⟩ := h
  rw [hall Tm hTm]
  exact finVec_of_mem_span (S := sgn ε S.V) hv (GlobalTheory.Chain.StepVac.placeModel_span_ne hv.1 (isSelfDualC_sgn ε hS) hT
    (GlobalTheory.PlaceDatum.idemSum_mul_self he) he.2 (GlobalTheory.PlaceDatum.infPart_idemSum he) hTm hSB).1

end Fin

variable {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (G : GridDat R)

def GoodX (t : T) (e : AE D) (i j : ℕ) (f : DX G i j) : Prop :=
  ∃ φ, OwnDepth e (depth G t) φ ∧ IsDatOwn R.ψ true (G.V (i + 1) j) (G.V i j) e (G.X i j).vac φ f

def GoodT (t : T) (e : AE D) (i j : ℕ) (f : DT G i j) : Prop :=
  ∃ φ, DualDepth e (depth G t) φ ∧ IsDatDual R.ψ (G.V i j) (G.V i (j + 1)) e (G.th t i j).vac φ f

end GlobalTheory.FlipPath

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotropicConditionLastTorusDiagonalIntegralStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropic_condition_last_torus_diagonal_integral : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ ρ) (p : Pieces V₀ W W₀ ρ ρ) (z : Fin V₀.rank → D.host.E) (LV : Lat V) (LV₀ : Lat V₀) (LW : Lat W) (LW₀ : Lat W₀) (v : GlobalTheory.FinPl.Pl D), GoodAt dV dW (xZero dW) ψ LV LV₀ LW LW₀ v → StdAt dV dW p LV LW v → (0 < ρ → ∀ a ∈ idAt D (· = v), dW.incAdj V₀ (a • yZero V₀ ρ z) ∈ latO V₀ W (LV₀ : Set _) (LW : Set _) (· = v) ↔ a ∈ intAt D (· = v)) → ∀ t : GL (Fin ρ) (AE D), (∀ i j, i ≠ j → t.1 i j = 0) → dW.levi t ∈ grpAt W (· = v) → (∀ ξ ∈ p.B₁, ∀ ξ' : Mx D ρ V₀.rank, MxAt (· = v) ξ → mt W (dW.levi t) ⬝ dW.incX V₀ ξ = dW.incX V₀ ξ' → ψ (symplO V₀ W (dW.incAdj V₀ (yZero V₀ ρ z)) (dW.incX V₀ ξ')) = ψ (symplO V₀ W (dW.incAdj V₀ (yZero V₀ ρ z)) (dW.incX V₀ ξ))) → ∀ i : Fin ρ, i.1 + 1 = ρ → t.1 i i - 1 ∈ intAt D (· = v) := by
  first | exact @GlobalTheory.AscFin.IsoDiag.last_diag_int_iso | exact GlobalTheory.AscFin.IsoDiag.last_diag_int_iso | (intros; apply GlobalTheory.AscFin.IsoDiag.last_diag_int_iso <;> assumption)
end

