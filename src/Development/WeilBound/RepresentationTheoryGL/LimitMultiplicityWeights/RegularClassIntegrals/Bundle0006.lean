import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1536
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAutLaurentCoeffSubConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1484
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0726
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2

-- bundled from Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.DDerVan
section
open MeasureTheory Set Filter NumberField IsDedekindDomain Matrix
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RapidDecay GlobalTheory.CompanionTheory.RegInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.TruncKer GlobalTheory.Cusp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.WeightKernel.Dec.DDerVan

theorem mem_aux {G : Type*} [Group G] (K : Set G) (B : Set ℝ) (c : ℝ → G) (x y m : G) (t : ℝ)
    (hk : x * m * (y * c t) ∈ K) (ht : t ∈ B) :
    m ∈ (fun p : G × ℝ => x⁻¹ * p.1 * (y * c p.2)⁻¹) '' (K ×ˢ B) :=
  ⟨(x * m * (y * c t), t), ⟨hk, ht⟩, by simp only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel, mul_one]⟩

end MainStatements.WeightKernel.Dec.DDerVan

theorem MainStatements.WeightKernel.Dec.derVan : MainStatements.WeightKernel.Dec.SmOf → MainStatements.WeightKernel.Dec.DerMem → MainStatements.WeightKernel.Dec.DerVan := by
  intro hSm hDer F E _ _ _ _ _ σ h n J hJ N hN f hf b hb hV ν _ x y
  have hfc := GlobalTheory.Orb.continuous_of_mem_ccAd (σ := σ) (J := J) hf
  have hf'c := GlobalTheory.Orb.continuous_of_mem_ccAd (σ := σ) (J := J) (hDer F E σ h n J hJ f hf b hb)
  have hs := hSm F E σ h n J hJ f hf
  have hbc : Continuous b := GlobalTheory.RealLineCont.continuous_of_isRealLine F E σ h n J b hb
  have hK : IsCompact (tsupport f ∪ tsupport (lineDer b f)) := IsCompact.union hfc.2 hf'c.2
  have hS : IsCompact ((fun p : GAd σ J × ℝ => x⁻¹ * p.1 * (y * b p.2)⁻¹) ''
      ((tsupport f ∪ tsupport (lineDer b f)) ×ˢ Metric.closedBall (0 : ℝ) 1)) :=
    (hK.prod (isCompact_closedBall 0 1)).image
      ((continuous_const.mul continuous_fst).mul ((continuous_const.mul (hbc.comp continuous_snd)).inv))
  have hC := hN.isClosedEmbedding_subtypeVal.isCompact_preimage hS
  have key := GlobalTheory.LaurentAut.hasDerivAt_integral_cpt (𝕜 := ℝ) ν (x₀ := 0)
    (Φ := fun t (m : N) => f (x * m * (y * b t))) (Φ' := fun t (m : N) => lineDer b f (x * m * (y * b t))) hC ?_ ?_ ?_ ?_
  · have h0 : (fun t : ℝ => ∫ m : N, f (x * m * (y * b t)) ∂ν) = fun _ => 0 := funext fun t => hV ν x (y * b t)
    rw [h0] at key
    have e := key.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))
    simpa [GlobalTheory.UAut.ConstAut.realLine_zero h hb] using e
  · intro t
    exact hfc.1.comp ((continuous_const.mul continuous_subtype_val).mul continuous_const)
  · exact hf'c.1.comp ((continuous_const.mul (continuous_subtype_val.comp continuous_snd)).mul
      (continuous_const.mul (hbc.comp continuous_fst)))
  · intro t ht m hm
    have hnot : x * ↑m * (y * b t) ∉ tsupport f ∪ tsupport (lineDer b f) := fun hk =>
      hm (MainStatements.WeightKernel.Dec.DDerVan.mem_aux _ _ b x y (↑m) t hk ht)
    exact ⟨image_eq_zero_of_notMem_tsupport (fun h' => hnot (Or.inl h')),
      image_eq_zero_of_notMem_tsupport (fun h' => hnot (Or.inr h'))⟩
  · intro t m
    have := GlobalTheory.UAut.ConstAut.hasDerivAt_foldr h hs (l := []) (by simp) hb (x * ↑m * y) t
    simpa [mul_assoc] using this
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.NsumLevel
section
open MeasureTheory Set Filter NumberField IsDedekindDomain Matrix
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RapidDecay GlobalTheory.CompanionTheory.RegInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.TruncKer GlobalTheory.Cusp
open PositivityTheory.ThKR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.WeightKernel.Dec.DCore

theorem nsum_level {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (Γ : Subgroup (GAd σ J)) (f : GAd σ J → ℂ)
    (z h κ : GAd σ J) (hκ : ∀ g, f (g * κ) = f g) : nsum Γ f z (h * κ) = nsum Γ f z h := by
  unfold nsum
  exact tsum_congr fun ν => by rw [← mul_assoc, hκ]

theorem nsum_left {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (Γ : Subgroup (GAd σ J)) (f : GAd σ J → ℂ)
    (z h γ : GAd σ J) (hγ : γ ∈ Γ) : nsum Γ f z (γ * h) = nsum Γ f z h := by
  unfold nsum
  have := (Equiv.mulRight (⟨γ, hγ⟩ : Γ)).tsum_eq (fun ν : Γ => f (z * ν * h))
  simpa [mul_assoc] using this

end MainStatements.WeightKernel.Dec.DCore

namespace MainStatements.WeightKernel.Dec
open MainStatements.WeightKernel.Dec.DCore

theorem core : DerMem → DerVan → Level → SumSm → Variation → NearCusp → Base → Core := by
  intro hDM hDV hL hSS hV hNC hBase D V r X Y hW c hc s
  have hcm := isCMExt_host D
  have hJV := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm).2 V
  have hiso : GlobalTheory.UAut.IsIsoCols D.sp.cm.sig V.gram (pre X s) :=
    GlobalTheory.UAut.isIsoCols_of_isWittFrame hW (sigma_sigma hcm) hJV s.2
  have hcl : IsClosed (unipRad D.sp.cm.sig V.gram (pre X s) : Set (GAd D.sp.cm.sig V.gram)) :=
    GlobalTheory.UAut.unipFlag_const (σ := D.sp.cm.sig) (J := V.gram) (pre X s) 0 ▸
      GlobalTheory.UAut.isClosed_unipFlag hJV (sigma_sigma hcm) hiso _
  obtain ⟨A, hA⟩ := hBase D V r X Y hW c hc
  refine ⟨A, fun m => ?_⟩
  induction m with
  | zero =>
    intro f hf _ C W hC hWc
    obtain ⟨B, hB⟩ := hA (NF D.sp.cm.sig V.gram (pre X s)) inf_le_left f (continuous_of_mem_ccAd hf).1 (continuous_of_mem_ccAd hf).2 C W hC hWc
    exact ⟨B, fun t ht a ha x hx y hy => by simpa using hB t ht a ha x hx y hy⟩
  | succ m ih =>
    intro f hf hvan C W hC hWc
    obtain ⟨q, b, Ω₀, Cv, δ₁, hb, hΩ₀, hδ₁, hCv, hmv⟩ := GlobalTheory.T.siegel_set_uniform_smooth_bound _ _ D.sp.cm.sig hcm _ V.gram hJV
    have hW' : IsCompact ((fun x : GAd D.sp.cm.sig V.gram × GAd D.sp.cm.sig V.gram => x.1 * x.2) '' (W ×ˢ Ω₀)) :=
      (hWc.prod hΩ₀).image (by fun_prop)
    choose B hB using fun i => ih (lineDer (b i) f) (hDM _ _ _ hcm _ _ hJV f hf (b i) (hb i))
      (hDV _ _ _ hcm _ _ hJV _ hcl f hf (b i) (hb i) hvan) C _ hC hW'
    obtain ⟨B₀, hB₀⟩ := ih f hf hvan C W hC hWc
    obtain ⟨U, hUo, hU⟩ := hL _ _ _ hcm _ _ hJV f hf
    obtain ⟨M, hM0, hM⟩ := hNC _ _ _ hcm _ _ hJV r X Y hW W c U hWc hc hUo s
    have hR1 : 1 ≤ max 1 (M / δ₁) := le_max_left _ _
    have hSum : 0 ≤ ∑ i, |B i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    refine ⟨max 1 (M / δ₁) * |B₀| + Cv * M * ∑ i, |B i|, fun t ht a ha x hx y hy => ?_⟩
    have hρ : 0 < ratio t s := ratio_pos ht s
    have hT : 0 ≤ (∏ i, max (t i) 1) ^ A :=
      pow_nonneg (Finset.prod_nonneg fun i _ => le_trans zero_le_one (le_max_right _ _)) _
    have hρm : 0 < (ratio t s)⁻¹ ^ m := pow_pos (inv_pos.2 hρ) m
    have hρm1 : 0 < (ratio t s)⁻¹ ^ (m + 1) := pow_pos (inv_pos.2 hρ) _
    have key : (ratio t s)⁻¹ ^ m = ratio t s * (ratio t s)⁻¹ ^ (m + 1) := by
      rw [pow_succ]; field_simp
    have hB0a : 0 ≤ |B₀| := abs_nonneg _
    have hX : 0 ≤ Cv * M * (∑ i, |B i|) * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ (m + 1) := by
      have := mul_nonneg (mul_nonneg hCv hM0) hSum
      positivity
    by_cases hcase : ratio t s ≤ max 1 (M / δ₁)
    · have h1 := hB₀ t ht a ha x hx y hy
      have h2 : B₀ * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ m ≤
          |B₀| * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ m :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hT) hρm.le
      have h3 : ratio t s * (|B₀| * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ (m + 1)) ≤
          max 1 (M / δ₁) * (|B₀| * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ (m + 1)) :=
        mul_le_mul_of_nonneg_right hcase (by positivity)
      have h4 : |B₀| * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ m =
          ratio t s * (|B₀| * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ (m + 1)) := by
        rw [key]; ring
      have h5 : (max 1 (M / δ₁) * |B₀| + Cv * M * ∑ i, |B i|) * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ (m + 1) =
          max 1 (M / δ₁) * (|B₀| * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ (m + 1)) +
          Cv * M * (∑ i, |B i|) * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ (m + 1) := by ring
      rw [h5]
      linarith
    · push Not at hcase
      have hδ : M / ratio t s ≤ δ₁ := by
        rw [div_le_iff₀ hρ]
        have h1 : M / δ₁ ≤ max 1 (M / δ₁) := le_max_right _ _
        rw [div_le_iff₀ hδ₁] at h1
        nlinarith
      have hsm := hSS _ _ _ hcm _ _ hJV (NF D.sp.cm.sig V.gram (pre X s)) inf_le_left f hf (x * a⁻¹)
      have hcc : ∀ i, ∀ x' ∈ Ω₀, ‖lineDer (b i) (nsum (NF D.sp.cm.sig V.gram (pre X s)) f (x * a⁻¹)) ((a * y) * x')‖ ≤
          |B i| * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ m := fun i x' hx' => by
        rw [hsm.2 (b i) (hb i), mul_assoc]
        exact (hB i t ht a ha x hx (y * x') ⟨(y, x'), ⟨hy, hx'⟩, rfl⟩).trans
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hT) hρm.le)
      have hvar := hV _ _ _ hcm _ _ hJV _ (pre X s) hiso f (continuous_of_mem_ccAd hf).1 (continuous_of_mem_ccAd hf).2
        hvan (x * a⁻¹) (a * y) (Cv * (M / ratio t s) * ∑ i, |B i| * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ m)
        (fun m' hm' => by
          obtain ⟨γ, hγ, u, κ, hu, hκU, hκf, e'⟩ := hM t ht a ha y hy m' hm'
          rw [e', nsum_level _ _ _ _ _ (hU κ hκU hκf), mul_assoc γ, nsum_left _ _ _ _ _ hγ]
          exact hmv _ hsm.1 (a * y) u _ (div_nonneg hM0 hρ.le) hδ hu _ hcc)
      have hsum : ∑ i, |B i| * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ m =
          (∑ i, |B i|) * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ m := by
        rw [Finset.sum_mul, Finset.sum_mul]
      have h6 : Cv * (M / ratio t s) * ∑ i, |B i| * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ m =
          Cv * M * (∑ i, |B i|) * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ (m + 1) := by
        rw [hsum, pow_succ, div_eq_mul_inv]; ring
      have h7 : 0 ≤ max 1 (M / δ₁) * |B₀| * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ (m + 1) := by positivity
      rw [h6] at hvar
      have h5 : (max 1 (M / δ₁) * |B₀| + Cv * M * ∑ i, |B i|) * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ (m + 1) =
          max 1 (M / δ₁) * |B₀| * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ (m + 1) +
          Cv * M * (∑ i, |B i|) * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ (m + 1) := by ring
      rw [h5]
      linarith

end MainStatements.WeightKernel.Dec
end
end

