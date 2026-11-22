import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1420
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0493
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0506
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0517
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0611
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0610
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0507
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.Bundle0001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0592
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0607
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnlinkedCommuteOfIrreducible
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalFinitePlaces
section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.RatFinG

theorem selberg {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (U Γ : Subgroup G) (C : Set G) (n₀ : G)
    (hC : IsCompact C) (hcov : ∀ g ∈ U, ∃ γ ∈ Γ, ∃ c ∈ C, g = γ * c)
    (hfin : ∀ X : Set G, IsCompact X → ((Γ : Set G) ∩ X).Finite) (hn : n₀ ∈ Γ) :
    ∃ C' : Set G, IsCompact C' ∧ ∀ t ∈ U, t * n₀ = n₀ * t → ∃ γ ∈ Γ, γ * n₀ = n₀ * γ ∧ ∃ c ∈ C', t = γ * c := by
  have hX : IsCompact ((fun p : G × G => p.1 * n₀ * p.2⁻¹) '' (C ×ˢ C)) :=
    (hC.prod hC).image (by fun_prop)
  have hF := hfin _ hX
  let rep : G → G := fun f => if h : ∃ γ ∈ Γ, γ⁻¹ * n₀ * γ = f then h.choose else 1
  have hrep : ∀ f, (∃ γ ∈ Γ, γ⁻¹ * n₀ * γ = f) → rep f ∈ Γ ∧ (rep f)⁻¹ * n₀ * rep f = f := by
    intro f h
    simp only [rep, dif_pos h]
    exact h.choose_spec
  refine ⟨⋃ f ∈ (Γ : Set G) ∩ _, (fun c => rep f * c) '' C, hF.isCompact_biUnion fun f _ =>
    hC.image (by fun_prop), ?_⟩
  intro t ht hcomm
  obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov t ht
  set f := γ⁻¹ * n₀ * γ with hf
  have hfc : f = c * n₀ * c⁻¹ := by
    have e : γ⁻¹ * n₀ * γ * c = c * n₀ := by
      have : n₀ * (γ * c) = γ * c * n₀ := hcomm.symm
      calc γ⁻¹ * n₀ * γ * c = γ⁻¹ * (n₀ * (γ * c)) := by group
        _ = γ⁻¹ * (γ * c * n₀) := by rw [this]
        _ = c * n₀ := by group
    rw [hf, eq_mul_inv_iff_mul_eq, e]
  have hfΓ : f ∈ Γ := mul_mem (mul_mem (inv_mem hγ) hn) hγ
  obtain ⟨h1, h2⟩ := hrep f ⟨γ, hγ, rfl⟩
  refine ⟨γ * (rep f)⁻¹, mul_mem hγ (inv_mem h1), ?_, rep f * c, ?_, by group⟩
  · have e : (rep f)⁻¹ * n₀ * rep f = γ⁻¹ * n₀ * γ := h2
    calc γ * (rep f)⁻¹ * n₀ = γ * ((rep f)⁻¹ * n₀ * rep f) * (rep f)⁻¹ := by group
      _ = γ * (γ⁻¹ * n₀ * γ) * (rep f)⁻¹ := by rw [e]
      _ = n₀ * (γ * (rep f)⁻¹) := by group
  · refine Set.mem_biUnion (x := f) ⟨hfΓ, ⟨(c, c), ⟨hc, hc⟩, hfc.symm⟩⟩ ⟨c, hc, rfl⟩

abbrev gam1 (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (δ : GL (Fin n) E) : Subgroup (GL (Fin n) (Af E)) :=
  (ratF E n).range ⊓ twCent (thF E n) (ratF E n δ)

theorem algebraMap_inj (E : Type) [Field E] [NumberField E] : Function.Injective (algebraMap E (Af E)) := by
  haveI : Nontrivial (Af E) := by
    obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 E)
    exact (Formalism.UG.evalV E ⟨P, hP.isPrime,
      Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField E)⟩).toRingHom.domain_nontrivial
  exact (algebraMap E (Af E)).injective

theorem ratF_injective (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) :
    Function.Injective (ratF E n) := by
  intro a b h
  refine Units.ext (Matrix.ext fun i j => algebraMap_inj E ?_)
  exact congrArg (fun g : GL (Fin n) (Af E) => g.val i j) h

theorem ratF_mem_UJ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (H : Matrix (Fin n) (Fin n) E)
    (γ : GL (Fin n) E) : ratF E n γ ∈ UJ (conjFin (IsCMField.complexConj E).toRingEquiv) (H.map (algebraMap E (Af E))) ↔
      γ ∈ UJ (IsCMField.complexConj E).toRingEquiv.toRingHom H := by
  have hi := algebraMap_inj E
  have hv : (ratF E n γ).val = γ.val.map (algebraMap E (Af E)) := rfl
  have hcT : cT (conjFin (IsCMField.complexConj E).toRingEquiv) (γ.val.map (algebraMap E (Af E))) =
      (cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ.val).map (algebraMap E (Af E)) := by
    refine Matrix.ext fun i j => ?_
    exact conjFin_algebraMap _ _
  change cT _ (ratF E n γ).val * _ * (ratF E n γ).val = _ ↔ cT _ γ.val * H * γ.val = H
  rw [hv, hcT, ← Matrix.map_mul, ← Matrix.map_mul]
  exact ⟨fun h => Matrix.map_injective hi h, fun h => by rw [h]⟩

theorem factor (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (δ : GL (Fin n) E) (hδ : polE δ ∈ Ell E n) :
    (∃ C : Set (GL (Fin n) (Af E)), IsCompact C ∧ ∀ t ∈ twCent (thF E n) (ratF E n δ), ∃ γ ∈ gam1 E n δ, ∃ c ∈ C, t = γ * c) ∧
    (∀ X : Set (GL (Fin n) (Af E)), IsCompact X → ((gam1 E n δ : Set (GL (Fin n) (Af E))) ∩ X).Finite) ∧
    {γ : GL (Fin n) (Af E) | γ ∈ gam1 E n δ ∧ IsOfFinOrder γ}.Finite := by
  have hs : (δ * thE E n δ).val.charpoly.Separable := hδ.2.2.1
  have hr : ∀ τ : E →+* ℂ, ∀ z ∈ ((δ * thE E n δ).val.charpoly.map τ).roots, ‖z‖ = 1 := hδ.2.2.2
  obtain ⟨H, hu, hh, hN, hp⟩ := GlobalTheory.T.exists_positive_hermitian_form E n _ hs hr
  obtain ⟨⟨C₀, hC₀, hcov⟩, hfin⟩ := GlobalTheory.T.unitary_group_compact_quotient E n H hu hh hp
  have hc := GlobalTheory.T.twisted_centralizer_unitary_iff E n δ H hs hu hN
  set U := UJ (conjFin (IsCMField.complexConj E).toRingEquiv) (H.map (algebraMap E (Af E))) with hU
  set Γ := (UJ (IsCMField.complexConj E).toRingEquiv.toRingHom H).map (ratF E n) with hΓ
  have hΓfin : ∀ X : Set (GL (Fin n) (Af E)), IsCompact X → ((Γ : Set (GL (Fin n) (Af E))) ∩ X).Finite := by
    intro X hX
    refine ((hfin X hX).image (ratF E n)).subset ?_
    rintro _ ⟨⟨γ, hγ, rfl⟩, hx⟩
    exact ⟨γ, ⟨hγ, hx⟩, rfl⟩
  have hsub : ∀ y ∈ gam1 E n δ, y ∈ Γ := by
    rintro _ ⟨⟨γ, rfl⟩, ht⟩
    exact ⟨γ, (ratF_mem_UJ E n H γ).1 ((hc _).1 ht).1, rfl⟩
  obtain ⟨C', hC', hsel⟩ := selberg U Γ C₀ (ratF E n (δ * thE E n δ)) hC₀
    (fun g hg => by
      obtain ⟨γ, hγ, k, hk, e⟩ := hcov g hg
      exact ⟨_, ⟨γ, hγ, rfl⟩, k, hk, e⟩)
    hΓfin ⟨_, hN, rfl⟩
  refine ⟨⟨C', hC', fun t ht => ?_⟩, fun X hX => (hΓfin X hX).subset fun y hy => ⟨hsub y hy.1, hy.2⟩, ?_⟩
  · obtain ⟨h1, h2⟩ := (hc t).1 ht
    obtain ⟨γ, hγ, hcm, c, hc', e⟩ := hsel t h1 h2
    obtain ⟨γ₀, hγ₀, rfl⟩ := hγ
    exact ⟨ratF E n γ₀, ⟨⟨γ₀, rfl⟩, (hc _).2 ⟨(ratF_mem_UJ E n H γ₀).2 hγ₀, hcm⟩⟩, c, hc', e⟩
  · refine ((GlobalTheory.T.finite_torsion_centralizer_alt E n _ hs).image (ratF E n)).subset ?_
    rintro y ⟨hy, hfo⟩
    obtain ⟨⟨γ, rfl⟩, ht⟩ := hy
    refine ⟨γ, ⟨ratF_injective E n ?_, ?_⟩, rfl⟩
    · rw [map_mul (ratF E n) γ, map_mul (ratF E n) _ γ]
      exact ((hc _).1 ht).2
    · exact (ratF_injective E n).isOfFinOrder_iff.1 hfo

theorem mem_twCent_thP {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} (x : GL (Fin a) (Af E)) (y : GL (Fin b) (Af E))
    (p : Gf E a b) : p ∈ twCent (thP E a b) (x, y) ↔ p.1 ∈ twCent (thF E a) x ∧ p.2 ∈ twCent (thF E b) y := by
  change p * (x, y) = (x, y) * thP E a b p ↔ p.1 * x = x * thF E a p.1 ∧ p.2 * y = y * thF E b p.2
  exact Prod.ext_iff

theorem mem_gam {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E)
    (p : Gf E a b) : p ∈ gam δ₁ δ₂ ↔ p.1 ∈ gam1 E a δ₁ ∧ p.2 ∈ gam1 E b δ₂ := by
  rw [gam, Subgroup.mem_inf, mem_twCent_thP, gam1, gam1, Subgroup.mem_inf, Subgroup.mem_inf]
  constructor
  · rintro ⟨⟨q, rfl⟩, h1, h2⟩
    exact ⟨⟨⟨q.1, rfl⟩, h1⟩, ⟨q.2, rfl⟩, h2⟩
  · rintro ⟨⟨⟨q₁, e₁⟩, h1⟩, ⟨q₂, e₂⟩, h2⟩
    exact ⟨⟨(q₁, q₂), Prod.ext e₁ e₂⟩, h1, h2⟩

theorem ratFin : PositivityTheory.Rg.BcB.G8.Fin.RatFin := by
  intro E _ _ _ _ a b δ₁ δ₂ h₁ h₂
  haveI : T2Space (Af E) :=
    inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
      (fun v => (v.adicCompletionIntegers E : Set (v.adicCompletion E))) Filter.cofinite))
  obtain ⟨⟨C₁, hC₁, hc₁⟩, hf₁, ht₁⟩ := factor E a δ₁ h₁
  obtain ⟨⟨C₂, hC₂, hc₂⟩, hf₂, ht₂⟩ := factor E b δ₂ h₂
  have hs₁ : (δ₁ * thE E a δ₁).val.charpoly.Separable := h₁.2.2.1
  have hs₂ : (δ₂ * thE E b δ₂).val.charpoly.Separable := h₂.2.2.1
  have hK₁ := GlobalTheory.T.finite_kernel_compact_open E a
  have hK₂ := GlobalTheory.T.finite_kernel_compact_open E b
  have hKc : (((Kf E a).prod (Kf E b) : Subgroup (Gf E a b)) : Set (Gf E a b)) = (Kf E a : Set _) ×ˢ (Kf E b : Set _) :=
    Subgroup.coe_prod _ _
  have hKo : IsOpen (((Kf E a).prod (Kf E b) : Subgroup (Gf E a b)) : Set (Gf E a b)) := by
    rw [hKc]; exact hK₁.1.prod hK₂.1
  have hKcp : IsCompact (((Kf E a).prod (Kf E b) : Subgroup (Gf E a b)) : Set (Gf E a b)) := by
    rw [hKc]; exact hK₁.2.prod hK₂.2
  have hcl : IsClosed ((twCent (thP E a b) (ratF E a δ₁, ratF E b δ₂) : Subgroup (Gf E a b)) : Set (Gf E a b)) := by
    have e : ((twCent (thP E a b) (ratF E a δ₁, ratF E b δ₂) : Subgroup (Gf E a b)) : Set (Gf E a b)) =
        (twCent (thF E a) (ratF E a δ₁) : Set _) ×ˢ (twCent (thF E b) (ratF E b δ₂) : Set _) := by
      ext p
      exact mem_twCent_thP _ _ p
    rw [e]
    exact (GlobalTheory.MassNorm.isClosed_twCent_thF E a _).prod (GlobalTheory.MassNorm.isClosed_twCent_thF E b _)
  set T := twCent (thP E a b) (ratF E a δ₁, ratF E b δ₂) with hTdef
  have hcomm : ∀ p ∈ T, ∀ q ∈ T, p * q = q * p := fun p hp q hq => by
    rw [hTdef, mem_twCent_thP] at hp hq
    exact Prod.ext (GlobalTheory.T.twCent_comm_of_charpoly_separable E a δ₁ hs₁ _ hp.1 _ hq.1) (GlobalTheory.T.twCent_comm_of_charpoly_separable E b δ₂ hs₂ _ hp.2 _ hq.2)
  have hle : gam δ₁ δ₂ ≤ T := fun p hp => hp.2
  have hcov : ∀ t ∈ T, ∃ γ ∈ gam δ₁ δ₂, ∃ c ∈ C₁ ×ˢ C₂, t = γ * c := fun t ht => by
    rw [hTdef, mem_twCent_thP] at ht
    obtain ⟨γ₁, hγ₁, c₁, hcc₁, e₁⟩ := hc₁ _ ht.1
    obtain ⟨γ₂, hγ₂, c₂, hcc₂, e₂⟩ := hc₂ _ ht.2
    exact ⟨(γ₁, γ₂), (mem_gam δ₁ δ₂ _).2 ⟨hγ₁, hγ₂⟩, (c₁, c₂), ⟨hcc₁, hcc₂⟩, Prod.ext e₁ e₂⟩
  have hfin : ∀ X : Set (Gf E a b), IsCompact X → ((gam δ₁ δ₂ : Set (Gf E a b)) ∩ X).Finite := fun X hX => by
    have h1 := hf₁ _ (hX.image continuous_fst)
    have h2 := hf₂ _ (hX.image continuous_snd)
    refine (h1.prod h2).subset ?_
    rintro p ⟨hp, hx⟩
    have hp' := (mem_gam δ₁ δ₂ p).1 hp
    exact ⟨⟨hp'.1, ⟨p, hx, rfl⟩⟩, hp'.2, ⟨p, hx, rfl⟩⟩
  have htor : {γ : Gf E a b | γ ∈ gam δ₁ δ₂ ∧ IsOfFinOrder γ}.Finite := by
    refine (ht₁.prod ht₂).subset ?_
    rintro p ⟨hp, hfo⟩
    have hp' := (mem_gam δ₁ δ₂ p).1 hp
    obtain ⟨k, hk, e⟩ := isOfFinOrder_iff_pow_eq_one.1 hfo
    have e' : p.1 ^ k = 1 ∧ p.2 ^ k = 1 := Prod.ext_iff.1 e
    exact ⟨⟨hp'.1, isOfFinOrder_iff_pow_eq_one.2 ⟨k, hk, e'.1⟩⟩, hp'.2, isOfFinOrder_iff_pow_eq_one.2 ⟨k, hk, e'.2⟩⟩
  have hmain := GlobalTheory.T.finite_torsion_lattice_compact (Gf E a b) ((Kf E a).prod (Kf E b)) T (gam δ₁ δ₂)
    (C₁ ×ˢ C₂) hKo hKcp hcl hcomm hle (hC₁.prod hC₂) hcov hfin htor
  exact ⟨⟨hcomm, hmain.1⟩, hmain.2.1, hmain.2.2.1, hmain.2.2.2⟩

end GlobalTheory.CompanionTheory.RatFinG
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealLocalFunctionalEquation
section
noncomputable section

open MeasureTheory Complex Set
open Ad3 Ad3.LR Ad3.LR.C

namespace GlobalTheory.CompanionTheory.WmFE

def jj (g : Matrix (Fin 2) (Fin 2) ℝ) : ℂ := (g 1 1 : ℂ) - (g 1 0 : ℂ) * I

def nn (g : Matrix (Fin 2) (Fin 2) ℝ) : ℂ := (g 0 1 : ℂ) - (g 0 0 : ℂ) * I

lemma range_val : range (Units.val : ℝˣ → ℝ) = {0}ᶜ := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    exact u.ne_zero
  · intro h
    exact ⟨Units.mk0 x h, rfl⟩

lemma measEmb_val : MeasurableEmbedding (Units.val : ℝˣ → ℝ) := by
  refine ⟨Units.val_injective, comap_measurable _, ?_⟩
  rintro s ⟨t, ht, rfl⟩
  rw [image_preimage_eq_inter_range, range_val]
  exact ht.inter (measurableSet_singleton 0).compl

lemma integral_mulR (f : ℝ → ℂ) :
    ∫ a : ℝˣ, f a ∂mulR = ∫ x in ({0}ᶜ : Set ℝ), ((|x|⁻¹ : ℝ) : ℂ) * f x := by
  have e := measEmb_val
  have hm : Measurable fun x : ℝ => ENNReal.ofReal |x|⁻¹ := by fun_prop
  unfold mulR
  rw [← e.integral_map, e.map_comap, range_val,
    restrict_withDensity (measurableSet_singleton 0).compl,
    integral_withDensity_eq_integral_toReal_smul hm (by simp)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [ENNReal.toReal_ofReal (inv_nonneg.2 (abs_nonneg x))]

lemma integral_mulR_pos (f : ℝ → ℂ) (hf : ∀ x, x < 0 → f x = 0) :
    ∫ a : ℝˣ, f a ∂mulR = ∫ x in Ioi (0 : ℝ), (x : ℂ)⁻¹ * f x := by
  rw [integral_mulR]
  have hs : Ioi (0 : ℝ) ⊆ ({0}ᶜ : Set ℝ) := fun x hx => (ne_of_gt hx)
  rw [setIntegral_eq_of_subset_of_forall_diff_eq_zero (measurableSet_singleton (0 : ℝ)).compl hs]
  · refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    simp [abs_of_pos (mem_Ioi.1 hx)]
  · rintro x ⟨h1, h2⟩
    have : x < 0 := lt_of_le_of_ne (not_lt.1 h2) h1
    simp [hf x this]

lemma integral_mulR_neg (f : ℝ → ℂ) (hf : ∀ x, 0 < x → f x = 0) :
    ∫ a : ℝˣ, f a ∂mulR = ∫ x in Ioi (0 : ℝ), (x : ℂ)⁻¹ * f (-x) := by
  rw [integral_mulR]
  have hs : Iio (0 : ℝ) ⊆ ({0}ᶜ : Set ℝ) := fun x hx => (ne_of_lt hx)
  rw [setIntegral_eq_of_subset_of_forall_diff_eq_zero (measurableSet_singleton (0 : ℝ)).compl hs]
  · have h := integral_comp_neg_Ioi (0 : ℝ) (fun x : ℝ => ((|x|⁻¹ : ℝ) : ℂ) * f x)
    rw [neg_zero, integral_Iic_eq_integral_Iio] at h
    rw [← h]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    simp [abs_of_pos (mem_Ioi.1 hx)]
  · rintro x ⟨h1, h2⟩
    have : 0 < x := lt_of_le_of_ne (not_lt.1 h2) (Ne.symm h1)
    simp [hf x this]

lemma integral_mulR_eps (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (f : ℝ → ℂ) (hf : ∀ x, ε * x < 0 → f x = 0) :
    ∫ a : ℝˣ, f a ∂mulR = ∫ x in Ioi (0 : ℝ), (x : ℂ)⁻¹ * f (ε * x) := by
  rcases hε with rfl | rfl
  · simpa using integral_mulR_pos f (fun x hx => hf x (by simpa using hx))
  · simpa using integral_mulR_neg f (fun x hx => hf x (by simpa using hx))

lemma jj_ne {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) : jj g ≠ 0 := by
  intro h
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp [jj] at h1 h2
  exact hg (by simp [Matrix.det_fin_two, h1, h2])

lemma real_whittaker_torus_mul (k : ℕ) (g : Matrix (Fin 2) (Fin 2) ℝ) (a : ℝ) (h : 0 < a * g.det) :
    Wm k (d2 a * g) = (((a * g.det) ^ ((2 * (k : ℝ) - 1) / 2) : ℝ) : ℂ) *
      (jj g) ^ (-(2 * (k : ℤ) - 1)) * Complex.exp (-2 * Real.pi * I * ((a : ℂ) * nn g / jj g)) := by
  have hdet : (d2 a * g).det = a * g.det := by
    rw [Matrix.det_mul]
    simp [d2, Matrix.det_fin_two_of]
  have e00 : (d2 a * g) 0 0 = a * g 0 0 := by simp [d2, Matrix.mul_apply, Fin.sum_univ_two]
  have e01 : (d2 a * g) 0 1 = a * g 0 1 := by simp [d2, Matrix.mul_apply, Fin.sum_univ_two]
  have e10 : (d2 a * g) 1 0 = g 1 0 := by simp [d2, Matrix.mul_apply, Fin.sum_univ_two]
  have e11 : (d2 a * g) 1 1 = g 1 1 := by simp [d2, Matrix.mul_apply, Fin.sum_univ_two]
  unfold Wm
  rw [hdet, if_pos h, e00, e01, e10, e11]
  simp only [jj, nn]
  push_cast
  congr 3
  ring

lemma real_whittaker_torus_mul_zero (k : ℕ) (g : Matrix (Fin 2) (Fin 2) ℝ) (a : ℝ) (h : ¬ 0 < a * g.det) :
    Wm k (d2 a * g) = 0 := by
  have hdet : (d2 a * g).det = a * g.det := by
    rw [Matrix.det_mul]
    simp [d2, Matrix.det_fin_two_of]
  unfold Wm
  rw [hdet, if_neg h]

lemma integrableOn_rpow_exp {σ b : ℝ} (hσ : -1 < σ) (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => t ^ σ * Real.exp (-(b * t))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := σ) (p := 1) (b := b) hσ one_pos hb
  simpa [Real.rpow_one, neg_mul] using h

end GlobalTheory.CompanionTheory.WmFE
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentRepJacquetWordMultiplicity
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.FineL

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem length_decWord (Γ : Segment k) : (decWord Γ).length = Γ.len := by
  simp [decWord]

theorem decWord_get (Γ : Segment k) (a : Fin (decWord Γ).length) :
    (decWord Γ).get a = Γ.first.nu ((Γ.len - 1 - (a : ℕ) : ℕ) : ℂ) := by
  have h : (a : ℕ) < (List.ofFn Γ.term).reverse.length := a.2
  show (List.ofFn Γ.term).reverse[(a : ℕ)] = _
  rw [List.getElem_reverse, List.getElem_ofFn]
  simp [Segment.term]

theorem isCusp_decWord_get (Γ : Segment k) (a : Fin (decWord Γ).length) : ((decWord Γ).get a).IsCusp := by
  rw [decWord_get]
  exact Γ.isCusp_first.nu _

theorem sum_decWord (Γ : Segment k) : ∑ a, ((decWord Γ).get a).1 = Γ.deg := by
  have h : ∀ a, ((decWord Γ).get a).1 = Γ.d := fun a => by rw [decWord_get]; rfl
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, length_decWord]
  rfl

theorem below_of_len_one {s : ℕ} (Γ : Fin s → Segment k) (h : ∀ a, (Γ a).len = 1) (a : Fin s) :
    below Γ a = s - 1 - (a : ℕ) := by
  simp only [below, h, Finset.sum_const, smul_eq_mul, mul_one]
  rw [Finset.filter_lt_eq_Ioi, Fin.card_Ioi]

theorem jmL_decWord (hJ : LSegJacquet k) (Γ : Segment k) {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin N) k) V} (hΓ : IsLSeg Γ π) : jmL (decWord Γ) π = 1 := by
  have hd : ∑ a, ((decWord Γ).get a).1 = N := (sum_decWord Γ).trans hΓ.deg_eq
  rw [jmL, dif_pos hd]
  refine (hJ Γ π hΓ _ (decWord Γ).get hd fun a => (isCusp_decWord_get Γ a).1).1
    ⟨fun a => Segment.single _ (isCusp_decWord_get Γ a), ⟨?_, fun a => ?_⟩,
      fun a => (single_spec (isCusp_decWord_get Γ a)).2.1⟩
  · have h : ∀ a, (Segment.single _ (isCusp_decWord_get Γ a)).len = 1 := fun _ => rfl
    simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one, length_decWord]
  · refine (decWord_get Γ a).trans ?_
    have e : (decWord Γ).length - 1 - (a : ℕ) = Γ.len - 1 - (a : ℕ) := by
      have := length_decWord Γ
      omega
    rw [below_of_len_one _ (fun _ => rfl), e]

theorem len_eq_one (hJ : LSegJacquet k) {Δ : Segment k} {x : IrrGL k} (hx : x.IsCusp) (h : IsLSeg Δ x.rep) :
    Δ.len = 1 := by
  have hd : ∑ a, ((decWord Δ).get a).1 = x.1 := (sum_decWord Δ).trans h.deg_eq
  have h1 := jmL_decWord hJ Δ h
  rw [jmL, dif_pos hd, jm] at h1
  have hsub : IsSubquotient (piTensor fun a => ((decWord Δ).get a).rep)
      (jac (stdBlocks (fun a => ((decWord Δ).get a).1) hd) x.rep) :=
    jhMult_ne_zero_iff.1 (by rw [h1]; exact one_ne_zero)
  have hu := GlobalTheory.SmGL.CuspRow.block_unique_of_isCuspidal k x.1 _ x.rep _ _ _ _
    (fun a => ((decWord Δ).get a).rep) hx.2 (fun a => nontrivial_of_irreducible ((decWord Δ).get a).2.rep.irr) hsub
  by_contra hne
  have hl : 2 ≤ (decWord Δ).length := by
    have := Δ.len_pos
    rw [length_decWord]
    omega
  have := hu ⟨0, by omega⟩ ⟨1, by omega⟩ (isCusp_decWord_get Δ _).1 (isCusp_decWord_get Δ _).1
  simp at this

theorem eq_of_isLSeg_single {ρ : IrrGL k} (hρ : ρ.IsCusp) {x : IrrGL k} (h : IsLSeg (.single ρ hρ) x.rep) : x = ρ := by
  have hdeg : ρ.1 = x.1 := by
    have := h.deg_eq
    simpa [Segment.deg, Segment.single, Segment.ofFirst] using this
  obtain ⟨n, c⟩ := x
  obtain ⟨m, r⟩ := ρ
  obtain rfl : m = n := hdeg
  obtain ⟨φ⟩ := (single_spec hρ).2.1.unique h
  exact (IrrGL.of_rep _).symm.trans ((IrrGL.of_eq_of.2 ⟨φ⟩).trans (IrrGL.of_rep _))

theorem eq_first_of_len_one {Δ : Segment k} (hl : Δ.len = 1) {x : IrrGL k} (h : IsLSeg Δ x.rep) : x = Δ.first := by
  have e : Δ = .single Δ.first Δ.isCusp_first := Segment.ext_first rfl hl
  exact eq_of_isLSeg_single Δ.isCusp_first (e ▸ h)

theorem jmL_cusp_word : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.Published.IrreducibleAdmissibleGL → LSegJacquet k → ∀ (Γ : Segment k) {N : ℕ} {V : Type} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsLSeg Γ π → ∀ W : List (IrrGL k), (∀ w ∈ W, w.IsCusp) →
    (W = decWord Γ → jmL W π = 1) ∧ (W ≠ decWord Γ → jmL W π = 0) := by
  intro k _ _ _ _ _ hJ Γ N V _ _ π hΓ W hW
  refine ⟨fun e => e ▸ jmL_decWord hJ Γ hΓ, fun hne => ?_⟩
  by_cases hd : ∑ a, (W.get a).1 = N
  · rw [jmL, dif_pos hd]
    refine (hJ Γ π hΓ _ W.get hd fun a => (hW _ (List.get_mem W a)).1).2 ?_
    rintro ⟨Γ', ⟨hs, hf⟩, hL⟩
    have hl : ∀ a, (Γ' a).len = 1 := fun a => len_eq_one hJ (hW _ (List.get_mem W a)) (hL a)
    have hlen : W.length = Γ.len := by
      simpa only [hl, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] using hs
    refine hne (List.ext_get (hlen.trans (length_decWord Γ).symm) fun n h1 h2 => ?_)
    have h3 : W.get ⟨n, h1⟩ = Γ.first.nu ((W.length - 1 - n : ℕ) : ℂ) := by
      have h4 := eq_first_of_len_one (hl ⟨n, h1⟩) (hL ⟨n, h1⟩)
      rw [hf, below_of_len_one Γ' hl] at h4
      exact h4
    rw [h3, decWord_get, hlen]
  · rw [jmL, dif_neg hd]

end GlobalTheory.CompanionTheory.FineL

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SliceType
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.EGlue.SliceTypePf

theorem restrict_left {A B : Type} [One B] (W₁ : Submodule ℂ (A → ℂ)) (W₂ : Submodule ℂ (B → ℂ)) (f : A × B → ℂ)
    (hf : f ∈ Submodule.span ℂ {f : A × B → ℂ | ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, f = fun k => w₁ k.1 * w₂ k.2}) :
    (fun k : A => f (k, 1)) ∈ W₁ := by
  induction hf using Submodule.span_induction with
  | mem f h =>
    obtain ⟨w₁, h₁, w₂, -, rfl⟩ := h
    have : (fun k : A => w₁ k * w₂ 1) = w₂ 1 • w₁ := by
      funext k
      simp [mul_comm]
    simpa [this] using W₁.smul_mem _ h₁
  | zero => exact W₁.zero_mem
  | add f g _ _ hf hg => exact W₁.add_mem hf hg
  | smul c f _ hf => exact W₁.smul_mem c hf

theorem restrict_right {A B : Type} [One A] (W₁ : Submodule ℂ (A → ℂ)) (W₂ : Submodule ℂ (B → ℂ)) (f : A × B → ℂ)
    (hf : f ∈ Submodule.span ℂ {f : A × B → ℂ | ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, f = fun k => w₁ k.1 * w₂ k.2}) :
    (fun k : B => f (1, k)) ∈ W₂ := by
  induction hf using Submodule.span_induction with
  | mem f h =>
    obtain ⟨w₁, -, w₂, h₂, rfl⟩ := h
    have : (fun k : B => w₁ 1 * w₂ k) = w₁ 1 • w₂ := by
      funext k
      simp
    simpa [this] using W₂.smul_mem _ h₂
  | zero => exact W₂.zero_mem
  | add f g _ _ hf hg => exact W₂.add_mem hf hg
  | smul c f _ hf => exact W₂.smul_mem c hf

theorem main : GlobalTheory.CompanionTheory.EGlue.SliceType := by
  intro E _ _ _ a b K₁ K₂ W₁ W₂ F hF
  obtain ⟨hl, hk⟩ := hF
  refine ⟨?_, ?_⟩
  · rintro φ m₂ hφ
    refine ⟨?_, ?_⟩
    · intro u hu g
      have := hl u hu 1 K₂.one_mem (g, m₂)
      simpa [hφ, Prod.mk_mul_mk] using this
    · intro g
      have := restrict_left W₁ W₂ _ (hk (g, m₂))
      simpa [hφ, Prod.mk_mul_mk] using this
  · rintro φ m₁ hφ
    refine ⟨?_, ?_⟩
    · intro u hu g
      have := hl 1 K₁.one_mem u hu (m₁, g)
      simpa [hφ, Prod.mk_mul_mk] using this
    · intro g
      have := restrict_right W₁ W₂ _ (hk (m₁, g))
      simpa [hφ, Prod.mk_mul_mk] using this

end GlobalTheory.CompanionTheory.EGlue.SliceTypePf

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TopologicalInfimum
section
open GlobalTheory.CompanionTheory.EGlue

noncomputable section

open GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.CompanionTheory.EGlue.Gl0

theorem topInf : GlobalTheory.CompanionTheory.EGlue.TopInf := by
  intro E _ _ _ τ
  refine ⟨rfl, fun u φ _ => ?_⟩
  simp [cap, Formalism.REAL.qdet, Formalism.REAL.qminor, Formalism.REAL.Tm]

end GlobalTheory.CompanionTheory.EGlue.Gl0

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnlinkedCommuteOfIrreducibleStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unlinked_commute_of_irreducible : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → GlobalTheory.BZSeg.LUnlinkedIrr k → GlobalTheory.BZSeg.LUnlinkedComm k := by
  first | exact @GlobalTheory.CompanionTheory.BZSegComm.lUnlinkedComm | exact GlobalTheory.CompanionTheory.BZSegComm.lUnlinkedComm | (intros; apply GlobalTheory.CompanionTheory.BZSegComm.lUnlinkedComm <;> assumption)
end

