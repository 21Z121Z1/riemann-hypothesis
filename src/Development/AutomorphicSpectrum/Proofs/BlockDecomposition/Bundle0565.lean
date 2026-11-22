import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0538
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0042
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0545
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0537
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.RegularClassTraces.RegClassFin
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.WeilBound.ThetaLifts.Reductions.SiegelOfCore
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0028
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ParabolicLeviDecomposition
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0321
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0523
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0529

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsWeightGamma0NeZero
section
open UpperHalfPlane ModularGroup CongruenceSubgroup Complex
open scoped MatrixGroups Modular Pointwise ENNReal

namespace GlobalTheory.CompanionTheory.ModularTiling

theorem finite_smul_mem_fd (z : ℍ) : {g : SL(2, ℤ) | g • z ∈ 𝒟}.Finite := by
  have hP : {p : Fin 2 → ℤ | normSq ((p 0 : ℂ) * z + p 1) ≤ 2 * z.im}.Finite := by
    have := (tendsto_normSq_coprime_pair z).eventually (Filter.eventually_gt_atTop (2 * z.im))
    rw [Filter.eventually_cofinite] at this
    refine this.subset fun p hp => ?_
    simpa using hp
  have hfib : ∀ p : Fin 2 → ℤ, {g : SL(2, ℤ) | g 1 = p ∧ |(g • z).re| ≤ 1 / 2}.Finite := by
    intro p
    by_cases hne : ∃ g : SL(2, ℤ), g 1 = p
    · obtain ⟨g₀, rfl⟩ := hne
      have hcop : IsCoprime (g₀ 1 0) (g₀ 1 1) := bottom_row_coprime g₀
      have := (tendsto_abs_re_smul z hcop).eventually (Filter.eventually_gt_atTop ((1 : ℝ) / 2))
      rw [Filter.eventually_cofinite] at this
      refine (this.image Subtype.val).subset fun g hg => ?_
      exact ⟨⟨g, hg.1⟩, by simpa using hg.2, rfl⟩
    · refine Set.Finite.subset Set.finite_empty fun g hg => ?_
      exact (hne ⟨g, hg.1⟩).elim
  refine (hP.biUnion fun p _ => hfib p).subset fun g hg => ?_
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  refine ⟨g 1, ?_, rfl, hg.2⟩
  have him := three_le_four_mul_im_sq_of_mem_fd hg
  have hpos := (g • z).im_pos
  have h12 : 1 / 2 ≤ (g • z).im := by nlinarith
  have hz := z.im_pos
  have heq := ModularGroup.im_smul_eq_div_normSq g z
  have hN : 0 < normSq (denom g z) := normSq_pos.2 (denom_ne_zero _ _)
  rw [heq, denom_apply] at h12
  rw [denom_apply] at hN
  rw [le_div_iff₀ hN] at h12
  have : normSq (((g 1 0 : ℤ) : ℂ) * z + ((g 1 1 : ℤ) : ℂ)) ≤ 2 * z.im := by linarith
  exact this

theorem countableSL : Countable SL(2, ℤ) := by
  have : Countable (Matrix (Fin 2) (Fin 2) ℤ) := by
    unfold Matrix
    infer_instance
  exact Subtype.countable

attribute [local instance] countableSL

theorem continuous_smul_const (g : SL(2, ℤ)) : Continuous fun z : ℍ => g • z :=
  continuous_const_smul
    (Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) g))

theorem isClosed_fd : IsClosed (𝒟 : Set ℍ) := by
  have h1 : IsClosed {z : ℍ | 1 ≤ normSq (z : ℂ)} :=
    isClosed_le continuous_const (Complex.continuous_normSq.comp UpperHalfPlane.continuous_coe)
  have h2 : IsClosed {z : ℍ | |z.re| ≤ (1 : ℝ) / 2} :=
    isClosed_le (continuous_abs.comp UpperHalfPlane.continuous_re) continuous_const
  exact h1.inter h2

variable (Γ : Subgroup SL(2, ℤ))

def tile : Set ℍ := ⋃ x : SL(2, ℤ) ⧸ Γ, {z : ℍ | (Quotient.out x : SL(2, ℤ)) • z ∈ 𝒟}

noncomputable def mult (z : ℍ) : ℝ≥0∞ :=
  ∑' γ : Γ, (tile Γ).indicator (fun _ => (1 : ℝ≥0∞)) ((γ : SL(2, ℤ)) • z)

noncomputable def weight (z : ℍ) : ℝ :=
  (tile Γ).indicator (fun z => 2 / (mult Γ z).toReal) z

variable {Γ}

theorem mem_tile_iff {z : ℍ} :
    z ∈ tile Γ ↔ ∃ x : SL(2, ℤ) ⧸ Γ, (Quotient.out x : SL(2, ℤ)) • z ∈ 𝒟 := by
  simp [tile]

theorem isClosed_tile [Γ.FiniteIndex] : IsClosed (tile Γ) := by
  have : Finite (SL(2, ℤ) ⧸ Γ) := Subgroup.finite_quotient_of_finiteIndex
  exact isClosed_iUnion_of_finite fun x => isClosed_fd.preimage (continuous_smul_const _)

theorem finite_smul_mem_tile [Γ.FiniteIndex] (z : ℍ) :
    {γ : Γ | (γ : SL(2, ℤ)) • z ∈ tile Γ}.Finite := by
  have : Finite (SL(2, ℤ) ⧸ Γ) := Subgroup.finite_quotient_of_finiteIndex
  have h : {g : SL(2, ℤ) | g • z ∈ tile Γ}.Finite := by
    have : {g : SL(2, ℤ) | g • z ∈ tile Γ} =
        ⋃ x : SL(2, ℤ) ⧸ Γ, (fun g => (Quotient.out x : SL(2, ℤ)) * g) ⁻¹' {g | g • z ∈ 𝒟} := by
      ext g
      simp [mem_tile_iff, mul_smul]
    rw [this]
    exact Set.finite_iUnion fun x =>
      (finite_smul_mem_fd z).preimage (mul_right_injective _).injOn
  exact h.preimage (f := (Subtype.val : Γ → SL(2, ℤ))) Subtype.val_injective.injOn

theorem exists_smul_mem_tile (z : ℍ) : ∃ γ : Γ, (γ : SL(2, ℤ)) • z ∈ tile Γ := by
  obtain ⟨g, hg⟩ := exists_smul_mem_fd z
  have hmem : (Quotient.out (QuotientGroup.mk g : SL(2, ℤ) ⧸ Γ) : SL(2, ℤ))⁻¹ * g ∈ Γ := by
    rw [← QuotientGroup.eq, QuotientGroup.out_eq']
  refine ⟨⟨_, hmem⟩, mem_tile_iff.2 ⟨QuotientGroup.mk g, ?_⟩⟩
  show Quotient.out (QuotientGroup.mk g : SL(2, ℤ) ⧸ Γ) •
    ((Quotient.out (QuotientGroup.mk g : SL(2, ℤ) ⧸ Γ) : SL(2, ℤ))⁻¹ * g) • z ∈ 𝒟
  rw [smul_smul, mul_inv_cancel_left]
  exact hg

theorem mult_eq_ncard [Γ.FiniteIndex] (z : ℍ) :
    mult Γ z = ({γ : Γ | (γ : SL(2, ℤ)) • z ∈ tile Γ}.ncard : ℝ≥0∞) := by
  classical
  have hf := finite_smul_mem_tile (Γ := Γ) z
  rw [mult, tsum_eq_sum (s := hf.toFinset), Set.ncard_eq_toFinset_card _ hf]
  · rw [Finset.sum_congr rfl (g := fun _ => (1 : ℝ≥0∞))]
    · simp
    · intro γ hγ
      exact Set.indicator_of_mem (by simpa using hγ) _
  · intro γ hγ
    exact Set.indicator_of_notMem (by simpa using hγ) _

theorem mult_smul (γ₀ : Γ) (z : ℍ) : mult Γ ((γ₀ : SL(2, ℤ)) • z) = mult Γ z := by
  unfold mult
  rw [← (Equiv.mulRight γ₀).tsum_eq
    (fun γ : Γ => (tile Γ).indicator (fun _ => (1 : ℝ≥0∞)) ((γ : SL(2, ℤ)) • z))]
  simp [mul_smul]

theorem measurable_mult [Γ.FiniteIndex] : Measurable (mult Γ) := by
  refine Measurable.ennreal_tsum fun γ => ?_
  exact (measurable_const.indicator isClosed_tile.measurableSet).comp
    (continuous_smul_const _).measurable

theorem measurable_weight [Γ.FiniteIndex] : Measurable (weight Γ) :=
  (measurable_const.div measurable_mult.ennreal_toReal).indicator isClosed_tile.measurableSet

theorem weight_nonneg (z : ℍ) : 0 ≤ weight Γ z := by
  unfold weight
  exact Set.indicator_nonneg (fun _ _ => by positivity) z

theorem hasSum_weight [Γ.FiniteIndex] (z : ℍ) :
    HasSum (fun γ : Γ => weight Γ ((γ : SL(2, ℤ)) • z)) 2 := by
  classical
  have hf := finite_smul_mem_tile (Γ := Γ) z
  obtain ⟨γ₁, hγ₁⟩ := exists_smul_mem_tile (Γ := Γ) z
  have hcard : hf.toFinset.card ≠ 0 :=
    Finset.card_ne_zero.2 ⟨γ₁, by simpa using hγ₁⟩
  have hm : (mult Γ z).toReal = hf.toFinset.card := by
    rw [mult_eq_ncard, Set.ncard_eq_toFinset_card _ hf]
    simp
  have hsum : ∑ γ ∈ hf.toFinset, weight Γ ((γ : SL(2, ℤ)) • z) = 2 := by
    rw [Finset.sum_congr rfl (g := fun _ => 2 / (hf.toFinset.card : ℝ))]
    · have : (hf.toFinset.card : ℝ) ≠ 0 := by exact_mod_cast hcard
      simp only [Finset.sum_const, nsmul_eq_mul]
      field_simp
    · intro γ hγ
      have : (γ : SL(2, ℤ)) • z ∈ tile Γ := by simpa using hγ
      rw [weight, Set.indicator_of_mem this, mult_smul, hm]
  rw [← hsum]
  refine hasSum_sum_of_ne_finset_zero fun γ hγ => ?_
  exact Set.indicator_of_notMem (by simpa using hγ) _

theorem two_le_ncard (hneg : (-1 : SL(2, ℤ)) ∈ Γ) [Γ.FiniteIndex] (z : ℍ) :
    2 ≤ {γ : Γ | (γ : SL(2, ℤ)) • z ∈ tile Γ}.ncard := by
  obtain ⟨γ, hγ⟩ := exists_smul_mem_tile (Γ := Γ) z
  have hf := finite_smul_mem_tile (Γ := Γ) z
  refine (Set.one_lt_ncard_iff hf).2 ⟨γ, ⟨-1, hneg⟩ * γ, hγ, ?_, ?_⟩
  · show ((-1 : SL(2, ℤ)) * (γ : SL(2, ℤ))) • z ∈ tile Γ
    rw [neg_one_mul, ModularGroup.SL_neg_smul]
    exact hγ
  · intro h
    have h' : (γ : SL(2, ℤ)) = (-1 : SL(2, ℤ)) * (γ : SL(2, ℤ)) := congrArg Subtype.val h
    have h1 : (-1 : SL(2, ℤ)) = 1 :=
      mul_right_cancel (b := (γ : SL(2, ℤ))) (by rw [one_mul]; exact h'.symm)
    have := congrArg (fun g : SL(2, ℤ) => (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0) h1
    simp at this

theorem weight_le_one (hneg : (-1 : SL(2, ℤ)) ∈ Γ) [Γ.FiniteIndex] (z : ℍ) : weight Γ z ≤ 1 := by
  unfold weight
  by_cases hz : z ∈ tile Γ
  · rw [Set.indicator_of_mem hz, mult_eq_ncard]
    have h2 : (2 : ℝ) ≤ ({γ : Γ | (γ : SL(2, ℤ)) • z ∈ tile Γ}.ncard : ℝ) := by
      exact_mod_cast two_le_ncard hneg z
    simp only [ENNReal.toReal_natCast]
    rw [div_le_one (by linarith)]
    exact h2
  · rw [Set.indicator_of_notMem hz]
    exact zero_le_one

theorem exists_weight (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hneg : (-1 : SL(2, ℤ)) ∈ Γ) :
    ∃ (T : Finset SL(2, ℤ)) (β : ℍ → ℝ), Measurable β ∧ (∀ z, 0 ≤ β z) ∧ (∀ z, β z ≤ 1) ∧
      Function.support β ⊆ ⋃ σ ∈ T, σ • (𝒟 : Set ℍ) ∧
      ∀ z, HasSum (fun γ : Γ => β ((γ : SL(2, ℤ)) • z)) 2 := by
  classical
  have : Fintype (SL(2, ℤ) ⧸ Γ) :=
    @Fintype.ofFinite _ Subgroup.finite_quotient_of_finiteIndex
  refine ⟨Finset.univ.image fun x : SL(2, ℤ) ⧸ Γ => (Quotient.out x : SL(2, ℤ))⁻¹, weight Γ,
    measurable_weight, weight_nonneg, weight_le_one hneg, ?_, hasSum_weight⟩
  intro z hz
  have hzt : z ∈ tile Γ := by
    by_contra h
    exact hz (Set.indicator_of_notMem h _)
  obtain ⟨x, hx⟩ := mem_tile_iff.1 hzt
  simp only [Set.mem_iUnion]
  refine ⟨(Quotient.out x : SL(2, ℤ))⁻¹, Finset.mem_image_of_mem _ (Finset.mem_univ x), ?_⟩
  rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv]
  exact hx

theorem exists_weight_Gamma0_neZero (L : ℕ) [NeZero L] :
    ∃ (T : Finset SL(2, ℤ)) (β : ℍ → ℝ), Measurable β ∧ (∀ z, 0 ≤ β z) ∧ (∀ z, β z ≤ 1) ∧
      Function.support β ⊆ ⋃ σ ∈ T, σ • (𝒟 : Set ℍ) ∧
      ∀ z, HasSum (fun γ : Gamma0 L => β ((γ : SL(2, ℤ)) • z)) 2 :=
  exists_weight (Gamma0 L) (by simp [Gamma0_mem])

theorem exists_weight_Gamma0 : Ad3.S.U0 := by
  intro L hL
  haveI : NeZero L := ⟨hL.ne'⟩
  obtain ⟨T, β, hm, h0, h1, hs, hsum⟩ := exists_weight_Gamma0_neZero L
  refine ⟨β, ⟨hm, fun z => ⟨h0 z, h1 z⟩, hsum⟩, T, fun z hz => ?_⟩
  have h := hs (Function.mem_support.2 hz)
  simp only [Set.mem_iUnion] at h
  obtain ⟨σ, hσ, hz'⟩ := h
  exact ⟨σ, hσ, Set.mem_smul_set_iff_inv_smul_mem.1 hz'⟩

end GlobalTheory.CompanionTheory.ModularTiling
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorizableSiegelWeilFiniteSet
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WhitFree

namespace PureTuple

open NumberField IsDedekindDomain
open GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem coord_projV (v : HeightOneSpectrum (𝓞 F)) {d M n : ℕ} (b : Module.Basis (Fin d) F E)
    (X : Fin n → Fin M → Af F ⊗[F] E) (a : Fin n) (i : Fin M) (k : Fin d) :
    PureSB.coordH (Fv F v) b (projV v X a i) k = (PureSB.coordH (Af F) b (X a i) k) v :=
  PureSB.repr_map b (evalV F v) (X a i) k

theorem continuous_projV (v : HeightOneSpectrum (𝓞 F)) {d M n : ℕ} (b : Module.Basis (Fin d) F E) :
    Continuous (projV v : (Fin n → Fin M → Af F ⊗[F] E) → Fin n → Fin M → Fv F v ⊗[F] E) := by
  refine continuous_pi fun a => continuous_pi fun i => ?_
  have h : (fun X : Fin n → Fin M → Af F ⊗[F] E => projV v X a i) = fun X =>
      (PureSB.coordH (Fv F v) b).symm (fun k => (PureSB.coordH (Af F) b (X a i) k) v) := by
    funext X
    apply (PureSB.coordH (Fv F v) b).injective
    rw [Homeomorph.apply_symm_apply]
    funext k
    exact coord_projV v b X a i k
  rw [h]
  refine (PureSB.coordH (Fv F v) b).symm.continuous.comp (continuous_pi fun k => ?_)
  exact (RestrictedProduct.continuous_eval v).comp ((continuous_apply k).comp
    ((PureSB.coordH (Af F) b).continuous.comp ((continuous_apply i).comp (continuous_apply a))))

theorem projV_mem_latV (v : HeightOneSpectrum (𝓞 F)) {d M n : ℕ} (b : Module.Basis (Fin d) F E)
    (X : Fin n → Fin M → Af F ⊗[F] E) :
    projV v X ∈ latV b v ↔ ∀ a i k, (PureSB.coordH (Af F) b (X a i) k) v ∈ v.adicCompletionIntegers F := by
  refine forall_congr' fun a => forall_congr' fun i => forall_congr' fun k => ?_
  rw [← coord_projV v b X a i k]
  rfl

variable {d M n : ℕ} (b : Module.Basis (Fin d) F E) (S : Finset (HeightOneSpectrum (𝓞 F)))
  (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))

include b in

theorem isClosed_boxF (hA : ∀ v, IsCompact (A v)) : IsClosed (boxF A) := by
  have h : boxF A = ⋂ v, projV v ⁻¹' A v := by
    ext X
    exact ⟨fun h => Set.mem_iInter.2 h, fun h => Set.mem_iInter.1 h⟩
  rw [h]
  refine isClosed_iInter fun v => ?_
  haveI : T2Space (Fv F v ⊗[F] E) := (PureSB.coordH (Fv F v) b).isEmbedding.t2Space
  exact (hA v).isClosed.preimage (continuous_projV v b)

theorem isOpen_boxF (hA : ∀ v, IsOpen (A v)) (hS : ∀ v, v ∉ S → A v = latV b v) : IsOpen (boxF A) := by
  have hT : IsOpen {y : Af F | ∀ v, v ∉ S → y v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_imp_mem fun v => Valued.isOpen_valuationSubring _
  have hI : IsOpen {X : Fin n → Fin M → Af F ⊗[F] E | ∀ a i k,
      PureSB.coordH (Af F) b (X a i) k ∈ {y : Af F | ∀ v, v ∉ S → y v ∈ v.adicCompletionIntegers F}} := by
    have e : {X : Fin n → Fin M → Af F ⊗[F] E | ∀ a i k,
        PureSB.coordH (Af F) b (X a i) k ∈ {y : Af F | ∀ v, v ∉ S → y v ∈ v.adicCompletionIntegers F}} =
        ⋂ a, ⋂ i, ⋂ k, (fun X : Fin n → Fin M → Af F ⊗[F] E => PureSB.coordH (Af F) b (X a i) k) ⁻¹'
          {y : Af F | ∀ v, v ∉ S → y v ∈ v.adicCompletionIntegers F} := by
      ext X
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
    rw [e]
    refine isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun k => ?_
    have hc : Continuous fun X : Fin n → Fin M → Af F ⊗[F] E => PureSB.coordH (Af F) b (X a i) k :=
      (continuous_apply k).comp
        ((PureSB.coordH (Af F) b).continuous.comp ((continuous_apply i).comp (continuous_apply a)))
    exact hT.preimage hc
  have h : boxF A = {X : Fin n → Fin M → Af F ⊗[F] E | ∀ a i k,
      PureSB.coordH (Af F) b (X a i) k ∈ {y : Af F | ∀ v, v ∉ S → y v ∈ v.adicCompletionIntegers F}} ∩
      ⋂ v ∈ S, projV v ⁻¹' A v := by
    ext X
    constructor
    · intro hX
      refine ⟨fun a i k v hv => ?_, Set.mem_iInter₂.2 fun v _ => hX v⟩
      have := hX v
      rw [hS v hv] at this
      exact (projV_mem_latV v b X).1 this a i k
    · rintro ⟨h1, h2⟩ v
      by_cases hv : v ∈ S
      · exact Set.mem_iInter₂.1 h2 v hv
      · rw [hS v hv]
        exact (projV_mem_latV v b X).2 fun a i k => h1 a i k v hv
  rw [h]
  exact hI.inter (isOpen_biInter_finset fun v _ => (hA v).preimage (continuous_projV v b))

theorem isCompact_boxF (hA : ∀ v, IsCompact (A v)) (hS : ∀ v, v ∉ S → A v = latV b v) :
    IsCompact (boxF A) := by
  let B : Fin n → Fin M → Fin d → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v) :=
    fun a i k v => (fun Y : Fin n → Fin M → Fv F v ⊗[F] E => PureSB.coordH (Fv F v) b (Y a i) k) '' A v
  have hB : ∀ a i k v, IsCompact (B a i k v) := fun a i k v =>
    (hA v).image ((continuous_apply k).comp
      ((PureSB.coordH (Fv F v) b).continuous.comp ((continuous_apply i).comp (continuous_apply a))))
  have hBS : ∀ a i k v, v ∉ S →
      B a i k v ⊆ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
    rintro a i k v hv _ ⟨Y, hY, rfl⟩
    rw [hS v hv] at hY
    exact hY a i k
  let eW : (Fin n → Fin M → Af F ⊗[F] E) ≃ₜ (Fin n → Fin M → Fin d → Af F) :=
    Homeomorph.piCongrRight fun _ => Homeomorph.piCongrRight fun _ => PureSB.coordH (Af F) b
  have hL : IsCompact (eW ⁻¹' Set.pi Set.univ fun a => Set.pi Set.univ fun i => Set.pi Set.univ fun k =>
      {y : Af F | ∀ v, y v ∈ B a i k v}) :=
    eW.isCompact_preimage.2 (isCompact_univ_pi fun a => isCompact_univ_pi fun i =>
      isCompact_univ_pi fun k => PureSB.isCompact_box S (B a i k) (hB a i k) (hBS a i k))
  refine hL.of_isClosed_subset (isClosed_boxF b A hA) fun X hX a _ i _ k _ v => ?_
  exact ⟨projV v X, hX v, coord_projV v b X a i k⟩

end PureTuple

theorem pureN_isSchwartzBruhat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, 0 < n → 2 * n < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) (φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (A : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Set (Fin n → Fin M → Fv F v ⊗[F] E)), GlobalTheory.Published.SiegelOneVector.IsSchwartzArch φ → (∀ v, IsCompact (A v) ∧ IsOpen (A v)) → (∀ v, v ∉ S → A v = latV b v) → GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat (pureN φ A) := by
  intro F E _ _ _ _ _ σ _ M J _ n _ _ d b S φ A hφ hA hS
  have hc := PureTuple.isCompact_boxF b S A (fun v => (hA v).1) hS
  have hcl := PureTuple.isClosed_boxF b A fun v => (hA v).1
  have ho := PureTuple.isOpen_boxF b S A (fun v => (hA v).2) hS
  refine GlobalTheory.Published.SiegelOneVector.isSchwartzBruhat_of_prod hφ (Φf := (boxF A).indicator fun _ => (1 : ℂ)) ⟨?_, ?_⟩ fun _ => rfl
  · exact (LocallyConstant.indicator (LocallyConstant.const _ (1 : ℂ)) ⟨hcl, ho⟩).isLocallyConstant
  · exact HasCompactSupport.intro' hc hcl fun Y hY => Set.indicator_of_notMem hY _

end GlobalTheory.CompanionTheory.WhitFree
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreVolumeCompactLowerBound
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.FibreMass

theorem fibre_mass_le_of_pushforward : ∀ (V K : Type) [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [T2Space V] [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K] [T2Space K] (μ : Measure V) (lam : Measure K) (Q : V → K) (Z : Set V) (m : K → Measure V), Continuous Q → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ Q id Z lam Set.univ m → ∀ [lam.IsOpenPosMeasure] [IsLocallyFiniteMeasure lam] (P : Set V), IsCompact P → IsOpen P → P ⊆ Z → ∀ c : ℝ≥0, (∀ S : Set K, MeasurableSet S → μ (P ∩ Q ⁻¹' S) ≤ (c : ℝ≥0∞) * lam S) → ∀ s, m s P ≤ (c : ℝ≥0∞) := by
  intro V K _ _ _ _ _ _ _ _ μ lam Q Z m hQ hfam _ _ P hPc hPo hPZ c hc s
  classical
  obtain ⟨hconc, hdis, hcont⟩ := hfam
  have hPm : MeasurableSet P := hPo.measurableSet
  have hφc : Continuous (P.indicator (fun _ => (1 : ℝ))) :=
    IsClopen.continuous_indicator ⟨hPc.isClosed, hPo⟩ continuous_const
  have hφs : HasCompactSupport (P.indicator (fun _ => (1 : ℝ))) :=
    HasCompactSupport.intro hPc (fun x hx => by simp [hx])
  have hφt : tsupport (P.indicator (fun _ => (1 : ℝ))) ⊆ Z :=
    (closure_minimal Set.support_indicator_subset hPc.isClosed).trans hPZ
  obtain ⟨hint, hgc⟩ := hcont _ hφc hφs hφt
  have hfin : ∀ b, m b P < ∞ := by
    intro b
    have h2 : IntegrableOn (fun _ => (1 : ℝ)) P (m b) :=
      (integrable_indicator_iff hPm).1 (hint b (Set.mem_univ b))
    exact ((integrableOn_const_iff (by simp)).1 h2).resolve_left (by simp)
  have hgeq : ∀ b, ∫ v, P.indicator (fun _ => (1 : ℝ)) v ∂(m b) = (m b P).toReal := by
    intro b
    rw [integral_indicator hPm, setIntegral_const]
    simp [Measure.real]
  have hgcont : Continuous (fun b => (m b P).toReal) := by
    have h := continuousOn_univ.1 hgc
    simpa only [hgeq] using h
  by_contra hlt
  rw [not_le] at hlt
  have hcs : (c : ℝ) < (m s P).toReal := by
    have h := (ENNReal.toReal_lt_toReal ENNReal.coe_ne_top (hfin s).ne).2 hlt
    simpa using h
  obtain ⟨d, hcd, hds⟩ := exists_between hcs
  obtain ⟨N, ⟨hsN, hNo⟩, hNfin⟩ := (lam.finiteAt_nhds s).exists_mem_basis (nhds_basis_opens s)
  have hWo : IsOpen ({b | d < (m b P).toReal} ∩ N) :=
    (isOpen_lt continuous_const hgcont).inter hNo
  have hWm : MeasurableSet ({b | d < (m b P).toReal} ∩ N) := hWo.measurableSet
  have hpos : lam ({b | d < (m b P).toReal} ∩ N) ≠ 0 :=
    (hWo.measure_pos lam ⟨s, hds, hsN⟩).ne'
  have hfinW : lam ({b | d < (m b P).toReal} ∩ N) ≠ ∞ :=
    ((measure_mono Set.inter_subset_right).trans_lt hNfin).ne
  have hAm : MeasurableSet (P ∩ Q ⁻¹' ({b | d < (m b P).toReal} ∩ N)) :=
    hPm.inter (hQ.measurable hWm)
  have key : ∀ b, m b (P ∩ Q ⁻¹' ({b | d < (m b P).toReal} ∩ N)) =
      ({b | d < (m b P).toReal} ∩ N).indicator (fun b => m b P) b := by
    intro b
    have hcb := hconc b
    rw [← measure_inter_conull hcb]
    by_cases hb : b ∈ ({b | d < (m b P).toReal} ∩ N)
    · rw [Set.indicator_of_mem hb, ← measure_inter_conull (s := P) hcb]
      congr 1
      ext v
      constructor
      · rintro ⟨⟨hvP, _⟩, hvT⟩
        exact ⟨hvP, hvT⟩
      · rintro ⟨hvP, hvT⟩
        refine ⟨⟨hvP, ?_⟩, hvT⟩
        have hQv : Q v = b := hvT.1
        show Q v ∈ ({b | d < (m b P).toReal} ∩ N)
        rw [hQv]
        exact hb
    · rw [Set.indicator_of_notMem hb]
      have hE : (P ∩ Q ⁻¹' ({b | d < (m b P).toReal} ∩ N)) ∩ (Q ⁻¹' {id b} ∩ Z) = ∅ := by
        ext v
        simp only [Set.mem_empty_iff_false, iff_false]
        rintro ⟨⟨_, hvW⟩, hvT⟩
        have hQv : Q v = b := hvT.1
        apply hb
        rw [← hQv]
        exact hvW
      rw [hE, measure_empty]
  have hlhs : ∫⁻ v in Z, (P ∩ Q ⁻¹' ({b | d < (m b P).toReal} ∩ N)).indicator 1 v ∂μ =
      μ (P ∩ Q ⁻¹' ({b | d < (m b P).toReal} ∩ N)) := by
    rw [lintegral_indicator_one hAm, Measure.restrict_apply hAm,
      Set.inter_eq_left.2 (Set.inter_subset_left.trans hPZ)]
  have hrhs : ∫⁻ b, ∫⁻ v, (P ∩ Q ⁻¹' ({b | d < (m b P).toReal} ∩ N)).indicator 1 v ∂(m b) ∂lam =
      ∫⁻ b in ({b | d < (m b P).toReal} ∩ N), m b P ∂lam := by
    simp_rw [lintegral_indicator_one hAm, key]
    rw [lintegral_indicator hWm]
  have hmain : ∫⁻ b in ({b | d < (m b P).toReal} ∩ N), m b P ∂lam ≤
      (c : ℝ≥0∞) * lam ({b | d < (m b P).toReal} ∩ N) := by
    rw [← hrhs, ← hdis _ (measurable_one.indicator hAm), hlhs]
    exact hc _ hWm
  have hlow : ENNReal.ofReal d * lam ({b | d < (m b P).toReal} ∩ N) ≤
      ∫⁻ b in ({b | d < (m b P).toReal} ∩ N), m b P ∂lam := by
    calc ENNReal.ofReal d * lam ({b | d < (m b P).toReal} ∩ N)
        = ∫⁻ _ in ({b | d < (m b P).toReal} ∩ N), ENNReal.ofReal d ∂lam :=
          (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ b in ({b | d < (m b P).toReal} ∩ N), m b P ∂lam :=
          setLIntegral_mono' hWm (fun b hb => ENNReal.ofReal_le_of_le_toReal hb.1.le)
  have hd0 : 0 ≤ d := (NNReal.coe_nonneg c).trans hcd.le
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top hfinW) (hlow.trans hmain)
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hd0, ENNReal.coe_toReal] at h
  have hLpos : 0 < (lam ({b | d < (m b P).toReal} ∩ N)).toReal := ENNReal.toReal_pos hpos hfinW
  have h' : d ≤ (c : ℝ) := le_of_mul_le_mul_right h hLpos
  linarith

end GlobalTheory.CompanionTheory.WeilSiegel.FibreMass
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLatticePointsInSiegelSetBoundStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open Matrix
open scoped Pointwise
open GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RegInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_lattice_points_in_siegel_set_bound : ∀ (D : D7) (V : HSp D) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E),
    IsWittFrame D.sp.cm.sig V.gram X Y → ∀ c : ℝ, 0 < c → ∀ C : Set (GA D V), IsCompact C →
    ∃ (A : ℕ) (B : ℝ), ∀ t ∈ cone r c, ∀ a : GA D V, IsTorusElt D.sp.cm.sig V.gram X Y t a →
      {δ : GF V | a⁻¹ * rat V δ * a ∈ C}.Finite ∧
      (({δ : GF V | a⁻¹ * rat V δ * a ∈ C}.ncard : ℕ) : ℝ) ≤ B * (∏ i, max (t i) 1) ^ A := by
  first | exact @GlobalTheory.CompanionTheory.TorusCount.torus_count | exact GlobalTheory.CompanionTheory.TorusCount.torus_count | (intros; apply GlobalTheory.CompanionTheory.TorusCount.torus_count <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianFamilyAnisotropicJointStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.ParCocompact
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_family_anisotropic_joint : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ ξ : Fin n → E, (∀ j, hE σ (hermFam σ J X Y j) ξ ξ = 0) → ξ = 0 := by
  first | exact @GlobalTheory.CompanionTheory.ParCocompact.hermFam_nondeg | exact GlobalTheory.CompanionTheory.ParCocompact.hermFam_nondeg | (intros; apply GlobalTheory.CompanionTheory.ParCocompact.hermFam_nondeg <;> assumption)
end

