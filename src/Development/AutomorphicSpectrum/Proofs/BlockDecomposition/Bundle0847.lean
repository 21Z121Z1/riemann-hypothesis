import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0835
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0844
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0843
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0833
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0845
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0834
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0801
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0113
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0788
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0620
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0084
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0051
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0043
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0028
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0026
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0032
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0021
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0760

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PureFunctionThetaSeriesInvariance
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical

namespace GlobalTheory.CompanionTheory.BasePsi

theorem finite_contributing : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ θ : ℝ →+* Ainf F, Continuous θ →
    ∀ (S T : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ) (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (a : (AF F)ˣ),
    Continuous G → HasCompactSupport G → (∀ v ∈ S, Continuous (g v) ∧ HasCompactSupport (g v)) → S ⊆ T →
    (∀ v, v ∉ T → (a : AF F).2 v ∈ v.adicCompletionIntegers F ∧ ((a⁻¹ : (AF F)ˣ) : AF F).2 v ∈ v.adicCompletionIntegers F) →
    ∀ δ : ℝ, 0 < δ →
    {x : F | (∀ v, v ∉ T → algebraMap F (Fv F v) x ∈ v.adicCompletionIntegers F) ∧
      phiA G a (fun _ => θ δ * algebraMap F (Ainf F) x) * ∏ v ∈ T, psiA S g a v (fun _ => algebraMap F (Fv F v) x) ≠ 0}.Finite := by
  intro F _ _ _ θ _ S T G g a _ hGc hg hST ha δ hδ
  obtain ⟨N, hN, hNint⟩ := GlobalTheory.T.bounded_denominators_compact_idele_set F {a} isCompact_singleton S (fun v => tsupport (g v))
    (fun v hv => (hg v hv).2)
  have h1 : ((↑a⁻¹ : AF F)).1 * (↑a : AF F).1 = 1 := congrArg Prod.fst (Units.inv_mul a)
  have h2 : θ δ⁻¹ * θ δ = 1 := by rw [← map_mul, inv_mul_cancel₀ hδ.ne', map_one]
  have hcd : ∀ z : Ainf F, θ δ⁻¹ * ((↑a⁻¹ : AF F)).1 * ((↑a : AF F).1 * (θ δ * z)) = z := by
    intro z
    calc θ δ⁻¹ * ((↑a⁻¹ : AF F)).1 * ((↑a : AF F).1 * (θ δ * z))
        = θ δ⁻¹ * (((↑a⁻¹ : AF F)).1 * (↑a : AF F).1) * θ δ * z := by ring
      _ = z := by rw [h1, mul_one, h2, one_mul]
  have hK : IsCompact ((fun z => θ δ⁻¹ * ((↑a⁻¹ : AF F)).1 * z) '' tsupport G) :=
    hGc.image (continuous_const.mul continuous_id)
  choose C hC using fun w : NumberField.InfinitePlace F =>
    hK.exists_bound_of_continuousOn (f := fun z : NumberField.InfiniteAdeleRing F => z w)
      (continuous_apply w).continuousOn
  refine ((NumberField.Embeddings.finite_of_norm_le F ℂ ((N : ℝ) * ∑ w, ‖C w‖)).image
    (fun y => y / (N : F))).subset ?_
  rintro x ⟨hxT, hne⟩
  have hG0 := left_ne_zero_of_mul hne
  have hpsi : ∀ v ∈ T, psiA S g a v (fun _ => algebraMap F (Fv F v) x) ≠ 0 :=
    fun v hv => Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hne) v hv
  have hS : ∀ v ∈ S, algebraMap F (Fv F v) x * (↑a : AF F).2 v ∈ tsupport (g v) := by
    intro v hv
    have h := hpsi v (hST hv)
    simp only [psiA, if_pos hv] at h
    rw [mul_comm]
    exact subset_tsupport _ h
  have hnS : ∀ v ∉ S, algebraMap F (Fv F v) x * (↑a : AF F).2 v ∈ v.adicCompletionIntegers F := by
    intro v hv
    by_cases hvT : v ∈ T
    · have h := hpsi v hvT
      simp only [psiA, if_neg hv] at h
      rw [mul_comm]
      by_contra hc
      exact h (if_neg hc)
    · exact mul_mem (hxT v hvT) (ha v hvT).1
  obtain ⟨y, hy⟩ := hNint a (Set.mem_singleton a) x hS hnS
  have hN0 : (N : F) ≠ 0 := by exact_mod_cast hN.ne'
  have harch : ∀ w : NumberField.InfinitePlace F, w x ≤ C w := by
    intro w
    have hmem : (↑a : AF F).1 * (θ δ * algebraMap F (Ainf F) x) ∈ tsupport G :=
      subset_tsupport _ hG0
    have hx' : algebraMap F (Ainf F) x ∈ (fun z => θ δ⁻¹ * ((↑a⁻¹ : AF F)).1 * z) '' tsupport G :=
      ⟨_, hmem, hcd _⟩
    have hb := hC w _ hx'
    have hn : ‖(algebraMap F (NumberField.InfiniteAdeleRing F) x) w‖ = w x := by
      rw [NumberField.InfiniteAdeleRing.algebraMap_apply, NumberField.InfinitePlace.Completion.norm_coe]
      simp
    rw [← hn]
    exact hb
  have hφ : ∀ φ : F →+* ℂ, ‖φ x‖ ≤ ∑ w, ‖C w‖ := by
    intro φ
    calc ‖φ x‖ = NumberField.InfinitePlace.mk φ x := (NumberField.InfinitePlace.apply φ x).symm
      _ ≤ C (NumberField.InfinitePlace.mk φ) := harch _
      _ ≤ ‖C (NumberField.InfinitePlace.mk φ)‖ := Real.le_norm_self _
      _ ≤ ∑ w, ‖C w‖ := Finset.single_le_sum (f := fun w => ‖C w‖) (fun w _ => norm_nonneg _)
          (Finset.mem_univ _)
  refine ⟨(N : F) * x, ⟨?_, fun φ => ?_⟩, ?_⟩
  · rw [← hy]
    exact NumberField.RingOfIntegers.isIntegral_coe y
  · rw [map_mul, norm_mul, map_natCast, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left (hφ φ) (Nat.cast_nonneg N)
  · field_simp

end GlobalTheory.CompanionTheory.BasePsi
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PureFunctionTranslateRayUnits
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical

namespace GlobalTheory.CompanionTheory.BasePsi

theorem pure_term : ∀ (F : Type) [Field F] [NumberField F] (θ : ℝ →+* Ainf F) (r : ℝ → (AF F)ˣ), IsRay θ r →
    ∀ (S T : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ) (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (a : (AF F)ˣ), S ⊆ T →
    (∀ v, v ∉ T → (a : AF F).2 v ∈ v.adicCompletionIntegers F ∧ ((a⁻¹ : (AF F)ˣ) : AF F).2 v ∈ v.adicCompletionIntegers F) →
    ∀ (δ : ℝ), 0 < δ → ∀ t : Fˣ,
    PositivityTheory.Rg.Base1.pure S G g (fun v => rv v 0) (pr t * (a * r δ)) =
      if ∀ v, v ∉ T → algebraMap F (Fv F v) (t : F) ∈ v.adicCompletionIntegers F then
        ENNReal.ofReal (phiA G a (fun _ => θ δ * algebraMap F (Ainf F) (t : F)) *
          ∏ v ∈ T, psiA S g a v (fun _ => algebraMap F (Fv F v) (t : F))) else 0 := by
  intro F _ _ θ r hr S T G g a hST hT δ hδ t
  obtain ⟨h1, h2⟩ := hr δ hδ
  have c1 : ((pr t * (a * r δ) : (AF F)ˣ) : AF F).1 = (a : AF F).1 * (θ δ * algebraMap F (Ainf F) (t : F)) := by
    have : ((pr t * (a * r δ) : (AF F)ˣ) : AF F).1 = algebraMap F (Ainf F) (t : F) * ((a : AF F).1 * (r δ : AF F).1) := rfl
    rw [this, h1]; ring
  have c2 : ∀ v, ((pr t * (a * r δ) : (AF F)ˣ) : AF F).2 v = (a : AF F).2 v * algebraMap F (Fv F v) (t : F) := by
    intro v
    have : ((pr t * (a * r δ) : (AF F)ˣ) : AF F).2 v = algebraMap F (Fv F v) (t : F) * ((a : AF F).2 v * (r δ : AF F).2 v) := rfl
    rw [this, h2]
    have h3 : ((1 : FiniteAdeleRing (𝓞 F) F)) v = 1 := rfl
    rw [h3, mul_one, mul_comm]
  have inv : ∀ v, (a : AF F).2 v * ((a⁻¹ : (AF F)ˣ) : AF F).2 v = 1 := by
    intro v
    have : ((a * a⁻¹ : (AF F)ˣ) : AF F).2 v = (a : AF F).2 v * ((a⁻¹ : (AF F)ˣ) : AF F).2 v := rfl
    rw [← this]; simp
  have key : ∀ v, v ∉ T → ((a : AF F).2 v * algebraMap F (Fv F v) (t : F) ∈ v.adicCompletionIntegers F ↔
      algebraMap F (Fv F v) (t : F) ∈ v.adicCompletionIntegers F) := by
    intro v hv
    constructor
    · intro h
      have h' := mul_mem (hT v hv).2 h
      have e : ((a⁻¹ : (AF F)ˣ) : AF F).2 v * ((a : AF F).2 v * algebraMap F (Fv F v) (t : F)) =
          algebraMap F (Fv F v) (t : F) := by
        rw [← mul_assoc, mul_comm (((a⁻¹ : (AF F)ˣ) : AF F).2 v), inv, one_mul]
      rwa [e] at h'
    · exact fun h => mul_mem (hT v hv).1 h
  rw [GlobalTheory.T.pure_adelic_function_formula F S G g (pr t * (a * r δ))]
  simp only [c1, c2]
  by_cases ht : ∀ v, v ∉ T → algebraMap F (Fv F v) (t : F) ∈ v.adicCompletionIntegers F
  · rw [if_pos ht]
    by_cases h : ∀ v, v ∉ S → (a : AF F).2 v * algebraMap F (Fv F v) (t : F) ∈ v.adicCompletionIntegers F
    · rw [if_pos h]
      have hp : ∏ v ∈ S, g v ((a : AF F).2 v * algebraMap F (Fv F v) (t : F)) =
          ∏ v ∈ T, psiA S g a v (fun _ => algebraMap F (Fv F v) (t : F)) := by
        rw [← Finset.prod_subset hST]
        · refine Finset.prod_congr rfl fun v hv => ?_
          simp [psiA, hv]
        · intro v _ hv
          simp [psiA, hv, h v hv]
      rw [hp]
      rfl
    · rw [if_neg h]
      push_neg at h
      obtain ⟨v, hvS, hv⟩ := h
      have hvT : v ∈ T := by
        by_contra hvT
        exact hv ((key v hvT).2 (ht v hvT))
      have hz : ∏ v ∈ T, psiA S g a v (fun _ => algebraMap F (Fv F v) (t : F)) = 0 :=
        Finset.prod_eq_zero hvT (by simp [psiA, hvS, hv])
      rw [hz]
      simp
  · rw [if_neg ht, if_neg]
    intro h
    exact ht fun v hv => (key v hv).1 (h v fun hs => hv (hST hs))

end GlobalTheory.CompanionTheory.BasePsi
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankOneThetaIntegralRayFormula
section
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

namespace GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.UnitBd

def cnt {F : Type} [Field F] [NumberField F] (θ : ℝ →+* Ainf F) (ι : Type) (K : Set (ι → Ainf F)) (ε : ℝ) : ℝ≥0∞ :=
  ∑' _y : {y : ι → F // (∀ v : HeightOneSpectrum (𝓞 F), ∀ i, algebraMap F (Fv F v) (y i) ∈ v.adicCompletionIntegers F) ∧
    (fun i => θ ε * algebraMap F (Ainf F) (y i)) ∈ K}, (1 : ℝ≥0∞)

theorem count : PositivityTheory.Rg.Mass.Equi → ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ θ : ℝ →+* Ainf F, Continuous θ →
    ∀ (li : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf li → (∀ v, IsStdV v (lam v)) →
    ∀ (ι : Type) [Fintype ι] (K : Set (ι → Ainf F)), IsCompact K → ∃ B : ℝ≥0, ∀ᶠ ε : ℝ in 𝓝[>] 0,
      ENNReal.ofReal (ε ^ (Module.finrank ℚ F * Fintype.card ι)) * cnt θ ι K ε ≤ B := by
  intro hEq F _ _ hF θ hθ li lam hli hlam ι _ K hK
  obtain ⟨_, _, _, _, -⟩ := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hF
  have : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI := hli.1
  obtain ⟨f, hf1, -, hfc, hf01⟩ := exists_continuous_one_zero_of_isCompact
    (hK.union (isCompact_singleton (x := (0 : ι → Ainf F)))) isClosed_empty (Set.disjoint_empty _)
  have hL := hEq F hF θ hθ li lam hli hlam ι ∅ (f : (ι → Ainf F) → ℝ) (fun _ _ => 0) f.continuous hfc (by simp)
  simp only [Finset.prod_empty, mul_one] at hL
  set L := ∫ y, f y ∂(Measure.pi fun _ : ι => li) with hLdef
  have hLpos : 0 < L := by
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero f.continuous hfc (fun x => (hf01 x).1)
      (x := 0) ?_
    rw [hf1 (Or.inr rfl)]
    exact one_ne_zero
  refine ⟨Real.toNNReal (L + 1), ?_⟩
  filter_upwards [hL.eventually (lt_mem_nhds (half_lt_self hLpos)), hL.eventually (gt_mem_nhds (lt_add_one L)),
    self_mem_nhdsWithin] with ε h1 h2 h3
  set u : {x : ι → F // ∀ v, v ∉ (∅ : Finset (HeightOneSpectrum (𝓞 F))) → ∀ i, algebraMap F (Fv F v) (x i) ∈ v.adicCompletionIntegers F} → ℝ :=
    fun x => f fun i => θ ε * algebraMap F (Ainf F) (x.1 i) with hu
  have hu0 : ∀ x, 0 ≤ u x := fun x => (hf01 _).1
  have hsum : Summable u := by
    by_contra hns
    have e0 : ∑' x, u x = 0 := tsum_eq_zero_of_not_summable hns
    simp only [hu] at e0
    rw [e0, mul_zero] at h1
    linarith
  have hle : cnt θ ι K ε ≤ ∑' x, ENNReal.ofReal (u x) := by
    have hinj : Function.Injective fun y : {y : ι → F // (∀ v : HeightOneSpectrum (𝓞 F), ∀ i, algebraMap F (Fv F v) (y i) ∈ v.adicCompletionIntegers F) ∧
      (fun i => θ ε * algebraMap F (Ainf F) (y i)) ∈ K} =>
        (⟨y.1, fun v _ i => y.2.1 v i⟩ : {x : ι → F // ∀ v, v ∉ (∅ : Finset (HeightOneSpectrum (𝓞 F))) → ∀ i, algebraMap F (Fv F v) (x i) ∈ v.adicCompletionIntegers F}) :=
      fun y y' e => Subtype.ext (Subtype.mk.inj e)
    refine le_trans (le_of_eq (tsum_congr fun y => ?_)) (ENNReal.tsum_comp_le_tsum_of_injective hinj fun x => ENNReal.ofReal (u x))
    simp only [hu]
    rw [hf1 (Or.inl y.2.2)]
    simp
  rw [← ENNReal.ofReal_tsum_of_nonneg hu0 hsum] at hle
  have hpos : 0 ≤ ε ^ (Module.finrank ℚ F * Fintype.card ι) := pow_nonneg (le_of_lt h3) _
  calc _ ≤ ENNReal.ofReal (ε ^ (Module.finrank ℚ F * Fintype.card ι)) * ENNReal.ofReal (∑' x, u x) := mul_le_mul' le_rfl hle
    _ = ENNReal.ofReal (ε ^ (Module.finrank ℚ F * Fintype.card ι) * ∑' x, u x) := (ENNReal.ofReal_mul hpos).symm
    _ ≤ ENNReal.ofReal (L + 1) := ENNReal.ofReal_le_ofReal (le_of_lt h2)
    _ = _ := rfl

def box (F : Type) [Field F] [NumberField F] (ι : Type) (ρ : ℝ) : Set (ι → Ainf F) :=
  {x | ∀ i w, ‖x i w‖ ≤ ρ}

theorem cnt_anti {F : Type} [Field F] [NumberField F] (hF : IsTotallyReal F) (θ : ℝ →+* Ainf F) (hθ : Continuous θ)
    (r : ℝ → (AF F)ˣ) (hr : IsRay θ r) (ι : Type) (ρ : ℝ) {δ ε : ℝ} (hδ : 0 < δ) (hδε : δ ≤ ε) :
    cnt θ ι (box F ι ρ) ε ≤ cnt θ ι (box F ι ρ) δ := by
  have hn := (GlobalTheory.T.ray_norm_and_module_formula F hF θ hθ r hr).1
  have hm : ∀ y : ι → F, (fun i => θ ε * algebraMap F (Ainf F) (y i)) ∈ box F ι ρ →
      (fun i => θ δ * algebraMap F (Ainf F) (y i)) ∈ box F ι ρ := fun y h i w => by
    have e : ∀ t : ℝ, ‖(θ t * algebraMap F (Ainf F) (y i)) w‖ = |t| * ‖algebraMap F (Ainf F) (y i) w‖ := fun t => by
      change ‖θ t w * algebraMap F (Ainf F) (y i) w‖ = _
      rw [norm_mul, hn]
    have h1 : ‖(θ ε * algebraMap F (Ainf F) (y i)) w‖ ≤ ρ := h i w
    change ‖(θ δ * algebraMap F (Ainf F) (y i)) w‖ ≤ ρ
    rw [e] at h1 ⊢
    rw [abs_of_pos hδ]
    rw [abs_of_pos (hδ.trans_le hδε)] at h1
    exact (mul_le_mul_of_nonneg_right hδε (norm_nonneg _)).trans h1
  have hinj : Function.Injective fun y : {y : ι → F // (∀ v : HeightOneSpectrum (𝓞 F), ∀ i, algebraMap F (Fv F v) (y i) ∈ v.adicCompletionIntegers F) ∧
      (fun i => θ ε * algebraMap F (Ainf F) (y i)) ∈ box F ι ρ} =>
      (⟨y.1, y.2.1, hm y.1 y.2.2⟩ : {y : ι → F // (∀ v : HeightOneSpectrum (𝓞 F), ∀ i, algebraMap F (Fv F v) (y i) ∈ v.adicCompletionIntegers F) ∧
      (fun i => θ δ * algebraMap F (Ainf F) (y i)) ∈ box F ι ρ}) :=
    fun y y' e => Subtype.ext (Subtype.mk.inj e)
  exact ENNReal.tsum_comp_le_tsum_of_injective hinj fun _ => (1 : ℝ≥0∞)

theorem isCompact_box {F : Type} [Field F] [NumberField F] (hF : IsTotallyReal F) (ι : Type) (ρ : ℝ) :
    IsCompact (box F ι ρ) := by
  obtain ⟨_, _, _, _, -⟩ := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hF
  have e : box F ι ρ = Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall 0 ρ := by
    ext x
    exact ⟨fun h i _ w _ => mem_closedBall_zero_iff.2 (h i w),
      fun h i w => mem_closedBall_zero_iff.1 (h i (Set.mem_univ _) w (Set.mem_univ _))⟩
  rw [e]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun w => isCompact_closedBall _ _

theorem Th_le {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (b : Module.Basis (Fin 2) F E)
    (θ : ℝ →+* Ainf F) (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ)
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)) (B0 : ℝ) (hB0 : ∀ x, ‖φ x‖ ≤ B0)
    (N : ℕ) (hN : 0 < N) (ρ ε : ℝ) (y : (AF F ⊗[F] E)ˣ)
    (hbox : ∀ X : Fin 1 → Fin 1 → E, Psi φ A (fun a i => (y : AF F ⊗[F] E) * inclR (AF F) (X a i)) ≠ 0 →
      (∀ (p : Fin 1 × Fin 1 × Fin 2) (v : HeightOneSpectrum (𝓞 F)),
        algebraMap F (Fv F v) ((N : F) * b.repr (X p.1 p.2.1) p.2.2) ∈ v.adicCompletionIntegers F) ∧
      ∀ (p : Fin 1 × Fin 1 × Fin 2) (w : InfinitePlace F),
        ‖(θ ε * algebraMap F (Ainf F) ((N : F) * b.repr (X p.1 p.2.1) p.2.2)) w‖ ≤ ρ) :
    Th φ A y ≤ Real.toNNReal B0 * cnt θ (Fin 1 × Fin 1 × Fin 2) (box F _ ρ) ε := by
  have hN0 : (N : F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  set Y := fun X : Fin 1 → Fin 1 → E => fun p : Fin 1 × Fin 1 × Fin 2 => (N : F) * b.repr (X p.1 p.2.1) p.2.2 with hY
  have hYi : Function.Injective Y := fun X X' e => by
    funext a i
    refine b.repr.injective (Finsupp.ext fun k => ?_)
    have h1 := congrFun e (a, i, k)
    exact mul_left_cancel₀ hN0 h1
  set g : ({X : Fin 1 → Fin 1 → E | X ≠ 0} : Set _) → ℝ≥0∞ :=
    fun X => Psi φ A (fun a i => (y : AF F ⊗[F] E) * inclR (AF F) (X.1 a i)) with hg
  set T : Set ({X : Fin 1 → Fin 1 → E | X ≠ 0} : Set _) := {X | g X ≠ 0} with hTdef
  have hPsi : ∀ Z : Fin 1 → Fin 1 → AF F ⊗[F] E, Psi φ A Z ≤ Real.toNNReal B0 := fun Z => by
    unfold Psi
    refine (Set.indicator_le_self' (fun _ _ => bot_le) _).trans ?_
    rw [ENNReal.ofReal, ENNReal.coe_le_coe]
    exact Real.toNNReal_le_toNNReal ((le_abs_self _).trans (hB0 _))
  have e1 : Th φ A y = ∑' X : T, g X.1 := by
    rw [tsum_subtype T g]
    refine tsum_congr fun X => ?_
    by_cases hX : X ∈ T
    · rw [Set.indicator_of_mem hX]
    · rw [Set.indicator_of_notMem hX]
      exact not_not.1 hX
  rw [e1, cnt, ← ENNReal.tsum_mul_left]
  have hmap : ∀ X : T, (∀ v : HeightOneSpectrum (𝓞 F), ∀ i,
      algebraMap F (Fv F v) (Y X.1.1 i) ∈ v.adicCompletionIntegers F) ∧
        (fun i => θ ε * algebraMap F (Ainf F) (Y X.1.1 i)) ∈ box F _ ρ := fun X => by
    obtain ⟨h2, h3⟩ := hbox X.1.1 X.2
    exact ⟨fun v i => h2 i v, fun i w => h3 i w⟩
  have hinj : Function.Injective fun X : T => (⟨Y X.1.1, hmap X⟩ : {y : Fin 1 × Fin 1 × Fin 2 → F // (∀ v : HeightOneSpectrum (𝓞 F), ∀ i,
      algebraMap F (Fv F v) (y i) ∈ v.adicCompletionIntegers F) ∧
        (fun i => θ ε * algebraMap F (Ainf F) (y i)) ∈ box F _ ρ}) := fun X X' e =>
    Subtype.ext (Subtype.ext (hYi (congrArg Subtype.val e)))
  refine le_trans (ENNReal.tsum_le_tsum fun X => ?_) (ENNReal.tsum_comp_le_tsum_of_injective hinj
    fun _ => (Real.toNNReal B0 : ℝ≥0∞) * 1)
  rw [mul_one]
  exact hPsi _

theorem unit_bound : PositivityTheory.Rg.Mass.Equi → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (J : Matrix (Fin 1) (Fin 1) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (li : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf li → (∀ v, IsStdV v (lam v)) → ∀ θ : ℝ →+* Ainf F, Continuous θ → ∀ r, IsRay θ r → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)), IsTest σ J b S φ A → ∀ K : Set (AF F ⊗[F] E)ˣ, IsCompact K → ∀ ε₁ : ℝ, ∃ C : ℝ≥0, ∀ k ∈ K, ∀ ε : ℝ, 0 < ε → ε ≤ ε₁ → ENNReal.ofReal (ε ^ (2 * Module.finrank ℚ F)) * Th φ A (k * ofF (r ε)) ≤ C := by
  intro hEq F E _ _ _ _ _ σ hcm J hJ d b li lam hli hlam θ hθ r hr S φ A hT K hK ε₁
  obtain ⟨N, ρ, hN, hbox⟩ := GlobalTheory.T.theta_test_function_ray_asymptotic F E σ hcm J hJ d b θ r hr S φ A hT K hK
  have hd : d = 2 := by
    have := Module.finrank_eq_card_basis b
    rw [hcm.2.2.1] at this
    simpa using this.symm
  subst hd
  obtain ⟨B, hB⟩ := count hEq F hcm.1 θ hθ li lam hli hlam (Fin 1 × Fin 1 × Fin 2) (box F _ ρ) (isCompact_box hcm.1 _ ρ)
  obtain ⟨B0, hB0⟩ := hT.2.1.exists_bound_of_continuous hT.1
  have e2 : Module.finrank ℚ F * Fintype.card (Fin 1 × Fin 1 × Fin 2) = 2 * Module.finrank ℚ F := by
    rw [show Fintype.card (Fin 1 × Fin 1 × Fin 2) = 2 from rfl, mul_comm]
  rw [e2] at hB
  set m := 2 * Module.finrank ℚ F with hm
  set c : ℝ → ℝ≥0∞ := cnt θ (Fin 1 × Fin 1 × Fin 2) (box F _ ρ) with hc
  obtain ⟨ε₀, hε₀, hI⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 hB
  have hε₀' : (0 : ℝ) < ε₀ := hε₀
  set ε₂ := ε₀ / 2 with hε₂
  have h2pos : 0 < ε₂ := half_pos hε₀'
  have h2 : ENNReal.ofReal (ε₂ ^ m) * c ε₂ ≤ B := hI ⟨h2pos, half_lt_self hε₀'⟩
  set E2 : ℝ≥0 := Real.toNNReal (ε₂ ^ m) with hE2
  have hE2pos : E2 ≠ 0 := by
    simp only [hE2, ne_eq, Real.toNNReal_eq_zero, not_le]
    exact pow_pos h2pos _
  set D : ℝ≥0 := B + Real.toNNReal (ε₁ ^ m) * (E2⁻¹ * B) with hD
  refine ⟨Real.toNNReal B0 * D, fun k hk ε hε hε1 => ?_⟩
  have hTh := Th_le b θ φ A B0 hB0 N hN ρ ε (k * ofF (r ε)) fun X h => hbox k hk X ε hε h
  have hcD : ENNReal.ofReal (ε ^ m) * c ε ≤ D := by
    by_cases hlt : ε < ε₀
    · have h1 : ENNReal.ofReal (ε ^ m) * c ε ≤ B := hI ⟨hε, hlt⟩
      refine h1.trans ?_
      rw [ENNReal.coe_le_coe, hD]
      exact le_self_add
    · have hle : ε₂ ≤ ε := (half_le_self hε₀'.le).trans (not_lt.1 hlt)
      have h3 : c ε ≤ c ε₂ := cnt_anti hcm.1 θ hθ r hr _ ρ h2pos hle
      have h4 : c ε₂ ≤ ((E2⁻¹ * B : ℝ≥0) : ℝ≥0∞) := by
        have e : c ε₂ = (E2 : ℝ≥0∞)⁻¹ * ((E2 : ℝ≥0∞) * c ε₂) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel (ENNReal.coe_ne_zero.2 hE2pos) ENNReal.coe_ne_top, one_mul]
        rw [e, ENNReal.coe_mul, ENNReal.coe_inv hE2pos]
        exact mul_le_mul' le_rfl h2
      have h5 : ENNReal.ofReal (ε ^ m) ≤ (Real.toNNReal (ε₁ ^ m) : ℝ≥0∞) :=
        ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hε.le hε1 m)
      calc ENNReal.ofReal (ε ^ m) * c ε ≤ (Real.toNNReal (ε₁ ^ m) : ℝ≥0∞) * ((E2⁻¹ * B : ℝ≥0) : ℝ≥0∞) :=
            mul_le_mul' h5 (h3.trans h4)
        _ ≤ D := by
            rw [← ENNReal.coe_mul, ENNReal.coe_le_coe, hD]
            exact le_add_self
  calc ENNReal.ofReal (ε ^ m) * Th φ A (k * ofF (r ε))
      ≤ ENNReal.ofReal (ε ^ m) * ((Real.toNNReal B0 : ℝ≥0∞) * c ε) := mul_le_mul' le_rfl hTh
    _ = (Real.toNNReal B0 : ℝ≥0∞) * (ENNReal.ofReal (ε ^ m) * c ε) := by ring
    _ ≤ (Real.toNNReal B0 : ℝ≥0∞) * D := mul_le_mul' le_rfl hcD
    _ = ((Real.toNNReal B0 * D : ℝ≥0) : ℝ≥0∞) := by rw [ENNReal.coe_mul]

end GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.UnitBd

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalarExtensionFibreIntegral
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Free

theorem compact_finite_block : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (t : F), t ≠ 0 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b) (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b), ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ m m₁ m', IsGramFibFree R σ (blockOne (algebraMap F E t) J) (n + 1) (coordW R b lam (n + 1) (M + 1)) (coordHerm R σ b lam (n + 1)) m → IsGramFib R σ (blockOne (algebraMap F E t) J) 1 (coordW R b lam 1 (M + 1)) (coordHerm R σ b lam 1) m₁ → IsGramFibFree R σ J n (coordW R b lam n M) (coordHerm R σ b lam n) m' → ∀ c : ℝ≥0, (coordK R b lam).map (fun y => inclR R (algebraMap F E t) * y) = c • coordK R b lam → (∀ C : Set (Fin n → Fin M → R ⊗[F] E), IsCompact C → m' (hermOf R σ T hT) C < ⊤) → ∀ C : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E), IsCompact C → m (hermOf R σ _ hT') C < ⊤ := by
  intro F E _ _ _ _ _ σ hcm M J hJ t ht n T hT hT' R _ _ _ _ _ hR d b lam hlam m m₁ m' hm hm₁ hm' c hc hfin C hC
  obtain ⟨b1, b2, -⟩ := GlobalTheory.T.block_one_det_hermitian_gram F E σ hcm M J t
  have hJ' : IsHermND σ (blockOne (algebraMap F E t) J) :=
    ⟨b2 hJ.1, by rw [b1]; exact mul_ne_zero ((map_ne_zero _).2 ht) hJ.2⟩
  have hR' := hR
  obtain ⟨_, _, _, _, -⟩ := hR'
  obtain ⟨_, _, _, _, -, -, -, hB, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm R
  have := hB n M
  have := hB 1 (M + 1)
  have := hB (n + 1) (M + 1)
  obtain ⟨hTG, _, _, _, _, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hcm _ _ hJ' R
  obtain ⟨-, k1, k2⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hcm R d b lam hlam
  have e0 : gramR R σ (blockOne (algebraMap F E t) J) (fun _ : Fin 1 => Fin.cons 1 fun _ => 0) =
      (hermScal R σ (algebraMap F R t) : HermR R σ 1) := by
    funext a a'
    simp only [gramR, hR, HeckeCharacterZeroLocus.SiegelWeilU.hR, hform, JR, blockOne, Fin.sum_univ_succ, hermScal, Fin.cons_zero, Fin.cons_succ,
      map_one, map_zero, one_mul, mul_one, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Matrix.map_apply,
      Matrix.of_apply]
    exact (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).commutes t
  obtain ⟨s, sm, s1, s2⟩ := GlobalTheory.T.rank_one_gram_measurable_section F E σ hcm _ _ hJ' R hR (fun _ : Fin 1 => Fin.cons 1 fun _ => 0) (by
    rw [e0, Matrix.det_unique]
    exact (ht.isUnit.map (algebraMap F R)).map (algebraMap R (R ⊗[F] E)))
  rw [e0] at s1 s2
  have hCm : MeasurableSet C := hC.measurableSet
  obtain ⟨Ψ, -, hΨ, hint⟩ := GlobalTheory.T.scalar_extension_fibre_measure F E σ hcm M J hJ t ht n T hT hT' R hR d b lam hlam m m₁ m' hm hm₁ hm' c hc
    (C.indicator 1) (measurable_one.indicator hCm)
  rw [lintegral_indicator_one hCm] at hint
  have hc' : Continuous (consTup : (Fin n → Fin M → R ⊗[F] E) → _) := by
    refine continuous_pi fun a => continuous_pi fun i => ?_
    refine Fin.cases ?_ (fun a => ?_) a <;> refine Fin.cases ?_ (fun i => ?_) i
    exacts [continuous_const, continuous_const, continuous_const, continuous_apply_apply a i]

  let p : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → (Fin 1 → Fin (M + 1) → R ⊗[F] E) := fun X _ => X 0
  have hpc : Continuous p := continuous_pi fun _ => continuous_apply 0
  have hC₁ : IsCompact (p '' C) := hC.image hpc
  obtain ⟨C', hC', hs⟩ := s2 _ hC₁

  let r : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → (Fin n → Fin M → R ⊗[F] E) := fun Y a i => Y a.succ i.succ
  have hrc : Continuous r := continuous_pi fun a => continuous_pi fun i => continuous_apply_apply a.succ i.succ
  have hD : IsCompact ((fun q : HA R σ (blockOne (algebraMap F E t) J) × (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) =>
      actW R σ _ q.1⁻¹ q.2) '' (C' ×ˢ C)) :=
    (hC'.prod hC).image ((hact (n + 1)).1.comp (continuous_fst.inv.prodMk continuous_snd))
  obtain ⟨K, hK, hKsub⟩ : ∃ K : Set (Fin n → Fin M → R ⊗[F] E), IsCompact K ∧
      ∀ h ∈ C', ∀ X, actW R σ _ h (consTup X) ∈ C → X ∈ K := by
    refine ⟨_, hD.image hrc, fun h hh X hX => ⟨consTup X, ⟨(h, _), ⟨hh, hX⟩, ?_⟩, rfl⟩⟩
    show actW R σ _ h⁻¹ (actW R σ _ h (consTup X)) = consTup X
    rw [← (hact _).2.2.1, inv_mul_cancel, (hact _).2.1]
  have hKf := hfin K hK
  have hfirst : ∀ (h : HA R σ (blockOne (algebraMap F E t) J)) (X : Fin n → Fin M → R ⊗[F] E),
      p (actW R σ _ h (consTup X)) = actW R σ _ h (fun _ : Fin 1 => Fin.cons 1 fun _ => 0) := fun h X => rfl
  have hae : ∀ᵐ y ∂(m₁ (hermScal R σ (algebraMap F R t))),
      gramR R σ (blockOne (algebraMap F E t) J) y = (hermScal R σ (algebraMap F R t) : HermR R σ 1) := by
    refine measure_mono_null ?_ (hm₁.1 (hermScal R σ (algebraMap F R t)))
    intro y hy hy'
    exact hy hy'.1
  have hbound : ∀ᵐ y ∂(m₁ (hermScal R σ (algebraMap F R t))),
      Ψ y ≤ (p '' C).indicator (fun _ => m' (hermOf R σ T hT) K) y := by
    filter_upwards [hae] with y hy
    have hy' := s1 y hy
    have hmeas : Measurable fun X : Fin n → Fin M → R ⊗[F] E => actW R σ _ (s y) (consTup X) :=
      ((hact _).1.comp (continuous_const.prodMk hc')).measurable
    have hΨy : Ψ y = m' (hermOf R σ T hT) {X | actW R σ _ (s y) (consTup X) ∈ C} := by
      have h1 := hΨ (s y)
      rw [hy'] at h1
      rw [h1]
      have h2 : (fun X : Fin n → Fin M → R ⊗[F] E =>
          C.indicator (1 : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞) (actW R σ _ (s y) (consTup X))) =
          {X | actW R σ _ (s y) (consTup X) ∈ C}.indicator 1 := by
        funext X
        simp [Set.indicator]
      rw [h2]
      exact lintegral_indicator_one (hmeas hCm)
    by_cases hyC : y ∈ p '' C
    · rw [Set.indicator_of_mem hyC, hΨy]
      exact measure_mono fun X hX => hKsub _ (hs y hyC hy) X hX
    · have hempty : {X | actW R σ _ (s y) (consTup X) ∈ C} = ∅ := by
        refine Set.eq_empty_of_forall_notMem fun X hX => hyC ⟨_, hX, ?_⟩
        rw [hfirst, hy']
      rw [hΨy, hempty, measure_empty]
      exact bot_le
  have hloc := (GlobalTheory.T.gram_fiber_measure_locallyFinite_and_ne_zero_of_isOpen F E σ hcm _ _ hJ' R hR 1 _ _ _ (k1 1 (M + 1)) (k2 1) hm₁
    (hermScal R σ (algebraMap F R t))).1
  have hΨf : ∫⁻ y, Ψ y ∂(m₁ (hermScal R σ (algebraMap F R t))) < ⊤ := by
    refine (lintegral_mono_ae hbound).trans_lt ?_
    rw [lintegral_indicator_const hC₁.measurableSet]
    exact ENNReal.mul_lt_top hKf hC₁.measure_lt_top
  rw [hint]
  exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) hΨf

end GlobalTheory.CompanionTheory.WeilSiegel.Free
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilFreeZeroRankOneOfThreeLeStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelWeilFree_zero_rank_one_of_three_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (h₀ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b), (framesE σ J (0 : Matrix (Fin 1) (Fin 1) E)).Nonempty → SWFree σ J (0 : Matrix (Fin 1) (Fin 1) E) h₀ := by
  first | exact @GlobalTheory.CompanionTheory.SW.OneZero.one_vector_zero | exact GlobalTheory.CompanionTheory.SW.OneZero.one_vector_zero | (intros; apply GlobalTheory.CompanionTheory.SW.OneZero.one_vector_zero <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitPlaceRankCutOfAlternativeStatement
section
open GlobalTheory.CompanionTheory.Jp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_place_rank_cut_of_alternative : GlobalTheory.CompanionTheory.Jp.JpCondition → GlobalTheory.CompanionTheory.Jp.SplitPlaceRankCutEigenvalue := by
  first | exact @GlobalTheory.CompanionTheory.Jp.split_place_rank_cut_of_local_computation | exact GlobalTheory.CompanionTheory.Jp.split_place_rank_cut_of_local_computation | (intros; apply GlobalTheory.CompanionTheory.Jp.split_place_rank_cut_of_local_computation <;> assumption)
end

