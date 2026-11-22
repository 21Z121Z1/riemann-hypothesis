import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaBdRPlusSurjectiveKerUnitsEquivariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0059
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0304
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFundamentalDomainIUnion
section
noncomputable section

open MeasureTheory
open scoped ENNReal Pointwise Matrix

namespace GlobalTheory.ThetaUnfold

section Abstract

variable {G ι : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]

theorem lintegral_unfold (μ : Measure G) [μ.IsMulLeftInvariant] (Γ Δ : Subgroup G) [Countable Γ]
    (r : ι → G) (e : Δ × ι ≃ Γ) (he : ∀ p, (e p : G) = p.1 * r p.2)
    {𝓕 𝓕' : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (h𝓕' : IsFundamentalDomain Δ 𝓕' μ)
    (f : G → ℝ≥0∞) (hf : ∀ δ ∈ Δ, ∀ g, f (δ * g) = f g) (hm : AEMeasurable f μ) :
    ∫⁻ g in 𝓕, ∑' i, f (r i * g) ∂μ = ∫⁻ g in 𝓕', f g ∂μ := by
  haveI : Countable ι := Function.Injective.countable (f := fun i => e (1, i))
    fun i j h => by simpa using congrArg Prod.snd (e.injective h)
  haveI : Countable Δ := Function.Injective.countable (f := fun δ => e (δ, (e.symm 1).2))
    fun i j h => by simpa using congrArg Prod.fst (e.injective h)
  haveI : MeasurableConstSMul Γ G := ⟨fun γ => measurable_const_mul (γ : G)⟩
  haveI : MeasurableConstSMul Δ G := ⟨fun γ => measurable_const_mul (γ : G)⟩
  haveI : SMulInvariantMeasure Γ G μ := ⟨fun γ s _ => measure_preimage_mul μ (γ : G) s⟩
  haveI : SMulInvariantMeasure Δ G μ := ⟨fun γ s _ => measure_preimage_mul μ (γ : G) s⟩
  have hset : ∀ (δ : Δ) (i : ι), (δ • (r i • 𝓕) ∩ 𝓕' : Set G) = 𝓕' ∩ e (δ, i) • 𝓕 := by
    intro δ i
    ext x
    simp only [Set.mem_inter_iff, Set.mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def, smul_eq_mul]
    rw [and_comm]
    refine and_congr_right fun _ => ?_
    rw [he]
    simp [mul_assoc]
  calc ∫⁻ g in 𝓕, ∑' i, f (r i * g) ∂μ = ∑' i, ∫⁻ g in 𝓕, f (r i * g) ∂μ :=
        lintegral_tsum fun i => (hm.comp_quasiMeasurePreserving
          (measurePreserving_mul_left μ (r i)).quasiMeasurePreserving).restrict
    _ = ∑' i, ∫⁻ g in r i • 𝓕, f g ∂μ := by
        refine tsum_congr fun i => ?_
        rw [(measurePreserving_mul_left μ (r i)).setLIntegral_comp_emb
          (measurableEmbedding_mulLeft (r i)) f 𝓕]
        rfl
    _ = ∑' i, ∑' δ : Δ, ∫⁻ g in 𝓕' ∩ e (δ, i) • 𝓕, f g ∂μ := by
        refine tsum_congr fun i => ?_
        rw [h𝓕'.setLIntegral_eq_tsum' f (r i • 𝓕)]
        refine tsum_congr fun δ => ?_
        rw [hset]
        congr 1
        funext g
        exact hf _ (δ⁻¹).2 g
    _ = ∑' p : Δ × ι, ∫⁻ g in 𝓕' ∩ e p • 𝓕, f g ∂μ := by
        rw [ENNReal.tsum_prod', ENNReal.tsum_comm]
    _ = ∑' γ : Γ, ∫⁻ g in 𝓕' ∩ γ • 𝓕, f g ∂μ := e.tsum_eq (fun γ => ∫⁻ g in 𝓕' ∩ γ • 𝓕, f g ∂μ)
    _ = ∫⁻ g in 𝓕', f g ∂μ := (h𝓕.setLIntegral_eq_tsum f 𝓕').symm

theorem isFundamentalDomain_iUnion (μ : Measure G) [μ.IsMulLeftInvariant] (Γ Δ : Subgroup G) [Countable Γ]
    (r : ι → G) (e : Δ × ι ≃ Γ) (he : ∀ p, (e p : G) = p.1 * r p.2)
    {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) : IsFundamentalDomain Δ (⋃ i, r i • 𝓕) μ := by
  haveI : Countable ι := Function.Injective.countable (f := fun i => e (1, i))
    fun i j h => by simpa using congrArg Prod.snd (e.injective h)
  have hset : ∀ (δ : Δ) (i : ι), (δ • (r i • 𝓕) : Set G) = e (δ, i) • 𝓕 := by
    intro δ i
    ext x
    simp only [Set.mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def, smul_eq_mul, Subgroup.coe_inv]
    rw [he]
    simp [mul_assoc]
  refine ⟨.iUnion fun i => h𝓕.nullMeasurableSet.smul (r i), h𝓕.ae_covers.mono ?_, fun δ δ' hδ => ?_⟩
  · rintro x ⟨γ, hγ⟩
    refine ⟨(e.symm γ⁻¹).1⁻¹, Set.mem_iUnion.2 ⟨(e.symm γ⁻¹).2, ?_⟩⟩
    rw [← Set.mem_smul_set_iff_inv_smul_mem, hset, Prod.mk.eta, e.apply_symm_apply,
      Set.mem_smul_set_iff_inv_smul_mem, inv_inv]
    exact hγ
  · simp only [Function.onFun, Set.smul_set_iUnion, hset, AEDisjoint.iUnion_left_iff, AEDisjoint.iUnion_right_iff]
    exact fun i j => h𝓕.aedisjoint fun h => hδ (by simpa using congrArg Prod.fst (e.injective h))

theorem integral_unfold {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (μ : Measure G) [μ.IsMulLeftInvariant] (Γ Δ : Subgroup G) [Countable Γ]
    (r : ι → G) (e : Δ × ι ≃ Γ) (he : ∀ p, (e p : G) = p.1 * r p.2)
    {𝓕 𝓕' : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (h𝓕' : IsFundamentalDomain Δ 𝓕' μ)
    (f : G → V) (hf : ∀ δ ∈ Δ, ∀ g, f (δ * g) = f g) (hm : AEStronglyMeasurable f μ)
    (hfin : ∫⁻ g in 𝓕, ∑' i, ‖f (r i * g)‖ₑ ∂μ ≠ ⊤) :
    (∀ᵐ g ∂μ.restrict 𝓕, Summable fun i => ‖f (r i * g)‖) ∧ IntegrableOn (fun g => ∑' i, f (r i * g)) 𝓕 μ ∧
      IntegrableOn f 𝓕' μ ∧ ∫ g in 𝓕, ∑' i, f (r i * g) ∂μ = ∫ g in 𝓕', f g ∂μ := by
  haveI : Countable ι := Function.Injective.countable (f := fun i => e (1, i))
    fun i j h => by simpa using congrArg Prod.snd (e.injective h)
  haveI : Countable Δ := Function.Injective.countable (f := fun δ => e (δ, (e.symm 1).2))
    fun i j h => by simpa using congrArg Prod.fst (e.injective h)
  haveI : SMulInvariantMeasure Δ G μ := ⟨fun γ s _ => measure_preimage_mul μ (γ : G) s⟩
  have hS := isFundamentalDomain_iUnion μ Γ Δ r e he h𝓕
  have hf' : ∀ (δ : Δ) (g : G), f (δ • g) = f g := fun δ g => hf δ δ.2 g
  have hmi : ∀ i, AEStronglyMeasurable (fun g => f (r i * g)) (μ.restrict 𝓕) := fun i =>
    (hm.comp_quasiMeasurePreserving (measurePreserving_mul_left μ (r i)).quasiMeasurePreserving).restrict
  have hI : IntegrableOn f 𝓕' μ := ⟨hm.restrict, by
    have := lintegral_unfold μ Γ Δ r e he h𝓕 h𝓕' (fun g => ‖f g‖ₑ) (fun δ h g => by rw [hf δ h]) hm.enorm
    exact lt_top_iff_ne_top.2 (this ▸ hfin)⟩
  have hr : ∀ i, (r i • 𝓕 : Set G) = e (1, i) • 𝓕 := fun i => by
    rw [Subgroup.smul_def, he]; simp
  refine ⟨?_, ⟨AEStronglyMeasurable.tsum hmi, ?_⟩, hI, ?_⟩
  · filter_upwards [ae_lt_top' (AEMeasurable.ennreal_tsum fun i => (hmi i).enorm) hfin] with g hg
    have := ENNReal.summable_toReal hg.ne
    simpa using this
  · exact lt_of_le_of_lt (lintegral_mono fun x => enorm_tsum_le_tsum_enorm) hfin.lt_top
  · rw [integral_tsum hmi (by rwa [← lintegral_tsum fun i => (hmi i).enorm]), h𝓕'.setIntegral_eq hS hf',
      integral_iUnion_ae (fun i => h𝓕.nullMeasurableSet.smul (r i))
        (fun i j hij => by
          simp only [Function.onFun, hr]
          exact h𝓕.aedisjoint fun h => hij (by simpa using congrArg Prod.snd (e.injective h)))
        ((h𝓕'.integrableOn_iff hS hf').1 hI)]
    refine tsum_congr fun i => ?_
    exact ((measurePreserving_mul_left μ (r i)).setIntegral_image_emb (measurableEmbedding_mulLeft (r i)) f 𝓕).symm

end Abstract

section Concrete

open GlobalTheory.CuspRep

variable {E : Type} [Field E] {a : ℕ}

theorem exists_vecMul_eq {v ξ : Fin a → E} (hv : v ≠ 0) (hξ : ξ ≠ 0) :
    ∃ γ : GL (Fin a) E, v ᵥ* (γ : Matrix (Fin a) (Fin a) E) = ξ := by
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq
    ((LinearEquiv.toSpanNonzeroSingleton E _ v hv).symm.trans (LinearEquiv.toSpanNonzeroSingleton E _ ξ hξ))
  have h1 := hg ⟨v, Submodule.mem_span_singleton_self v⟩
  rw [← LinearEquiv.toSpanNonzeroSingleton_one E _ v hv, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply, LinearEquiv.toSpanNonzeroSingleton_one,
    LinearEquiv.toSpanNonzeroSingleton_one] at h1
  set A := LinearMap.toMatrix' g.toLinearMap
  set B := LinearMap.toMatrix' g.symm.toLinearMap
  have hAB : A * B = 1 := by rw [← LinearMap.toMatrix'_comp]; simp
  have hBA : B * A = 1 := by rw [← LinearMap.toMatrix'_comp]; simp
  refine ⟨⟨Aᵀ, Bᵀ, by rw [← Matrix.transpose_mul, hBA, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, hAB, Matrix.transpose_one]⟩, ?_⟩
  change v ᵥ* Aᵀ = ξ
  rw [Matrix.vecMul_transpose, LinearMap.toMatrix'_mulVec]
  first | exact h1 | exact h1.symm

variable [NumberField E]

theorem vecMul_ratGL_mul (ξ : Fin a → E) (γ : GL (Fin a) E) (g : GA E a) :
    (algebraMap E (Ad E) ∘ ξ) ᵥ* (ratGL E a γ * g).val = (algebraMap E (Ad E) ∘ (ξ ᵥ* γ.val)) ᵥ* g.val := by
  rw [Units.val_mul, ← Matrix.vecMul_vecMul]
  congr 1
  ext j
  simp [ratGL, Matrix.vecMul, dotProduct, map_sum]

theorem ratGL_injective : Function.Injective (ratGL E a) := fun _ _ h => by
  ext i j
  exact NumberField.AdeleRing.algebraMap_injective _ E
    (congrArg (fun z : GA E a => (z : Matrix (Fin a) (Fin a) (Ad E)) i j) h)

theorem countable_range_ratGL : Countable (ratGL E a).range := by
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin a) (Fin a) E) := inferInstanceAs (Countable (Fin a → Fin a → E))
  haveI : Countable (GL (Fin a) E) := Units.val_injective.countable
  exact (ratGL E a).rangeRestrict_surjective.countable

theorem exists_transversal {v : Fin a → E} (hv : v ≠ 0) {P : Subgroup (GL (Fin a) E)}
    (hP : ∀ γ, γ ∈ P ↔ v ᵥ* γ.val = v) :
    ∃ (γ : {ξ : Fin a → E // ξ ≠ 0} → GL (Fin a) E) (e : P.map (ratGL E a) × {ξ : Fin a → E // ξ ≠ 0} ≃ (ratGL E a).range),
      (∀ ξ, v ᵥ* (γ ξ).val = ξ.1) ∧ ∀ p, (e p : GA E a) = p.1 * ratGL E a (γ p.2) := by
  choose γ hγ using fun ξ : {ξ : Fin a → E // ξ ≠ 0} => exists_vecMul_eq hv ξ.2
  let φ : P.map (ratGL E a) × {ξ : Fin a → E // ξ ≠ 0} → (ratGL E a).range := fun p =>
    ⟨p.1 * ratGL E a (γ p.2), mul_mem (Subgroup.map_le_range _ _ p.1.2) ⟨_, rfl⟩⟩
  refine ⟨γ, Equiv.ofBijective φ ⟨?_, ?_⟩, hγ, fun _ => rfl⟩
  · rintro ⟨⟨_, δ, hδ, rfl⟩, ξ⟩ ⟨⟨_, δ', hδ', rfl⟩, ξ'⟩ h
    have h1 : δ * γ ξ = δ' * γ ξ' := ratGL_injective (by simpa only [map_mul] using congrArg Subtype.val h)
    have h2 : ξ = ξ' := Subtype.ext (by
      have := congrArg (fun x : GL (Fin a) E => v ᵥ* x.val) h1
      simpa only [Units.val_mul, ← Matrix.vecMul_vecMul, (hP _).1 hδ, (hP _).1 hδ', hγ] using this)
    subst h2
    obtain rfl := mul_right_cancel h1
    rfl
  · rintro ⟨_, x, rfl⟩
    have h0 : v ᵥ* x.val ≠ 0 := fun h => hv (by
      have := congrArg (· ᵥ* (x⁻¹).val) h
      simpa only [Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one, Matrix.zero_vecMul] using this)
    have h1 : x * (γ ⟨_, h0⟩)⁻¹ ∈ P := (hP _).2 (by
      have h2 : v ᵥ* (γ ⟨_, h0⟩).val = v ᵥ* x.val := hγ _
      generalize γ ⟨_, h0⟩ = y at h2 ⊢
      rw [Units.val_mul, ← Matrix.vecMul_vecMul, ← h2, Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one])
    refine ⟨⟨⟨_, _, h1, rfl⟩, ⟨_, h0⟩⟩, Subtype.ext ?_⟩
    change ratGL E a _ * ratGL E a _ = _
    rw [← map_mul, inv_mul_cancel_right]

section Stabiliser

variable [MeasurableSpace (GA E a)] [MeasurableMul (GA E a)] (μ : Measure (GA E a)) [μ.IsMulLeftInvariant]
  {v : Fin a → E} (hv : v ≠ 0) {P : Subgroup (GL (Fin a) E)} (hP : ∀ γ, γ ∈ P ↔ v ᵥ* γ.val = v)
  {𝓕 𝓕' : Set (GA E a)} (h𝓕 : IsFundamentalDomain (ratGL E a).range 𝓕 μ)
  (h𝓕' : IsFundamentalDomain (P.map (ratGL E a)) 𝓕' μ)

include hv hP h𝓕 h𝓕'

theorem lintegral_tsum_vecMul (F : GA E a → (Fin a → Ad E) → ℝ≥0∞) (hF : ∀ γ g y, F (ratGL E a γ * g) y = F g y)
    (hm : AEMeasurable (fun g : GA E a => F g ((algebraMap E (Ad E) ∘ v) ᵥ* g.val)) μ) :
    ∫⁻ g in 𝓕, ∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, F g ((algebraMap E (Ad E) ∘ ξ.1) ᵥ* g.val) ∂μ =
      ∫⁻ g in 𝓕', F g ((algebraMap E (Ad E) ∘ v) ᵥ* g.val) ∂μ := by
  haveI := countable_range_ratGL (E := E) (a := a)
  obtain ⟨γ, e, hγ, he⟩ := exists_transversal hv hP
  have := lintegral_unfold μ _ _ (fun ξ => ratGL E a (γ ξ)) e he h𝓕 h𝓕' _
    (by rintro _ ⟨δ, hδ, rfl⟩ g; simp only [vecMul_ratGL_mul, hF, (hP _).1 hδ]) hm
  simpa only [vecMul_ratGL_mul, hF, hγ] using this

theorem integral_tsum_vecMul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (F : GA E a → (Fin a → Ad E) → V) (hF : ∀ γ g y, F (ratGL E a γ * g) y = F g y)
    (hm : AEStronglyMeasurable (fun g : GA E a => F g ((algebraMap E (Ad E) ∘ v) ᵥ* g.val)) μ)
    (hfin : ∫⁻ g in 𝓕, ∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖F g ((algebraMap E (Ad E) ∘ ξ.1) ᵥ* g.val)‖ₑ ∂μ ≠ ⊤) :
    (∀ᵐ g ∂μ.restrict 𝓕, Summable fun ξ : {ξ : Fin a → E // ξ ≠ 0} => ‖F g ((algebraMap E (Ad E) ∘ ξ.1) ᵥ* g.val)‖) ∧
    IntegrableOn (fun g => ∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, F g ((algebraMap E (Ad E) ∘ ξ.1) ᵥ* g.val)) 𝓕 μ ∧
    IntegrableOn (fun g => F g ((algebraMap E (Ad E) ∘ v) ᵥ* g.val)) 𝓕' μ ∧
    ∫ g in 𝓕, ∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, F g ((algebraMap E (Ad E) ∘ ξ.1) ᵥ* g.val) ∂μ =
      ∫ g in 𝓕', F g ((algebraMap E (Ad E) ∘ v) ᵥ* g.val) ∂μ := by
  haveI := countable_range_ratGL (E := E) (a := a)
  obtain ⟨γ, e, hγ, he⟩ := exists_transversal hv hP
  have := integral_unfold μ _ _ (fun ξ => ratGL E a (γ ξ)) e he h𝓕 h𝓕' _
    (by rintro _ ⟨δ, hδ, rfl⟩ g; simp only [vecMul_ratGL_mul, hF, (hP _).1 hδ]) hm
    (by simpa only [vecMul_ratGL_mul, hF, hγ] using hfin)
  simpa only [vecMul_ratGL_mul, hF, hγ] using this

end Stabiliser

theorem continuous_vecMul (y : Fin a → Ad E) : Continuous fun g : GA E a => y ᵥ* g.val :=
  continuous_const.matrix_vecMul Units.continuous_val

end Concrete

end GlobalTheory.ThetaUnfold
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsHodgeTateIffDiagonalAdaptedBasis
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.HTDiag

theorem theta_zero_of_pow_eq {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] (θ : R →+* S)
    {t w v : R} {n m : ℕ} (ht : t ≠ 0) (hθt : θ t = 0) (hv : θ v = 0 → v = 0)
    (h : t ^ n * w = t ^ m * v) (hnm : n ≠ m) : θ w = 0 := by
  rcases Nat.lt_or_gt_of_ne hnm with hlt | hgt
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    have e : t ^ (n + k + 1) = t ^ n * t ^ (k + 1) := by ring
    rw [e, mul_assoc] at h
    have hw : w = t ^ (k + 1) * v := mul_left_cancel₀ (pow_ne_zero n ht) h
    rw [hw, map_mul, map_pow, hθt, zero_pow (Nat.succ_ne_zero k), zero_mul]
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hgt
    have e : t ^ (m + k + 1) = t ^ m * t ^ (k + 1) := by ring
    rw [e, mul_assoc] at h
    have hv' : v = t ^ (k + 1) * w := (mul_left_cancel₀ (pow_ne_zero m ht) h).symm
    have hv0 : v = 0 := hv (by rw [hv', map_mul, map_pow, hθt, zero_pow (Nat.succ_ne_zero k), zero_mul])
    rw [hv0, mul_zero] at h
    have h' : t ^ (k + 1) * w = 0 := (mul_eq_zero.1 h).resolve_left (pow_ne_zero _ ht)
    have hw : w = 0 := (mul_eq_zero.1 h').resolve_left (pow_ne_zero _ ht)
    rw [hw, map_zero]

end GlobalTheory.BKLim.HTDiag

open GlobalTheory.BKLim.HTDiag in

theorem GlobalTheory.BKLim.isHT_iff_diag : ∀ (l : ℕ) [Fact l.Prime] (K K' : FinExt l) (C : Core l), C.InvdR → ∀ (ξ : Ainf l), Ideal.span {ξ} = RingHom.ker (Per.θ l) → ∀ (a : ℕ) (ρ : ↥(GK K) → Matrix (Fin a) (Fin a) (Om l)) (H : Hodge C ξ ρ K') (z : ℂ_[l]) (u : Matrix (Fin a) (Fin a) (ℂ_[l])), K.1 ≤ K'.1 → (u * H.V.map (Per.θD l) = H.V.map (Per.θD l) * Matrix.diagonal (fun i => z ^ ((H.p i : ℤ) - H.q)) ↔ IsHT C ξ ρ z u) := by
  intro l _ K K' C hI ξ hξ a ρ H z u hKK'
  constructor
  · intro hm K'' p q x y hfix hxy
    obtain ⟨hdom, hinj, hF, -⟩ := BdRField.bdR_isField l
    haveI := hdom
    set ι := algebraMap (Per.BdRp l) (Per.BdR l) with hι

    have hxiker : xi C.ε ∈ Ideal.span {ξ} := by
      rw [hξ, C.ker_theta]; exact Ideal.mem_span_singleton_self _
    obtain ⟨c0, hc0⟩ := Ideal.mem_span_singleton'.1 hxiker
    have hXu : IsUnit (ι (aDp l ξ)) := by
      have h1 := TiedUnif.isUnit_xi (core_isEps l C)
      rw [← hc0, map_mul, map_mul] at h1
      exact isUnit_of_mul_isUnit_right h1
    set e := ι (aDp l ξ) with he
    obtain ⟨i0, hie⟩ : ∃ i0, i0 * e = 1 := ⟨_, hXu.val_inv_mul⟩
    have ht0 : aDp l ξ ≠ 0 := by
      intro h0
      rw [he, h0, map_zero, mul_zero] at hie
      exact zero_ne_one (hinj (by rw [map_zero, map_one]; exact hie))

    have hVdet : IsUnit H.V.det := (Matrix.isUnit_iff_isUnit_det _).1 H.unit
    set W := H.V⁻¹ with hW
    have hVW : H.V * W = 1 := Matrix.mul_nonsing_inv _ hVdet
    have hWV : W * H.V = 1 := Matrix.nonsing_inv_mul _ hVdet
    have hWVι : W.map ι * H.V.map ι = 1 := by
      rw [← Matrix.map_mul, hWV, Matrix.map_one _ (map_zero _) (map_one _)]

    set d : Fin a → Per.BdR l := fun k => i0 ^ H.q * e ^ H.p k with hd
    set d' : Fin a → Per.BdR l := fun k => e ^ H.q * i0 ^ H.p k with hd'
    have hdd : ∀ k, d' k * d k = 1 := fun k => by
      calc d' k * d k = (i0 * e) ^ H.q * (i0 * e) ^ H.p k := by simp only [hd, hd']; ring
        _ = 1 := by rw [hie, one_pow, one_pow, one_mul]
    have hQ : H.Q = H.V.map ι * Matrix.diagonal d := by
      ext i k
      rw [Matrix.mul_diagonal, Matrix.map_apply]
      have h := H.Q_eq i k
      simp only [map_mul, map_pow] at h
      rw [← he] at h
      calc H.Q i k = (i0 * e) ^ H.q * H.Q i k := by rw [hie, one_pow, one_mul]
        _ = i0 ^ H.q * (e ^ H.q * H.Q i k) := by ring
        _ = ι (H.V i k) * d k := by rw [h]; simp only [hd]; ring
    set Qi := Matrix.diagonal d' * W.map ι with hQi
    have hQiQ : Qi * H.Q = 1 := by
      rw [hQi, hQ, Matrix.mul_assoc, ← Matrix.mul_assoc (W.map ι), hWVι, Matrix.one_mul,
        Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1; funext k; exact hdd k
    have hQQi : H.Q * Qi = 1 := mul_eq_one_comm.1 hQiQ
    set av := Qi *ᵥ x with hav
    have hxa : x = H.Q *ᵥ av := by rw [hav, Matrix.mulVec_mulVec, hQQi, Matrix.one_mulVec]

    let K3 : FinExt l := ⟨K'.1 ⊔ K''.1, by
      haveI := K'.2; haveI := K''.2; exact IntermediateField.finiteDimensional_sup _ _⟩
    have hmono : ∀ {A B : FinExt l}, A.1 ≤ B.1 → ∀ g, g ∈ GK B → g ∈ GK A := fun h g hg =>
      (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx =>
        (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg x (h hx)
    have h3' : K'.1 ≤ K3.1 := le_sup_left
    have h3'' : K''.1 ≤ K3.1 := le_sup_right
    have h3 : K.1 ≤ K3.1 := hKK'.trans h3'

    have hinv : ∀ g : GQ l, g ∈ GK K3 → ∀ j, Per.σD g (av j) = av j := by
      intro g hg
      let g' : ↥(GK K) := ⟨g, hmono h3 g hg⟩
      have h1 := hfix g' (hmono h3'' g hg)
      have h2 := H.inv g' (hmono h3' g hg)
      have hσx : (fun i => Per.σD (g' : GQ l) (x i)) =
          H.Q.map (Per.σD (g' : GQ l)) *ᵥ (fun k => Per.σD (g' : GQ l) (av k)) := by
        funext i
        rw [hxa]
        exact RingHom.map_mulVec _ _ _ i
      rw [hσx, Matrix.mulVec_mulVec, h2] at h1
      have h4 : av = (fun k => Per.σD (g' : GQ l) (av k)) := by
        calc av = Qi *ᵥ x := hav
          _ = Qi *ᵥ (H.Q *ᵥ (fun k => Per.σD (g' : GQ l) (av k))) := by rw [h1]
          _ = _ := by rw [Matrix.mulVec_mulVec, hQiQ, Matrix.one_mulVec]
      intro j
      exact (congrFun h4 j).symm
    choose c hcK hc using fun j => hI K3 (av j) (fun g hg => hinv g hg j)

    have hWx : ∀ k, e ^ q * (W.map ι *ᵥ x) k = e ^ p * (W.map ι *ᵥ (fun i => ι (y i))) k := by
      have hv : e ^ q • x = e ^ p • (fun i => ι (y i)) := by
        funext i
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [hxy i, map_mul, map_pow]
      intro k
      have := congrFun (congrArg (fun v => W.map ι *ᵥ v) hv) k
      simpa [Matrix.mulVec_smul] using this
    have hD : ∀ k, aDp l ξ ^ (H.q + p) * (W *ᵥ y) k = aDp l ξ ^ (q + H.p k) * C.o (c k) := by
      intro k
      apply hinj
      have hck : ι (C.o (c k)) = av k := hc k
      rw [map_mul, map_mul, map_pow, map_pow, hck, RingHom.map_mulVec]
      have hak : av k = d' k * (W.map ι *ᵥ x) k := by
        rw [hav, hQi, ← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal]
      rw [hak]
      calc e ^ (H.q + p) * (W.map ι *ᵥ (fun i => ι (y i))) k = e ^ H.q * (e ^ p * (W.map ι *ᵥ (fun i => ι (y i))) k) := by ring
        _ = e ^ H.q * (e ^ q * (W.map ι *ᵥ x) k) := by rw [hWx k]
        _ = (i0 * e) ^ H.p k * (e ^ H.q * (e ^ q * (W.map ι *ᵥ x) k)) := by rw [hie, one_pow, one_mul]
        _ = e ^ (q + H.p k) * (d' k * (W.map ι *ᵥ x) k) := by simp only [hd']; ring

    have hθξ : Per.θD l (aDp l ξ) = 0 := by
      rw [(thetaD_props l).2.2.2.1 ξ]
      have : Per.θ l ξ = 0 := RingHom.mem_ker.1 (hξ ▸ Ideal.mem_span_singleton_self ξ)
      rw [this]; rfl
    have hkey : ∀ k, z ^ ((H.p k : ℤ) - H.q) * Per.θD l ((W *ᵥ y) k) =
        z ^ ((p : ℤ) - q) * Per.θD l ((W *ᵥ y) k) := by
      intro k
      by_cases hk : (H.p k : ℤ) - H.q = (p : ℤ) - q
      · rw [hk]
      · have hz : Per.θD l ((W *ᵥ y) k) = 0 := by
          refine theta_zero_of_pow_eq (Per.θD l) ht0 hθξ ?_ (hD k) ?_
          · intro h0
            rw [C.o_sec.th] at h0
            have : c k = 0 := by
              first
                | exact (algebraMap (Om l) ℂ_[l]).injective (by simpa using h0)
                | exact UniformSpace.Completion.coe_injective _ (by simpa using h0)
            rw [this, map_zero]
          · intro hn; apply hk; omega
        rw [hz, mul_zero, mul_zero]

    have hyw : y = H.V *ᵥ (W *ᵥ y) := by rw [Matrix.mulVec_mulVec, hVW, Matrix.one_mulVec]
    have hθy : (fun i => Per.θD l (y i)) = H.V.map (Per.θD l) *ᵥ (fun k => Per.θD l ((W *ᵥ y) k)) := by
      funext i
      conv_lhs => rw [hyw]
      exact RingHom.map_mulVec _ _ _ i
    have hdiag : Matrix.diagonal (fun i => z ^ ((H.p i : ℤ) - H.q)) *ᵥ (fun k => Per.θD l ((W *ᵥ y) k)) =
        z ^ ((p : ℤ) - q) • (fun k => Per.θD l ((W *ᵥ y) k)) := by
      funext k
      rw [Matrix.mulVec_diagonal, hkey k]; rfl
    rw [hθy, Matrix.mulVec_mulVec, hm, ← Matrix.mulVec_mulVec, hdiag, Matrix.mulVec_smul]
  · intro hHT
    ext i j
    have h := hHT K' (H.p j) H.q (fun i => H.Q i j) (fun i => H.V i j) ?_ ?_
    · have := congrFun h i
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
      rw [Matrix.mul_diagonal, Matrix.map_apply, Matrix.mul_apply]
      simp only [Matrix.map_apply]
      rw [this, mul_comm]
    · intro g hg
      funext i
      have := congrFun (congrFun (H.inv g hg) i) j
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
    · intro i; exact H.Q_eq i j
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSemilinearBaseChangeIffIsBaseChange
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

open TensorProduct in

theorem _root_.GlobalTheory.BSP.semiBC_iff_isBaseChange (A B : Type) [CommRing A] [CommRing B]
    [Algebra A B] (M : Type)
    [AddCommGroup M] [Module A M] (N : Type) [AddCommGroup N] [Module B N] [Module A N]
    [IsScalarTower A B N] (u : M →ₛₗ[algebraMap A B] N) (u' : M →ₗ[A] N)
    (h : ∀ x, u' x = u x) : _root_.GlobalTheory.Prism.SemiBC u ↔ IsBaseChange B u' := by
  constructor
  · intro hu
    refine IsBaseChange.of_lift_unique _ fun Q _ _ _ _ g => ?_
    letI : AddCommGroup Q := Module.addCommMonoidToAddCommGroup B
    let v : M →ₛₗ[algebraMap A B] Q :=
      { toFun := g
        map_add' := g.map_add
        map_smul' := fun a x => by simp [algebraMap_smul] }
    obtain ⟨w, hw, hw'⟩ := hu Q v
    refine ⟨w, ?_, fun w₂ hw₂ => hw' w₂ fun x => ?_⟩
    · ext x
      simp [h, hw x, v]
    · rw [← h]
      exact LinearMap.congr_fun hw₂ x
  · intro hb Q _ _ v
    letI : Module A Q := Module.compHom Q (algebraMap A B)
    haveI : IsScalarTower A B Q :=
      ⟨fun a b q => by
        show (a • b) • q = algebraMap A B a • b • q
        rw [Algebra.smul_def, mul_smul]⟩
    let g : M →ₗ[A] Q :=
      { toFun := v
        map_add' := v.map_add
        map_smul' := fun a x => by
          rw [v.map_smulₛₗ]
          rfl }
    refine ⟨hb.lift g, fun x => ?_, fun w hw => hb.algHom_ext _ _ fun x => ?_⟩
    · rw [← h, hb.lift_eq]
      rfl
    · rw [hb.lift_eq, h, hw]
      rfl

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsStablePrismHomComp
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem qmap_comp {l : ℕ} {R : Type} [CommRing R] {B C D : Obj l R} (h : Hom B C) (h₂ : Hom C D) (m : ℕ) :
    qmap (h₂.comp h) m = (qmap h₂ m).comp (qmap h m) :=
  Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)

theorem stable_comp : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B C D : Obj l R) (h : Hom B C)
    (h₂ : Hom C D), Stable h → Stable h₂ → Stable (h₂.comp h) := by
  intro l _ R _ B C D h h₂ s s₂
  refine ⟨fun m => ?_, fun B' k => ?_⟩
  · rw [qmap_comp]
    exact RingHom.Flat.comp (s.flat m) (s₂.flat m)
  · obtain ⟨C', k', h', p⟩ := s.po B' k
    obtain ⟨D', k'', h₂', p₂⟩ := s₂.po C' k'
    refine ⟨D', k'', h₂'.comp h', ⟨?_, fun m => ?_⟩⟩
    · apply Hom.ext'
      have e1 := congrArg Hom.f p.comm
      have e2 := congrArg Hom.f p₂.comm
      change k''.f.comp (h₂.f.comp h.f) = (h₂'.f.comp h'.f).comp k.f
      change k'.f.comp h.f = h'.f.comp k.f at e1
      change k''.f.comp h₂.f = h₂'.f.comp k'.f at e2
      rw [← RingHom.comp_assoc, e2, RingHom.comp_assoc, e1, RingHom.comp_assoc]
    · have := (p.po m).paste_horiz (p₂.po m)
      rw [qmap_comp, qmap_comp, CommRingCat.ofHom_comp, CommRingCat.ofHom_comp]
      exact this

end GlobalTheory.BSP
end

