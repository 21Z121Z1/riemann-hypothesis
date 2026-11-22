import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0936
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0957
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0607
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0946
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0042
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0322
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolValueAtIntegralOfExpansion
section
noncomputable section

namespace GlobalTheory.DefDoubling

open MeasureTheory Filter Topology Set GlobalTheory.Eis GlobalTheory.Cont GlobalTheory.Doubling GlobalTheory.AutomorphicL2Unitary
open scoped ENNReal NNReal

section Unfold

variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] {Γ : Subgroup G} [Countable Γ]
  {μ : Measure G} [μ.IsMulLeftInvariant] {𝓕 : Set G}

theorem lintegral_tsum_eq (h : IsFundamentalDomain Γ 𝓕 μ) {f : G → ℝ≥0∞} (hf : AEMeasurable f μ) :
    ∫⁻ x in 𝓕, ∑' γ : Γ, f (γ * x) ∂μ = ∫⁻ x, f x ∂μ := by
  rw [h.lintegral_eq_tsum'' f, lintegral_tsum (f := fun (γ : Γ) x => f (γ * x)) fun γ : Γ =>
    (hf.comp_quasiMeasurePreserving (measurePreserving_mul_left μ (γ : G)).quasiMeasurePreserving).restrict]
  rfl

theorem integral_tsum_eq (h : IsFundamentalDomain Γ 𝓕 μ) {f : G → ℂ} (hf : Integrable f μ) :
    IntegrableOn (fun x => ∑' γ : Γ, f (γ * x)) 𝓕 μ ∧ ∫ x in 𝓕, ∑' γ : Γ, f (γ * x) ∂μ = ∫ x, f x ∂μ := by
  have hm : ∀ γ : Γ, AEStronglyMeasurable (fun x => f (γ * x)) (μ.restrict 𝓕) := fun γ =>
    (hf.1.comp_quasiMeasurePreserving (measurePreserving_mul_left μ (γ : G)).quasiMeasurePreserving).restrict
  have hl : ∑' γ : Γ, ∫⁻ x in 𝓕, ‖f (γ * x)‖ₑ ∂μ = ∫⁻ x, ‖f x‖ₑ ∂μ := by
    rw [← lintegral_tsum fun γ => (hm γ).enorm, lintegral_tsum_eq h hf.1.enorm]
  refine ⟨⟨AEStronglyMeasurable.tsum hm, ?_⟩, ?_⟩
  · refine lt_of_le_of_lt (lintegral_mono fun x => enorm_tsum_le_tsum_enorm) ?_
    rw [lintegral_tsum fun γ => (hm γ).enorm, hl]
    exact hf.2
  · rw [integral_tsum hm (hl ▸ hf.2.ne), h.integral_eq_tsum'' f hf]
    rfl

end Unfold

section Dbl

variable {G G₂ : Type} [Group G] [Group G₂] (i : G × G →* G₂) {P Γ₂ : Subgroup G₂} {Γ : Subgroup G} {r : Γ → Γ₂}

theorem cosetSum_io {Φ : G₂ → ℂ} (hΦ : LeftInv (P ⊓ Γ₂) Φ) (hri : ∀ δ, (r δ : G₂) = i (1, δ))
    (hr : Function.Bijective fun δ => mk (P.subgroupOf Γ₂) (r δ)) (h x : G) :
    cosetSum P Γ₂ Φ (i (h, x)) = ∑' δ : Γ, Φ (i (h, δ * x)) ∧
      (CosetConv P Γ₂ Φ (i (h, x)) ↔ Summable fun δ : Γ => ‖Φ (i (h, δ * x))‖) := by
  have e : ∀ δ : Γ, (r δ : G₂) * i (h, x) = i (h, δ * x) := fun δ => by
    rw [hri, ← map_mul, Prod.mk_mul_mk, one_mul]
  refine ⟨(cosetSum_eq_tsum hΦ hr _).trans (tsum_congr fun δ => by rw [e]), ?_⟩
  rw [cosetConv_iff hΦ hr]
  exact summable_congr fun δ => by rw [e]

variable [MeasurableSpace G] [MeasurableMul G] [Countable Γ] {μ : Measure G} [μ.IsMulLeftInvariant] {𝓕 : Set G}

theorem unfold_core (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) {Φ : G₂ → ℂ} (hΦ : LeftInv (P ⊓ Γ₂) Φ)
    (hri : ∀ δ, (r δ : G₂) = i (1, δ)) (hr : Function.Bijective fun δ => mk (P.subgroupOf Γ₂) (r δ))
    {c : G → ℂ} (hlaw : ∀ h y, Φ (i (h, h) * y) = c h * Φ y) {w : G → ℂ} (hw : ∀ x y, w (x * y) = w x * w y)
    (hwΓ : ∀ γ ∈ Γ, w γ = 1) (hw1 : ∀ x, ‖w x‖ = 1) (hwm : AEStronglyMeasurable w μ)
    (hm : ∀ h, AEStronglyMeasurable (fun x => Φ (i (h, x))) μ) (h : G)
    (hfin : ∫⁻ x in 𝓕, ∑' δ : Γ, ‖Φ (i (h, δ * x))‖ₑ ∂μ ≠ ⊤) :
    Integrable (fun g => Φ (i (1, g)) * w g) μ ∧ IntegrableOn (fun x => cosetSum P Γ₂ Φ (i (h, x)) * w x) 𝓕 μ ∧
      ∫ x in 𝓕, cosetSum P Γ₂ Φ (i (h, x)) * w x ∂μ = c h * w h * ∫ g, Φ (i (1, g)) * w g ∂μ := by
  set F : G → ℂ := fun x => Φ (i (h, x)) * w x with hF
  have hFm : AEStronglyMeasurable F μ := (hm h).mul hwm
  have hFn : ∀ x, ‖F x‖ₑ = ‖Φ (i (h, x))‖ₑ := fun x => by
    rw [hF, enorm_mul, ← ofReal_norm_eq_enorm (w x), hw1, ENNReal.ofReal_one, mul_one]
  have hFi : Integrable F μ := by
    refine ⟨hFm, ?_⟩
    rw [HasFiniteIntegral, lintegral_congr (fun x => hFn x), ← lintegral_tsum_eq h𝓕 (hm h).enorm]
    exact lt_top_iff_ne_top.2 hfin
  have hδ : ∀ x, ∑' δ : Γ, F (δ * x) = cosetSum P Γ₂ Φ (i (h, x)) * w x := fun x => by
    rw [(cosetSum_io i hΦ hri hr h x).1, ← tsum_mul_right]
    exact tsum_congr fun δ => by
      show Φ _ * w (δ * x) = _
      rw [hw, hwΓ _ δ.2, one_mul]
  have hsh : ∀ x, F (h * x) = c h * w h * (Φ (i (1, x)) * w x) := fun x => by
    have : i (h, h * x) = i (h, h) * i (1, x) := by rw [← map_mul, Prod.mk_mul_mk, mul_one]
    rw [hF]; simp only [this, hlaw, hw]; ring
  have hsh' : ∀ x, Φ (i (1, x)) * w x = c h⁻¹ * w h⁻¹ * F (h * x) := fun x => by
    have : i (1, x) = i (h⁻¹, h⁻¹) * i (h, h * x) := by
      rw [← map_mul, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel_left]
    have hx : w x = w h⁻¹ * w (h * x) := by rw [← hw, inv_mul_cancel_left]
    rw [hF]; simp only [this, hlaw, hx]; ring
  have hFh : Integrable (fun x => F (h * x)) μ := hFi.comp_mul_left h
  obtain ⟨h1, h2⟩ := integral_tsum_eq h𝓕 hFi
  refine ⟨(hFh.const_mul (c h⁻¹ * w h⁻¹)).congr (Eventually.of_forall fun x => (hsh' x).symm), ?_, ?_⟩
  · exact Integrable.congr h1 (Eventually.of_forall hδ)
  · rw [← setIntegral_congr_fun₀ ?_ (fun x _ => hδ x), h2, ← integral_mul_left_eq_self F h]
    · simp only [hsh]; rw [integral_const_mul]
    · exact h𝓕.nullMeasurableSet

end Dbl

section Passage

variable {s₀ : ℂ}

theorem holValueAt_sum {ι : Type} (T : Finset ι) {f : ι → ℂ → ℂ} {z : ι → ℂ}
    (h : ∀ j ∈ T, HolValueAt (f j) s₀ (z j)) : HolValueAt (fun s => ∑ j ∈ T, f j s) s₀ (∑ j ∈ T, z j) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using holValueAt_const 0 s₀
  | insert a T ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem holValueAt_integral_of_expansion {X ι : Type} [MeasurableSpace X] {ν : Measure X} [Fintype ι]
    {Φ : ℂ → X → ℂ} {Ψ : X → ℂ} {c : ι → X → ℂ} {v : ι → ℂ → ℂ} {w : ι → ℂ} {σ : ℝ}
    (hc : ∀ j, Integrable (c j) ν) (hexp : ∀ s : ℂ, σ < s.re → ∀ x, Φ s x = ∑ j, c j x * v j s)
    (hv : ∀ j, HolValueAt (v j) s₀ (w j)) (hΨ : ∀ x, HolValueAt (fun s => Φ s x) s₀ (Ψ x)) :
    (∀ x, Ψ x = ∑ j, c j x * w j) ∧ Integrable Ψ ν ∧ HolValueAt (fun s => ∫ x, Φ s x ∂ν) s₀ (∫ x, Ψ x ∂ν) := by
  have hΨe : ∀ x, Ψ x = ∑ j, c j x * w j := fun x =>
    (hΨ x).unique ((holValueAt_sum Finset.univ fun j _ => (holValueAt_const (c j x) s₀).mul (hv j)).congr
      ⟨σ, fun s hs => (hexp s hs x).symm⟩)
  have hΨi : Integrable Ψ ν := by
    rw [funext hΨe]
    exact integrable_finset_sum _ fun j _ => (hc j).mul_const (w j)
  refine ⟨hΨe, hΨi, ?_⟩
  have e1 : ∫ x, Ψ x ∂ν = ∑ j, (∫ x, c j x ∂ν) * w j := by
    rw [funext hΨe, integral_finset_sum _ fun j _ => (hc j).mul_const (w j)]
    exact Finset.sum_congr rfl fun j _ => integral_mul_const _ _
  rw [e1]
  refine (holValueAt_sum Finset.univ fun j _ => (holValueAt_const (∫ x, c j x ∂ν) s₀).mul (hv j)).congr
    ⟨σ, fun s hs => ?_⟩
  simp only
  rw [integral_congr_ae (Eventually.of_forall (hexp s hs)),
    integral_finset_sum _ fun j _ => (hc j).mul_const (v j s)]
  exact Finset.sum_congr rfl fun j _ => (integral_mul_const _ _).symm

end Passage

section Expansion

variable {G₂ : Type} [Group G₂] {P Γ₂ K : Subgroup G₂} {ι : Type} [Fintype ι] {kk : ι → G₂} {c : ι → G₂ → ℂ}

theorem flatSec_expansion {δ : P →* ℝ≥0} (hI : IsIwasawa δ K) {f : G₂ → ℂ} (hkk : ∀ j, kk j ∈ K)
    (hexp : ∀ g, ∀ k ∈ K, f (g * k) = ∑ j, c j k * f (g * kk j)) (s₀ s : ℂ) (g : G₂) {k : G₂} (hk : k ∈ K) :
    flatSec δ K f s₀ s (g * k) = ∑ j, c j k * flatSec δ K f s₀ s (g * kk j) := by
  simp only [flatSec, hI.iwAbs_right g hk, hI.iwAbs_right g (hkk _), hexp g k hk, Finset.sum_mul, mul_assoc]

theorem cosetSum_expansion {Φ : G₂ → ℂ} (hexp : ∀ g, ∀ k ∈ K, Φ (g * k) = ∑ j, c j k * Φ (g * kk j)) (y : G₂)
    (hconv : ∀ j, CosetConv P Γ₂ Φ (y * kk j)) {k : G₂} (hk : k ∈ K) :
    cosetSum P Γ₂ Φ (y * k) = ∑ j, c j k * cosetSum P Γ₂ Φ (y * kk j) := by
  have e : ∀ q, term P Γ₂ Φ (y * k) q = ∑ j, c j k * term P Γ₂ Φ (y * kk j) q := fun q => by
    simp only [term, ← mul_assoc]
    exact hexp _ k hk
  rw [cosetSum, tsum_congr e, Summable.tsum_finsetSum fun j _ => ((hconv j).of_norm).mul_left (c j k)]
  exact Finset.sum_congr rfl fun j _ => tsum_mul_left

theorem cosetSum_norm_expansion {Φ : G₂ → ℂ} (hexp : ∀ g, ∀ k ∈ K, Φ (g * k) = ∑ j, c j k * Φ (g * kk j))
    (y : G₂) {k : G₂} (hk : k ∈ K) :
    ∑' q, ‖term P Γ₂ Φ (y * k) q‖ₑ ≤ ∑ j, ‖c j k‖ₑ * ∑' q, ‖term P Γ₂ Φ (y * kk j) q‖ₑ := by
  have e : ∀ q, ‖term P Γ₂ Φ (y * k) q‖ₑ ≤ ∑ j, ‖c j k‖ₑ * ‖term P Γ₂ Φ (y * kk j) q‖ₑ := fun q => by
    simp only [term, ← mul_assoc]
    rw [hexp _ k hk]
    refine (enorm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => (enorm_mul _ _).le)
  refine (ENNReal.tsum_le_tsum e).trans ?_
  rw [Summable.tsum_finsetSum fun j _ => ENNReal.summable]
  exact le_of_eq (Finset.sum_congr rfl fun j _ => ENNReal.tsum_mul_left)

end Expansion

section Cover

theorem measure_le_of_cover {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] {Γ : Subgroup G} [Countable Γ]
    {μ : Measure G} [μ.IsMulLeftInvariant] {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) {C : Set G}
    (hcov : ∀ x, ∃ γ : Γ, (γ : G) * x ∈ C) : μ 𝓕 ≤ μ C := by
  rw [h𝓕.measure_eq_tsum C]
  refine le_trans (measure_mono fun x hx => ?_) (measure_iUnion_le _)
  obtain ⟨γ, hγ⟩ := hcov x
  exact mem_iUnion.2 ⟨γ⁻¹, Set.mem_smul_set_iff_inv_smul_mem.2 (by simpa [Subgroup.smul_def] using hγ), hx⟩

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  {Γ K : Subgroup G} [Countable Γ]

theorem measure_lt_top_of_cover {μ : Measure G} [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ] {𝓕 : Set G}
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (hKc : IsCompact (K : Set G)) (A : Finset G)
    (hcov : ∀ x, ∃ a ∈ A, ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k) : μ 𝓕 < ⊤ := by
  refine lt_of_le_of_lt (measure_le_of_cover h𝓕 (C := ⋃ a ∈ A, (a * ·) '' (K : Set G)) fun x => ?_)
    ((A.isCompact_biUnion fun a _ => hKc.image (continuous_mul_left a)).measure_lt_top)
  obtain ⟨a, ha, γ, hγ, k, hk, rfl⟩ := hcov x
  exact ⟨⟨γ⁻¹, inv_mem hγ⟩, mem_biUnion ha ⟨k, hk, by simp [mul_assoc]⟩⟩

open Classical in

theorem exists_coeff (hK : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) (A : Finset G)
    (hcov : ∀ x, ∃ a ∈ A, ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k) {ι : Type} [Fintype ι] (c : ι → G → ℂ)
    (hc : ∀ j, Continuous (c j)) :
    ∃ C : G → ι → G → ℂ, (∀ a j, Measurable (C a j)) ∧ (∃ M : ℝ, ∀ a j x, ‖C a j x‖ ≤ M) ∧
      ∀ x, ∃ a ∈ A, ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k ∧ ∀ a' j, C a' j x = if a' = a then c j k else 0 := by
  classical
  haveI : Nonempty (Γ × A) := by
    obtain ⟨a, ha, γ, hγ, -⟩ := hcov 1
    exact ⟨(⟨γ, hγ⟩, ⟨a, ha⟩)⟩
  obtain ⟨e, he⟩ := exists_surjective_nat (Γ × A)
  set y : ℕ → G → G := fun n x => ((e n).2 : G)⁻¹ * ((e n).1 : G)⁻¹ * x with hy
  have hyc : ∀ n, Continuous (y n) := fun n => continuous_const.mul continuous_id
  have hex : ∀ x, ∃ n, y n x ∈ K := fun x => by
    obtain ⟨a, ha, γ, hγ, k, hk, rfl⟩ := hcov x
    obtain ⟨n, hn⟩ := he (⟨γ, hγ⟩, ⟨a, ha⟩)
    exact ⟨n, by simpa [hy, hn, mul_assoc] using hk⟩
  have hM : ∀ j, ∃ M, ∀ x ∈ K, ‖c j x‖ ≤ M := fun j => hKc.exists_bound_of_continuousOn (hc j).continuousOn
  choose M hM using hM
  refine ⟨fun a' j x => if a' = ((e (Nat.find (hex x))).2 : G) then c j (y (Nat.find (hex x)) x) else 0,
    fun a' j => ?_, ⟨∑ j, |M j|, fun a' j x => ?_⟩, fun x => ?_⟩
  · refine Measurable.find (f := fun n x => if a' = ((e n).2 : G) then c j (y n x) else 0)
      (p := fun n x => y n x ∈ K) (fun n => ?_) (fun n => (hK.preimage (hyc n)).measurableSet) hex
    by_cases h : a' = ((e n).2 : G)
    · simp only [h, ite_true]; exact ((hc j).comp (hyc n)).measurable
    · simpa [h] using measurable_const
  · dsimp only
    split_ifs
    · exact (hM j _ (Nat.find_spec (hex x))).trans ((le_abs_self _).trans
        (Finset.single_le_sum (f := fun j => |M j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)))
    · rw [norm_zero]; exact Finset.sum_nonneg fun j _ => abs_nonneg _
  · refine ⟨((e (Nat.find (hex x))).2 : G), (e (Nat.find (hex x))).2.2, ((e (Nat.find (hex x))).1 : G),
      (e (Nat.find (hex x))).1.2, y (Nat.find (hex x)) x, Nat.find_spec (hex x), by simp [hy, mul_assoc], fun a' j => rfl⟩

end Cover

end GlobalTheory.DefDoubling
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousComponentInRangeEmbedding
section
open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair

namespace GlobalTheory.CharPair.GradR

theorem mR_isHomogeneous (P Q R : ℕ) (a : Fin P) (b : Fin Q) : (mR P Q R a b).IsHomogeneous 2 := by
  unfold mR
  exact IsHomogeneous.sum _ _ _ fun c _ => (isHomogeneous_X ℂ _).mul (isHomogeneous_X ℂ _)

theorem detR_isHomogeneous (P Q R : ℕ) (h : P ≤ R) : (detR P Q R h).IsHomogeneous P := by
  unfold detR
  rw [Matrix.det_apply']
  refine IsHomogeneous.sum _ _ _ fun σ _ => ?_
  have h1 : (∏ i : Fin P, (Matrix.of fun a c : Fin P =>
      (X (Sum.inl a, Sum.inl (Fin.castLE h c)) : Pol P Q R 0)) (σ i) i).IsHomogeneous (∑ _i : Fin P, 1) :=
    IsHomogeneous.prod _ _ _ fun i _ => isHomogeneous_X ℂ _
  have h0 : (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : Pol P Q R 0).IsHomogeneous 0 := by
    have := isHomogeneous_C (Ix P Q × Ix R 0) (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ)
    rwa [map_intCast] at this
  simpa using h0.mul h1

theorem embR_isHomogeneous (P Q R : ℕ) (h : P ≤ R) (k : ℕ) {G : Mdl P Q} {m : ℕ} (hG : G.IsHomogeneous m) :
    (embR P Q R h k G).IsHomogeneous (2 * m + P * k) :=
  (hG.aeval _ fun ab => mR_isHomogeneous P Q R ab.1 ab.2).mul ((detR_isHomogeneous P Q R h).pow k)

theorem homogeneousComponent_embR_mem (P Q R : ℕ) (h : P ≤ R) (k : ℕ) (G : Mdl P Q) (n : ℕ) :
    homogeneousComponent n (embR P Q R h k G) ∈ LinearMap.range (embR P Q R h k) := by
  rw [← sum_homogeneousComponent G, map_sum, map_sum]
  refine Submodule.sum_mem _ fun m _ => ?_
  rw [homogeneousComponent_of_mem (embR_isHomogeneous P Q R h k (homogeneousComponent_isHomogeneous m G))]
  split_ifs
  · exact LinearMap.mem_range_self _ _
  · exact Submodule.zero_mem _

end GlobalTheory.CharPair.GradR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousFormVanishingCombinationChartIndep
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

theorem GlobalTheory.HomFixUniv.formVanish_chart_indep : ∀ (Rg : Type) [CommRing Rg] (A₀ T X : Scheme.{0}) (N : LB A₀) (mA mB : ℕ) (a : Fin mA → LB.Sec N) (φ : X ⟶ A₀) (p : X ⟶ T) (t : T ⟶ Sp Rg) (c : Fin mA → Fin mB → Γ(T, ⊤)) (d : ℕ) (F : MvPolynomial (Fin mB) Rg), F.IsHomogeneous d → ∀ (z : X) (q q' : N.ι), φ z ∈ N.U q → φ z ∈ N.U q' → (MvPolynomial.eval₂Hom (gc (p ≫ t) z) (comb a φ p c z q) F = 0 ↔ MvPolynomial.eval₂Hom (gc (p ≫ t) z) (comb a φ p c z q') F = 0) := by
  intro Rg _ A₀ T X N mA mB a φ p t c d F hF z q q' hq hq'
  have hV : φ z ∈ N.U q ⊓ N.U q' := ⟨hq, hq'⟩
  have hsec : ∀ i, gs φ z (N.U q) ((a i).f q) =
      (gm φ z (N.U q ⊓ N.U q') (N.g q q')).val * gs φ z (N.U q') ((a i).f q') := by
    intro i
    rw [← gs_res φ z (inf_le_left : N.U q ⊓ N.U q' ≤ N.U q) hV, (a i).compat q q', gs_mul φ z _ hV,
      gs_unit φ z _ hV, gs_res φ z (inf_le_right : N.U q ⊓ N.U q' ≤ N.U q') hV]
  have hcomb : comb a φ p c z q = fun j => (gm φ z (N.U q ⊓ N.U q') (N.g q q')).val * comb a φ p c z q' j := by
    funext j
    simp only [comb, hsec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hev : ∀ (w : X.presheaf.stalk z) (y : Fin mB → X.presheaf.stalk z),
      MvPolynomial.eval₂Hom (gc (p ≫ t) z) (fun j => w * y j) F = w ^ d * MvPolynomial.eval₂Hom (gc (p ≫ t) z) y F := by
    intro w y
    simp only [MvPolynomial.coe_eval₂Hom]
    rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hd := hF (MvPolynomial.mem_support_iff.mp hm)
    have hs : ∑ i ∈ m.support, m i = d := by
      rw [← hd]; simp [Finsupp.weight_apply, Finsupp.sum]
    simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hs]
    ring
  rw [hcomb, hev]
  exact IsUnit.mul_right_eq_zero ((gm φ z (N.U q ⊓ N.U q') (N.g q q')).isUnit.pow d)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomomorphismsSameMatrixIsomorphicTestData
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

noncomputable section

namespace GlobalTheory.HomFixMat

private theorem topS_tensor_left_ext {Rg : Type} [CommRing Rg] (A : Over (Sp Rg)) {Z : Scheme.{0}}
    (f g : Z ⟶ (topS Rg ⊗ A).left) (h : f ≫ (snd (topS Rg) A).left = g ≫ (snd (topS Rg) A).left) : f = g := by
  have P := IsPullback.of_hasPullback (topS Rg).hom A.hom
  have h' : f ≫ pullback.snd (topS Rg).hom A.hom = g ≫ pullback.snd (topS Rg).hom A.hom := h
  apply P.hom_ext
  · have hm : Mono (topS Rg).hom := by
      change Mono ((⊤ : (Sp Rg).Opens).ι ≫ 𝟙 _); infer_instance
    rw [← cancel_mono (topS Rg).hom, Category.assoc, Category.assoc, P.w, ← Category.assoc, h', Category.assoc]
  · exact h'

end GlobalTheory.HomFixMat

namespace GlobalTheory.HomFixMat

theorem mat_determines : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (k : ℕ) (mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))), Hyps L M k bA bB eA eB → ∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A₁ B₁ : Over (Sp R)) [GrpObj A₁] [GrpObj B₁] (φA₁ : A₁.left ⟶ A.left) (φB₁ : B₁.left ⟶ B.left) (Φ₁ : A₁ ⟶ B₁) (A₂ B₂ : Over (Sp R)) [GrpObj A₂] [GrpObj B₂] (φA₂ : A₂.left ⟶ A.left) (φB₂ : B₂.left ⟶ B.left) (Φ₂ : A₂ ⟶ B₂) (c : Fin mA → Fin mB → Γ(Sp R, ⊤)), IsTest A B L M t A₁ B₁ φA₁ φB₁ Φ₁ → IsTest A B L M t A₂ B₂ φA₂ φB₂ Φ₂ → IsMat L M k bA bB eA eB t A₁ B₁ φA₁ φB₁ Φ₁ c → IsMat L M k bA bB eA eB t A₂ B₂ φA₂ φB₂ Φ₂ c → IsPullD φA₁ φB₁ Φ₁ φA₂ φB₂ Φ₂ (𝟙 (Sp R)) := by
  intro Rg _ _ A B _ _ _ _ L M k mA mB bA bB eA eB hH R _ t A₁ B₁ _ _ φA₁ φB₁ Φ₁ A₂ B₂ _ _ φA₂ φB₂ Φ₂ c T₁ T₂ M₁ M₂
  obtain ⟨-, hBab, hL, hM, -, -, -, -, hva, -, hbc⟩ := hH
  let ψA : A₂.left ⟶ A₁.left := T₁.1.1.lift φA₂ A₂.hom T₂.1.1.w
  let ψB : B₂.left ⟶ B₁.left := T₁.2.1.1.lift φB₂ B₂.hom T₂.2.1.1.w
  have hψA1 : ψA ≫ φA₁ = φA₂ := T₁.1.1.lift_fst _ _ _
  have hψA2 : ψA ≫ A₁.hom = A₂.hom := T₁.1.1.lift_snd _ _ _
  have hψB1 : ψB ≫ φB₁ = φB₂ := T₁.2.1.1.lift_fst _ _ _
  have hψB2 : ψB ≫ B₁.hom = B₂.hom := T₁.2.1.1.lift_snd _ _ _
  have gA : IsGrpPullback A₂ A₁ (𝟙 _) ψA :=
    IsGrpPullback.cancel T₁.1 (by rw [Category.id_comp, hψA1]; exact T₂.1) (by rw [hψA2, Category.comp_id])
  have gB : IsGrpPullback B₂ B₁ (𝟙 _) ψB :=
    IsGrpPullback.cancel T₁.2.1 (by rw [Category.id_comp, hψB1]; exact T₂.2.1) (by rw [hψB2, Category.comp_id])
  refine ⟨ψA, ψB, gA, gB, hψA1, hψB1, ?_⟩
  suffices key : Φ₂.left ≫ φB₂ = ψA ≫ Φ₁.left ≫ φB₁ by
    apply T₁.2.1.1.hom_ext
    · rw [Category.assoc, hψB1, key, Category.assoc]
    · rw [Category.assoc, hψB2, Over.w Φ₂, Category.assoc, Over.w Φ₁, hψA2]

  obtain ⟨ψA₁, ψB₁, eA₁, eB₁, g₁⟩ := GlobalTheory.T.isMatrixIdentity_germ_pullback_chart M₁
  obtain ⟨ψA₂, ψB₂, eA₂, eB₂, g₂⟩ := GlobalTheory.T.isMatrixIdentity_germ_pullback_chart M₂
  obtain ⟨x, b', hx, hb', hemb⟩ := GlobalTheory.T.embeds_after_baseChange_specTopOpen_of_stable_basis B M k bB hBab hM hva hbc
  have hG : ψA ≫ ψA₁ = ψA₂ := topS_tensor_left_ext A _ _ (by rw [Category.assoc, eA₁, eA₂, hψA1])
  let H : (baseAt x ⊗ B).left ⟶ (topS Rg ⊗ B).left := (homAt x ▷ B).left
  have hHi : IsIso (homAt x) := by
    have : IsIso ((Over.forget _).map (homAt x)) := hx
    exact isIso_of_reflects_iso (homAt x) (Over.forget _)
  have hH : IsIso H := (inferInstance : IsIso ((Over.forget _).map (homAt x ▷ B)))
  have hHs : H ≫ (snd (topS Rg) B).left = (snd (baseAt x) B).left := by
    rw [← Over.comp_left, whiskerRight_snd]
  let F₁ : A₂.left ⟶ (topS Rg ⊗ B).left := ψA ≫ Φ₁.left ≫ ψB₁
  let F₂ : A₂.left ⟶ (topS Rg ⊗ B).left := Φ₂.left ≫ ψB₂
  suffices hF : F₂ ≫ inv H = F₁ ≫ inv H by
    have e1 : F₂ = F₁ := by simpa using congrArg (· ≫ H) hF
    have e2 : F₂ ≫ (snd (topS Rg) B).left = F₁ ≫ (snd (topS Rg) B).left := by rw [e1]
    simp only [F₁, F₂, Category.assoc] at e2
    rwa [eB₁, eB₂] at e2

  have memw : ∀ {P Q : Scheme.{0}} (W : LB Q) (φ : P ⟶ Q) (j : Fin 1 → W.ι) (y : P), φ y ∈ W.U (j 0) →
      y ∈ LB.wchart W (fun _ : Fin 1 => φ) j := fun W φ j y h =>
    Set.mem_iInter.2 fun i => by rw [Subsingleton.elim i 0]; exact h
  have hsx : (snd (topS Rg) B).left = inv H ≫ (snd (baseAt x) B).left := by
    rw [← hHs, IsIso.inv_hom_id_assoc]
  have hbase : ∀ (Z : Scheme.{0}) (r : Z ⟶ (baseAt x ⊗ B).left) (z : Z) (pM : Fin 1 → M.ι) (j : Fin mB),
      r z ∈ (LPow B M (k : ℤ) (baseAt x)).U pM →
      gs r z _ ((b' j).f pM) = gs (r ≫ H) z _ ((bB j).f pM) := by
    intro Z r z pM j hz
    rw [hb' j pM, gs_res _ _ _ hz, gs_pull]
    exact chart_le_res B M (homAt x ▷ B) (whiskerRight_snd (homAt x) B) (k : ℤ) pM hz
  have hmono : Mono (baseAt x).hom := by
    have : Mono (topS Rg).hom := by
      change Mono ((⊤ : (Sp Rg).Opens).ι ≫ 𝟙 _); infer_instance
    change Mono (x ≫ (topS Rg).hom); infer_instance
  have hπ : ∀ F : A₂.left ⟶ (topS Rg ⊗ B).left, F ≫ inv H ≫ (fst (baseAt x) B).left ≫ (baseAt x).hom =
      F ≫ (snd (topS Rg) B).left ≫ B.hom := by
    intro F
    have w : (fst (baseAt x) B).left ≫ (baseAt x).hom = (snd (baseAt x) B).left ≫ B.hom :=
      pullback.condition
    rw [w, hsx]; simp only [Category.assoc]
  refine GlobalTheory.T.eq_of_proportional_germs_sectionsEmbedProjectively (fst (baseAt x) B).left b' hemb _ _ ?_ ?_
  · rw [← cancel_mono (baseAt x).hom]
    simp only [Category.assoc]
    rw [hπ, hπ]
    simp only [F₁, F₂, Category.assoc]
    rw [reassoc_of% eB₁, reassoc_of% eB₂, T₁.2.1.1.w, T₂.2.1.1.w, reassoc_of% (Over.w Φ₂), reassoc_of% (Over.w Φ₁),
      reassoc_of% hψA2]
  · intro z
    obtain ⟨q0, hq0⟩ := exists_chart hL (φA₂ z)
    obtain ⟨p₁, hp₁⟩ := exists_chart hM ((ψA ≫ Φ₁.left ≫ φB₁) z)
    obtain ⟨p₂, hp₂⟩ := exists_chart hM ((Φ₂.left ≫ φB₂) z)
    have mA₂ : (𝟙 A₂.left ≫ ψA₂) z ∈ (LPow A L (k : ℤ) (topS Rg)).U (fun _ => q0) := by
      refine memw L _ _ _ ?_
      rw [← Scheme.Hom.comp_apply, Category.id_comp, eA₂]; exact hq0
    have mA₁ : (ψA ≫ ψA₁) z ∈ (LPow A L (k : ℤ) (topS Rg)).U (fun _ => q0) := by
      rw [hG]; simpa using mA₂
    have mB₂ : (𝟙 A₂.left ≫ Φ₂.left ≫ ψB₂) z ∈ (LPow B M (k : ℤ) (topS Rg)).U (fun _ => p₂) := by
      refine memw M _ _ _ ?_
      rw [← Scheme.Hom.comp_apply, Category.id_comp, Category.assoc, eB₂]; exact hp₂
    have mB₁ : (ψA ≫ Φ₁.left ≫ ψB₁) z ∈ (LPow B M (k : ℤ) (topS Rg)).U (fun _ => p₁) := by
      refine memw M _ _ _ ?_
      rw [← Scheme.Hom.comp_apply, Category.assoc, Category.assoc, eB₁]; exact hp₁
    obtain ⟨u₂, hu₂⟩ := g₂ A₂.left (𝟙 _) z _ _ mB₂ mA₂
    obtain ⟨u₁, hu₁⟩ := g₁ A₂.left ψA z _ _ mB₁ mA₁
    simp only [Category.id_comp] at hu₂
    rw [hψA2, hG] at hu₁
    refine ⟨fun j => ∑ i, gs A₂.hom z ⊤ (c i j) * gs ψA₂ z _ ((bA i).f (fun _ => q0)), ⟨fun _ => p₂, ?_, u₂, fun l => ?_⟩,
      ⟨fun _ => p₁, ?_, u₁, fun l => ?_⟩⟩
    · refine memw M _ _ _ ?_
      rw [← Scheme.Hom.comp_apply, Category.assoc, ← hsx]; simp only [F₂, Category.assoc]; rw [eB₂]; exact hp₂
    · rw [hbase _ _ _ _ _ (memw M _ _ _ (by rw [← Scheme.Hom.comp_apply, Category.assoc, ← hsx]; simp only [F₂, Category.assoc]; rw [eB₂]; exact hp₂)),
        Category.assoc, IsIso.inv_hom_id, Category.comp_id]
      exact hu₂ l
    · refine memw M _ _ _ ?_
      rw [← Scheme.Hom.comp_apply, Category.assoc, ← hsx]; simp only [F₁, Category.assoc]; rw [eB₁]; exact hp₁
    · rw [hbase _ _ _ _ _ (memw M _ _ _ (by rw [← Scheme.Hom.comp_apply, Category.assoc, ← hsx]; simp only [F₁, Category.assoc]; rw [eB₁]; exact hp₁)),
        Category.assoc, IsIso.inv_hom_id, Category.comp_id]
      exact hu₁ l

end GlobalTheory.HomFixMat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentAdeleOfPlacesMulEqSumComponents
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct Pointwise

noncomputable section

namespace GlobalTheory.PlaceIdemSum

open GlobalTheory.CompanionTheory.SaGen

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem idem_eq_sum (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F)
    (h : IsPlacesIdem S₁ S₂ ε) :
    ε = ∑ w ∈ S₁, (placeMapInf w).inj 1 + ∑ v ∈ S₂, (placeMapFin v).inj 1 := by
  classical
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine adele_ext ?_ (finAdele_ext fun u => ?_)
  · have hfin : ∀ v ∈ S₂, fstA F ((placeMapFin v).inj 1) = 0 := fun v _ => rfl
    have hinf : ∀ w ∈ S₁, fstA F ((placeMapInf w).inj 1) = singleI w 1 := fun w _ => rfl
    rw [map_add, map_sum, map_sum, Finset.sum_congr rfl hfin, Finset.sum_const_zero, add_zero,
      Finset.sum_congr rfl hinf]
    refine ainf_ext fun u => ?_
    change fstA F ε u = (∑ w ∈ S₁, (singleI w 1 : ∀ u : InfinitePlace F, u.Completion)) u
    refine Eq.trans ?_ (Finset.sum_apply u S₁ (fun w => (singleI w 1 : ∀ u : InfinitePlace F, u.Completion))).symm
    by_cases hu : u ∈ S₁
    · rw [h1 u hu, Finset.sum_eq_single u (fun w _ hw => singleI_ne (Ne.symm hw) 1) (fun h => absurd hu h),
        singleI_self]
    · rw [h2 u hu, Finset.sum_eq_zero fun w hw => singleI_ne (fun e : u = w => hu (e ▸ hw)) 1]
  · have hinf : ∀ w ∈ S₁, sndA F ((placeMapInf w).inj 1) = 0 := fun w _ => rfl
    have hfin : ∀ v ∈ S₂, sndA F ((placeMapFin v).inj 1) = singleV F v 1 := fun v _ => rfl
    rw [map_add, map_sum, map_sum, Finset.sum_congr rfl hinf, Finset.sum_const_zero, zero_add,
      Finset.sum_congr rfl hfin, map_sum]
    by_cases hu : u ∈ S₂
    · rw [h3 u hu, Finset.sum_eq_single u (fun v _ hv => StrongApprox.evalV_single_ne (Ne.symm hv) 1)
        (fun h => absurd hu h), StrongApprox.evalV_single_same]
    · rw [h4 u hu, Finset.sum_eq_zero fun v hv => StrongApprox.evalV_single_ne (fun e : u = v => hu (e ▸ hv)) 1]

theorem iB_tmul {K : Type} [Field K] [Algebra F K] [TopologicalSpace K] (P : PlaceMap F K) (y : K) (e : E) :
    iB (E := E) P (y ⊗ₜ[F] e) = P.inj y ⊗ₜ[F] e := rfl

theorem iB_map_tmul {K : Type} [Field K] [Algebra F K] [TopologicalSpace K] (P : PlaceMap F K) (x : AF F) (e : E) :
    iB P (Algebra.TensorProduct.map P.proj (AlgHom.id F E) (x ⊗ₜ[F] e)) = (P.inj 1 * x) ⊗ₜ[F] e := by
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, iB_tmul, P.inj_proj]

theorem idem_mul_eq_sum : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε →
    ∀ a : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * a =
      ∑ w ∈ S₁, GlobalTheory.CompanionTheory.SaGen.iB (GlobalTheory.CompanionTheory.SaGen.placeMapInf w)
          (Algebra.TensorProduct.map (GlobalTheory.CompanionTheory.SaGen.placeMapInf w).proj (AlgHom.id F E) a) +
        ∑ v ∈ S₂, GlobalTheory.CompanionTheory.SaGen.iB (GlobalTheory.CompanionTheory.SaGen.placeMapFin v)
          (Algebra.TensorProduct.map (GlobalTheory.CompanionTheory.SaGen.placeMapFin v).proj (AlgHom.id F E) a) := by
  intro F E _ _ _ _ S₁ S₂ ε hε a
  induction a using TensorProduct.induction_on with
  | zero => simp only [mul_zero, map_zero, Finset.sum_const_zero, add_zero]
  | tmul x e =>
    simp only [iB_map_tmul]
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← TensorProduct.sum_tmul, ← TensorProduct.sum_tmul,
      ← TensorProduct.add_tmul, ← Finset.sum_mul, ← Finset.sum_mul, ← add_mul, ← idem_eq_sum S₁ S₂ ε hε]
  | add a b ha hb =>
    rw [mul_add, ha, hb]
    simp only [map_add, Finset.sum_add_distrib]
    abel

end GlobalTheory.PlaceIdemSum
end
end

