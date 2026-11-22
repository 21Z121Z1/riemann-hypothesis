import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFundamentalDomainEqSum
section
open MeasureTheory IsDedekindDomain NumberField

namespace GlobalTheory.ClassIntegral

variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G]

def dcoset (Γ K : Subgroup G) (g : G) : Set G := {x | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * g * k}

theorem measurableSet_dcoset (Γ K : Subgroup G) [Countable Γ] (hK : MeasurableSet (K : Set G)) (g : G) :
    MeasurableSet (dcoset Γ K g) := by
  have : dcoset Γ K g = ⋃ γ : Γ, (fun y => ((γ : G) * g)⁻¹ * y) ⁻¹' (K : Set G) := by
    ext x
    simp only [dcoset, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe]
    constructor
    · rintro ⟨γ, hγ, k, hk, rfl⟩
      exact ⟨⟨γ, hγ⟩, by simpa [mul_assoc] using hk⟩
    · rintro ⟨γ, h⟩
      exact ⟨γ, γ.2, _, h, by group⟩
  rw [this]
  exact MeasurableSet.iUnion fun γ => (measurable_const_mul _) hK

omit [MeasurableSpace G] [MeasurableMul G] in
theorem tsum_indicator_eq (Γ K : Subgroup G) (g x : G) :
    ∑' γ : Γ, ((fun y => g⁻¹ * y) ⁻¹' (K : Set G)).indicator (1 : G → ENNReal) (γ • x) =
      (∑' _ : {γ : Γ // g⁻¹ * (γ : G) * g ∈ K}, (1 : ENNReal)) * (dcoset Γ K g).indicator 1 x := by
  classical
  by_cases hx : x ∈ dcoset Γ K g
  · rw [Set.indicator_of_mem hx, Pi.one_apply, mul_one]
    obtain ⟨δ, hδ, k, hk, rfl⟩ := hx
    rw [← (Equiv.mulRight (⟨δ, hδ⟩ : Γ)⁻¹).tsum_eq]
    have := tsum_subtype {γ : Γ | g⁻¹ * (γ : G) * g ∈ K} (fun _ => (1 : ENNReal))
    refine Eq.trans ?_ this.symm
    refine tsum_congr fun γ => ?_
    have e : g⁻¹ * ((γ : G) * δ⁻¹ * (δ * g * k)) = g⁻¹ * γ * g * k := by group
    simp only [Set.indicator, Set.mem_preimage, Subgroup.smul_def, smul_eq_mul, Equiv.coe_mulRight,
      Subgroup.coe_mul, Subgroup.coe_inv, SetLike.mem_coe, Pi.one_apply, Set.mem_setOf_eq, e,
      K.mul_mem_cancel_right hk]
  · rw [Set.indicator_of_notMem hx, mul_zero, ENNReal.tsum_eq_zero]
    intro γ
    apply Set.indicator_of_notMem
    intro h
    apply hx
    refine ⟨(γ : G)⁻¹, Γ.inv_mem γ.2, _, h, ?_⟩
    simp only [Subgroup.smul_def, smul_eq_mul]
    group

theorem measure_dcoset (Γ K : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant]
    (hK : MeasurableSet (K : Set G)) (hK1 : μ K = 1) (g : G) {𝓕 : Set G}
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) :
    (∑' _ : {γ : Γ // g⁻¹ * (γ : G) * g ∈ K}, (1 : ENNReal)) * μ.restrict 𝓕 (dcoset Γ K g) = 1 := by
  have i1 : MeasurableConstSMul Γ G :=
    ⟨fun γ => by simpa [Subgroup.smul_def, smul_eq_mul] using measurable_const_mul (γ : G)⟩
  have i2 : SMulInvariantMeasure Γ G μ :=
    ⟨fun γ s _ => by
      have : ((fun x => γ • x) ⁻¹' s) = ((fun x => (γ : G) * x) ⁻¹' s) := by
        ext x; simp [Subgroup.smul_def, smul_eq_mul]
      rw [this, measure_preimage_mul]⟩
  have hT : MeasurableSet ((fun y => g⁻¹ * y) ⁻¹' (K : Set G)) := (measurable_const_mul _) hK
  have hf : Measurable (((fun y => g⁻¹ * y) ⁻¹' (K : Set G)).indicator (1 : G → ENNReal)) :=
    measurable_one.indicator hT
  have hC := measurableSet_dcoset Γ K hK g
  rw [← lintegral_indicator_one hC, ← lintegral_const_mul _ (measurable_one.indicator hC)]
  simp only [← tsum_indicator_eq]
  have hmeas : ∀ γ : Γ, Measurable fun x : G =>
      ((fun y => g⁻¹ * y) ⁻¹' (K : Set G)).indicator (1 : G → ENNReal) (γ • x) :=
    fun γ => hf.comp (measurable_const_smul γ)
  rw [lintegral_tsum fun γ => (hmeas γ).aemeasurable,
    ← h𝓕.lintegral_eq_tsum'', lintegral_indicator_one hT, measure_preimage_mul, hK1]

theorem tsum_one_mul_eq_one {α : Type} {m : ENNReal} (h : (∑' _ : α, (1 : ENNReal)) * m = 1) :
    m ≠ ⊤ ∧ m.toReal = (Nat.card α : ℝ)⁻¹ := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at h
  have hN0 : (∑' _ : α, (1 : ENNReal)) ≠ 0 := by intro h0; rw [h0] at h; simp at h
  have hN : (∑' _ : α, (1 : ENNReal)) ≠ ⊤ := by
    intro h0; rw [h0, ENNReal.top_mul hm0] at h; simp at h
  have hm : m ≠ ⊤ := by
    intro h0; rw [h0, ENNReal.mul_top hN0] at h; simp at h
  have : Finite α := by
    by_contra hα
    have : Infinite α := not_finite_iff_infinite.mp hα
    exact hN (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero)
  refine ⟨hm, ?_⟩
  have := Fintype.ofFinite α
  rw [tsum_fintype] at h
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    Fintype.card_eq_nat_card] at h
  have h' := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_one] at h'
  exact eq_inv_of_mul_eq_one_right h'

theorem integral_fundamentalDomain_eq_sum : ∀ {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (Γ K : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant], MeasurableSet (K : Set G) → μ K = 1 → ∀ {ι : Type} [Fintype ι] (g : ι → G), (∀ x : G, ∃! i, ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * g i * k) → ∀ 𝓕 : Set G, IsFundamentalDomain Γ 𝓕 μ → ∀ Φ : G → ℂ, (∀ γ ∈ Γ, ∀ k ∈ K, ∀ x, Φ (γ * x * k) = Φ x) → IntegrableOn Φ 𝓕 μ ∧ ∫ x in 𝓕, Φ x ∂μ = ∑ i, ((Nat.card {γ : Γ // (g i)⁻¹ * (γ : G) * g i ∈ K} : ℂ))⁻¹ * Φ (g i) := by
  intro G _ _ _ Γ K _ μ _ hK hK1 ι _ g hcov 𝓕 h𝓕 Φ hΦ
  have hm := fun i => tsum_one_mul_eq_one (measure_dcoset Γ K μ hK hK1 (g i) h𝓕)
  have hC := fun i => measurableSet_dcoset Γ K hK (g i)
  have hpt : Φ = fun x => ∑ i, (dcoset Γ K (g i)).indicator (fun _ => Φ (g i)) x := by
    funext x
    obtain ⟨j, hj, huniq⟩ := hcov x
    rw [Finset.sum_eq_single j]
    · rw [Set.indicator_of_mem (s := dcoset Γ K (g j)) hj]
      obtain ⟨γ, hγ, k, hk, rfl⟩ := hj
      exact hΦ γ hγ k hk _
    · intro i _ hij
      have hx : x ∉ dcoset Γ K (g i) := fun h => hij (huniq i h)
      exact Set.indicator_of_notMem hx _
    · intro h; exact absurd (Finset.mem_univ j) h
  have hint : ∀ i, Integrable ((dcoset Γ K (g i)).indicator (fun _ => Φ (g i))) (μ.restrict 𝓕) :=
    fun i => (integrable_indicator_iff (hC i)).mpr (integrableOn_const (hm i).1)
  constructor
  · rw [IntegrableOn, hpt]
    exact integrable_finset_sum _ fun i _ => hint i
  · calc ∫ x in 𝓕, Φ x ∂μ
        = ∫ x in 𝓕, ∑ i, (dcoset Γ K (g i)).indicator (fun _ => Φ (g i)) x ∂μ := by
          conv_lhs => rw [hpt]
      _ = _ := by
          rw [integral_finset_sum _ fun i _ => hint i]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [integral_indicator_const _ (hC i), Measure.real, (hm i).2, Complex.real_smul]
          push_cast
          rfl

end GlobalTheory.ClassIntegral
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralRowSpaceBasisExists
section
namespace GlobalTheory

theorem exists_basis_matrix_of_integral_preimage
    (O k : Type) [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field k] [Algebra O k]
    [IsFractionRing O k] (m n : ℕ) (P : Matrix (Fin m) (Fin n) k)
    (hP : ∀ c, Matrix.vecMul c P = 0 → c = 0) :
    ∃ M : Matrix (Fin m) (Fin m) k, M.det ≠ 0 ∧ ∀ c : Fin m → k,
      (∃ a : Fin n → O, Matrix.vecMul c P = fun j => algebraMap O k (a j)) ↔
        ∃ b : Fin m → O, c = Matrix.vecMul (fun i => algebraMap O k (b i)) M := by
  classical
  let ι : (Fin n → O) →ₗ[O] (Fin n → k) := (Algebra.linearMap O k).compLeft (Fin n)
  let f : (Fin m → k) →ₗ[O] (Fin n → k) := (Matrix.vecMulLinear P).restrictScalars O
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    exact hP c hc
  let L : Submodule O (Fin m → k) := (LinearMap.range ι).comap f
  have hL : ∀ c, c ∈ L ↔ ∃ a : Fin n → O,
      Matrix.vecMul c P = fun j => algebraMap O k (a j) := by
    intro c
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨a, ha.symm⟩
    · rintro ⟨a, ha⟩
      exact ⟨a, ha.symm⟩
  have hfg : L.FG := by
    have h1 : (LinearMap.range ι).FG := by
      rw [← Module.Finite.iff_fg]; infer_instance
    have h2 : (L.map f).FG := by
      have : IsNoetherian O (LinearMap.range ι) := isNoetherian_of_fg_of_noetherian _ h1
      have : IsNoetherian O (L.map f) := isNoetherian_of_le (Submodule.map_comap_le f _)
      rw [← Module.Finite.iff_fg]; infer_instance
    exact Submodule.fg_of_fg_map_injective f hf h2
  have hsp : Submodule.span k (L : Set (Fin m → k)) = ⊤ := by
    rw [eq_top_iff]
    intro c _
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O)
      (Matrix.vecMul c P)
    choose a ha using hd
    have hd0 : algebraMap O k d ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2
    have hmem : (algebraMap O k d) • c ∈ L := by
      rw [hL]
      refine ⟨a, ?_⟩
      funext j
      rw [Matrix.smul_vecMul, ha j]
      simp [Algebra.smul_def]
    have : c = (algebraMap O k d)⁻¹ • ((algebraMap O k d) • c) := by
      rw [smul_smul, inv_mul_cancel₀ hd0, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
  haveI : Submodule.IsLattice k L := ⟨hfg, hsp⟩
  have hr : Module.finrank O L = m := by
    simpa using Submodule.IsLattice.finrank_of_pi k L
  let b : Module.Basis (Fin m) O L := Module.finBasisOfFinrankEq O L hr
  let M : Matrix (Fin m) (Fin m) k := Matrix.of fun i => (b i : Fin m → k)
  have hv : ∀ x : Fin m → O, Matrix.vecMul (fun i => algebraMap O k (x i)) M
      = ((∑ i, x i • b i : L) : Fin m → k) := by
    intro x
    funext j
    simp [Matrix.vecMul, dotProduct, M, Algebra.smul_def]
  refine ⟨M, ?_, ?_⟩
  · have hli : LinearIndependent k M.row := by
      have := (b.extendOfIsLattice k).linearIndependent
      have e : M.row = ⇑(b.extendOfIsLattice k) := by
        funext i
        rw [Module.Basis.extendOfIsLattice_apply]
        rfl
      rw [e]
      exact this
    have := Matrix.linearIndependent_rows_iff_isUnit.mp hli
    exact ((Matrix.isUnit_iff_isUnit_det M).mp this).ne_zero
  · intro c
    rw [← hL]
    constructor
    · intro hc
      refine ⟨b.repr ⟨c, hc⟩, ?_⟩
      rw [hv, b.sum_repr]
    · rintro ⟨x, rfl⟩
      rw [hv]
      exact Subtype.property _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMemConnectedComponentInFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem inv_mem_connectedComponentIn_fibre (S : Scheme.{0}) (G : Over S) [GrpObj G] (y : G.left)
    (hy : y ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))}) :
    (ι[G]).left y ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} := by
  simp only [Set.mem_setOf_eq] at hy ⊢
  have hw : ∀ z : G.left, G.hom ((ι[G]).left z) = G.hom z := by
    intro z
    have h := Over.w (ι[G])
    rw [← Scheme.Hom.comp_apply, h]
  have hη : ∀ s : S, (ι[G]).left ((η[G]).left s) = (η[G]).left s := by
    intro s
    have h : (η[G] ≫ ι[G]).left = (η[G]).left := by rw [GrpObj.one_inv]
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, h]
  rw [hw]
  set F := G.hom ⁻¹' {G.hom y}
  set e := (η[G]).left (G.hom y)
  have heF : e ∈ F := (connectedComponentIn_nonempty_iff.mp ⟨y, hy⟩)
  have hsub : (ι[G]).left '' connectedComponentIn F e ⊆ connectedComponentIn F e := by
    refine (isPreconnected_connectedComponentIn.image _ (ι[G]).left.continuous.continuousOn).subset_connectedComponentIn
      ⟨e, mem_connectedComponentIn heF, hη _⟩ ?_
    rintro _ ⟨z, hz, rfl⟩
    have hzF : z ∈ F := connectedComponentIn_subset _ _ hz
    simp only [F, Set.mem_preimage, Set.mem_singleton_iff] at hzF ⊢
    rw [hw, hzF]
  exact hsub ⟨y, hy, rfl⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvolutionNormClassRemoveRationalFactor
section
open scoped TensorProduct Classical

namespace GlobalTheory.RatRed

def LUnit (ℓ : ℕ) (r : ℚ) : Prop :=
  ∃ N : ℕ, ¬ ℓ ∣ N ∧ (∃ m : ℤ, (N : ℚ) * r = m) ∧ ∃ m : ℤ, (N : ℚ) * r⁻¹ = m

theorem lunit_one (ℓ : ℕ) (hℓ : ℓ.Prime) : LUnit ℓ 1 :=
  ⟨1, hℓ.not_dvd_one, ⟨1, by simp⟩, ⟨1, by simp⟩⟩

theorem lunit_mul {ℓ : ℕ} (hℓ : ℓ.Prime) {r s : ℚ} (hr : LUnit ℓ r) (hs : LUnit ℓ s) :
    LUnit ℓ (r * s) := by
  obtain ⟨N, hN, ⟨m₁, h₁⟩, ⟨m₂, h₂⟩⟩ := hr
  obtain ⟨M, hM, ⟨k₁, g₁⟩, ⟨k₂, g₂⟩⟩ := hs
  refine ⟨N * M, fun h => (hℓ.dvd_mul.1 h).elim hN hM, ⟨m₁ * k₁, ?_⟩, ⟨m₂ * k₂, ?_⟩⟩
  · push_cast; rw [← h₁, ← g₁]; ring
  · push_cast; rw [← h₂, ← g₂, mul_inv]; ring

theorem lunit_inv {ℓ : ℕ} {r : ℚ} (hr : LUnit ℓ r) : LUnit ℓ r⁻¹ := by
  obtain ⟨N, hN, h₁, h₂⟩ := hr
  exact ⟨N, hN, h₂, by simpa using h₁⟩

theorem lunit_neg {ℓ : ℕ} {r : ℚ} (hr : LUnit ℓ r) : LUnit ℓ (-r) := by
  obtain ⟨N, hN, ⟨m₁, h₁⟩, ⟨m₂, h₂⟩⟩ := hr
  refine ⟨N, hN, ⟨-m₁, ?_⟩, ⟨-m₂, ?_⟩⟩
  · push_cast; rw [← h₁]; ring
  · push_cast; rw [← h₂, inv_neg]; ring

theorem lunit_nat {ℓ : ℕ} {n : ℕ} (hn : ¬ ℓ ∣ n) : LUnit ℓ (n : ℚ) := by
  have hn0 : (n : ℚ) ≠ 0 := by
    rintro h; exact hn (by rw [Nat.cast_eq_zero.1 h]; exact dvd_zero _)
  refine ⟨n, hn, ⟨(n : ℤ) * n, by push_cast; ring⟩, ⟨1, by rw [mul_inv_cancel₀ hn0]; simp⟩⟩

theorem lunit_pow {ℓ : ℕ} (hℓ : ℓ.Prime) {r : ℚ} (hr : LUnit ℓ r) (k : ℕ) : LUnit ℓ (r ^ k) := by
  induction k with
  | zero => simpa using lunit_one ℓ hℓ
  | succ k ih => rw [pow_succ]; exact lunit_mul hℓ ih hr

theorem lunit_zpow {ℓ : ℕ} (hℓ : ℓ.Prime) {r : ℚ} (hr : LUnit ℓ r) (k : ℤ) : LUnit ℓ (r ^ k) := by
  rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
  · simpa using lunit_pow hℓ hr n
  · simpa [zpow_neg] using lunit_inv (lunit_pow hℓ hr n)

theorem lunit_prime {ℓ p : ℕ} (hℓ : ℓ.Prime) (hp : p.Prime) (hne : p ≠ ℓ) : LUnit ℓ (p : ℚ) :=
  lunit_nat (fun h => hne ((Nat.prime_dvd_prime_iff_eq hℓ hp).1 h).symm)

theorem lunit_decomp {ℓ : ℕ} (hℓ : ℓ.Prime) {c : ℚ} (hc : c ≠ 0) :
    ∃ k : ℤ, LUnit ℓ (c / (ℓ : ℚ) ^ k) := by
  have hnum : c.num.natAbs ≠ 0 := by simpa using Rat.num_ne_zero.2 hc
  obtain ⟨e₁, n, hn, hne⟩ := Nat.exists_eq_pow_mul_and_not_dvd hnum ℓ hℓ.ne_one
  obtain ⟨e₂, m, hm, hme⟩ := Nat.exists_eq_pow_mul_and_not_dvd c.den_nz ℓ hℓ.ne_one
  have hℓ0 : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  have hm0 : (m : ℚ) ≠ 0 := by
    rintro h; exact hm (by rw [Nat.cast_eq_zero.1 h]; exact dvd_zero _)
  refine ⟨(e₁ : ℤ) - e₂, ?_⟩
  have hden : (c.den : ℚ) = (ℓ : ℚ) ^ e₂ * m := by rw [hme]; push_cast; ring
  have key : c * ((ℓ : ℚ) ^ e₂ * m) = (c.num : ℚ) := by rw [← hden]; exact Rat.mul_den_eq_num c
  rw [zpow_sub₀ hℓ0, zpow_natCast, zpow_natCast]
  rcases Int.natAbs_eq c.num with h | h
  · have hv : c / ((ℓ : ℚ) ^ e₁ / (ℓ : ℚ) ^ e₂) = (n : ℚ) * (m : ℚ)⁻¹ := by
      have : (c.num : ℚ) = (ℓ : ℚ) ^ e₁ * n := by rw [h, hne]; push_cast; ring
      rw [this] at key
      have hp : (ℓ : ℚ) ^ e₁ ≠ 0 := pow_ne_zero _ hℓ0
      field_simp at key ⊢
      linear_combination key
    rw [hv]; exact lunit_mul hℓ (lunit_nat hn) (lunit_inv (lunit_nat hm))
  · have hv : c / ((ℓ : ℚ) ^ e₁ / (ℓ : ℚ) ^ e₂) = -((n : ℚ) * (m : ℚ)⁻¹) := by
      have : (c.num : ℚ) = -((ℓ : ℚ) ^ e₁ * n) := by rw [h, hne]; push_cast; ring
      rw [this] at key
      have hp : (ℓ : ℚ) ^ e₁ ≠ 0 := pow_ne_zero _ hℓ0
      field_simp at key ⊢
      linear_combination key
    rw [hv]; exact lunit_neg (lunit_mul hℓ (lunit_nat hn) (lunit_inv (lunit_nat hm)))

theorem lunit_integral {E : Type} [CommRing E] [Algebra ℚ E] {ℓ : ℕ} (hℓ : ℓ.Prime) {r : ℚ}
    (hr : LUnit ℓ r) {d : ℕ} (hd : ¬ ℓ ∣ d) {x y : E} (hx : IsIntegral ℤ ((d : E) * x))
    (hy : IsIntegral ℤ ((d : E) * y)) :
    ∃ d' : ℕ, ¬ ℓ ∣ d' ∧ IsIntegral ℤ ((d' : E) * (algebraMap ℚ E r * x)) ∧
      IsIntegral ℤ ((d' : E) * (algebraMap ℚ E r⁻¹ * y)) := by
  obtain ⟨N, hN, ⟨m₁, h₁⟩, ⟨m₂, h₂⟩⟩ := hr
  refine ⟨d * N, fun h => (hℓ.dvd_mul.1 h).elim hd hN, ?_, ?_⟩
  · have e : ((d * N : ℕ) : E) * (algebraMap ℚ E r * x) = (m₁ : E) * ((d : E) * x) := by
      have : (m₁ : E) = algebraMap ℚ E ((N : ℚ) * r) := by rw [h₁]; simp
      rw [this, map_mul, map_natCast]; push_cast; ring
    rw [e]; exact (isIntegral_intCast m₁).mul hx
  · have e : ((d * N : ℕ) : E) * (algebraMap ℚ E r⁻¹ * y) = (m₂ : E) * ((d : E) * y) := by
      have : (m₂ : E) = algebraMap ℚ E ((N : ℚ) * r⁻¹) := by rw [h₂]; simp
      rw [this, map_mul, map_natCast]; push_cast; ring
    rw [e]; exact (isIntegral_intCast m₂).mul hy

theorem exists_nat_mul_integral {E : Type} [CommRing E] [Algebra ℚ E] [FiniteDimensional ℚ E]
    (z : E) : ∃ D : ℕ, D ≠ 0 ∧ IsIntegral ℤ ((D : E) * z) := by
  have hz : IsAlgebraic ℤ z :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic z)
  obtain ⟨y, hy, hint⟩ := hz.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_ne_zero.2 hy, ?_⟩
  rw [zsmul_eq_mul] at hint
  rcases Int.natAbs_eq y with h | h
  · have := congrArg (Int.cast : ℤ → E) h
    rw [Int.cast_natCast] at this
    rwa [this] at hint
  · have := congrArg (Int.cast : ℤ → E) h
    rw [Int.cast_neg, Int.cast_natCast] at this
    rw [this, neg_mul] at hint
    simpa using hint.neg

theorem ratred : ∀ (E : Type) [CommRing E] [Algebra ℚ E] [FiniteDimensional ℚ E] (τ : E ≃ₐ[ℚ] E) (S : Finset ℕ) (A : Finset E),
    (∀ a : E, IsUnit a → τ a = a →
      (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∃ (b x y : E), IsUnit b ∧ a = x * (b * τ b) ∧ b * τ b = y * a ∧
        ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : E) * x) ∧ IsIntegral ℤ ((d : E) * y)) →
      ∃ a₀ ∈ A, ∃ e : Eˣ, a = (e : E) * a₀ * τ e) →
    ∀ a : E, IsUnit a → τ a = a →
    (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∃ (c : ℚ) (b x y : E), c ≠ 0 ∧ IsUnit b ∧ a = x * (algebraMap ℚ E c * (b * τ b)) ∧
      algebraMap ℚ E c * (b * τ b) = y * a ∧ ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : E) * x) ∧ IsIntegral ℤ ((d : E) * y)) →
    ∃ a₀ ∈ A, ∃ (r : ℚˣ) (e : Eˣ), a = algebraMap ℚ E (r : ℚ) * ((e : E) * a₀ * τ e) := by
  intro E _ _ _ τ S A hA a ha hτa hloc
  obtain ⟨u, rfl⟩ := ha
  obtain ⟨D₁, hD₁, hi₁⟩ := exists_nat_mul_integral (u : E)
  obtain ⟨D₂, hD₂, hi₂⟩ := exists_nat_mul_integral ((u⁻¹ : Eˣ) : E)
  have hD0 : D₁ * D₂ ≠ 0 := mul_ne_zero hD₁ hD₂
  have hDu : IsIntegral ℤ (((D₁ * D₂ : ℕ) : E) * u) := by
    have e : (((D₁ * D₂ : ℕ) : E) * u) = (D₂ : E) * ((D₁ : E) * u) := by push_cast; ring
    rw [e]; exact (isIntegral_natCast D₂).mul hi₁
  have hDu' : IsIntegral ℤ (((D₁ * D₂ : ℕ) : E) * ((u⁻¹ : Eˣ) : E)) := by
    have e : (((D₁ * D₂ : ℕ) : E) * ((u⁻¹ : Eˣ) : E)) = (D₁ : E) * ((D₂ : E) * ((u⁻¹ : Eˣ) : E)) := by
      push_cast; ring
    rw [e]; exact (isIntegral_natCast D₁).mul hi₂
  choose! c b x y hc hb h₁ h₂ d hd hix hiy using hloc
  have hk : ∀ ℓ, ℓ.Prime → ℓ ∉ S → ∃ k : ℤ, LUnit ℓ (c ℓ / (ℓ : ℚ) ^ k) :=
    fun ℓ hℓ hS => lunit_decomp hℓ (hc ℓ hℓ hS)
  choose! k hk using hk
  let T : Finset ℕ := (D₁ * D₂).primeFactors.filter (· ∉ S)
  have hTmem : ∀ p, p ∈ T ↔ p.Prime ∧ p ∣ D₁ * D₂ ∧ p ∉ S := by
    intro p
    simp only [T, Finset.mem_filter, Nat.mem_primeFactors]
    tauto
  let q : ℚ := ∏ p ∈ T, (p : ℚ) ^ (k p)
  have hq0 : q ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun p hp => zpow_ne_zero _ ?_
    exact_mod_cast ((hTmem p).1 hp).1.ne_zero
  have hqU : ∀ ℓ, ℓ.Prime → ℓ ∉ T → LUnit ℓ q := by
    intro ℓ hℓ hT
    refine Finset.prod_induction _ (LUnit ℓ) (fun _ _ => lunit_mul hℓ) (lunit_one ℓ hℓ) ?_
    intro p hp
    exact lunit_zpow hℓ (lunit_prime hℓ ((hTmem p).1 hp).1 (fun h => hT (h ▸ hp))) _
  have hcqU : ∀ ℓ ∈ T, LUnit ℓ (c ℓ / q) := by
    intro ℓ hℓT
    obtain ⟨hℓ, -, hS⟩ := (hTmem ℓ).1 hℓT
    have e : c ℓ / q = c ℓ / (ℓ : ℚ) ^ (k ℓ) * (∏ p ∈ T.erase ℓ, (p : ℚ) ^ (k p))⁻¹ := by
      simp only [q]
      rw [← Finset.mul_prod_erase T (fun p => (p : ℚ) ^ (k p)) hℓT, div_mul_eq_div_div, div_eq_mul_inv]
    rw [e]
    refine lunit_mul hℓ (hk ℓ hℓ hS) (lunit_inv ?_)
    refine Finset.prod_induction _ (LUnit ℓ) (fun _ _ => lunit_mul hℓ) (lunit_one ℓ hℓ) ?_
    intro p hp
    obtain ⟨hpl, hpT⟩ := Finset.mem_erase.1 hp
    exact lunit_zpow hℓ (lunit_prime hℓ ((hTmem p).1 hpT).1 hpl) _
  have hq1 : algebraMap ℚ E q * algebraMap ℚ E q⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hq0, map_one]
  have ha' : IsUnit (algebraMap ℚ E q⁻¹ * (u : E)) :=
    ((isUnit_iff_ne_zero.2 (inv_ne_zero hq0)).map (algebraMap ℚ E)).mul u.isUnit
  have hτ' : τ (algebraMap ℚ E q⁻¹ * (u : E)) = algebraMap ℚ E q⁻¹ * (u : E) := by
    rw [map_mul, AlgEquiv.commutes, hτa]
  obtain ⟨a₀, ha₀, e, he⟩ := hA _ ha' hτ' (by
    intro ℓ hℓ hS
    by_cases hT : ℓ ∈ T
    · obtain ⟨d', hd', hx', hy'⟩ :=
        lunit_integral hℓ (hcqU ℓ hT) (hd ℓ hℓ hS) (hix ℓ hℓ hS) (hiy ℓ hℓ hS)
      refine ⟨b ℓ, _, _, hb ℓ hℓ hS, ?_, ?_, d', hd', hx', hy'⟩
      · rw [div_eq_mul_inv, map_mul, h₁ ℓ hℓ hS]; ring
      · have hc1 : algebraMap ℚ E (c ℓ) * algebraMap ℚ E (c ℓ)⁻¹ = 1 := by
          rw [← map_mul, mul_inv_cancel₀ (hc ℓ hℓ hS), map_one]
        rw [inv_div, div_eq_mul_inv, map_mul]
        linear_combination (-(b ℓ * τ (b ℓ))) * hc1 + algebraMap ℚ E (c ℓ)⁻¹ * h₂ ℓ hℓ hS -
          (algebraMap ℚ E (c ℓ)⁻¹ * y ℓ * (u : E)) * hq1
    · have hD : ¬ ℓ ∣ D₁ * D₂ := fun h => hT ((hTmem ℓ).2 ⟨hℓ, h, hS⟩)
      obtain ⟨d', hd', hx', hy'⟩ := lunit_integral hℓ (lunit_inv (hqU ℓ hℓ hT)) hD hDu hDu'
      refine ⟨1, _, _, isUnit_one, ?_, ?_, d', hd', hx', hy'⟩
      · simp
      · rw [inv_inv, map_one, mul_one]
        linear_combination (-((u : E) * ((u⁻¹ : Eˣ) : E))) * hq1 - u.mul_inv)
  refine ⟨a₀, ha₀, Units.mk0 q hq0, e, ?_⟩
  rw [← he, Units.val_mk0, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hq0, map_one, one_mul]

end GlobalTheory.RatRed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleDvdOfDvdCharpolyOfAevalMatrix
section
open Matrix Polynomial

namespace GlobalTheory

theorem irreducible_dvd_of_dvd_charpoly_of_aeval_matrix {K : Type} [Field K] {h : ℕ}
    (M : Matrix (Fin h) (Fin h) K) (p q : K[X]) (hp : Irreducible p)
    (hd : p ∣ M.charpoly) (hq : aeval M q = 0) : p ∣ q := by
  classical
  have : Fact (Irreducible p) := ⟨hp⟩
  let L := AdjoinRoot p
  let M' := M.map (algebraMap K L)
  have hM' : aeval M' q = 0 := by
    have := Polynomial.aeval_algHom_apply ((Algebra.ofId K L).mapMatrix (m := Fin h)) M q
    rw [hq, map_zero] at this
    exact this
  have hroot : M'.charpoly.IsRoot (AdjoinRoot.root p) := by
    rw [Matrix.charpoly_map, IsRoot.def, eval_map, ← aeval_def,
      AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero]
    exact hd
  have hs : AdjoinRoot.root p ∈ spectrum L M' := Matrix.mem_spectrum_iff_isRoot_charpoly.2 hroot
  have h2 := spectrum.subset_polynomial_aeval M' (q.map (algebraMap K L)) ⟨_, hs, rfl⟩
  rw [aeval_map_algebraMap, hM'] at h2
  have hnt : Nontrivial (Matrix (Fin h) (Fin h) L) := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    exact (spectrum.mem_iff.1 hs) (isUnit_of_subsingleton _)
  rw [spectrum.zero_eq, Set.mem_singleton_iff] at h2
  simp only [eval_map, ← aeval_def] at h2
  rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero] at h2
  exact h2

theorem charpoly_eq_pow_of_aeval_irreducible_eq_zero :
    ∀ (K : Type) [Field K] (h N : ℕ) (M : Matrix (Fin h) (Fin h) K) (f : K[X]), f.Monic →
      Irreducible f → Polynomial.aeval M f = 0 → h = f.natDegree * N → M.charpoly = f ^ N := by
  intro K _ h N M f hfm hfi hf hh
  classical
  have hc0 : M.charpoly ≠ 0 := (Matrix.charpoly_monic M).ne_zero
  have hmem : ∀ b ∈ UniqueFactorizationMonoid.normalizedFactors M.charpoly, b = f := by
    intro b hb
    have hbi := UniqueFactorizationMonoid.irreducible_of_normalized_factor b hb
    have hbd := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hb
    have hbn := UniqueFactorizationMonoid.normalize_normalized_factor b hb
    have hbm : b.Monic := by
      rw [← hbn]; exact Polynomial.monic_normalize hbi.ne_zero
    have hbf := irreducible_dvd_of_dvd_charpoly_of_aeval_matrix M b f hbi hbd hf
    exact eq_of_monic_of_associated hbm hfm (hbi.associated_of_dvd hfi hbf)
  set n := Multiset.card (UniqueFactorizationMonoid.normalizedFactors M.charpoly)
  have hrep : UniqueFactorizationMonoid.normalizedFactors M.charpoly = Multiset.replicate n f :=
    Multiset.eq_replicate.mpr ⟨rfl, hmem⟩
  have hass := UniqueFactorizationMonoid.prod_normalizedFactors hc0
  rw [hrep, Multiset.prod_replicate] at hass
  have hcp : M.charpoly = f ^ n :=
    (eq_of_monic_of_associated (hfm.pow n) (Matrix.charpoly_monic M) hass).symm
  have hdeg : f.natDegree * n = f.natDegree * N := by
    have := congrArg Polynomial.natDegree hcp
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, hfm.natDegree_pow] at this
    rw [← hh]; linarith
  have hpos : 0 < f.natDegree := Irreducible.natDegree_pos hfi
  rw [hcp, Nat.eq_of_mul_eq_mul_left hpos hdeg]

end GlobalTheory
end

