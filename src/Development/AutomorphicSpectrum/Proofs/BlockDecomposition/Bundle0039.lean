import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelL2RowsColumns
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0017
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0016
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0049
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0018
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KerLinOfKerBasic
section
open PositivityTheory.Rg.BcB.E1

namespace GlobalTheory.CompanionTheory.KerLinear

theorem kerLin_of_kerBasic : KerBasic → KerLin := by
  intro hb X ι _ φ c hφ
  constructor
  · refine ⟨continuous_finsetSum _ fun i _ => (hφ i).1.mul continuous_const, ?_⟩
    have key : ∀ s : Finset ι, HasCompactSupport (fun y => ∑ i ∈ s, φ i y * c i) := by
      intro s
      induction s using Finset.cons_induction with
      | empty => exact (HasCompactSupport.zero : HasCompactSupport (0 : X.G → ℂ))
      | cons a s ha ih =>
        have h1 : HasCompactSupport (fun y => φ a y * c a) :=
          (hφ a).2.mul_right
        have h2 := h1.add ih
        have h3 : (fun y => ∑ i ∈ Finset.cons a s ha, φ i y * c i) =
            (fun y => φ a y * c a) + fun y => ∑ i ∈ s, φ i y * c i := by
          funext y
          simp [Finset.sum_cons]
        rw [h3]
        exact h2
    exact key Finset.univ
  · intro x y
    have hfin : ∀ i, (Function.support fun γ : X.Γ => φ i (x⁻¹ * (γ : X.G) * y)).Finite :=
      fun i => (hb X (φ i) (hφ i)).1 x y
    have hfin' : ∀ i ∈ (Finset.univ : Finset ι),
        (Function.support fun γ : X.Γ => φ i (x⁻¹ * (γ : X.G) * y) * c i).Finite := fun i _ =>
      (hfin i).subset (Function.support_mul_subset_left _ _)
    unfold ker
    rw [finsum_sum_comm _ _ hfin']
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [finsum_mul]

end GlobalTheory.CompanionTheory.KerLinear
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KerMulOfKerBasicOfCvTest
section
open MeasureTheory PositivityTheory.Rg.BcB.E1
open scoped ENNReal Pointwise

namespace GlobalTheory.CompanionTheory.KernelComposition

theorem integral_ker_mul_eq_unfolded (hk : KerBasic) (X : Ctx) (φ ψ : X.G → ℂ) (hφ : Tst φ)
    (hψ : Tst ψ) (x y : X.G) :
    ∫ z, ker X.Γ φ x z * ker X.Γ ψ z y ∂X.ν = ∫ z, φ (x⁻¹ * z) * ker X.Γ ψ z y ∂X.μ := by
  haveI : MeasurableConstSMul X.Γ X.G := ⟨fun γ => measurable_const_mul (γ : X.G)⟩
  haveI : SMulInvariantMeasure X.Γ X.G X.μ := ⟨fun γ s _ => measure_preimage_mul _ γ.1 s⟩
  set g : X.G → ℂ := fun z => φ (x⁻¹ * z) * ker X.Γ ψ z y with hg
  have hkc : Continuous fun z => ker X.Γ ψ z y :=
    (hk X ψ hψ).2.1.comp (continuous_id.prodMk continuous_const)
  have hgc : Continuous g := (hφ.1.comp (continuous_const.mul continuous_id)).mul hkc
  have hgs : HasCompactSupport g :=
    HasCompactSupport.mul_right (hφ.2.comp_homeomorph (Homeomorph.mulLeft x⁻¹))
  have hgi : Integrable g X.μ := hgc.integrable_of_hasCompactSupport hgs
  have hpt : ∀ z, ker X.Γ φ x z * ker X.Γ ψ z y = ∑' γ : X.Γ, g (γ • z) := by
    intro z
    have h1 : ∀ γ : X.Γ, g (γ • z) = φ (x⁻¹ * (γ : X.G) * z) * ker X.Γ ψ z y := by
      intro γ
      have h2 : γ • z = (γ : X.G) * z := rfl
      simp only [hg, h2, (hk X ψ hψ).2.2.1 γ γ.2 z y |>.1, mul_assoc]
    simp only [h1]
    rw [tsum_mul_right, ker, tsum_eq_finsum ((hk X φ hφ).1 x z)]
  have hmeas : ∀ γ : X.Γ, Continuous fun z => g (γ • z) := fun γ =>
    hgc.comp (continuous_const.mul continuous_id)
  have hfin : ∑' γ : X.Γ, ∫⁻ z, ‖g (γ • z)‖ₑ ∂X.ν ≠ ∞ := by
    have h3 : ∑' γ : X.Γ, ∫⁻ z, ‖g (γ • z)‖ₑ ∂X.ν = ∫⁻ z, ‖g z‖ₑ ∂X.μ :=
      (X.fd.lintegral_eq_tsum'' fun z => ‖g z‖ₑ).symm
    rw [h3]
    exact hgi.2.ne
  simp only [hpt]
  rw [integral_tsum (fun γ => (hmeas γ).aestronglyMeasurable) hfin]
  exact (X.fd.integral_eq_tsum'' g hgi).symm

theorem integral_shifted_eq_ker_cv (hc : CvTest) (X : Ctx) (φ ψ : X.G → ℂ) (hφ : Tst φ)
    (hψ : Tst ψ) (x y : X.G) :
    ∫ z, φ z * ker X.Γ ψ (x * z) y ∂X.μ = ker X.Γ (cv X.μ φ ψ) x y := by
  have hC : IsCompact ((fun w => x * w * y⁻¹) '' (tsupport φ * tsupport ψ)) :=
    (hφ.2.isCompact.mul hψ.2.isCompact).image (by fun_prop)
  have hfin := X.proper _ hC
  set s : Finset X.Γ := hfin.toFinset with hs
  have hmem : ∀ γ : X.Γ, x⁻¹ * (γ : X.G) * y ∈ tsupport φ * tsupport ψ → γ ∈ s := by
    intro γ h
    rw [hs, Set.Finite.mem_toFinset]
    exact ⟨_, h, by simp [mul_assoc]⟩
  have h1 : ∀ z, φ z * ker X.Γ ψ (x * z) y =
      ∑ γ ∈ s, φ z * ψ (z⁻¹ * (x⁻¹ * (γ : X.G) * y)) := by
    intro z
    by_cases hz : z ∈ tsupport φ
    · rw [ker, finsum_eq_sum_of_support_subset (s := s), Finset.mul_sum]
      · refine Finset.sum_congr rfl fun γ _ => ?_
        simp only [mul_inv_rev, mul_assoc]
      · intro γ hγ
        refine Finset.mem_coe.2 (hmem γ ?_)
        have hγ' : (x * z)⁻¹ * (γ : X.G) * y ∈ tsupport ψ := subset_tsupport _ hγ
        refine ⟨z, hz, _, hγ', ?_⟩
        simp [mul_assoc]
    · simp [image_eq_zero_of_notMem_tsupport hz]
  have hint : ∀ w : X.G, Integrable (fun z => φ z * ψ (z⁻¹ * w)) X.μ := by
    intro w
    have hcont : Continuous fun z => φ z * ψ (z⁻¹ * w) :=
      hφ.1.mul (hψ.1.comp (continuous_inv.mul continuous_const))
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.mul_right hφ.2)
  simp only [h1]
  rw [integral_finset_sum _ fun γ _ => hint _, ker,
    finsum_eq_sum_of_support_subset (s := s)]
  · rfl
  · intro γ hγ
    exact Finset.mem_coe.2 (hmem γ ((hc X φ ψ hφ hψ).2.1 hγ))

theorem kerMul_of_kerBasic_of_cvTest : KerBasic → CvTest → KerMul := by
  intro hk hc X φ ψ hφ hψ x y
  rw [integral_ker_mul_eq_unfolded hk X φ ψ hφ hψ x y,
    ← integral_shifted_eq_ker_cv hc X φ ψ hφ hψ x y,
    ← integral_mul_left_eq_self (fun z => φ (x⁻¹ * z) * ker X.Γ ψ z y) x]
  simp

end GlobalTheory.CompanionTheory.KernelComposition
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelBaseChangeTowerEquivStatement
section
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_base_change_tower_equiv : ∀ (R A K Q P : Type) [CommRing R] [CommRing A] [CommRing K] [Algebra R A] [Algebra A K] [Algebra R K] [IsScalarTower R A K] [AddCommGroup Q] [Module R Q] [AddCommGroup P] [Module R P] (d : Q →ₗ[R] P), Nonempty (LinearMap.ker ((d.baseChange A).baseChange K) ≃ₗ[K] LinearMap.ker (d.baseChange K)) := by
  first | exact @GlobalTheory.CompanionTheory.PerfectFirstCohomology.ker_baseChange_tower | exact GlobalTheory.CompanionTheory.PerfectFirstCohomology.ker_baseChange_tower | (intros; apply GlobalTheory.CompanionTheory.PerfectFirstCohomology.ker_baseChange_tower <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelFreeAtPrimesOfConstantRankStatement
section
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_free_at_primes_of_constant_rank : ∀ (R Q P : Type) [CommRing R] [AddCommGroup Q] [Module R Q] [AddCommGroup P] [Module R P] (d : Q →ₗ[R] P) (g : ℕ), Module.Finite R (LinearMap.ker d) → Module.Projective R (LinearMap.ker d) → (∀ p : PrimeSpectrum R, Module.rankAtStalk (LinearMap.ker d) p = g) → ∀ (p : Ideal R) [p.IsPrime], Module.Free (Localization.AtPrime p) (LinearMap.ker (d.baseChange (Localization.AtPrime p))) ∧ Module.Finite (Localization.AtPrime p) (LinearMap.ker (d.baseChange (Localization.AtPrime p))) ∧ Module.finrank (Localization.AtPrime p) (LinearMap.ker (d.baseChange (Localization.AtPrime p))) = g := by
  first | exact @GlobalTheory.CompanionTheory.KerLocal.ker_baseChange_localization_free | exact GlobalTheory.CompanionTheory.KerLocal.ker_baseChange_localization_free | (intros; apply GlobalTheory.CompanionTheory.KerLocal.ker_baseChange_localization_free <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelRowsColumnsSquareIntegrable
section
open MeasureTheory
open scoped ENNReal Pointwise
open PositivityTheory.Rg.BcB.E1

namespace GlobalTheory.CompanionTheory.KerSquare

theorem memLp_column (hK : KerBasic) (hC : CntBasic) (hS : ColSq) (X : Ctx) (φ : X.G → ℂ)
    (hφ : Tst φ) (y : X.G) : MemLp (fun x => ker X.Γ φ x y) 2 X.ν := by
  have hcont : Continuous fun x => ker X.Γ φ x y :=
    (hK X φ hφ).2.1.comp (continuous_id.prodMk continuous_const)
  refine ⟨hcont.aestronglyMeasurable, ?_⟩
  obtain ⟨B, hB⟩ := hφ.1.bounded_above_of_compact_support hφ.2
  have hΩ : IsCompact (tsupport φ) := hφ.2
  have hbound := hS X φ B (tsupport φ) hφ hB hΩ (subset_tsupport φ) y
  have hμ : X.μ (tsupport φ)⁻¹ ≠ ⊤ := hΩ.inv.measure_lt_top.ne
  have hcnt : cnt X.Γ ((tsupport φ)⁻¹ * tsupport φ) y ≠ ⊤ :=
    (hC X).1 _ (hΩ.inv.mul hΩ) y
  have hfin : ENNReal.ofReal B ^ 2 * X.μ (tsupport φ)⁻¹ *
      cnt X.Γ ((tsupport φ)⁻¹ * tsupport φ) y < ⊤ :=
    ENNReal.mul_lt_top
      (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) hμ.lt_top) hcnt.lt_top
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat]
  exact hbound.trans_lt hfin

theorem memLp_row (hK : KerBasic) (hC : CntBasic) (hS : ColSq) (X : Ctx) (φ : X.G → ℂ)
    (hφ : Tst φ) (x : X.G) : MemLp (fun y => ker X.Γ φ x y) 2 X.ν := by
  obtain ⟨-, hcont, -, hadj, hconj, -⟩ := hK X φ hφ
  have hc : Continuous fun y => ker X.Γ φ x y :=
    hcont.comp (continuous_const.prodMk continuous_id)
  refine (memLp_column hK hC hS X (adj φ) hadj x).of_le hc.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  rw [hconj y x, RCLike.norm_conj]

theorem kernel_rows_columns_square_integrable : KerBasic → CntBasic → ColSq → KernelL2RowsColumns := fun hK hC hS X φ hφ =>
  ⟨memLp_column hK hC hS X φ hφ, memLp_row hK hC hS X φ hφ⟩

end GlobalTheory.CompanionTheory.KerSquare
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeAnnihilatorWithinNhdsStatement
section
open Matrix
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_annihilator_within_nhds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (U : Set (Fin n → k)), U ∈ nhds (0 : Fin n → k) → ∃ A : AddSubgroup (Fin n → k), IsCompact (A : Set (Fin n → k)) ∧ IsOpen (A : Set (Fin n → k)) ∧ {ξ : Fin n → k | ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1} ⊆ U := by
  first | exact @GlobalTheory.CompanionTheory.AnnihShrink.exists_compact_open_annihilator_subset | exact GlobalTheory.CompanionTheory.AnnihShrink.exists_compact_open_annihilator_subset | (intros; apply GlobalTheory.CompanionTheory.AnnihShrink.exists_compact_open_annihilator_subset <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeSumDecayBound
section
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Count

theorem one_dim_step (b x : ℝ) (hb : 0 < b) (hx : 0 ≤ x) :
    ((1 + (x + 1) / b) ^ 2)⁻¹ ≤ b ^ 2 / (b + x) - b ^ 2 / (b + x + 1) := by
  have h1 : 0 < b + x := by linarith
  have h2 : 0 < b + x + 1 := by linarith
  have e1 : (1 + (x + 1) / b) = (b + x + 1) / b := by field_simp; ring
  have e2 : b ^ 2 / (b + x) - b ^ 2 / (b + x + 1) = b ^ 2 / ((b + x) * (b + x + 1)) := by
    field_simp; ring
  rw [e1, e2, div_pow, inv_div]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  nlinarith

theorem one_dim_partial (b : ℝ) (hb : 0 < b) (N : ℕ) :
    ∑ k ∈ Finset.range N, ((1 + ((k : ℝ) + 1) / b) ^ 2)⁻¹ ≤ b - b ^ 2 / (b + N) := by
  induction N with
  | zero =>
    have : b ^ 2 / (b + ((0 : ℕ) : ℝ)) = b := by
      simp only [Nat.cast_zero, add_zero]; field_simp
    rw [Finset.range_zero, Finset.sum_empty, this, sub_self]
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have := one_dim_step b N hb (Nat.cast_nonneg N)
    push_cast
    have e : b + ((N : ℝ) + 1) = b + N + 1 := by ring
    rw [e]
    linarith

theorem one_dim_nat (b : ℝ) (hb : 0 < b) :
    ∑' k : ℕ, ENNReal.ofReal (((1 + ((k : ℝ) + 1) / b) ^ 2)⁻¹) ≤ ENNReal.ofReal b := by
  rw [ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun N => ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have := one_dim_partial b hb N
  have h3 : 0 ≤ b ^ 2 / (b + N) := by positivity
  linarith

theorem one_dim (b : ℝ) (hb : 0 < b) :
    ∑' n : ℤ, ENNReal.ofReal (((1 + |(n : ℝ)| / b) ^ 2)⁻¹) ≤ ENNReal.ofReal (1 + 2 * b) := by
  set f : ℤ → ℝ≥0∞ := fun n => ENNReal.ofReal (((1 + |(n : ℝ)| / b) ^ 2)⁻¹) with hf
  have hsplit : HasSum f ((∑' n : ℕ, f n) + ∑' n : ℕ, f (-((n : ℤ) + 1))) :=
    HasSum.of_nat_of_neg_add_one ENNReal.summable.hasSum ENNReal.summable.hasSum
  have hneg : ∀ n : ℕ, f (-((n : ℤ) + 1)) =
      ENNReal.ofReal (((1 + ((n : ℝ) + 1) / b) ^ 2)⁻¹) := by
    intro n
    have : |(((-((n : ℤ) + 1) : ℤ)) : ℝ)| = (n : ℝ) + 1 := by
      push_cast
      rw [abs_neg, abs_of_nonneg (by positivity)]
    simp only [hf, this]
  have hpos : ∀ n : ℕ, f ((n + 1 : ℕ) : ℤ) =
      ENNReal.ofReal (((1 + ((n : ℝ) + 1) / b) ^ 2)⁻¹) := by
    intro n
    have : |((((n + 1 : ℕ) : ℤ)) : ℝ)| = (n : ℝ) + 1 := by
      push_cast
      rw [abs_of_nonneg (by positivity)]
    simp only [hf, this]
  have h0 : f ((0 : ℕ) : ℤ) = 1 := by simp [hf]
  have hN := one_dim_nat b hb
  have hz : ∑' n : ℕ, f n ≤ 1 + ENNReal.ofReal b := by
    rw [ENNReal.tsum_eq_iSup_nat]
    refine iSup_le fun N => ?_
    cases N with
    | zero => simp
    | succ N =>
      rw [Finset.sum_range_succ', h0, add_comm]
      gcongr
      calc ∑ k ∈ Finset.range N, f ((k + 1 : ℕ) : ℤ)
          ≤ ∑' k : ℕ, f ((k + 1 : ℕ) : ℤ) := ENNReal.sum_le_tsum _
        _ ≤ ENNReal.ofReal b := by rw [tsum_congr hpos]; exact hN
  rw [hsplit.tsum_eq, tsum_congr hneg]
  calc _ ≤ 1 + ENNReal.ofReal b + ENNReal.ofReal b := add_le_add hz hN
    _ = ENNReal.ofReal (1 + 2 * b) := by
      rw [two_mul, ← add_assoc, ENNReal.ofReal_add (by positivity) hb.le,
        ENNReal.ofReal_add (by norm_num) hb.le, ENNReal.ofReal_one]

theorem multi_dim {P : Type} [Fintype P] (g : P → ℤ → ℝ≥0∞) :
    ∑' x : P → ℤ, ∏ p, g p (x p) ≤ ∏ p, ∑' n, g p n :=
  _root_.UpperTheory.Reformulated.B.MultiDimensional.multi_dim g

theorem tsum_le_prod_of_injOn {S P : Type} [Fintype P] (m : S → P → ℤ) (b : P → ℝ)
    (hb : ∀ p, 0 < b p) (h : S → ℝ≥0∞) (hinj : Set.InjOn m {ξ | h ξ ≠ 0})
    (hh : ∀ ξ, h ξ ≤ ∏ p, ENNReal.ofReal (((1 + |(m ξ p : ℝ)| / b p) ^ 2)⁻¹)) :
    ∑' ξ, h ξ ≤ ∏ p, ENNReal.ofReal (1 + 2 * b p) := by
  set g : P → ℤ → ℝ≥0∞ := fun p n => ENNReal.ofReal (((1 + |(n : ℝ)| / b p) ^ 2)⁻¹) with hg
  have hsupp : ∑' ξ, h ξ = ∑' ξ : {ξ | h ξ ≠ 0}, h ξ :=
    (tsum_subtype_eq_of_support_subset (f := h) (s := {ξ | h ξ ≠ 0})
      (fun _ hx => hx)).symm
  have hinj' : Function.Injective (fun ξ : {ξ | h ξ ≠ 0} => m ξ) :=
    fun x y hxy => Subtype.ext (hinj x.2 y.2 hxy)
  calc ∑' ξ, h ξ = ∑' ξ : {ξ | h ξ ≠ 0}, h ξ := hsupp
    _ ≤ ∑' ξ : {ξ | h ξ ≠ 0}, (fun x : P → ℤ => ∏ p, g p (x p)) (m ξ) :=
        ENNReal.tsum_le_tsum fun ξ => hh ξ
    _ ≤ ∑' x : P → ℤ, ∏ p, g p (x p) :=
        ENNReal.tsum_comp_le_tsum_of_injective hinj' _
    _ ≤ ∏ p, ∑' n, g p n := multi_dim g
    _ ≤ ∏ p, ENNReal.ofReal (1 + 2 * b p) :=
        Finset.prod_le_prod' fun p _ => one_dim (b p) (hb p)

end GlobalTheory.CompanionTheory.Count
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeOneOfPowerBoundsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.le_one_of_power_bounds : ∀ (δ r : ℝ), 0 < δ → δ < 1 → 0 ≤ r → (∀ ε : ℝ, 0 < ε → δ⁻¹ * (Real.sqrt δ * r) ^ (2 + ε) < 1) → r ≤ 1 := by
  first | exact @GlobalTheory.CompanionTheory.Casselman.le_one_of_forall_sqrt_mul_rpow_lt | exact GlobalTheory.CompanionTheory.Casselman.le_one_of_forall_sqrt_mul_rpow_lt | (intros; apply GlobalTheory.CompanionTheory.Casselman.le_one_of_forall_sqrt_mul_rpow_lt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftCommLTensorNatural
section
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.Dblock.AmiBc

theorem leftComm_lTensor_natural {A B C M N : Type} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup C] [Module A C] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (d : M →ₗ[A] N) (c : C) (w : B ⊗[A] M) :
    (d.lTensor C).lTensor B (TensorProduct.leftComm A C B M (c ⊗ₜ[A] w)) =
      TensorProduct.leftComm A C B N (c ⊗ₜ[A] (d.lTensor B w)) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul b m => simp [TensorProduct.leftComm_tmul]
  | add x y hx hy =>
    simp only [TensorProduct.tmul_add, map_add, hx, hy]

theorem contraction_lTensor :
    ∀ (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (C : Type) [AddCommGroup C] [Module A C] (K : ℕ → Type) [∀ n, AddCommGroup (K n)] [∀ n, Module A (K n)] (d : ∀ n, K n →ₗ[A] K (n + 1)) (H : ∀ n, K (n + 1) →ₗ[A] B ⊗[A] K n), ((∀ z, H 0 (d 0 z) = (1 : B) ⊗ₜ[A] z) ∧ ∀ n z, (d n).lTensor B (H n z) + H (n + 1) (d (n + 1) z) = (1 : B) ⊗ₜ[A] z) → ∃ H₁ : ∀ n, C ⊗[A] K (n + 1) →ₗ[A] B ⊗[A] (C ⊗[A] K n), (∀ z, H₁ 0 ((d 0).lTensor C z) = (1 : B) ⊗ₜ[A] z) ∧ ∀ n z, ((d n).lTensor C).lTensor B (H₁ n z) + H₁ (n + 1) ((d (n + 1)).lTensor C z) = (1 : B) ⊗ₜ[A] z := by
  intro A _ B _ _ C _ _ K _ _ d H ⟨h0, hS⟩
  refine ⟨fun n => (TensorProduct.leftComm A C B (K n)).toLinearMap ∘ₗ (H n).lTensor C, ?_, ?_⟩
  · intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul c k =>
      simp [h0, TensorProduct.leftComm_tmul]
    | add x y hx hy =>
      simp only [map_add, hx, hy, TensorProduct.tmul_add]
  · intro n z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul c k =>
      have key := congrArg (fun t => TensorProduct.leftComm A C B (K (n + 1)) (c ⊗ₜ[A] t)) (hS n k)
      simp only [TensorProduct.tmul_add, map_add] at key
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.lTensor_tmul]
      rw [leftComm_lTensor_natural, key, TensorProduct.leftComm_tmul]
    | add x y hx hy =>
      simp only [map_add, TensorProduct.tmul_add]
      rw [← hx, ← hy]
      abel

end GlobalTheory.CompanionTheory.Dblock.AmiBc
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieAlgebraFunctionCalculusStatement
section
open Matrix Topology Filter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_algebra_function_calculus : ∀ {n : ℕ} (𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (h : Fin n → ℝ), Matrix.diagonal (fun i => (h i : ℂ)) ∈ 𝔤 → (∀ X ∈ 𝔤, ∀ Y ∈ 𝔤, X * Y - Y * X ∈ 𝔤) → ∀ (f : ℝ → ℝ), ∀ X ∈ 𝔤, (Matrix.of fun i j => (f (h i - h j) : ℂ) * X i j) ∈ 𝔤 := by
  first | exact @GlobalTheory.CompanionTheory.AdProj.mem_of_entrywise | exact GlobalTheory.CompanionTheory.AdProj.mem_of_entrywise | (intros; apply GlobalTheory.CompanionTheory.AdProj.mem_of_entrywise <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieAlgebraStarClosedBracketStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolic_stabilizer_block_unit : ∀ {n D m : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) (J' : Matrix (Fin m) (Fin m) ℂ) (C : Matrix (Fin n) (Fin D) ℂ) (R : Matrix (Fin n) (Fin m) ℂ), J * J = 1 → Jᴴ = J → Cᴴ * C = 1 → Rᴴ * R = 1 → J * R = R * J' → Cᴴ * R = 0 → C * Cᴴ + J * C * Cᴴ * J + R * Rᴴ = 1 → ∀ (g : Matrix (Fin n) (Fin n) ℂ) (h : Matrix (Fin D) (Fin D) ℂ), gᴴ * J * g = J → g * C = C * h → gᴴ * C = C * hᴴ → IsUnit h ∧ g * (J * C) = (J * C) * (hᴴ)⁻¹ ∧ g * R = R * (Rᴴ * g * R) ∧ (Rᴴ * g * R)ᴴ * J' * (Rᴴ * g * R) = J' := by
  first | exact @GlobalTheory.CompanionTheory.UnitaryBlock.block_diagonal_of_keeps_frame | exact GlobalTheory.CompanionTheory.UnitaryBlock.block_diagonal_of_keeps_frame | (intros; apply GlobalTheory.CompanionTheory.UnitaryBlock.block_diagonal_of_keeps_frame <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftIdempotentAdicComplete
section
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.IdemLift

theorem sub_pow_three_eq {R : Type*} [CommRing R] {a b : R}
    (ha : IsIdempotentElem a) (hb : IsIdempotentElem b) : (a - b) ^ 3 = a - b := by
  have ha' : a * a = a := ha
  have hb' : b * b = b := hb
  linear_combination (a + 1 - 3 * b) * ha' + (3 * a - b - 1) * hb'

theorem eq_of_isNilpotent_sub {R : Type*} [CommRing R] {a b : R}
    (ha : IsIdempotentElem a) (hb : IsIdempotentElem b) (h : IsNilpotent (a - b)) : a = b := by
  obtain ⟨n, hn⟩ := h
  have h3 := sub_pow_three_eq ha hb
  have hpow : ∀ m : ℕ, (a - b) ^ (2 * m + 1) = a - b := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc (a - b) ^ (2 * (m + 1) + 1) = (a - b) ^ (2 * m + 1) * (a - b) ^ 2 := by ring
        _ = (a - b) ^ 3 := by rw [ih]; ring
        _ = a - b := h3
  have h0 : a - b = 0 := by
    rw [← hpow n, show 2 * n + 1 = n + (n + 1) by ring, pow_add, hn, zero_mul]
  exact sub_eq_zero.1 h0

theorem eq_of_sub_mem_jacobson {R : Type*} [CommRing R] {a b : R}
    (ha : IsIdempotentElem a) (hb : IsIdempotentElem b)
    (h : a - b ∈ Ideal.jacobson (⊥ : Ideal R)) : a = b := by
  have hu : IsUnit ((a - b) * (-(a - b)) + 1) := Ideal.mem_jacobson_bot.1 h _
  have h3 := sub_pow_three_eq ha hb
  have hz : (a - b) * ((a - b) * (-(a - b)) + 1) = 0 := by
    linear_combination -h3
  exact sub_eq_zero.1 ((hu.mul_left_eq_zero).1 hz)

theorem existsUnique_idempotent_lift {S : Type} [CommRing S] (ϖ : S)
    [IsAdicComplete (Ideal.span {ϖ}) S] (k : ℕ) (hk : k ≠ 0)
    (e : S ⧸ Ideal.span {ϖ ^ k}) (he : IsIdempotentElem e) :
    ∃! e' : S, IsIdempotentElem e' ∧ Ideal.Quotient.mk (Ideal.span {ϖ ^ k}) e' = e := by
  have hJI : Ideal.span {ϖ ^ k} ≤ Ideal.span {ϖ} := by
    rw [Ideal.span_singleton_le_span_singleton]
    exact dvd_pow_self ϖ hk
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective e
  have haJ : a * a - a ∈ Ideal.span {ϖ ^ k} := by
    apply Ideal.Quotient.eq_zero_iff_mem.1
    have he' : Ideal.Quotient.mk (Ideal.span {ϖ ^ k}) a * Ideal.Quotient.mk _ a
        = Ideal.Quotient.mk _ a := he
    rw [map_sub, map_mul, he', sub_self]
  have haI : a * a - a ∈ Ideal.span {ϖ} := hJI haJ
  have hH : HenselianRing S (Ideal.span {ϖ}) := IsAdicComplete.henselianRing S _
  have hmon : ((Polynomial.X : Polynomial S) ^ 2 - Polynomial.X).Monic := by
    apply Polynomial.monic_X_pow_sub
    simpa using lt_of_le_of_lt Polynomial.degree_X_le (by norm_num : (1 : WithBot ℕ) < 2)
  have heval : ((Polynomial.X : Polynomial S) ^ 2 - Polynomial.X).eval a ∈ Ideal.span {ϖ} := by
    have : ((Polynomial.X : Polynomial S) ^ 2 - Polynomial.X).eval a = a * a - a := by
      simp [sq]
    rwa [this]
  have hunit : IsUnit (Ideal.Quotient.mk (Ideal.span {ϖ})
      (Polynomial.derivative ((Polynomial.X : Polynomial S) ^ 2 - Polynomial.X) |>.eval a)) := by
    have hd : (Polynomial.derivative ((Polynomial.X : Polynomial S) ^ 2 - Polynomial.X)).eval a
        = 2 * a - 1 := by
      simp
      ring
    rw [hd]
    have hsq : Ideal.Quotient.mk (Ideal.span {ϖ}) (2 * a - 1)
        * Ideal.Quotient.mk (Ideal.span {ϖ}) (2 * a - 1) = 1 := by
      rw [← map_mul, ← map_one (Ideal.Quotient.mk (Ideal.span {ϖ}))]
      apply Ideal.Quotient.eq.2
      have : (2 * a - 1) * (2 * a - 1) - 1 = 4 * (a * a - a) := by ring
      rw [this]
      exact Ideal.mul_mem_left _ _ haI
    exact IsUnit.of_mul_eq_one _ hsq
  obtain ⟨y, hy, hya⟩ := hH.is_henselian _ hmon a heval hunit
  have hyid : IsIdempotentElem y := by
    have : y ^ 2 - y = 0 := by simpa [Polynomial.IsRoot] using hy
    have h2 : y * y - y = 0 := by rw [← sq]; exact this
    exact sub_eq_zero.1 h2
  have hlift : Ideal.Quotient.mk (Ideal.span {ϖ ^ k}) y = Ideal.Quotient.mk _ a := by
    apply eq_of_isNilpotent_sub (hyid.map (Ideal.Quotient.mk _)) he
    refine ⟨k, ?_⟩
    rw [← map_sub, ← map_pow]
    apply Ideal.Quotient.eq_zero_iff_mem.2
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 hya
    rw [hc, mul_pow]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  refine ⟨y, ⟨hyid, hlift⟩, ?_⟩
  rintro z ⟨hz, hza⟩
  apply eq_of_sub_mem_jacobson hz hyid
  apply IsAdicComplete.le_jacobson_bot (Ideal.span {ϖ})
  apply hJI
  apply Ideal.Quotient.eq.1
  rw [hza, hlift]

end GlobalTheory.CompanionTheory.IdemLift
end

