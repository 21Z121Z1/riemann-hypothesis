import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.HeisenbergTheta.HeisenbergThetaConstant.ThetaC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBruhatUniformSummableMajorant
import GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0064
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0176
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0183
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0194
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0196
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSummableMajorantLatticeSum
section
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.EisRkNBound

open NumberField NumberField.mixedEmbedding IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
  Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing SchwartzMap Classical nonZeroDivisors Pointwise
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix GlobalTheory.CompanionTheory.EisRk1Bound

set_option synthInstance.maxSize 1000

noncomputable section

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem summable_prod_coord {α : Type*} {g : α → ℝ} (h0 : ∀ x, 0 ≤ g x) (hg : Summable g) :
    Summable fun ξ : ι → α ↦ ∏ i, g (ξ i) :=
  _root_.UpperTheory.Reformulated.B.Qo1.summable_prod_coord h0 hg

theorem inv_mulVec_mulVec (x : ι → 𝔸[K]) (h : GL ι 𝔸[K]) :
    ((h⁻¹ : GL ι 𝔸[K]) : Matrix ι ι 𝔸[K]) *ᵥ ((h : Matrix ι ι 𝔸[K]) *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem continuous_inv_entry (i j : ι) :
    Continuous fun h : GL ι 𝔸[K] ↦ ((h⁻¹ : GL ι 𝔸[K]) : Matrix ι ι 𝔸[K]) i j := by
  have h : Continuous fun h : GL ι 𝔸[K] ↦ ((h⁻¹ : GL ι 𝔸[K]) : Matrix ι ι 𝔸[K]) :=
    Units.continuous_val.comp continuous_inv
  exact h.matrix_elem i j

omit [DecidableEq ι] in

theorem finPartPi_mulVec (M : Matrix ι ι 𝔸[K]) (x : ι → 𝔸[K]) :
    finPartPi (M *ᵥ x) = M.map Adele2.finRingHom *ᵥ finPartPi x := by
  funext i
  show Adele2.finRingHom (∑ j, M i j * x j) = _
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ ↦ map_mul _ _ _

omit [DecidableEq ι] in

theorem infPartPi_mulVec (M : Matrix ι ι 𝔸[K]) (x : ι → 𝔸[K]) :
    infPartPi (M *ᵥ x) = M.map Adele2.infRingHom *ᵥ infPartPi x := by
  funext i
  show Adele2.infRingHom (∑ j, M i j * x j) = _
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ ↦ map_mul _ _ _

omit [DecidableEq ι] in

theorem norm_mulVec_le (M : Matrix ι ι (mixedSpace K)) (u : ι → mixedSpace K) :
    ‖M *ᵥ u‖ ≤ (∑ i, ∑ j, ‖M i j‖) * ‖u‖ := by
  have hc : 0 ≤ ∑ i, ∑ j, ‖M i j‖ :=
    Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hc (norm_nonneg _))).mpr fun i ↦ ?_
  calc ‖(M *ᵥ u) i‖ = ‖∑ j, M i j * u j‖ := rfl
    _ ≤ ∑ j, ‖M i j * u j‖ := norm_sum_le _ _
    _ ≤ ∑ j, ‖M i j‖ * ‖u‖ := Finset.sum_le_sum fun j _ ↦
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm u j) (norm_nonneg _))
    _ = (∑ j, ‖M i j‖) * ‖u‖ := by rw [Finset.sum_mul]
    _ ≤ (∑ i, ∑ j, ‖M i j‖) * ‖u‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact Finset.single_le_sum (f := fun i ↦ ∑ j, ‖M i j‖)
          (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ norm_nonneg _) (Finset.mem_univ i)

theorem exists_fractionalIdeal_of_isCompact (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (b : ι → 𝔸ᶠ[K])
    {C : Set (GL ι 𝔸[K])} (hC : IsCompact C) :
    ∃ J : (FractionalIdeal (𝓞 K)⁰ K)ˣ, ∀ h ∈ C, ∀ ξ : ι → K,
      (∀ i, finPartPi ((h : Matrix ι ι 𝔸[K]) *ᵥ fun i ↦ algebraMap K 𝔸[K] (ξ i)) i - b i ∈
        idealFiniteAdeles I) → ∀ i, ξ i ∈ (J : FractionalIdeal (𝓞 K)⁰ K) := by
  set B : Set (ι → 𝔸ᶠ[K]) :=
    Set.pi Set.univ fun i ↦ b i +ᵥ (idealFiniteAdeles I : Set 𝔸ᶠ[K])
  have hB : IsCompact B := isCompact_univ_pi fun i ↦ (isCompact_idealFiniteAdeles I).vadd (b i)
  let T : GL ι 𝔸[K] × (ι → 𝔸ᶠ[K]) → ι → 𝔸ᶠ[K] := fun p ↦
    (((p.1⁻¹ : GL ι 𝔸[K]) : Matrix ι ι 𝔸[K]).map Adele2.finRingHom) *ᵥ p.2
  have hT : Continuous T := by
    refine continuous_pi fun i ↦ ?_
    simp only [T, Matrix.mulVec, dotProduct, Matrix.map_apply]
    refine continuous_finset_sum _ fun j _ ↦ ?_
    exact (continuous_finRingHom.comp ((continuous_inv_entry i j).comp continuous_fst)).mul
      ((continuous_apply j).comp continuous_snd)
  set S : Set 𝔸ᶠ[K] := ⋃ i : ι, (fun x : ι → 𝔸ᶠ[K] ↦ x i) '' (T '' (C ×ˢ B))
  have hS : IsCompact S := isCompact_iUnion fun i ↦
    ((hC.prod hB).image hT).image (continuous_apply i)
  obtain ⟨d, hd0, hd⟩ := exists_mul_mem_integralFiniteAdeles_of_isCompact hS
  set dK := algebraMap (𝓞 K) K d
  have hdK : dK ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hd0
  refine ⟨Units.mk0 (FractionalIdeal.spanSingleton (𝓞 K)⁰ dK⁻¹)
    ((FractionalIdeal.spanSingleton_ne_zero_iff).mpr (inv_ne_zero hdK)), ?_⟩
  intro h hh ξ hξ i
  set X : ι → 𝔸[K] := fun i ↦ algebraMap K 𝔸[K] (ξ i)
  have hTX : T (h, finPartPi ((h : Matrix ι ι 𝔸[K]) *ᵥ X)) =
      fun i ↦ algebraMap K 𝔸ᶠ[K] (ξ i) := by
    show _ *ᵥ finPartPi ((h : Matrix ι ι 𝔸[K]) *ᵥ X) = _
    rw [← finPartPi_mulVec, inv_mulVec_mulVec, finPartPi_algebraMap]
  have hmem : algebraMap K 𝔸ᶠ[K] (ξ i) ∈ S := by
    have hp : finPartPi ((h : Matrix ι ι 𝔸[K]) *ᵥ X) ∈ B := fun j _ ↦
      mem_vadd_idealFiniteAdeles.mpr (hξ j)
    have hq : (fun i ↦ algebraMap K 𝔸ᶠ[K] (ξ i)) ∈ T '' (C ×ˢ B) :=
      ⟨(h, finPartPi ((h : Matrix ι ι 𝔸[K]) *ᵥ X)), ⟨hh, hp⟩, hTX⟩
    exact Set.mem_iUnion.mpr ⟨i, _, hq, rfl⟩
  have h1 := hd _ hmem
  rw [← map_mul] at h1
  have h2 : dK * ξ i ∈ ((1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [← algebraMap_mem_idealFiniteAdeles_iff, ← SetLike.mem_coe, idealFiniteAdeles_one]
    exact h1
  rw [Units.val_one] at h2
  obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).mp h2
  refine (FractionalIdeal.mem_spanSingleton _).mpr ⟨r, ?_⟩
  rw [Algebra.smul_def, hr, mul_comm dK, mul_assoc, mul_inv_cancel₀ hdK, mul_one]

theorem summable_latticeWeight_prod (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Summable fun ξ : ι → K ↦
      ∏ i, latticeWeight J (Module.finrank ℤ (idealLattice K J) + 1) (ξ i) :=
  summable_prod_coord (latticeWeight_nonneg J _)
    (summable_ite_mem_of_summable_idealLattice J
      (h := fun x ↦ ((1 + ‖x‖) ^ (Module.finrank ℤ (idealLattice K J) + 1))⁻¹)
      (summable_inv_one_add_norm_pow_idealLattice J))

theorem exists_summable_bound_tensor_cosetIndicator (φ : 𝓢(ι → mixedSpace K, ℂ))
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (b : ι → 𝔸ᶠ[K]) {C : Set (GL ι 𝔸[K])}
    (hC : IsCompact C) :
    ∃ u : (ι → K) → ℝ, Summable u ∧ ∀ h ∈ C, ∀ ξ : ι → K,
      ‖schwartzBruhatTensorPi φ (finiteTensor fun i ↦ cosetIndicator I (b i))
        ((h : Matrix ι ι 𝔸[K]) *ᵥ fun i ↦ algebraMap K 𝔸[K] (ξ i))‖ ≤ u ξ := by
  obtain ⟨J, hJ⟩ := exists_fractionalIdeal_of_isCompact I b hC
  set k := Module.finrank ℤ (idealLattice K J) + 1
  set n := Fintype.card ι
  obtain ⟨A, hA, hφ⟩ := exists_norm_le_inv_one_add_pow φ (k * n)
  let c : GL ι 𝔸[K] → ℝ := fun h ↦ ∑ i, ∑ j,
    ‖(((h⁻¹ : GL ι 𝔸[K]) : Matrix ι ι 𝔸[K]).map Adele2.infRingHom) i j‖
  have hc : Continuous c := continuous_finset_sum _ fun i _ ↦ continuous_finset_sum _ fun j _ ↦
    (continuous_infRingHom.comp (continuous_inv_entry i j)).norm
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hc.continuousOn
  set B' := max B 1
  have hB'1 : 1 ≤ B' := le_max_right _ _
  have hB'0 : 0 < B' := zero_lt_one.trans_le hB'1
  refine ⟨fun ξ ↦ A * B' ^ (k * n) * ∏ i, latticeWeight J k (ξ i),
    (summable_latticeWeight_prod J).mul_left _, ?_⟩
  intro h hh ξ
  have hu0 : 0 ≤ A * B' ^ (k * n) * ∏ i, latticeWeight J k (ξ i) :=
    mul_nonneg (by positivity) (Finset.prod_nonneg fun i _ ↦ latticeWeight_nonneg J k _)
  set X : ι → 𝔸[K] := fun i ↦ algebraMap K 𝔸[K] (ξ i)
  set Y := (h : Matrix ι ι 𝔸[K]) *ᵥ X
  simp only [schwartzBruhatTensorPi, finiteTensor]
  by_cases hm : ∀ i, finPartPi Y i - b i ∈ idealFiniteAdeles I
  · have h1 : ∏ i, cosetIndicator I (b i) (finPartPi Y i) = 1 :=
      Finset.prod_eq_one fun i _ ↦ by rw [cosetIndicator_apply, if_pos (hm i)]
    rw [h1, mul_one]
    have hξJ := hJ h hh ξ hm
    have hw : ∀ i, latticeWeight J k (ξ i) = ((1 + ‖mixedEmbedding K (ξ i)‖) ^ k)⁻¹ :=
      fun i ↦ if_pos (hξJ i)
    simp only [hw]
    set y := infPartPi Y
    have hy : embPi K ξ =
        (((h⁻¹ : GL ι 𝔸[K]) : Matrix ι ι 𝔸[K]).map Adele2.infRingHom) *ᵥ y := by
      rw [← infPartPi_mulVec, inv_mulVec_mulVec, infPartPi_algebraMap]
    have hcB : c h ≤ B' := (le_abs_self _).trans (((Real.norm_eq_abs _).symm.trans_le (hB h hh)).trans
      (le_max_left _ _))
    have he : ‖embPi K ξ‖ ≤ B' * ‖y‖ := by
      rw [hy]
      exact (norm_mulVec_le _ _).trans (mul_le_mul_of_nonneg_right hcB (norm_nonneg _))
    set t := B' * (1 + ‖y‖)
    have ht : 0 < t := by positivity
    have hle : ∀ i, 1 + ‖mixedEmbedding K (ξ i)‖ ≤ t := fun i ↦ by
      have h1 : ‖mixedEmbedding K (ξ i)‖ ≤ ‖embPi K ξ‖ := norm_le_pi_norm (embPi K ξ) i
      have : t = B' + B' * ‖y‖ := by simp only [t]; ring
      linarith
    have hinv : ∀ i, (t ^ k)⁻¹ ≤ ((1 + ‖mixedEmbedding K (ξ i)‖) ^ k)⁻¹ := fun i ↦ by
      have h0 : 0 < 1 + ‖mixedEmbedding K (ξ i)‖ := by positivity
      gcongr
      exact hle i
    calc ‖φ y‖ ≤ A * ((1 + ‖y‖) ^ (k * n))⁻¹ := hφ y
      _ = A * B' ^ (k * n) * ∏ _i : ι, (t ^ k)⁻¹ := by
          have hB0 : B' ^ (k * n) ≠ 0 := by positivity
          have hprod : ∏ _i : ι, (t ^ k)⁻¹ = (t ^ (k * n))⁻¹ := by
            rw [Finset.prod_const, Finset.card_univ, inv_pow, ← pow_mul]
          have ht' : t ^ (k * n) = B' ^ (k * n) * (1 + ‖y‖) ^ (k * n) := mul_pow _ _ _
          rw [hprod, ht', mul_inv, ← mul_assoc, mul_assoc A, mul_inv_cancel₀ hB0, mul_one]
      _ ≤ A * B' ^ (k * n) * ∏ i, ((1 + ‖mixedEmbedding K (ξ i)‖) ^ k)⁻¹ := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact Finset.prod_le_prod (fun _ _ ↦ by positivity) fun i _ ↦ hinv i
  · push_neg at hm
    obtain ⟨i, hi⟩ := hm
    have hz : ∏ i, cosetIndicator I (b i) (finPartPi Y i) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by rw [cosetIndicator_apply, if_neg hi])
    rw [hz, mul_zero, norm_zero]
    exact hu0

theorem exists_summable_bound_mulVec {F : (ι → 𝔸[K]) → ℂ} (hF : F ∈ schwartzBruhatPi K ι)
    {C : Set (GL ι 𝔸[K])} (hC : IsCompact C) :
    ∃ u : (ι → K) → ℝ, Summable u ∧ ∀ h ∈ C, ∀ ξ : ι → K,
      ‖F ((h : Matrix ι ι 𝔸[K]) *ᵥ fun i ↦ algebraMap K 𝔸[K] (ξ i))‖ ≤ u ξ := by
  rw [schwartzBruhatPi_eq_cosetSpanPi] at hF
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, I, b, rfl⟩ := hG
    exact exists_summable_bound_tensor_cosetIndicator φ I b hC
  | zero => exact ⟨0, summable_zero, fun _ _ _ ↦ by simp⟩
  | add G H _ _ hG hH =>
    obtain ⟨u, hu, hGu⟩ := hG
    obtain ⟨w, hw, hHw⟩ := hH
    exact ⟨u + w, hu.add hw,
      fun a ha ξ ↦ (norm_add_le _ _).trans (add_le_add (hGu a ha ξ) (hHw a ha ξ))⟩
  | smul r G _ hG =>
    obtain ⟨u, hu, hGu⟩ := hG
    refine ⟨fun ξ ↦ ‖r‖ * u ξ, hu.mul_left _, fun a ha ξ ↦ ?_⟩
    rw [Pi.smul_apply, smul_eq_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (hGu a ha ξ) (norm_nonneg r)

theorem exists_summable_bound_thetaC {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι]
    [DecidableEq ι] {F : (ι → 𝔸[k]) → ℂ} (hF : F ∈ schwartzBruhatPi k ι)
    {C : Set (GL ι 𝔸[k])} (hC : IsCompact C) :
    ∃ u : (ι → k) → ℝ, Summable u ∧ ∀ h ∈ C, ∀ ξ : ι → k,
      ‖F ((h : Matrix ι ι 𝔸[k]) *ᵥ PositivityTheory.RgEis.ratV ξ)‖ ≤ u ξ :=
  exists_summable_bound_mulVec hF hC

end

end GlobalTheory.CompanionTheory.EisRkNBound
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFiltrationGeneratedByDividedXi
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.PerfFil

namespace GradedFiltration

theorem Fil0_succ_le {l : ℕ} [Fact l.Prime] (A : PAlg l) (r : ℕ) : A.Fil0 (r + 1) ≤ A.Fil0 r :=
  Ideal.span_mono fun _ ⟨k, hk, e⟩ => ⟨k, by omega, e⟩

theorem dividedXi_mem_filtration {l : ℕ} [Fact l.Prime] (A : PAlg l) (r : ℕ) : A.dxi0 r ∈ A.Fil0 r :=
  Ideal.subset_span ⟨r, le_rfl, rfl⟩

theorem mem_filtration_of_prime_pow_mul {l : ℕ} [Fact l.Prime] (A : PAlg l) (r n : ℕ) (z : A.Acr0)
    (h : (l : A.Acr0) ^ n * z ∈ A.Fil0 r) : z ∈ A.Fil0 r := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    apply ih
    apply GlobalTheory.T.crystalline_filtration_saturated A r
    rwa [pow_succ', mul_assoc, mul_comm, mul_assoc, mul_comm z, ← mul_assoc, mul_comm _ (l : A.Acr0), mul_assoc] at h

theorem mkAcr_surjective {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ) :
    Function.Surjective (A.mkAcr n) := Ideal.Quotient.mk_surjective

end GradedFiltration

open GradedFiltration in

theorem graded_mod_pow : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n r : ℕ),
    (∀ z ∈ A.Fil n r, ∃ w : A.W, z - A.toAcr n w * A.dxi n r ∈ A.Fil n (r + 1)) ∧
    ∀ w : A.W, A.toAcr n w * A.dxi n r ∈ A.Fil n (r + 1) ↔ A.th w ∈ Ideal.span {(l : A.U) ^ n} := by
  intro l _ A n r
  have hF : ∀ s, A.Fil n s = (A.Fil0 s).map (A.mkAcr n) := (GlobalTheory.T.crystalline_filtration_multiplicative A).2.2.2.2.1 n
  have hsurj := mkAcr_surjective A n
  have hto : ∀ w, A.toAcr n w = A.mkAcr n (algebraMap A.W A.Acr0 w) := fun _ => rfl
  have hdx : A.dxi n r = A.mkAcr n (A.dxi0 r) := rfl
  refine ⟨fun z hz => ?_, fun w => ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [hF, Ideal.mem_map_iff_of_surjective _ hsurj] at hz
    obtain ⟨z0, hz0, rfl⟩ := hz
    obtain ⟨w, hw⟩ := (GlobalTheory.T.crystalline_graded_pieces_description A r).1 z0 hz0
    refine ⟨w, ?_⟩
    rw [hF, hto, hdx, ← map_mul, ← map_sub]
    exact Ideal.mem_map_of_mem _ hw
  · rw [hF, Ideal.mem_map_iff_of_surjective _ hsurj, hto, hdx, ← map_mul] at h
    obtain ⟨z', hz', e⟩ := h
    have hd : algebraMap A.W A.Acr0 w * A.dxi0 r - z' ∈ Ideal.span {(l : A.Acr0) ^ n} := by
      apply Ideal.Quotient.eq.1
      exact e.symm
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.1 hd
    have hzr : z ∈ A.Fil0 r := by
      apply mem_filtration_of_prime_pow_mul A r n
      rw [← hz]
      exact sub_mem (Ideal.mul_mem_left _ _ (dividedXi_mem_filtration A r)) (Fil0_succ_le A r hz')
    obtain ⟨w', hw'⟩ := (GlobalTheory.T.crystalline_graded_pieces_description A r).1 z hzr
    have hxi : w - (l : A.W) ^ n * w' ∈ Ideal.span {A.xi} := by
      rw [← (GlobalTheory.T.crystalline_graded_pieces_description A r).2.1]
      have : algebraMap A.W A.Acr0 (w - (l : A.W) ^ n * w') * A.dxi0 r =
          z' + (l : A.Acr0) ^ n * (z - algebraMap A.W A.Acr0 w' * A.dxi0 r) := by
        rw [map_sub, map_mul, map_pow, map_natCast]
        linear_combination hz
      rw [this]
      exact add_mem hz' (Ideal.mul_mem_left _ _ hw')
    have : A.th w = (l : A.U) ^ n * A.th w' := by
      have h0 : A.th (w - (l : A.W) ^ n * w') = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hxi
      rw [map_sub, map_mul, map_pow, map_natCast, sub_eq_zero] at h0
      exact h0
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  · obtain ⟨u, hu⟩ := Ideal.mem_span_singleton.1 h
    obtain ⟨w', rfl⟩ : ∃ w', A.th w' = u := Ideal.Quotient.mk_surjective u
    have hxi : w - (l : A.W) ^ n * w' ∈ Ideal.span {A.xi} := by
      apply Ideal.Quotient.eq_zero_iff_mem.1
      change A.th (w - (l : A.W) ^ n * w') = 0
      rw [map_sub, map_mul, map_pow, map_natCast, hu, sub_self]
    have h1 := (GlobalTheory.T.crystalline_graded_pieces_description A r).2.1 _ |>.2 hxi
    have h2 : A.toAcr n (w - (l : A.W) ^ n * w') * A.dxi n r ∈ A.Fil n (r + 1) := by
      rw [hF, hto, hdx, ← map_mul]
      exact Ideal.mem_map_of_mem _ h1
    have h3 : A.toAcr n (w - (l : A.W) ^ n * w') = A.toAcr n w := by
      rw [map_sub, map_mul, map_pow, map_natCast, pow_l_acr, zero_mul, sub_zero]
    rwa [h3] at h2

end GlobalTheory.CompanionTheory.PerfFil
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InnerToL
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace ENNReal

namespace GlobalTheory.CompanionTheory.WaveCp

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

section Ops

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

def Ld (X : Mat n) (f : Mat n → V) : Mat n → V := fun g => fderiv ℝ f g (X * g)

def Lw (w : List (Bool × Fin n × Fin n)) (f : Mat n → V) : Mat n → V :=
  w.foldr (fun p h => Ld (bs p) h) f

@[simp] theorem Lw_nil (f : Mat n → V) : Lw [] f = f := rfl

theorem Lw_cons (p : Bool × Fin n × Fin n) (w : List (Bool × Fin n × Fin n)) (f : Mat n → V) :
    Lw (p :: w) f = Ld (bs p) (Lw w f) := rfl

def transl (x : G n) (f : Mat n → V) : Mat n → V := fun g => f ((x⁻¹ : G n).val * g)

def Ac (c : ℝ) (f : Mat n → V) : Mat n → V := (c : ℂ) • f - Om f

end Ops

def DS (E : KMod n) : Submodule ℂ (Mat n → E.V) where
  carrier := {f | f ∈ CE E ∧ Cpt f}
  add_mem' := by
    rintro f h ⟨⟨hf, hf'⟩, R, hR⟩ ⟨⟨hh, hh'⟩, S, hS⟩
    refine ⟨⟨hf.add hh, fun g hg k => ?_⟩, max R S, fun y hy hl => ?_⟩
    · simp [hf' g hg k, hh' g hg k]
    · simp [hR y hy (lt_of_le_of_lt (le_max_left _ _) hl), hS y hy (lt_of_le_of_lt (le_max_right _ _) hl)]
  zero_mem' := by
    refine ⟨⟨contDiffOn_const, fun g _ k => ?_⟩, 0, fun y _ _ => rfl⟩
    simp
  smul_mem' := by
    rintro a f ⟨⟨hf, hf'⟩, R, hR⟩
    refine ⟨⟨contDiffOn_const.smul hf, fun g hg k => ?_⟩, R, fun y hy hl => ?_⟩
    · simp [hf' g hg k]
    · simp [hR y hy hl]

section L2

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable [MeasurableSpace (G n)]

def toL (μ : Measure (G n)) (f : Mat n → V) : Lp V 2 μ :=
  open Classical in if h : MemLp (fun y : G n => f y.val) 2 μ then h.toLp _ else 0

def IsRep (μ : Measure (G n)) (b : Mat n → V) (y : Lp V 2 μ) : Prop :=
  (y : G n → V) =ᵐ[μ] fun g => b g.val

theorem toL_coe {μ : Measure (G n)} {f : Mat n → V} (h : MemLp (fun y : G n => f y.val) 2 μ) :
    IsRep μ f (toL μ f) := by
  unfold IsRep toL
  rw [dif_pos h]
  exact h.coeFn_toLp

variable [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]

def LT (x : G n) : Lp V 2 μ →L[ℂ] Lp V 2 μ :=
  (Lp.compMeasurePreservingₗᵢ ℂ (fun g : G n => x⁻¹ * g) (measurePreserving_mul_left μ x⁻¹)).toContinuousLinearMap

def RK [μ.IsMulRightInvariant] (E : KMod n) (k : Matrix.unitaryGroup (Fin n) ℂ) : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ :=
  (ContinuousLinearMap.compLpL 2 μ (E.ρ k)).comp
    (Lp.compMeasurePreservingₗᵢ ℂ (fun g : G n => g * (Unitary.toUnits k : G n))
      (measurePreserving_mul_right μ (Unitary.toUnits k : G n))).toContinuousLinearMap

end L2

end GlobalTheory.CompanionTheory.WaveCp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

def gconv (g g' : ℝ → ℝ) (r : ℝ) : ℝ := ∫ t, g t * g' (r - t)

theorem gconv_comm (g g' : ℝ → ℝ) : gconv g g' = gconv g' g := by
  funext r
  unfold gconv
  rw [← integral_sub_left_eq_self (fun t => g t * g' (r - t)) volume r]
  simp [mul_comm]

variable {n : ℕ}

def KReg {V : Type} [NormedAddCommGroup V] (k : Mat n → V) : Prop :=
  ContinuousOn k (GLs n) ∧ ∃ R, ∀ y ∈ GLs n, R < lg y → k y = 0

theorem inv_mem_GLs {y : Mat n} (hy : y ∈ GLs n) : y⁻¹ ∈ GLs n := by
  have : y.det ≠ 0 := hy
  change (y⁻¹).det ≠ 0
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  exact inv_ne_zero this

section
variable [MeasurableSpace (G n)] (μ : Measure (G n)) (E : KMod n)

theorem isMult_of_fintype {ι : Type} [Fintype ι] {k : Mat n → (E.V →L[ℂ] E.V)} {val : Inf n → ℂ} {T : ℝ}
    (c : ι → ℂ) (w : ι → List (Bool × ℕ)) (g : ι → ℝ → ℝ) (ks : ι → Mat n → (E.V →L[ℂ] E.V))
    (h1 : ∀ i, IsBump (g i) T ∧ IsKer μ E (w i) (g i) (ks i)) (h2 : ∀ y ∈ GLs n, k y = ∑ i, c i • ks i y)
    (h3 : ∀ χ, val χ = ∑ i, c i * zVal (w i) χ * coshT (g i) (cas χ)) : IsMult μ E k val T := by
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, c ∘ e.symm, w ∘ e.symm, g ∘ e.symm, ks ∘ e.symm, fun i => h1 _, fun y hy => ?_, fun χ => ?_⟩
  · rw [h2 y hy]
    exact (Equiv.sum_comp e.symm (fun i => c i • ks i y)).symm
  · rw [h3 χ]
    exact (Equiv.sum_comp e.symm (fun i => c i * zVal (w i) χ * coshT (g i) (cas χ))).symm
end

theorem zVal_append (w w' : List (Bool × ℕ)) (χ : Inf n) : zVal (w ++ w') χ = zVal w χ * zVal w' χ := by
  simp [zVal]

section Ops

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

noncomputable def EpowT (s : Bool) : ℕ → Fin n → Fin n → (Mat n → V) → (Mat n → V)
  | 0, a, b => fun f => if a = b then f else 0
  | m + 1, a, b => fun f => ∑ c, Eu s c a (EpowT s m c b f)

def gelT (s : Bool) (m : ℕ) (f : Mat n → V) : Mat n → V := ∑ a, EpowT s m a a f

end Ops

section Alg

variable {A : Type} [Ring A]

noncomputable def Epw (e : Fin n → Fin n → A) : ℕ → Fin n → Fin n → A
  | 0, a, b => if a = b then 1 else 0
  | m + 1, a, b => ∑ c, e a c * Epw e m c b

def trE (e : Fin n → Fin n → A) (m : ℕ) : A := ∑ a, Epw e m a a

noncomputable def bco (N : A) (τ : ℕ → A) : ℕ → ℕ → A
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | m + 1, 0 => N * bco N τ m 0 - τ m
  | m + 1, j + 1 => bco N τ m j + N * bco N τ m (j + 1)

noncomputable def phiSeq (N : A) (τ : ℕ → A) (m : ℕ) : A :=
  τ m - ∑ j : Fin m, bco N τ m j * phiSeq N τ j
termination_by m
decreasing_by exact j.isLt

end Alg

def gser (c : Fin n → ℂ) : PowerSeries ℂ := PowerSeries.mk (GlobalTheory.Dec.gelfVal c)

end GlobalTheory.CompanionTheory.WaveMult
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MasterIdentityStatement
section
open PositivityTheory.RgEis PositivityTheory.RgEis.MG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.master_identity : AvgMem → DGood → HGood → BGood → Master := by
  first | exact @GlobalTheory.CompanionTheory.RgEisMG.master | exact GlobalTheory.CompanionTheory.RgEisMG.master | (intros; apply GlobalTheory.CompanionTheory.RgEisMG.master <;> assumption)
end

