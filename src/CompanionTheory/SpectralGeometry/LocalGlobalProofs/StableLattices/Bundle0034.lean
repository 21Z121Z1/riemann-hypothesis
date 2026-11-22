import Mathlib
import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.PhMeas
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaCore
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.CapelliEigenvalues.Bundle0001
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TruncatedDerivationLimit
section
open Matrix Filter Topology Set MeasureTheory Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu
open scoped ContDiff InnerProductSpace ComplexConjugate

noncomputable section

namespace GlobalTheory.CompanionTheory.BesselCutLim

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem tendsto_cut {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {μ : Measure (PI.MtM n)}
    {f : PI.MtM n → E} (hf : Integrable f μ) {ρ : Mat n → ℝ} (hρ : Continuous ρ) (hc : HasCompactSupport ρ) :
    Tendsto (fun N : ℕ => ∫ y : PI.MtM n, (ρ (((N : ℝ) + 1)⁻¹ • Matrix.of y) : ℂ) • f y ∂μ) atTop
      (𝓝 ((ρ 0 : ℂ) • ∫ y, f y ∂μ)) := by
  obtain ⟨C, hC⟩ := hρ.bounded_above_of_compact_support hc
  rw [← integral_smul]
  refine tendsto_integral_of_dominated_convergence (fun y => C * ‖f y‖) (fun N => ?_)
    (hf.norm.const_mul C) (fun N => Eventually.of_forall fun y => ?_) (Eventually.of_forall fun y => ?_)
  · have h1 : Continuous fun y : PI.MtM n => (ρ (((N : ℝ) + 1)⁻¹ • Matrix.of y) : ℂ) :=
      Complex.continuous_ofReal.comp (hρ.comp
        ((show Continuous fun y : PI.MtM n => (Matrix.of y : Mat n) from continuous_id).const_smul
          (((N : ℝ) + 1)⁻¹)))
    exact h1.aestronglyMeasurable.smul hf.1
  · rw [norm_smul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)
  · refine Tendsto.smul_const ?_ _
    refine (Complex.continuous_ofReal.comp hρ).continuousAt.tendsto.comp ?_
    have h0 : Tendsto (fun N : ℕ => ((N : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
      simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa using h0.smul_const (Matrix.of y : Mat n)

theorem integrable_conj_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {G : Set (Mat n)}
    (hG : IsClosed G) {μ : Measure (PI.MtM n)} (hae : ∀ᵐ y ∂μ, (Matrix.of y : Mat n) ∈ G)
    {c : PI.MtM n → ℂ} (hc : Integrable c μ) {g : Mat n → E} (hg : ContinuousOn g G) {K : ℝ}
    (hK : ∀ x ∈ G, ‖g x‖ ≤ K) : Integrable (fun y => conj (c y) • g (Matrix.of y)) μ := by
  have hms : MeasurableSet {y : PI.MtM n | (Matrix.of y : Mat n) ∈ G} :=
    IsClosed.measurableSet (α := PI.MtM n) hG
  have hg' : ContinuousOn (fun y : PI.MtM n => g (Matrix.of y)) {y : PI.MtM n | (Matrix.of y : Mat n) ∈ G} := hg
  have hm := hg'.aestronglyMeasurable (μ := μ) hms
  rw [Measure.restrict_eq_self_of_ae_mem (s := {y : PI.MtM n | (Matrix.of y : Mat n) ∈ G}) hae] at hm
  refine Integrable.mono' (hc.norm.mul_const K)
    ((Complex.continuous_conj.comp_aestronglyMeasurable hc.1).smul hm) ?_
  filter_upwards [hae] with y hy
  rw [norm_smul, Complex.norm_conj]
  exact mul_le_mul_of_nonneg_left (hK _ hy) (norm_nonneg _)

theorem lieW_of {Hm : Mat n} {W : List (Mat n)} (hW : LieWd Hm W) : LieW (UH Hm) W :=
  fun X hX t => ex_mem_of_lie (hW X hX) t

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Hm : Mat n}
  {σ : Mat n → (H →L[ℂ] H)}

theorem tendsto_dsW (hD : CutDer) (hσ : URep Hm σ) {μ : Measure (PI.MtM n)} (hμ : PI.IsHaarOnM (UH Hm) μ)
    {w : H} (hw : IsSm (UH Hm) σ w)
    (hi : ∀ v, IsSm (UH Hm) σ v → Integrable (fun y : PI.MtM n => ⟪v, σ (Matrix.of y) w⟫_ℂ) μ) {κ : ℂ}
    (hκ : ∀ v, IsSm (UH Hm) σ v →
      ∫ y : PI.MtM n, conj ⟪v, σ (Matrix.of y) w⟫_ℂ • σ (Matrix.of y) w ∂μ = κ • v)
    (W : List (Mat n)) : LieWd Hm W → ∀ ρ : Mat n → ℝ, ContDiff ℝ ∞ ρ → HasCompactSupport ρ →
      ∀ v, IsSm (UH Hm) σ v →
      Tendsto (fun N : ℕ => dsW σ W (cutI σ μ w ((N : ℝ) + 1) ρ v)) atTop (𝓝 ((ρ 0 : ℂ) • κ • dsW σ W v)) := by
  induction W using List.reverseRecOn with
  | nil =>
    intro _ ρ hρ hc v hv
    have h1 := integrable_conj_smul hσ.grp.1 hμ.2.2.1 (hi v hv) (g := fun x => σ x w)
      (SmOn.continuousOn hw) (K := ‖w‖) fun x hx => (hσ.iso x hx w).le
    have h2 := tendsto_cut h1 hρ.continuous hc
    rw [hκ v hv] at h2
    simpa only [dsW, List.foldr_nil, cutI, mul_smul] using h2
  | append_singleton W X ih =>
    intro hWX ρ hρ hc v hv
    have hW : LieWd Hm W := fun Y hY => hWX Y (List.mem_append_left _ hY)
    have hX : Lie Hm X := hWX X (by simp)
    have hX' : LieWd Hm [X] := fun Y hY => by rw [List.mem_singleton.1 hY]; exact hX
    have hv' : IsSm (UH Hm) σ (ds σ X v) := hv.dsW hσ.rep (lieW_of hX')
    have hρ' := contDiff_Lx X hρ
    have hc' : HasCompactSupport (Lx X ρ) := hasCompactSupport_LW hc [X]
    have e : ∀ u, dsW σ (W ++ [X]) u = dsW σ W (ds σ X u) := fun u => by
      simp only [dsW, List.foldr_append, List.foldr_cons, List.foldr_nil]
    have h1 := (ih hW _ hρ' hc' v hv).add (ih hW ρ hρ hc _ hv')
    have h0 : Lx X ρ 0 = 0 := by simp [Lx]
    rw [h0, Complex.ofReal_zero, zero_smul, zero_add] at h1
    rw [e]
    refine h1.congr fun N => ?_
    have hR : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    rw [e, (hD n Hm H σ hσ μ hμ w hw _ hR ρ hρ hc v hv).2 X hX,
      dsW_add hσ.rep (hD n Hm H σ hσ μ hμ w hw _ hR _ hρ' hc' v hv).1
        (hD n Hm H σ hσ μ hμ w hw _ hR ρ hρ hc _ hv').1 (lieW_of hW)]

theorem dsW_cutI (hσ : URep Hm σ) {μ : Measure (PI.MtM n)} (hμ : PI.IsHaarOnM (UH Hm) μ)
    {w : H} (hw : IsSm (UH Hm) σ w) {R : ℝ} (hR : 0 < R) {ρ : Mat n → ℝ} (hρ : Continuous ρ)
    (hc : HasCompactSupport ρ) (v : H) {W : List (Mat n)} (hW : LieWd Hm W) :
    Integrable (fun y : PI.MtM n => ((ρ (R⁻¹ • Matrix.of y) : ℂ) * conj ⟪v, σ (Matrix.of y) w⟫_ℂ) •
      dsW σ W (σ (Matrix.of y) w)) μ ∧
    dsW σ W (cutI σ μ w R ρ v) = ∫ y : PI.MtM n, ((ρ (R⁻¹ • Matrix.of y) : ℂ) * conj ⟪v, σ (Matrix.of y) w⟫_ℂ) •
      dsW σ W (σ (Matrix.of y) w) ∂μ := by
  have hG := hσ.grp
  have hι := CompanionTheory.D.Upq.ModEx.MG.measurableEmbedding_toM (hG := hG)
  have hmap := CompanionTheory.D.Upq.Quot.map_comap_toM hG (μ := μ) hμ.2.2.1
  set μ' := μ.comap (CompanionTheory.D.Upq.ModEx.MG.toM (hG := hG)) with hμ'
  have : IsFiniteMeasureOnCompacts μ' := ⟨fun K hK => by
    rw [hμ', hι.comap_apply]
    exact CompanionTheory.D.Upq.Quot.IsHaarOnM.lt_top_of_isCompact hG hμ
      (hK.image (CompanionTheory.D.Upq.ModEx.MG.continuous_mat (hG := hG)))⟩
  let φ : CompanionTheory.D.Upq.ModEx.MG (UH Hm) hG → ℂ := fun g =>
    (ρ (R⁻¹ • g.mat) : ℂ) * conj ⟪v, σ g.mat w⟫_ℂ
  have ho : Continuous fun g : CompanionTheory.D.Upq.ModEx.MG (UH Hm) hG => σ g.mat w :=
    continuous_orbit hσ.rep hw (W := []) fun _ h => by simp at h
  have hφ : Continuous φ :=
    (Complex.continuous_ofReal.comp (hρ.comp
      (CompanionTheory.D.Upq.ModEx.MG.continuous_mat.const_smul R⁻¹))).mul
      (Complex.continuous_conj.comp (continuous_const.inner ho))
  have hcs : HasCompactSupport fun x : Mat n => (ρ (R⁻¹ • x) : ℂ) :=
    (hc.comp_smul (inv_ne_zero hR.ne')).comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero
  have hφc : HasCompactSupport φ :=
    (hcs.comp_isClosedEmbedding CompanionTheory.D.Upq.ModEx.MG.isClosedEmbedding_mat).mul_right
  unfold cutI
  rw [← hmap, hι.integrable_map_iff, hι.integral_map, hι.integral_map]
  exact ⟨integrable_csmul hφ hφc (continuous_orbit hσ.rep hw (lieW_of hW)),
    dsW_integral hσ.rep hw hφ hφc (lieW_of hW)⟩

theorem cutLim_of (hF : Factor) (hD : CutDer) : CutLim := by
  intro n Hm H _ _ _ σ hσ V _ _ _ B hB μ hμ w hw hi κ hκ ⟨K, hK⟩ v hv
  have : CompleteSpace V := FiniteDimensional.complete ℂ V
  obtain ⟨M, W, β, hW, hBβ⟩ := hF n Hm H σ hσ V B hB
  obtain ⟨ρ, -, hc, hρ, -, hρ1⟩ := exists_contDiff_tsupport_subset (n := ⊤)
    (Filter.univ_mem : (univ : Set (Mat n)) ∈ 𝓝 0)
  have hae : ∀ᵐ y ∂μ, (Matrix.of y : Mat n) ∈ UH Hm := hμ.2.2.1
  have h1 : Tendsto (fun N : ℕ => ∑ i, β i (dsW σ (W i) (cutI σ μ w ((N : ℝ) + 1) ρ v))) atTop
      (𝓝 (∑ i, β i ((ρ 0 : ℂ) • κ • dsW σ (W i) v))) :=
    tendsto_finsetSum _ fun i _ => ((β i).continuous.tendsto _).comp
      (tendsto_dsW hD hσ hμ hw hi hκ (W i) (hW i) ρ hρ hc v hv)
  have hBc : ContinuousOn (fun x => B (σ x w)) (UH Hm) :=
    (continuousOn_finsetSum _ fun i _ => (β i).continuous.comp_continuousOn
      (continuousOn_dsW_orbit hσ.rep hw (lieW_of (hW i)))).congr
      fun x hx => hBβ _ (hw.apply hσ.rep hx)
  have h2 := tendsto_cut (integrable_conj_smul hσ.grp.1 hae (hi v hv) hBc hK) hρ.continuous hc
  rw [hρ1, Complex.ofReal_one] at h1 h2
  simp only [one_smul, map_smul] at h1 h2
  rw [← Finset.smul_sum, ← hBβ v hv] at h1
  refine tendsto_nhds_unique h1 (h2.congr fun N => ?_)
  have hR : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have h3 := fun i => dsW_cutI hσ hμ hw hR hρ.continuous hc v (hW i)
  rw [Finset.sum_congr rfl fun i _ => by rw [(h3 i).2, ← (β i).integral_comp_comm (h3 i).1],
    ← integral_finsetSum _ fun i _ => (β i).integrable_comp (h3 i).1]
  refine integral_congr_ae ?_
  filter_upwards [hae] with y hy
  rw [hBβ _ (hw.apply hσ.rep hy)]
  simp only [map_smul, mul_smul, Finset.smul_sum]

end GlobalTheory.CompanionTheory.BesselCutLim

end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.WordLengthBoundOfLinear
section
open Matrix Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu

noncomputable section

namespace GlobalTheory.CompanionTheory.BmuWordBd

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def lieSub {n : ℕ} (Hm : Mat n) : Submodule ℝ (Mat n) where
  carrier := {X | Lie Hm X}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Lie] at *
    rw [conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, ha, hb, add_zero]
  zero_mem' := by simp [Lie]
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_ofPred_eq, Lie] at *
    rw [conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, ha, smul_zero]

theorem exists_basis_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (S : Submodule ℝ E) :
    ∃ (N : ℕ) (b : Fin N → E) (κ : ℝ), 0 ≤ κ ∧ (∀ i, b i ∈ S) ∧
      ∀ X, X ∈ S → ∃ c : Fin N → ℝ, X = ∑ i, c i • b i ∧ ∀ i, |c i| ≤ κ * ‖X‖ := by
  let bS := Module.finBasis ℝ S
  let L : Fin (Module.finrank ℝ S) → (S →L[ℝ] ℝ) := fun i => LinearMap.toContinuousLinearMap (bS.coord i)
  refine ⟨Module.finrank ℝ S, fun i => (bS i : E), ∑ i, ‖L i‖,
    Finset.sum_nonneg (fun i _ => norm_nonneg _), fun i => (bS i).2, ?_⟩
  intro X hX
  refine ⟨fun i => bS.repr ⟨X, hX⟩ i, ?_, ?_⟩
  · calc X = ((⟨X, hX⟩ : S) : E) := rfl
      _ = ((∑ i, bS.repr ⟨X, hX⟩ i • bS i : S) : E) := by rw [bS.sum_repr]
      _ = ∑ i, bS.repr ⟨X, hX⟩ i • (bS i : E) := by simp only [Submodule.coe_sum, Submodule.coe_smul]
  · intro i
    have h1 : |bS.repr ⟨X, hX⟩ i| ≤ ‖L i‖ * ‖X‖ := by
      have := (L i).le_opNorm ⟨X, hX⟩
      simpa [L, Real.norm_eq_abs] using this
    have h2 : ‖L i‖ ≤ ∑ j, ‖L j‖ := Finset.single_le_sum (fun j _ => norm_nonneg (L j)) (Finset.mem_univ i)
    exact h1.trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))

theorem exists_basis {n : ℕ} (Hm : Mat n) :
    ∃ (N : ℕ) (b : Fin N → Mat n) (κ : ℝ), 0 ≤ κ ∧ (∀ i, Lie Hm (b i)) ∧
      ∀ X, Lie Hm X → ∃ c : Fin N → ℝ, X = ∑ i, c i • b i ∧ ∀ i, |c i| ≤ κ * ‖X‖ := by
  obtain ⟨N, b, κ, hκ, hb, hX⟩ := exists_basis_sub (lieSub Hm)
  exact ⟨N, b, κ, hκ, hb, fun X hXL => hX X hXL⟩

theorem dsW_sum {n : ℕ} {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] {G : Set (Mat n)}
    {σ : Mat n → (H →L[ℂ] H)} (h : RepOn G σ) {ι : Type*} (s : Finset ι) (v : ι → H)
    (hv : ∀ i, IsSm G σ (v i)) {W : List (Mat n)} (hW : LieW G W) :
    IsSm G σ (∑ i ∈ s, v i) ∧ dsW σ W (∑ i ∈ s, v i) = ∑ i ∈ s, dsW σ W (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨IsSm.zero, by simpa using dsW_smul h (IsSm.zero (G := G) (σ := σ)) (0 : ℂ) hW⟩
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact ⟨(hv a).add ih.1, by rw [dsW_add h (hv a) ih.1 hW, ih.2]⟩

private theorem ex_mem_UH_of_lie {n : ℕ} {Hm X : Mat n} (hsq : Hm * Hm = 1) (hX : Lie Hm X) (t : ℝ) :
    ex X t ∈ Formalism.QuantumDeterminants.UH Hm := by
  have hinv : Hm⁻¹ = Hm := Matrix.inv_eq_right_inv hsq
  have hU : IsUnit Hm := ⟨⟨Hm, Hm, hsq, hsq⟩, rfl⟩
  have h1 : Xᴴ * Hm = -(Hm * X) := eq_neg_of_add_eq_zero_left hX
  have hXH : Xᴴ = Hm * (-X) * Hm := by
    calc Xᴴ = Xᴴ * Hm * Hm := by rw [mul_assoc, hsq, mul_one]
      _ = Hm * (-X) * Hm := by rw [h1, Matrix.mul_neg]
  have hconj : ((t : ℂ) • X)ᴴ = Hm * (-((t : ℂ) • X)) * Hm⁻¹ := by
    rw [Matrix.conjTranspose_smul, hXH, hinv]
    simp [Matrix.mul_smul, Matrix.smul_mul, Complex.conj_ofReal]
  show (NormedSpace.exp ((t : ℂ) • X))ᴴ * Hm * NormedSpace.exp ((t : ℂ) • X) = Hm
  rw [← Matrix.exp_conjTranspose, hconj, Matrix.exp_conj _ _ hU, hinv, mul_assoc (Hm * _) Hm Hm, hsq,
    mul_one, mul_assoc, ← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl ((t : ℂ) • X))),
    neg_add_cancel, NormedSpace.exp_zero, mul_one]

private theorem dsW_append' {n : ℕ} {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (σ : Mat n → (H →L[ℂ] H)) (P W : List (Mat n)) (v : H) :
    dsW σ (P ++ W) v = dsW σ P (dsW σ W v) := by
  show List.foldr (ds σ) v (P ++ W) = List.foldr (ds σ) (List.foldr (ds σ) v W) P
  exact List.foldr_append

theorem wordBd_of_dsLin : DsLin → WordBd := by
  intro hD
  unfold WordBd
  intro n Hm H _ _ _ σ hU w hw m
  have hrep : RepOn (Formalism.QuantumDeterminants.UH Hm) σ := hU.rep
  have hsq : Hm * Hm = 1 := hU.sq
  have hlie : ∀ W : List (Mat n), LieWd Hm W → LieW (Formalism.QuantumDeterminants.UH Hm) W :=
    fun W hW X hX t => ex_mem_UH_of_lie hsq (hW X hX) t
  obtain ⟨N, b, κ, hκ, hb, hc⟩ := exists_basis Hm
  have hexp : ∀ v, IsSm (Formalism.QuantumDeterminants.UH Hm) σ v → ∀ X, Lie Hm X →
      ∃ c : Fin N → ℝ, (∀ i, |c i| ≤ κ * ‖X‖) ∧ ds σ X v = ∑ i, (c i : ℂ) • ds σ (b i) v := by
    intro v hv X hX
    obtain ⟨Λ, hΛ⟩ := hD n Hm H σ hU v hv
    obtain ⟨c, hXc, hcb⟩ := hc X hX
    refine ⟨c, hcb, ?_⟩
    rw [hΛ X hX, hXc, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, ← hΛ (b i) (hb i), Complex.coe_smul]
  have hlb : ∀ i, LieWd Hm [b i] := by
    intro i Y hY
    rw [List.mem_singleton] at hY
    subst hY
    exact hb i
  have key : ∀ k : ℕ, ∀ P : List (Mat n), LieWd Hm P → ∃ C : ℝ, 0 ≤ C ∧
      ∀ W : List (Mat n), LieWd Hm W → W.length ≤ k →
        ‖dsW σ (P ++ W) w‖ ≤ C * (W.map (fun X => ‖X‖)).prod := by
    intro k
    induction k with
    | zero =>
      intro P _
      refine ⟨‖dsW σ P w‖, norm_nonneg _, fun W _ hW => ?_⟩
      have hW0 : W = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hW)
      subst hW0
      simp
    | succ k ih =>
      intro P hP
      have hPb : ∀ i, LieWd Hm (P ++ [b i]) := by
        intro i Y hY
        rcases List.mem_append.1 hY with h | h
        · exact hP Y h
        · exact hlb i Y h
      choose C hC0 hC using fun i : Fin N => ih (P ++ [b i]) (hPb i)
      refine ⟨max ‖dsW σ P w‖ (κ * ∑ i, C i), le_max_of_le_left (norm_nonneg _), ?_⟩
      intro W hW hlen
      cases W with
      | nil =>
        simp only [List.append_nil, List.map_nil, List.prod_nil, mul_one]
        exact le_max_left _ _
      | cons X W' =>
        have hX : Lie Hm X := hW X List.mem_cons_self
        have hW' : LieWd Hm W' := fun Y hY => hW Y (List.mem_cons_of_mem _ hY)
        have hlen' : W'.length ≤ k := by simpa using hlen
        have hv : IsSm (Formalism.QuantumDeterminants.UH Hm) σ (dsW σ W' w) := hw.dsW hrep (hlie W' hW')
        obtain ⟨c, hcb, hds⟩ := hexp _ hv X hX
        have hsm : ∀ i, IsSm (Formalism.QuantumDeterminants.UH Hm) σ (ds σ (b i) (dsW σ W' w)) :=
          fun i => hv.dsW hrep (hlie [b i] (hlb i))
        have heq : dsW σ (P ++ X :: W') w = ∑ i, (c i : ℂ) • dsW σ ((P ++ [b i]) ++ W') w := by
          rw [dsW_append', dsW_cons, hds,
            (dsW_sum hrep Finset.univ _ (fun i => (hsm i).smul (c i : ℂ)) (hlie P hP)).2]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [dsW_smul hrep (hsm i) _ (hlie P hP), dsW_append', dsW_append']
          rfl
        have hprod : 0 ≤ (W'.map (fun X => ‖X‖)).prod :=
          List.prod_nonneg (fun a ha => by
            obtain ⟨Y, _, rfl⟩ := List.mem_map.1 ha
            exact norm_nonneg _)
        simp only [List.map_cons, List.prod_cons]
        rw [heq]
        calc ‖∑ i, (c i : ℂ) • dsW σ ((P ++ [b i]) ++ W') w‖
            ≤ ∑ i, ‖(c i : ℂ) • dsW σ ((P ++ [b i]) ++ W') w‖ := norm_sum_le _ _
          _ ≤ ∑ i, (κ * ‖X‖) * (C i * (W'.map (fun X => ‖X‖)).prod) := by
              refine Finset.sum_le_sum fun i _ => ?_
              rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
              exact mul_le_mul (hcb i) (hC i W' hW' hlen') (norm_nonneg _)
                (mul_nonneg hκ (norm_nonneg _))
          _ = (κ * ∑ i, C i) * (‖X‖ * (W'.map (fun X => ‖X‖)).prod) := by
              rw [Finset.mul_sum, Finset.sum_mul]
              refine Finset.sum_congr rfl fun i _ => ?_
              ring
          _ ≤ max ‖dsW σ P w‖ (κ * ∑ i, C i) * (‖X‖ * (W'.map (fun X => ‖X‖)).prod) :=
              mul_le_mul_of_nonneg_right (le_max_right _ _) (mul_nonneg (norm_nonneg _) hprod)
  obtain ⟨C, hC0, hC⟩ := key m [] (fun X hX => absurd hX List.not_mem_nil)
  exact ⟨C, hC0, fun W hW hlen => by simpa using hC W hW hlen⟩

end GlobalTheory.CompanionTheory.BmuWordBd
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ZuckermanHypothesis
section
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

noncomputable section

namespace GlobalTheory.CompanionTheory.ZuckTransport

open PI.UpqRep CompanionTheory.LimBd.SchurHpk

theorem dot_conj {n : ℕ} (P a Q : Matrix (Fin n) (Fin n) ℂ) (u x : Fin n → ℂ) :
    u ⬝ᵥ ((P * a * Q) *ᵥ x) = (u ᵥ* P) ⬝ᵥ (a *ᵥ (Q *ᵥ x)) := by
  rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem dot_expand {n : ℕ} (a : Matrix (Fin n) (Fin n) ℂ) (u x : Fin n → ℂ) :
    u ⬝ᵥ (a *ᵥ x) = ∑ p : Fin n × Fin n, u p.1 * x p.2 * a p.1 p.2 := by
  rw [Fintype.sum_prod_type]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}

theorem kfin_smul {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)} {v : H} (c : ℂ)
    (hv : IsKFinHpk (k := k) (r := r) σ v) : IsKFinHpk (k := k) (r := r) σ (c • v) := by
  obtain ⟨S, h1, h2, h3⟩ := hv
  exact ⟨S, h1, S.smul_mem c h2, h3⟩

theorem transport (U : URep k r) {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hP : IsCayleyU k r ε P)
    (q : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hq : ∀ g, q (P * g * P⁻¹) = P * q g * P⁻¹)
    (ν : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℝ)
    (Sm : Finset (Fin (2 * r + k + 1))) (Hs : Fin (2 * r + k + 1) → Type)
    [∀ s, NormedAddCommGroup (Hs s)] [∀ s, InnerProductSpace ℂ (Hs s)] [∀ s, CompleteSpace (Hs s)]
    (σs : ∀ s, Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Hs s →L[ℂ] Hs s))
    (hSm : ∀ s, s ∈ Sm ↔ IsHCParam (ν s))
    (ds : ∀ s ∈ Sm, IsHCParam (ν s) ∧ IsDS ε (ν s) (σs s))
    (toSum : ∀ (v w : U.R.H) (x y : Fin (2 * r + k + 1) → ℂ), IsKFin ε (fun g => U.R.σ (P⁻¹ * g * P)) v →
      IsKFin ε (fun g => U.R.σ (P⁻¹ * g * P)) w →
      ∃ (ι : Type) (_ : Fintype ι) (sI : ι → Fin (2 * r + k + 1)) (vI wI : ∀ i, Hs (sI i)),
        (∀ i, sI i ∈ Sm ∧ IsKFin ε (σs (sI i)) (vI i) ∧ IsKFin ε (σs (sI i)) (wI i)) ∧
        ∀ g ∈ UJset ε, ⟪w, U.R.σ (P⁻¹ * g * P) v⟫_ℂ * (star y ⬝ᵥ (q g *ᵥ x)) =
          ∑ i, ⟪wI i, σs (sI i) g (vI i)⟫_ℂ)
    (ofSum : ∀ s ∈ Sm, ∀ v w : Hs s, IsKFin ε (σs s) v → IsKFin ε (σs s) w →
      ∃ (ι : Type) (_ : Fintype ι) (vI wI : ι → U.R.H) (xI yI : ι → Fin (2 * r + k + 1) → ℂ),
        (∀ i, IsKFin ε (fun g => U.R.σ (P⁻¹ * g * P)) (vI i) ∧ IsKFin ε (fun g => U.R.σ (P⁻¹ * g * P)) (wI i)) ∧
        ∀ g ∈ UJset ε, ⟪w, σs s g v⟫_ℂ =
          ∑ i, ⟪wI i, U.R.σ (P⁻¹ * g * P) (vI i)⟫_ℂ * (star (yI i) ⬝ᵥ (q g *ᵥ xI i))) :
    ∃ T : {s // IsHCParam (ν s)} → URep k r, (∀ s, (T s).R.IsDS ε (ν s)) ∧
      (∀ v w, U.R.KFin v → U.R.KFin w → ∀ c d, ∃ (I : Type) (_ : Fintype I) (s : I → {s // IsHCParam (ν s)})
        (y y' : ∀ i, (T (s i)).R.H),
        ∀ g ∈ GG k r, ⟪w, U.R.σ g v⟫_ℂ * q g c d = ∑ i, ⟪y' i, (T (s i)).R.σ g (y i)⟫_ℂ) ∧
      ∀ s, ∃ y : (T s).R.H, y ≠ 0 ∧ ∃ (I : Type) (_ : Fintype I) (v w : I → U.R.H)
        (c d : I → Fin (2 * r + k + 1)), (∀ i, U.R.KFin (v i) ∧ U.R.KFin (w i)) ∧
        ∀ g ∈ GG k r, ⟪y, (T s).R.σ g y⟫_ℂ = ∑ i, ⟪w i, U.R.σ g (v i)⟫_ℂ * q g (c i) (d i) := by
  have hk := fun v => CompanionTheory.CapEig.kfin_iff k r ε P U.R.H U.R.σ v hP
  have hds : ∀ s : {s // IsHCParam (ν s)}, IsDSHpk k r ε (ν s) (fun x => σs s (P * x * P⁻¹)) := fun s =>
    ⟨P, hP, by
      have e : (fun g => (fun x => σs s (P * x * P⁻¹)) (P⁻¹ * g * P)) = σs s := funext fun g => by
        simp only [forth_back hP.1]
      rw [e]
      exact (ds s ((hSm s).2 s.2)).2⟩
  refine ⟨fun s => ⟨⟨Hs s, fun x => σs s (P * x * P⁻¹)⟩, isURepOn_of_ds (hds s)⟩, fun s => ⟨s.2, hds s⟩,
    fun v w hv hw c d => ?_, fun s => ?_⟩
  · obtain ⟨ι, _, sI, vI, wI, hI, hsum⟩ := toSum v w (P *ᵥ Pi.single d 1) (star (Pi.single c 1 ᵥ* P⁻¹))
      ((hk v).1 hv) ((hk w).1 hw)
    refine ⟨ι, inferInstance, fun i => ⟨sI i, (hSm _).1 (hI i).1⟩, vI, wI, fun g hg => ?_⟩
    have := hsum _ (forth_mem hP.1 hg)
    rw [back_forth hP.1, hq, star_star, dot_conj, Matrix.vecMul_vecMul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_assoc (q g), inv_mul_P hP.1, Matrix.mul_one, Matrix.vecMul_one, single_one_dotProduct,
      Matrix.mulVec_single_one] at this
    exact this
  · have hs := (hSm s).2 s.2
    obtain ⟨S, hS, hSK, -, ⟨y, hyS, hy0, -⟩, -⟩ := (ds s hs).2.2.2.2.2.2.1
    have hy : IsKFin ε (σs s) y := ⟨S, hS, hyS, hSK⟩
    obtain ⟨ι, _, vI, wI, xI, yI, hI, hsum⟩ := ofSum s hs y y hy hy
    refine ⟨y, hy0, ι × Fin (2 * r + k + 1) × Fin (2 * r + k + 1), inferInstance,
      fun p => ((star (yI p.1) ᵥ* P) p.2.1 * (P⁻¹ *ᵥ xI p.1) p.2.2) • vI p.1, fun p => wI p.1,
      fun p => p.2.1, fun p => p.2.2, fun p => ⟨kfin_smul _ ((hk _).2 (hI p.1).1), (hk _).2 (hI p.1).2⟩,
      fun g hg => ?_⟩
    have := hsum _ (forth_mem hP.1 hg)
    refine this.trans ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [back_forth hP.1, hq, dot_conj, dot_expand, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_smul, inner_smul_right]
    ring

theorem zuckerman_hypothesis_holds : ZuckH := by
  intro t hZ k r ε μ U b h hU hg hlt
  obtain ⟨hμ, P, hP, hτ⟩ := hU
  obtain ⟨⟨X, hX⟩, ⟨Y, hY⟩⟩ := hZ _ ε μ U.R.H _ hμ hτ h hg hlt
  cases b
  · exact transport U hP (fun g => g) (fun _ => rfl) (shift false μ) X.Sm X.Hs X.σs hX X.ds X.toSum X.ofSum
  · have hi : ∀ g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, (P * g * P⁻¹)⁻¹ = P * g⁻¹ * P⁻¹ :=
      fun g => by
        rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev,
          Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP.1.1), Matrix.mul_assoc]
    obtain ⟨T, h1, h2, h3⟩ :=
      transport U hP (fun g => g⁻¹) hi (shift true μ) Y.Sm Y.Hs Y.σs hY Y.ds Y.toSum Y.ofSum
    refine ⟨T, h1, fun v w hv hw c d => h2 v w hv hw d c, fun s => ?_⟩
    obtain ⟨y, hy, I, _, v, w, c, d, hk, he⟩ := h3 s
    exact ⟨y, hy, I, inferInstance, v, w, d, c, hk, he⟩

end GlobalTheory.CompanionTheory.ZuckTransport

end
end

