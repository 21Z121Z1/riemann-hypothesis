import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0003
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0096
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0095
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0097
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0136
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0143
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicLeviEmbeddingHomomorphismProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicStabilizerRadicalStructure
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaDecompComplexifiedMaxCompact
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaDecompositionUnitaryIsotropicFlag
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0074
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0140
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0144

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasDerivAtCompletedTensorOrbitSmoothAverage
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.AverageDeriv

theorem hasDerivAt_average {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant]
    [IsFiniteMeasureOnCompacts μ] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : G → (H →L[ℂ] H)} (hσ : IsURep σ) (w : H) {a : ℝ → G} (ha : Continuous a) (ha0 : a 0 = 1)
    {f f' : G → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) (hf' : Continuous f')
    (hfc' : HasCompactSupport f')
    (hd : ∀ g t, HasDerivAt (fun s => f ((a s)⁻¹ * g)) (f' ((a t)⁻¹ * g)) t) :
    HasDerivAt (fun t => σ (a t) (∫ g, f g • σ g w ∂μ)) (∫ g, f' g • σ g w ∂μ) 0 := by
  obtain ⟨-, hmul, hnorm, hcont⟩ := hσ
  have hcw : Continuous fun g => σ g w := hcont w

  have key : ∀ t, σ (a t) (∫ g, f g • σ g w ∂μ) = ∫ g, f ((a t)⁻¹ * g) • σ g w ∂μ := by
    intro t
    have hint : Integrable (fun g => f g • σ g w) μ :=
      (hf.smul hcw).integrable_of_hasCompactSupport (hfc.smul_right)
    rw [← (σ (a t)).integral_comp_comm hint]
    rw [← integral_mul_left_eq_self (fun g => f ((a t)⁻¹ * g) • σ g w) (a t)]
    congr 1
    funext g
    rw [map_smul, inv_mul_cancel_left, hmul]
    rfl

  obtain ⟨C, hC⟩ := hf'.bounded_above_of_compact_support hfc'
  set K : Set G := (fun p : ℝ × G => a p.1 * p.2) '' (Set.Icc (-1 : ℝ) 1 ×ˢ tsupport f') with hK
  have hKc : IsCompact K :=
    (isCompact_Icc.prod hfc').image ((ha.comp continuous_fst).mul continuous_snd)
  have hsupp : ∀ s ∈ Metric.ball (0 : ℝ) 1, ∀ g, g ∉ K → f' ((a s)⁻¹ * g) = 0 := by
    intro s hs g hg
    by_contra h
    apply hg
    refine ⟨(s, (a s)⁻¹ * g), ⟨?_, subset_tsupport _ h⟩, by simp⟩
    rw [Real.ball_eq_Ioo, zero_sub, zero_add] at hs
    exact Set.Ioo_subset_Icc_self hs
  have hbound_int : Integrable (K.indicator fun _ => C * ‖w‖) μ :=
    (continuousOn_const.integrableOn_compact hKc).integrable_indicator hKc.isClosed.measurableSet
  have hcont_tr : ∀ (k : G → ℂ), Continuous k → ∀ s : ℝ, Continuous fun g => k ((a s)⁻¹ * g) • σ g w :=
    fun k hk s => (hk.comp (continuous_const.mul continuous_id)).smul hcw
  have hder := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := (0 : ℝ))
    (F := fun s g => f ((a s)⁻¹ * g) • σ g w) (F' := fun s g => f' ((a s)⁻¹ * g) • σ g w)
    (bound := K.indicator fun _ => C * ‖w‖) (Metric.ball_mem_nhds 0 one_pos)
    (Filter.Eventually.of_forall fun s => (hcont_tr f hf s).aestronglyMeasurable)
    (by
      simp only [ha0, inv_one, one_mul]
      exact (hf.smul hcw).integrable_of_hasCompactSupport (hfc.smul_right))
    (hcont_tr f' hf' 0).aestronglyMeasurable
    (Filter.Eventually.of_forall fun g s hs => by
      by_cases hg : g ∈ K
      · rw [Set.indicator_of_mem hg, norm_smul, hnorm]
        exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)
      · rw [Set.indicator_of_notMem hg, hsupp s hs g hg, zero_smul, norm_zero])
    hbound_int
    (Filter.Eventually.of_forall fun g s _ => (hd g s).smul_const (σ g w))
  have hfun : (fun t => σ (a t) (∫ g, f g • σ g w ∂μ)) = fun t => ∫ g, f ((a t)⁻¹ * g) • σ g w ∂μ :=
    funext key
  rw [hfun]
  simpa only [ha0, inv_one, one_mul] using hder.2

theorem expU_zero {n : ℕ} {ε : Fin n → Bool} : expU (0 : gLie ε) = 1 := by
  apply Subtype.ext
  apply Units.ext
  refine (uMat_expU _).trans ?_
  simp

theorem expU_add {n : ℕ} {ε : Fin n → Bool} (X : gLie ε) (a b : ℝ) :
    expU ((a + b) • X) = expU (a • X) * expU (b • X) := by
  apply Subtype.ext
  apply Units.ext
  refine (uMat_expU _).trans ?_
  refine Eq.trans ?_ (congrArg₂ (· * ·) (uMat_expU (a • X)).symm (uMat_expU (b • X)).symm)
  rw [Submodule.coe_smul, Submodule.coe_smul, Submodule.coe_smul, add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl _).smul_left a).smul_right b)

theorem expU_inv {n : ℕ} {ε : Fin n → Bool} (X : gLie ε) (t : ℝ) : (expU (t • X))⁻¹ = expU ((-t) • X) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← expU_add, add_neg_cancel, zero_smul, expU_zero]

theorem continuous_expU {n : ℕ} {ε : Fin n → Bool} (X : gLie ε) : Continuous fun t : ℝ => expU (t • X) := by
  have hcexp : ∀ A : Matrix (Fin n) (Fin n) ℂ, Continuous fun t : ℝ => NormedSpace.exp (t • A) := by
    intro A
    letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
    exact (differentiable_exp_smul_const ℝ A).continuous
  apply Continuous.subtype_mk
  rw [Units.continuous_iff]
  constructor
  · have e : (fun t : ℝ => (((expU (t • X) : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
        Matrix (Fin n) (Fin n) ℂ)) = fun t : ℝ => NormedSpace.exp (t • X.1) := by
      funext t
      rw [← Submodule.coe_smul]
      exact uMat_expU (t • X)
    have h := hcexp X.1
    rw [← e] at h
    exact h
  · have e : (fun t : ℝ => ((((expU (t • X) : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ :
        (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) =
        fun t : ℝ => NormedSpace.exp (t • (-X.1)) := by
      funext t
      have h1 := congrArg (fun g : Formalism.REAL.UJ ε => ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
        Matrix (Fin n) (Fin n) ℂ)) (expU_inv X t)
      refine h1.trans ((uMat_expU _).trans ?_)
      rw [Submodule.coe_smul, neg_smul, smul_neg]
    have h := hcexp (-X.1)
    rw [← e] at h
    exact h

theorem hasDerivAt_exp_mul_entry {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) (i j : Fin n) :
    HasDerivAt (fun s : ℝ => (NormedSpace.exp (s • X) * Y) i j) ((X * (NormedSpace.exp (t • X) * Y)) i j) t := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  have h := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) X t).mul_const Y
  let l : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun M => M i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have h2 := (LinearMap.toContinuousLinearMap l).hasFDerivAt.comp_hasDerivAt t h
  have h3 : HasDerivAt (fun s : ℝ => (NormedSpace.exp (s • X) * Y) i j)
      ((X * NormedSpace.exp (t • X) * Y) i j) t := h2
  rw [← mul_assoc]
  exact h3

theorem uMat_inv_mul {n : ℕ} {ε : Fin n → Bool} (X : gLie ε) (t : ℝ) (g : UJ ε) :
    uMat ((expU (t • X))⁻¹ * g) = NormedSpace.exp (t • (-X.1)) * uMat g := by
  rw [expU_inv]
  show uMat (expU ((-t) • X)) * uMat g = _
  rw [uMat_expU, Submodule.coe_smul, neg_smul, smul_neg]

theorem hasDerivAt_orbit_average : ∀ (B : RowsAut) (F : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ) (E : gInf B) (w : B.Hs), IsURep B.σs → ContDiff ℝ ∞ F → HasCompactSupport F → ∃ F' : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ, ContDiff ℝ ∞ F' ∧ HasCompactSupport F' ∧ HasDerivAt (orbit B E (∫ g, F (fun v i j => uMat (g v) i j) • B.σs g w ∂(muInf B.I))) (∫ g, F' (fun v i j => uMat (g v) i j) • B.σs g w ∂(muInf B.I)) 0 := by
  intro B F E w hσ hF hFc

  have hμ : muInf B.I = Measure.pi (fun v => Formalism.REAL.muG (B.I.ε v)) := rfl
  haveI : (muInf B.I).IsMulLeftInvariant := by rw [hμ]; infer_instance
  haveI : IsFiniteMeasureOnCompacts (muInf B.I) := by rw [hμ]; infer_instance
  let c : B.I.Ginf → (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) :=
    fun g v i j => uMat (g v) i j
  have hc : Topology.IsClosedEmbedding c :=
    Topology.IsClosedEmbedding.piMap fun v => (Formalism.REAL.isClosedEmbeddingMatrix B.I.n (B.I.ε v)).1

  let Lm : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) →ₗ[ℝ]
      (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) :=
    { toFun := fun M v i j => ∑ k, (-(E v).1) i k * M v k j
      map_add' := by
        intro M N
        funext v i j
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro r M
        funext v i j
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Complex.real_smul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => mul_left_comm _ _ _ }
  let L := LinearMap.toContinuousLinearMap Lm
  let F' : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ := fun M => fderiv ℝ F M (L M)
  have hF's : ContDiff ℝ ∞ F' := (contDiff_infty_iff_fderiv.1 hF).2.clm_apply L.contDiff
  have hF'c : HasCompactSupport F' := by
    refine (hFc.fderiv (𝕜 := ℝ)).mono' fun M hM => subset_tsupport _ ?_
    intro h0
    apply hM
    show fderiv ℝ F M (L M) = 0
    rw [h0]
    rfl
  refine ⟨F', hF's, hF'c, ?_⟩
  let a : ℝ → B.I.Ginf := fun t v => expU (t • E v)
  have ha : Continuous a := continuous_pi fun v => continuous_expU (E v)
  have ha0 : a 0 = 1 := by
    funext v
    show expU ((0 : ℝ) • E v) = 1
    rw [zero_smul, expU_zero]
  have hcc : Continuous c := hc.continuous
  have hd : ∀ g t, HasDerivAt (fun s => F (c ((a s)⁻¹ * g))) (F' (c ((a t)⁻¹ * g))) t := by
    intro g t
    let p : ℝ → (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) :=
      fun s v i j => (NormedSpace.exp (s • (-(E v).1)) * uMat (g v)) i j
    have hp : ∀ s, c ((a s)⁻¹ * g) = p s := by
      intro s
      funext v i j
      show uMat ((expU (s • E v))⁻¹ * g v) i j = _
      rw [uMat_inv_mul]
    have hp' : HasDerivAt p (L (p t)) t := by
      refine hasDerivAt_pi.2 fun v => hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
      exact hasDerivAt_exp_mul_entry _ _ t i j
    have hFd : HasFDerivAt F (fderiv ℝ F (p t)) (p t) :=
      (hF.differentiable (by simp)).differentiableAt.hasFDerivAt
    have h := hFd.comp_hasDerivAt t hp'
    simp only [hp]
    exact h
  have main := hasDerivAt_average (muInf B.I) hσ w (a := a) ha ha0 (f := fun g => F (c g))
    (f' := fun g => F' (c g)) (hF.continuous.comp hcc) (hFc.comp_isClosedEmbedding hc)
    (hF's.continuous.comp hcc) (hF'c.comp_isClosedEmbedding hc) hd
  exact main

end GlobalTheory.AverageDeriv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormExistsConjNearReference
section
noncomputable section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt.NormalPos

section
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}

theorem mem_smul_iff (s : V ≃ₗ[K] V) (Λ : Submodule (𝓞 K) V) (y : V) :
    y ∈ s • Λ ↔ ∃ x ∈ Λ, s x = y := by
  rw [Submodule.mem_smul_pointwise_iff_exists]
  rfl

theorem smul_inf_eq (s : V ≃ₗ[K] V) (Λ : Submodule (𝓞 K) V) (S : Submodule K V)
    (h : ∀ y ∈ S, s y = y) : (s • Λ) ⊓ rs (𝓞 K) S = Λ ⊓ rs (𝓞 K) S := by
  ext y
  simp only [Submodule.mem_inf, Submodule.restrictScalars_mem, mem_smul_iff]
  constructor
  · rintro ⟨⟨x, hx, hxy⟩, hy⟩
    have : x = y := s.injective (hxy.trans (h y hy).symm)
    exact ⟨this ▸ hx, hy⟩
  · rintro ⟨hx, hy⟩
    exact ⟨⟨y, hx, h y hy⟩, hy⟩

theorem line_le (A : Submodule (𝓞 K) K) (v : V) (S : Submodule K V) (hv : v ∈ S) :
    line A v ≤ rs (𝓞 K) S := by
  rintro _ ⟨t, -, rfl⟩
  exact S.smul_mem t hv

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem e_mem_II (N : NF H r) (a : Fin r) (ha : N.j ≤ a.val) : N.F.e a.castSucc ∈ II N.F N.F' := by
  have hc : N.c ≠ 0 := by
    intro h
    have := N.c_norm
    rw [h, zero_mul] at this
    exact zero_ne_one this
  refine ⟨Submodule.subset_span ⟨a, a.2, rfl⟩, ?_⟩
  have h1 : N.F'.e a.castSucc ∈ N.F'.X := Submodule.subset_span ⟨a, a.2, rfl⟩
  have h2 := N.F'.X.smul_mem N.c⁻¹ h1
  rwa [N.same a.castSucc ha, smul_smul, inv_mul_cancel₀ hc, one_smul] at h2

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem isotropicMeet_le_jointSpan (N : NF H r) : II N.F N.F' ≤ V0 N.F N.F' :=
  inf_le_left.trans (le_sup_left.trans le_sup_left)

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem eq_zero_of_mem (N : NF H r)
    (hrad : ∀ v ∈ V0 N.F N.F', (∀ w ∈ V0 N.F N.F', H.B v w = 0) ↔ v ∈ II N.F N.F')
    (d : V) (hd : d ∈ N.Ist) (hd' : d ∈ V0 N.F N.F') : d = 0 := by
  let φ : V →ₗ[K] V := ∑ a ∈ Finset.univ.filter (fun a : Fin r => N.j ≤ a.val),
    (H.B.flip (N.F.e a.castSucc)).smulRight (N.ist a)
  have h1 : N.Ist ≤ LinearMap.eqLocus φ LinearMap.id := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, hb, rfl⟩
    have hb' : N.j ≤ b.val := hb
    show φ (N.ist b) = N.ist b
    simp only [φ, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.flip_apply]
    rw [Finset.sum_eq_single b]
    · rw [← H.herm, N.ist_e b b hb']; simp
    · intro a _ hab
      rw [← H.herm, N.ist_e a b hb']; simp [hab]
    · intro h; exact absurd (by simpa using hb') h
  have h2 : φ d = d := h1 hd
  rw [← h2]
  simp only [φ, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.flip_apply]
  refine Finset.sum_eq_zero fun a ha => ?_
  have ha' : N.j ≤ a.val := by simpa using ha
  have he := e_mem_II N a ha'
  rw [← H.herm, (hrad _ (isotropicMeet_le_jointSpan N he)).2 he d hd']
  simp

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem Xa_le_X (F : FlagD H r) (j : ℕ) : F.Xa j ≤ F.X :=
  Submodule.span_mono (Set.image_mono fun b _ => b.2)

theorem P0_inf_V0_le_sup_of_radical (N : NF H r)
    (hrad : ∀ v ∈ V0 N.F N.F', (∀ w ∈ V0 N.F N.F', H.B v w = 0) ↔ v ∈ II N.F N.F') :
    N.P0 ⊓ rs (𝓞 K) (V0 N.F N.F') ≤ (N.P0 ⊓ rs (𝓞 K) (N.F.Xa N.j)) ⊔ (N.P0 ⊓ rs (𝓞 K) (N.F'.Xa N.j)) ⊔
      (N.P0 ⊓ rs (𝓞 K) (II N.F N.F')) ⊔ line 1 N.F.z := by
  set Q := (N.P0 ⊓ rs (𝓞 K) (N.F.Xa N.j)) ⊔ (N.P0 ⊓ rs (𝓞 K) (N.F'.Xa N.j)) ⊔
      (N.P0 ⊓ rs (𝓞 K) (II N.F N.F')) ⊔ line 1 N.F.z with hQ
  have hQV : Q ≤ rs (𝓞 K) (V0 N.F N.F') := by
    refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
    · exact inf_le_right.trans fun x hx =>
        ((Xa_le_X N.F N.j).trans (le_sup_left.trans le_sup_left) : N.F.Xa N.j ≤ V0 N.F N.F') hx
    · exact inf_le_right.trans fun x hx =>
        ((Xa_le_X N.F' N.j).trans (le_sup_right.trans le_sup_left) : N.F'.Xa N.j ≤ V0 N.F N.F') hx
    · exact inf_le_right.trans fun x hx => isotropicMeet_le_jointSpan N hx
    · exact line_le _ _ _ (Submodule.mem_sup_right (Submodule.subset_span (by simp)))
  have hP : N.P0 ≤ Q ⊔ rs (𝓞 K) N.Ist := by
    refine sup_le (le_sup_of_le_left (sup_le (sup_le ?_ ?_) le_sup_right)) (le_sup_of_le_right ?_)
    · refine iSup_le fun a => ?_
      have h0 : line (N.aa a) (N.F.e a.castSucc) ≤ N.P0 :=
        le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
          (le_iSup (fun a : Fin r => line (N.aa a) (N.F.e a.castSucc)) a)))
      by_cases ha : a.val < N.j
      · exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
          (le_inf h0 (line_le _ _ _ (Submodule.subset_span ⟨a, ha, rfl⟩)))))
      · exact le_sup_of_le_left (le_sup_of_le_right
          (le_inf h0 (line_le _ _ _ (e_mem_II N a (not_lt.1 ha)))))
    · refine iSup₂_le fun a ha => ?_
      have h0 : line (N.aa a) (N.F'.e a.castSucc) ≤ N.P0 :=
        le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_right
          (le_iSup₂ (f := fun (a : Fin r) (_ : a.val < N.j) => line (N.aa a) (N.F'.e a.castSucc)) a ha)))
      exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_right
          (le_inf h0 (line_le _ _ _ (Submodule.subset_span ⟨a, ha, rfl⟩)))))
    · exact iSup₂_le fun a ha => line_le _ _ _ (Submodule.subset_span ⟨a, ha, rfl⟩)
  rintro p ⟨hp, hpV⟩
  obtain ⟨u, hu, d, hd, rfl⟩ := Submodule.mem_sup.1 (hP hp)
  have hdV : d ∈ V0 N.F N.F' := by
    have := (V0 N.F N.F').sub_mem hpV (hQV hu)
    rwa [add_sub_cancel_left] at this
  rw [eq_zero_of_mem N hrad d hd hdV, add_zero]
  exact hu

theorem fix_of_mem_Rs (N : NF H r) {s : V ≃ₗ[K] V} (hs : s ∈ N.Rs) : ∀ y ∈ N.Wt, s y = y :=
  fun y hy => (mem_fixingSubgroup_iff _).1 hs.2 y hy

theorem split_smul (N : NF H r) {s : V ≃ₗ[K] V} (hs : s ∈ N.Rs) {Λ : Submodule (𝓞 K) V}
    (hT : latTh N.F N.F' (s • Λ) = latTh N.F N.F' Λ) (h : N.Split Λ) : N.Split (s • Λ) := by
  unfold NF.Split at h ⊢
  rw [hT, smul_inf_eq s Λ _ (fix_of_mem_Rs N hs), h]

theorem near_mono (N : NF H r) {𝔞 𝔟 : Ideal (𝓞 K)} (h : 𝔞 ≤ 𝔟) {Λ : Submodule (𝓞 K) V}
    (hn : N.Near 𝔟 Λ) : N.Near 𝔞 Λ :=
  ⟨(Submodule.smul_mono_left h).trans hn.1, (Submodule.smul_mono_left h).trans hn.2⟩

end

theorem exists_near : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ 𝔠 : Ideal (𝓞 K), 𝔠 ≠ ⊥ → (∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) → (∀ x ∈ 𝔠, (N.T : 𝓞 K) ∣ x) → (∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠, ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)), (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧ (x : K) * y / star (Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K)) → N.Split Λ → ∃ s ∈ N.Rs, N.Split (s • Λ) ∧ N.Near (𝔠 ^ (12 * r + 50)) (s • Λ) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ hg hΛ 𝔠 h0 hst hT hD hS
  have hrad := (GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N).1.2.2.2.1
  obtain ⟨s₁, hs₁, -, h₁⟩ := GlobalTheory.T.normalForm_flag_lattices_near_under_stabiliser K V H hK r N g Λ hg hΛ 𝔠 h0 hst hT hD
  obtain ⟨a₁, a₂, a₃, a₄⟩ := h₁ _ rfl
  obtain ⟨t₁, -, th₁, -⟩ := GlobalTheory.T.commonUnipotent_stabiliser_preserves_terms_and_datum K V H hK r N g Λ hg hΛ s₁ hs₁.1
  have hS₁ := split_smul N hs₁ th₁ hS
  obtain ⟨s₂, hs₂, hfix, h₂⟩ := GlobalTheory.T.normal_form_ideal_divisibility K V H hK r N g _ hg t₁ 𝔠 h0 hst hT hD
  obtain ⟨b₁, b₂, b₃⟩ := h₂ _ rfl
  obtain ⟨t₂, -, th₂, -⟩ := GlobalTheory.T.commonUnipotent_stabiliser_preserves_terms_and_datum K V H hK r N g _ hg t₁ s₂ hs₂.1
  have hS₂ := split_smul N hs₂ th₂ hS₁
  have e₁ := smul_inf_eq s₂ (s₁ • Λ) (N.F.Xa N.j) fun y hy => hfix y (Submodule.mem_sup_left hy)
  have e₂ := smul_inf_eq s₂ (s₁ • Λ) (N.F'.Xa N.j) fun y hy => hfix y (Submodule.mem_sup_right hy)
  have key : 𝔠 ^ (2 * r + 2) • (N.P0 ⊓ rs (𝓞 K) (V0 N.F N.F')) ≤ s₂ • s₁ • Λ := by
    refine (smul_mono_right _ (P0_inf_V0_le_sup_of_radical N hrad)).trans ?_
    rw [Submodule.smul_sup, Submodule.smul_sup, Submodule.smul_sup]
    refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
    · refine le_trans ?_ (e₁.ge.trans inf_le_left)
      exact le_inf a₁ (Submodule.smul_le_right.trans inf_le_right)
    · refine le_trans ?_ (e₂.ge.trans inf_le_left)
      exact le_inf a₂ (Submodule.smul_le_right.trans inf_le_right)
    · exact (Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))).trans b₁
    · exact (Submodule.smul_mono_left (Ideal.pow_le_self (by omega))).trans b₃
  obtain ⟨s₃, hs₃, hn⟩ := GlobalTheory.T.hermFramePair_split_term_near_reference_by_skew K V H hK r N g _ hg t₂ 𝔠 h0 hst hT hD hS₂ (2 * r + 2) (by omega)
    key (by rw [e₁]; exact a₃) (by rw [e₂]; exact a₄) b₂
  have hs₃' : s₃ ∈ N.Rs := ⟨hs₃.1.1, hs₃.2⟩
  obtain ⟨-, -, th₃, -⟩ := GlobalTheory.T.commonUnipotent_stabiliser_preserves_terms_and_datum K V H hK r N g _ hg t₂ s₃ hs₃'.1
  refine ⟨s₃ * (s₂ * s₁), N.Rs.mul_mem hs₃' (N.Rs.mul_mem hs₂ hs₁), ?_, ?_⟩
  · rw [mul_smul, mul_smul]
    exact split_smul N hs₃' th₃ hS₂
  · rw [mul_smul, mul_smul]
    exact near_mono N (Ideal.pow_le_pow_right (by omega)) hn

end GlobalTheory.DegCnt.NormalPos
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagUnipotentRadicalClosedSubgroupKeepsStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropicFlagUnipotentRadical_closed_subgroup_keeps : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → (∃ N : Subgroup (Formalism.REAL.UJ ε), (N : Set (Formalism.REAL.UJ ε)) = flagN ε W) ∧ IsClosed (flagN ε W) ∧ ∀ u ∈ flagN ε W, ∀ i, ∀ y ∈ W i, uMat u *ᵥ y ∈ W i := by
  first | exact @GlobalTheory.FlagMeas.UnipRad.flagN_subgroup_closed_keeps | exact GlobalTheory.FlagMeas.UnipRad.flagN_subgroup_closed_keeps | (intros; apply GlobalTheory.FlagMeas.UnipRad.flagN_subgroup_closed_keeps <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicLeviEmbeddingHomomorphismPropertiesStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropicLeviEmbedding_homomorphism_properties : ∀ k r : ℕ, (∀ u u' : Matrix (Fin r) (Fin r) ℂ, IsUnit u.det → IsUnit u'.det → uEmb k r (u * u') = uEmb k r u * uEmb k r u') ∧ uEmb k r 1 = 1 ∧ (∀ u : Matrix (Fin r) (Fin r) ℂ, IsUnit u.det → uEmb k r u ∈ GG k r ∧ (uEmb k r u)⁻¹ = uEmb k r u⁻¹ ∧ (∀ b : Fin r, uEmb k r u *ᵥ bvec (eI k r b) = ∑ a, u a b • bvec (eI k r a)) ∧ (∀ b : Fin r, uEmb k r u *ᵥ bvec (esI k r b) = ∑ a, star (u⁻¹ b a) • bvec (esI k r a)) ∧ ∀ w, inWb k r w → uEmb k r u *ᵥ w = w) ∧ (∀ x : UT r → ℂ, (upper x).det = 1 ∧ uEmb k r (upper x) ∈ Nset k r) := by
  first | exact @GlobalTheory.Amp.UEmb.uEmb_hom | exact GlobalTheory.Amp.UEmb.uEmb_hom | (intros; apply GlobalTheory.Amp.UEmb.uEmb_hom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicStabilizerRadicalStructureStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropicStabilizerRadical_structure : ∀ k r : ℕ, (∀ (B : Fin r → Fin (k + 1) → ℂ) (S : Matrix (Fin r) (Fin r) ℂ), (∀ a : Fin r, pEl k r B S *ᵥ bvec (eI k r a) = bvec (eI k r a)) ∧ (∀ j : Fin (k + 1), pEl k r B S *ᵥ bvec (wI k r j) = bvec (wI k r j) - ∑ b, herm (Hb k) (bvec j) (B b) • bvec (eI k r b)) ∧ (∀ b : Fin r, pEl k r B S *ᵥ bvec (esI k r b) = bvec (esI k r b) + (∑ j, B b j • bvec (wI k r j)) + ∑ a, (S a b - herm (Hb k) (B b) (B a) / 2) • bvec (eI k r a)) ∧ (Sᴴ = -S → pEl k r B S ∈ Nset k r ∧ (pEl k r B S)⁻¹ = pEl k r (-B) (-S))) ∧ (∀ (s : UT r → ℂ) (t : Fin r → ℝ), (skewM s t)ᴴ = -skewM s t) ∧ (∀ S : Matrix (Fin r) (Fin r) ℂ, Sᴴ = -S → ∃! p : (UT r → ℂ) × (Fin r → ℝ), S = skewM p.1 p.2) ∧ (∀ B B' (S S' : Matrix (Fin r) (Fin r) ℂ), pEl k r B S * pEl k r B' S' = pEl k r (B + B') (S + S' + Matrix.of fun a b => (herm (Hb k) (B b) (B' a) - herm (Hb k) (B' b) (B a)) / 2)) ∧ ∀ m ∈ UH (Hb k), mEmb k r m ∈ GG k r ∧ (mEmb k r m)⁻¹ = mEmb k r m⁻¹ := by
  first | exact @GlobalTheory.Amp.Rad.radical | exact GlobalTheory.Amp.Rad.radical | (intros; apply GlobalTheory.Amp.Rad.radical <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaDecompComplexifiedMaxCompactStatement
section
open GlobalTheory.Dec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_decomp_complexifiedMaxCompact : IwasawaKC := by
  first | exact @GlobalTheory.Dec.iwasawaKC | exact GlobalTheory.Dec.iwasawaKC | (intros; apply GlobalTheory.Dec.iwasawaKC <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaDecompositionUnitaryIsotropicFlagStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_decomposition_unitary_isotropicFlag : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → (∀ g : Formalism.REAL.UJ ε, ∃ u ∈ flagN ε W, ∃ m ∈ flagM ε W, ∃ k ∈ maxK ε, g = u * m * k) ∧ ∀ u ∈ flagN ε W, ∀ m ∈ flagM ε W, u * m ∈ maxK ε → u = 1 := by
  first | exact @GlobalTheory.RealIwasawa.iwasawa | exact GlobalTheory.RealIwasawa.iwasawa | (intros; apply GlobalTheory.RealIwasawa.iwasawa <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeStabiliserCommensurableIntegralPoints
section
open NumberField GlobalTheory.HL
open scoped Pointwise Classical

namespace GlobalTheory.HL.CommInt

theorem stabL_relIndex_K0_ne_zero_of_four_mul_add_seven_le : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig) (r k : ℕ) (G : GFrames A r k), 4 * r + 7 ≤ k → ∀ Λ : G.Lt, Submodule.IsLattice E Λ → (G.stabL Λ).relIndex G.K0 ≠ 0 ∧ G.K0.relIndex (G.stabL Λ) ≠ 0 := by
  intro F E _ _ _ _ _ sig A r k G hk Λ hΛ
  obtain ⟨-, hlat, -⟩ := GlobalTheory.T.numberField_lattice_determined_by_local_lattices A (k + 2 * r + 1) Λ hΛ
  obtain ⟨hfin, -⟩ := GlobalTheory.HL.MassProduct.mass_eq_finprod A r k G hk Λ hΛ
  let U : ∀ p, Subgroup (G.S p).GLV :=
    fun p => (G.S p).St ⊓ MulAction.stabilizer (G.S p).GLV (A.lat p Λ)
  let K : ∀ p, Subgroup (G.S p).GLV := fun p => (G.S p).K0
  have hidx : ∀ p, (K p).relIndex (U p) ≠ 0 ∧ (U p).relIndex (K p) ≠ 0 := by
    intro p
    haveI := (A.loc p).lf
    haveI := (A.loc p).char0
    obtain ⟨a, b, -⟩ := (GlobalTheory.HL.volSt (A.L p) r k (G.S p)).1 (A.lat p Λ) (hlat p)
    exact ⟨a, b⟩
  have hKU : {p | K p ≠ U p}.Finite := hfin.subset fun p hp h => hp h.symm
  obtain ⟨h1, h2, -⟩ := GlobalTheory.T.haarInvVolumeRelIndex_pi_univ_eq_finprod K U hKU hidx
  let φ := GlobalTheory.HL.MassProduct.extHom A (k + 2 * r + 1)
  have e1 : G.K0 = (Subgroup.pi Set.univ K).comap φ := (GlobalTheory.HL.MassProduct.comap_pi A _ K).symm
  have e2 : G.stabL Λ = (Subgroup.pi Set.univ U).comap φ := (GlobalTheory.HL.MassProduct.comap_pi A _ U).symm
  rw [e1, e2, Subgroup.relIndex_comap, Subgroup.relIndex_comap]
  exact ⟨fun h0 => h2 (Subgroup.relIndex_eq_zero_of_le_right (Subgroup.map_comap_le _ _) h0),
    fun h0 => h1 (Subgroup.relIndex_eq_zero_of_le_right (Subgroup.map_comap_le _ _) h0)⟩

end GlobalTheory.HL.CommInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralFlagSizeDensityLeOneStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_flagSizeDensity_le_one : ∀ (n f a : ℕ) (j : Fin a → ℕ), 1 ≤ f → (∀ i, 1 ≤ j i) → 2 * ∑ i, j i + 1 ≤ n → ∫⁻ τ in simplexH a, ENNReal.ofReal (dens n f j τ) ≤ 1 := by
  first | exact @GlobalTheory.DensityIntegral.lintegral_dens_le_one | exact GlobalTheory.DensityIntegral.lintegral_dens_le_one | (intros; apply GlobalTheory.DensityIntegral.lintegral_dens_le_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocDecOfDecGapGapGe
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.Dec

theorem locDec_of_decGap_gapGe : DecGap → ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → GapGe B h →
    (∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) → LocDec B h := by
  intro hD B d h hds hgap hh v g
  obtain ⟨h1, h2, h3, -⟩ := hds v
  have hw : B.w v ∈ lowKSub (B.I.ε v) (B.lam v) (B.σ v) := h3.2
  have hn : ‖B.w v‖ = 1 := h3.1
  have := (hD _ _ _ _ _ h1 h2 h (hgap v) (hh v) (uMat g) g.2 _ hw _ hw).2
  simpa [hn] using this

end GlobalTheory.Dec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LogUnitarySphereVolumeProductRatioLeLargeRankStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_unitarySphereVolumeProduct_ratio_le_large_rank : ∀ (n p j : ℕ), 18 ≤ n → j ≤ p → p ≤ n → (n : ℝ) - 2 * Real.sqrt n ≤ (p : ℝ) - j → (n : ℝ) / 2 ≤ (p : ℝ) - j → Real.log (sphV p / sphV (p - j)) ≤ j * Real.log (2 * Real.pi) - j * ((n : ℝ) - 2 * Real.sqrt n) * Real.log (n / (2 * Real.pi * Real.exp 1)) := by
  first | exact @GlobalTheory.SphRatio.log_sphV_ratio_le | exact GlobalTheory.SphRatio.log_sphV_ratio_le | (intros; apply GlobalTheory.SphRatio.log_sphV_ratio_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassRatioRankFactorStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mass_ratio_rank_factor : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (M : ℕ), 1 ≤ M → Formalism.HermitianLatticesTheory.massRatioRightSide E M * volU M ^ Formalism.HermitianLatticesTheory.fDeg E = rankFac E M * volU (M - 1) ^ Formalism.HermitianLatticesTheory.fDeg E := by
  first | exact @GlobalTheory.FlagMeas.mass_ratio_mul_unitary_volume | exact GlobalTheory.FlagMeas.mass_ratio_mul_unitary_volume | (intros; apply GlobalTheory.FlagMeas.mass_ratio_mul_unitary_volume <;> assumption)
end

