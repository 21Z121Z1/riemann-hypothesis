import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0211
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0215
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DensityInChart
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
import Formalism.PeriodIntegrals.Bundle0008
import Formalism.LocalRingCardinality.DataCD
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0210
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0179
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolEqOfAedisjoint
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EmbeddedDatumOfTermDefiniteSpace
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0003
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0214
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0209
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFinEmb
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0190
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0213
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsCoordinatesInverseFirstColumnInfiniteGL
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGramRepresentativeSizeLeHHSq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsFolnerSequenceBessel
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CwContIntegralCommStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cwCont_integral_comm_alt : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] (Bm : R.H → V), (∀ v ∈ R.sm, ∀ w ∈ R.sm, Bm (v + w) = Bm v + Bm w) → (∀ (a : ℂ), ∀ v ∈ R.sm, Bm (a • v) = a • Bm v) → PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ Bm → ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] (μ : Measure X) [IsFiniteMeasure μ] (κ : X → Mx k r) (p : X → ℂ), Continuous κ → (∀ x, κ x ∈ GG k r) → Continuous p → ∀ v ∈ R.sm, (∫ x, p x • R.σ (κ x) v ∂μ) ∈ R.sm → Bm (∫ x, p x • R.σ (κ x) v ∂μ) = ∫ x, p x • Bm (R.σ (κ x) v) ∂μ := by
  first | exact @GlobalTheory.cwCont_integral_comm | exact GlobalTheory.cwCont_integral_comm | (intros; apply GlobalTheory.cwCont_integral_comm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteLatticeDiscriminantModuleCardDetSq
section
namespace GlobalTheory.LoopC.DetCard

section General

open NumberField GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.MainNotions.S

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V] [Module K V]
  [IsScalarTower (𝓞 K) K V]

theorem map_latIn {U : Submodule K V} {N : Submodule (𝓞 K) V} (hN : ∀ x ∈ N, x ∈ U) :
    N.toAddSubgroup = (latIn U N).toAddSubgroup.map U.subtype.toAddMonoidHom := by
  ext x
  constructor
  · intro h1
    exact ⟨⟨x, hN x h1⟩, h1, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact hy

theorem idxN_latIn {U : Submodule K V} {A B : Submodule (𝓞 K) V} (hA : ∀ x ∈ A, x ∈ U)
    (hB : ∀ x ∈ B, x ∈ U) : idxN A B = idxN (latIn U A) (latIn U B) := by
  rw [idxN, idxN, map_latIn hA, map_latIn hB, AddSubgroup.relIndex_map_map_of_injective _ _ U.injective_subtype]

theorem isLattice_latIn_span {U : Submodule K V} {N : Submodule (𝓞 K) V} (hN : N.FG)
    (hU : Submodule.span K (N : Set V) = U) : Submodule.IsLattice K (latIn U N) := by
  refine ⟨?_, ?_⟩
  · refine Submodule.fg_of_fg_map_injective (U.subtype.restrictScalars (𝓞 K)) U.injective_subtype ?_
    exact Submodule.FG.of_le hN (Submodule.map_comap_le _ _)
  · apply Submodule.map_injective_of_injective U.injective_subtype
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
    refine Eq.trans ?_ hU
    congr 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hU ▸ Submodule.subset_span hx⟩, hx, rfl⟩

variable [StarRing K]

theorem latIn_dualInH (h : V →ₗ⋆[K] V →ₗ[K] K) {U : Submodule K V} {N : Submodule (𝓞 K) V}
    (hU : Submodule.span K (N : Set V) = U) :
    latIn U (Lat.dualInH h N) = dual (hRes h U) (latIn U N) := by
  ext x
  constructor
  · rintro ⟨h1, -⟩
    exact (dualBasic_mem_dual _ _ _).2 fun y hy => (dualBasic_mem_dual _ _ _).1 h1 y hy
  · intro hx
    refine ⟨(dualBasic_mem_dual _ _ _).2 fun z hz => ?_, ?_⟩
    · exact (dualBasic_mem_dual _ _ _).1 hx ⟨z, hU ▸ Submodule.subset_span hz⟩ hz
    · change (x : V) ∈ Submodule.span K (N : Set V)
      rw [hU]
      exact x.2

theorem idxN_dualInH (h : V →ₗ⋆[K] V →ₗ[K] K) {U : Submodule K V} {N : Submodule (𝓞 K) V}
    (hU : Submodule.span K (N : Set V) = U) :
    idxN (Lat.dualInH h N) N = discN (hRes h U) (latIn U N) := by
  rw [idxN_latIn (U := U) (A := Lat.dualInH h N) (B := N) (fun x hx => hU ▸ (Submodule.mem_inf.1 hx).2) (fun x hx => hU ▸ Submodule.subset_span hx),
    latIn_dualInH h hU, discN]

theorem general [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (hK : IsCMUnram K) (hs : h.IsSymm) (hp : PD h)
    (M : Submodule (𝓞 K) V) (hM : M.FG) (hI : IsIntegralLat h M) :
    1 ≤ idxN (Lat.dualInH h M) M ∧ (idxN (Lat.dualInH h M) M : ℝ) = Lat.latDetH h M ^ 2 ∧
      ∀ P : Submodule (𝓞 K) V, P ≤ M →
        Module.finrank K (Submodule.span K (P : Set V)) = Module.finrank K (Submodule.span K (M : Set V)) →
        1 ≤ idxN M P ∧ Lat.latDetH h P = Lat.latDetH h M * idxN M P := by
  set U := Submodule.span K (M : Set V) with hUdef
  have hsU : (hRes h U).IsSymm := ⟨fun x y => hs.eq x y⟩
  have hpU : PD (hRes h U) := fun τ x hx => hp τ x fun e => hx (Subtype.ext e)
  have hnU := DetAgree.nondeg_of_pd hpU
  have key : ∀ N : Submodule (𝓞 K) V, N ≤ M → Submodule.span K (N : Set V) = U →
      IsIntLat (hRes h U) (latIn U N) ∧ discN (hRes h U) (latIn U N) ≠ 0 ∧
        Lat.latDetH h N = Real.sqrt (discN (hRes h U) (latIn U N) : ℝ) := by
    intro N hN hU
    have a : IsIntLat (hRes h U) (latIn U N) :=
      ⟨isLattice_latIn_span (hM.of_le hN) hU, fun x hx y hy => hI x (hN hx) y (hN hy)⟩
    have n0 := (DiscOrder.main K U _ hK hsU hnU _ a).1
    refine ⟨a, n0, ?_⟩
    rw [← idxN_dualInH h hU] at n0 ⊢
    rw [Lat.latDetH, DetAgree.genIdxH_eq_idxN _ n0]
    intro x hx
    exact ⟨(dualBasic_mem_dual _ _ _).2 fun y hy => hI y (hN hy) x (hN hx), Submodule.subset_span hx⟩
  obtain ⟨m1, m2, m3⟩ := key M le_rfl rfl
  refine ⟨?_, ?_, fun P hP hr => ?_⟩
  · rw [idxN_dualInH h hUdef.symm]
    exact Nat.pos_of_ne_zero m2
  · rw [idxN_dualInH h hUdef.symm, m3, Real.sq_sqrt (Nat.cast_nonneg _)]
  · have hU : Submodule.span K (P : Set V) = U :=
      Submodule.eq_of_le_of_finrank_eq (Submodule.span_mono hP) hr
    obtain ⟨p1, -, p3⟩ := key P hP hU
    obtain ⟨q1, q2⟩ := (DiscOrder.main K U _ hK hsU hnU _ p1).2.2.1 _ m1 (Submodule.comap_mono hP)
    rw [← idxN_latIn (U := U) (fun x hx => Submodule.subset_span hx)
      (fun x hx => Submodule.subset_span (hP hx))] at q1 q2
    refine ⟨Nat.pos_of_ne_zero q1, ?_⟩
    rw [p3, m3, q2, Nat.cast_mul, Nat.cast_pow, Real.sqrt_mul (Nat.cast_nonneg _),
      Real.sqrt_sq (Nat.cast_nonneg _)]

end General

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem main : ∀ (D : D7) (M : LatW D), M.FG → IsPosDef (D.sp.X 0).hT → Formalism.HermitianLatticesTheory.IsIntegralLat (D.sp.X 0).hT M → 1 ≤ idxW D (dualInH (D.sp.X 0).hT M) M ∧ (idxW D (dualInH (D.sp.X 0).hT M) M : ℝ) = detW D M ^ 2 ∧ ∀ P : LatW D, P ≤ M → rkW D P = rkW D M → 1 ≤ idxW D M P ∧ detW D P = detW D M * idxW D M P := by
  intro D M hM hp hI
  exact general (D.sp.X 0).hT D.sp.cm.cmUnram (D.sp.X 0).herm hp M hM hI

end GlobalTheory.LoopC.DetCard
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DensityInChartStatement
section
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_measure_image_ball_div_volume : ∀ (m : ℕ) (S : Set (Matrix (Fin m) (Fin m) ℂ)) (μ : Measure (PI.MtM m)) (c : ℝ≥0∞), PI.IsMatGroup S → PI.IsHaarOnM S μ → HasDens S μ c → ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (Φ : E → Matrix (Fin m) (Fin m) ℂ) (L : E ≃L[ℝ] lieE S), Φ 0 = 1 → (∀ᶠ x in 𝓝 (0 : E), Φ x ∈ S) → (∀ i j, ∃ D : E →L[ℝ] ℂ, HasStrictFDerivAt (fun x => Φ x i j) D 0 ∧ ∀ v, D v = unrealify ((L v : lieE S) : EuclideanSpace ℝ _) i j) → Tendsto (fun ρ : ℝ => μ ((fun x => Matrix.of.symm (Φ x)) '' Metric.ball 0 ρ) / volume (L '' Metric.ball (0 : E) ρ)) (𝓝[>] 0) (𝓝 c) := by
  first | exact @GlobalTheory.ChartDensity.density_in_chart | exact GlobalTheory.ChartDensity.density_in_chart | (intros; apply GlobalTheory.ChartDensity.density_in_chart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DetMatrixSandwichLinearMapStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.MeanDual
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_matrix_sandwich_linear_map : ∀ (ι : Type) [Fintype ι] (j : ℕ) (A B : ι → Matrix (Fin j) (Fin j) ℂ) (L : (ι → Fin j → Fin j → ℂ) →ₗ[ℝ] (ι → Fin j → Fin j → ℂ)), (∀ h w, Matrix.of (L h w) = A w * Matrix.of (h w) * B w) → LinearMap.det L = ∏ w, (‖(A w).det‖ ^ 2 * ‖(B w).det‖ ^ 2) ^ j := by
  first | exact @GlobalTheory.MatMulDet.det_real_mul_mul | exact GlobalTheory.MatMulDet.det_real_mul_mul | (intros; apply GlobalTheory.MatMulDet.det_real_mul_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DetNormSqEqOneOfMemLatticeAutStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detNorm_eq_one_of_mem_autGL_var : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ (j : ℕ) (Λ : Submodule (𝓞 E) (Fin j → E)), Submodule.IsLattice E Λ → ∀ γ ∈ autGL E j Λ, detNorm E j γ = 1 := by
  first | exact @GlobalTheory.OrbitTerm.detNorm_eq_one_of_mem_autGL | exact GlobalTheory.OrbitTerm.detNorm_eq_one_of_mem_autGL | (intros; apply GlobalTheory.OrbitTerm.detNorm_eq_one_of_mem_autGL <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EmbeddedDatumOfTermDefiniteSpaceStatement
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embeddedDatum_of_term_definiteSpace : ∀ (K V W : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (H : HermSpace K V) (HW : HermSpace K W) (e : W →ₗ[K] V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (F G : FlagD H r) (𝔡 : Ideal (𝓞 K)) (N : NF H r) (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → IsEmb F HW e → Adapt F G 𝔡 N → N.IsTerm g Λ → IsDat HW g (lat0 F e Λ) r (N.gI g Λ) (datOf F G e g Λ) ∧ 1 ≤ N.gI g Λ ∧ (N.gI g Λ : ℝ) ≤ N.Del ∧ GlobalTheory.Mass.PD HW.B.flip ∧ Module.finrank K W + 2 * r + 1 = Module.finrank K V := by
  first | exact @GlobalTheory.DegAsm.isDat_datOf | exact GlobalTheory.DegAsm.isDat_datOf | (intros; apply GlobalTheory.DegAsm.isDat_datOf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EuclideanBallAsymptoticsFinitePi
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.LeviIso

theorem IsRadial.comp_measurableEquiv {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X}
    {ν : Measure Y} (e : X ≃ᵐ Y) (he : MeasurePreserving e μ ν) {q : X → ℝ} {p : Y → ℝ} {d : ℕ}
    (hq : ∀ x, q x = p (e x)) (h : IsRadial ν p d) : IsRadial μ q d := by
  unfold IsRadial at *
  refine h.congr fun r => ?_
  rw [← he.measure_preimage_equiv]
  simp only [hq, Set.preimage_ofPred_eq]

theorem isRadial_pi : ∀ (a : ℕ) (X : Fin a → Type) [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i))
    [∀ i, SigmaFinite (μ i)] (q : ∀ i, X i → ℝ) (d : Fin a → ℕ), (∀ i, Measurable (q i)) →
    (∀ i x, 0 ≤ q i x) → (∀ i, IsRadial (μ i) (q i) (d i)) →
    IsRadial (Measure.pi μ) (fun x => ∑ i, q i (x i)) (∑ i, d i) := by
  intro a
  induction a with
  | zero =>
    intro X _ μ _ q d _ _ _
    rw [Fin.sum_univ_zero]
    unfold IsRadial
    rw [volume_euclideanSpace_eq_dirac, Measure.dirac_apply_of_mem (Metric.mem_ball_self one_pos)]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr' : (0 : ℝ) ≤ r := le_of_lt hr
    rw [Measure.pi_of_empty, Measure.dirac_apply_of_mem (by simpa using hr')]
    simp
  | succ a ih =>
    intro X _ μ _ q d hm h0 hr
    have h := GlobalTheory.T.hasEuclideanBallVolumeSublevelAsymptotics_prod _ _ (μ 0) (Measure.pi fun j => μ (Fin.succAbove 0 j)) (q 0)
      (fun x => ∑ j, q (Fin.succAbove 0 j) (x j)) (d 0) (∑ j, d (Fin.succAbove 0 j)) (hm 0)
      (Finset.measurable_sum _ fun j _ => (hm _).comp (measurable_pi_apply j)) (h0 0)
      (fun y => Finset.sum_nonneg fun j _ => h0 _ _) (hr 0)
      (ih _ _ _ _ (fun j => hm _) (fun j => h0 _) fun j => hr _)
    rw [Fin.sum_univ_succAbove d 0]
    exact h.comp_measurableEquiv _ (measurePreserving_piFinSuccAbove μ 0)
      fun x => Fin.sum_univ_succAbove (fun i => q i (x i)) 0

end GlobalTheory.LeviIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAddEquivOfCard
section
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

namespace GlobalTheory.RowLev

theorem exists_addEquiv_of_card {Q : Type} [AddCommGroup Q] {p N : ℕ} [hp : Fact p.Prime] [Module (ZMod p) Q]
    (hc : Nat.card Q = p ^ N) : Nonempty (Q ≃+ (Fin N → ZMod p)) := by
  have : Finite Q := Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ hp.out.ne_zero)
  have hr : Module.finrank (ZMod p) Q = N := by
    apply Nat.pow_right_injective hp.out.two_le
    have := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Q)
    rw [Nat.card_zmod, hc] at this
    exact this.symm
  exact ⟨(Module.finBasisOfFinrankEq (ZMod p) Q hr).equivFun.toAddEquiv⟩

theorem exists_coords_of_card {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {p N : ℕ} (hp : p.Prime)
    (r : R →+* ZMod p) (hc : Nat.card (M ⧸ (RingHom.ker r • (⊤ : Submodule R M))) = p ^ N) :
    ∃ c : M →ₛₗ[r] (Fin N → ZMod p), Function.Surjective c ∧
      ∀ y, c y = 0 ↔ y ∈ RingHom.ker r • (⊤ : Submodule R M) := by
  have : Fact p.Prime := ⟨hp⟩
  set S : Submodule R M := RingHom.ker r • (⊤ : Submodule R M) with hS
  have hk : ∀ a : R, r a = 0 → ∀ q : M ⧸ S, a • q = 0 := by
    intro a ha q
    obtain ⟨y, rfl⟩ := S.mkQ_surjective q
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul ha Submodule.mem_top
  have hpq : ∀ q : M ⧸ S, p • q = 0 := fun q => by
    rw [← Nat.cast_smul_eq_nsmul R]
    exact hk _ (by rw [map_natCast, ZMod.natCast_self]) q
  obtain ⟨e⟩ := @exists_addEquiv_of_card (M ⧸ S) _ p N _ (AddCommGroup.zmodModule hpq) hc
  have hs : ∀ (a : R) (q : M ⧸ S), e (a • q) = r a • e q := by
    intro a q
    have h1 : (a - ((r a).val : R)) • q = 0 := hk _ (by simp) q
    rw [sub_smul, sub_eq_zero] at h1
    rw [h1, Nat.cast_smul_eq_nsmul, map_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]
  refine ⟨{ toFun := fun y => e (S.mkQ y)
            map_add' := fun x y => by rw [map_add, map_add]
            map_smul' := fun a y => by rw [map_smul, hs] },
    e.surjective.comp S.mkQ_surjective, fun y => ?_⟩
  show e (S.mkQ y) = 0 ↔ _
  rw [map_eq_zero_iff _ e.injective, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]

theorem plFrame_nonempty : ∀ (I : AutInst) (N p : ℕ) (w : HeightOneSpectrum (𝓞 I.E)), I.n = N → p.Prime → Ideal.absNorm w.asIdeal = p → Nonempty (PlFrame I N p w) ∧ ∀ (fr : PlFrame I N p w) (y : I.Lf), fr.c y = 0 ↔ (y : Fin I.n → (I.E ⊗[I.F] Af I.F)) ∈ extId I w.asIdeal • I.Lf := by
  intro I N p w hN hp hw
  refine ⟨?_, fun fr y => fr.c_ker y⟩
  obtain ⟨r, hr⟩ := Inhab.exists_reduction (F := I.F) p hp w hw
  have hk := Inhab.ker_eq_extId hp.ne_zero r hr
  have hc := GlobalTheory.T.card_lattice_quot_prime I p w hp hw
  subst hN
  rw [← hk] at hc
  obtain ⟨c, h1, h2⟩ := exists_coords_of_card hp r hc
  refine ⟨⟨r, fun a _ => hr a, c, h1, fun y => ?_⟩⟩
  rw [h2, hk]
  exact Submodule.mem_smul_top_iff _ _ y

end GlobalTheory.RowLev
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsClosedEmbeddingOrthogonalUnitaryRealPlace
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

namespace GlobalTheory.StabUnfold

theorem star_dot_Jm {n : ℕ} (ε : Fin n → Bool) (x : Fin n → ℂ) :
    star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ x) = (qEps ε x : ℂ) := by
  unfold qEps Formalism.REAL.Jm
  simp only [dotProduct, mulVec_diagonal, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_mul,
    Complex.ofReal_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi : (starRingEnd ℂ) (x i) * x i = ((‖x i‖ : ℝ) : ℂ) ^ 2 := Complex.conj_mul' (x i)
  split_ifs
  · simp [hi]
  · simp [hi]

theorem realUJ_eq {n : ℕ} (ε : Fin n → Bool) :
    Formalism.UG.UJ (starRingEnd ℂ) (Formalism.REAL.Jm ε) = Formalism.REAL.UJ ε := by
  unfold Formalism.REAL.UJ Formalism.UG.UJ Formalism.REAL.inUJ
  have hc : ∀ M : Matrix (Fin n) (Fin n) ℂ, Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ := by
    intro M
    ext i j
    simp [Formalism.UG.cT, Matrix.conjTranspose_apply, Complex.star_def]
  ext g
  change Formalism.UG.cT (starRingEnd ℂ) (g : Matrix (Fin n) (Fin n) ℂ) * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε ↔
    (g : Matrix (Fin n) (Fin n) ℂ)ᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε
  rw [hc]

theorem exists_closedEmbedding_unitary_orthogonal (n m : ℕ) (ε : Fin n → Bool) (ε' : Fin m → Bool) (s : Bool)
    (x₀ : Fin n → ℂ) (B : Matrix (Fin n) (Fin m) ℂ) (hn : m + 1 = n) (hq : qEps ε x₀ = sgn ℝ s)
    (hx : star x₀ ᵥ* (Formalism.REAL.Jm ε * B) = 0) (hB : Bᴴ * Formalism.REAL.Jm ε * B = Formalism.REAL.Jm ε') :
    ∃ j : Formalism.REAL.UJ ε' →* Formalism.REAL.UJ ε, Topology.IsClosedEmbedding j ∧
      ∀ g, uMat (j g) *ᵥ x₀ = x₀ ∧ uMat (j g) * B = B * uMat g := by
  unfold uMat
  have hJh : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := by
    unfold Formalism.REAL.Jm
    rw [diagonal_conjTranspose]
    congr 1
    funext a
    by_cases h : ε a <;> simp [h]
  have hdet : (Formalism.REAL.Jm ε').det ≠ 0 := by
    unfold Formalism.REAL.Jm
    rw [det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun a _ => by by_cases h : ε' a <;> simp [h]
  have hβ : star x₀ ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ x₀) ≠ 0 := by
    rw [star_dot_Jm, hq]
    cases s <;> simp [sgn]
  obtain ⟨u, A', hA'B, hA'x, huB, hux, hres, hBJx⟩ :=
    exists_dual_of_anisotropic_orthogonal ℂ n m (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε') x₀ B hn hJh hdet hβ hx hB
  have hcT : ∀ {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℂ), Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ := by
    intro p q M
    ext i k
    simp [Formalism.UG.cT, Matrix.conjTranspose_apply, Complex.star_def]
  have hstar : (fun i => starRingEnd ℂ (x₀ i)) = star x₀ := by
    funext i
    simp [Complex.star_def]
  obtain ⟨j, hjmat, hjrange⟩ := GlobalTheory.T.exists_unitary_orthogonal_embedding_stabilizer ℂ (starRingEnd ℂ) n m (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε') x₀ u B A'
    (by rw [hstar]; exact isUnit_iff_ne_zero.mpr hβ) (by rw [hstar]; exact hx) (by rw [hcT]; exact hBJx)
    (by rw [hcT]; exact hB) hA'B hA'x huB hux hres
  obtain ⟨jj, hjj, hrange⟩ : ∃ jj : Formalism.REAL.UJ ε' →* Formalism.REAL.UJ ε,
      (∀ g, ((jj g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) =
        vecMulVec x₀ u + B * ((g : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) * A') ∧
      ∀ h : Formalism.REAL.UJ ε, ((h : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) *ᵥ x₀ = x₀ → ∃ g, jj g = h := by
    refine ⟨(MulEquiv.subgroupCongr (realUJ_eq ε)).toMonoidHom.comp
      (j.comp (MulEquiv.subgroupCongr (realUJ_eq ε')).symm.toMonoidHom), fun g => hjmat _, ?_⟩
    intro h hh
    obtain ⟨g', hg'⟩ := hjrange ((MulEquiv.subgroupCongr (realUJ_eq ε)).symm h) hh
    refine ⟨MulEquiv.subgroupCongr (realUJ_eq ε') g', ?_⟩
    apply Subtype.ext
    exact congrArg Subtype.val hg'
  have h0 : vecMulVec x₀ u * B = 0 := by
    ext i k
    have hk := congrFun huB k
    simp only [vecMul, dotProduct, Pi.zero_apply] at hk
    simp only [mul_apply, vecMulVec_apply, Matrix.zero_apply, mul_assoc, ← Finset.mul_sum, hk, mul_zero]
  have hv : vecMulVec x₀ u *ᵥ x₀ = x₀ := by
    ext i
    simp only [mulVec, dotProduct, vecMulVec_apply, mul_assoc, ← Finset.mul_sum]
    rw [show ∑ k, u k * x₀ k = 1 from hux, mul_one]
  have hfix : ∀ g, ((jj g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) *ᵥ x₀ = x₀ := by
    intro g
    rw [hjj, add_mulVec, hv, ← mulVec_mulVec, hA'x, mulVec_zero, add_zero]
  have hcomm : ∀ g, ((jj g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) * B =
      B * ((g : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) := by
    intro g
    rw [hjj, Matrix.add_mul, h0, zero_add, Matrix.mul_assoc (B * _), hA'B, Matrix.mul_one]
  have hback : ∀ M : Matrix (Fin m) (Fin m) ℂ, A' * (vecMulVec x₀ u + B * M * A') * B = M := by
    intro M
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc A' (vecMulVec x₀ u), h0, Matrix.mul_zero, zero_add,
      Matrix.mul_assoc, Matrix.mul_assoc, hA'B, Matrix.mul_one, ← Matrix.mul_assoc, hA'B, Matrix.one_mul]
  have hval' : Continuous fun g : Formalism.REAL.UJ ε' => ((g : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) :=
    Units.continuous_val.comp continuous_subtype_val
  have hinv' : Continuous fun g : Formalism.REAL.UJ ε' => (((g : GL (Fin m) ℂ)⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) :=
    Units.continuous_coe_inv.comp continuous_subtype_val
  have hjinv : ∀ g, ((((jj g : GL (Fin n) ℂ))⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) =
      vecMulVec x₀ u + B * (((g : GL (Fin m) ℂ)⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) * A' := by
    intro g
    have h1 := hjj g⁻¹
    rw [map_inv] at h1
    exact h1
  have hcont : Continuous jj := by
    refine continuous_induced_rng.2 ?_
    rw [Units.continuous_iff]
    constructor
    · exact Continuous.congr (continuous_const.add ((continuous_const.matrix_mul hval').matrix_mul continuous_const))
        fun g => (hjj g).symm
    · exact Continuous.congr (continuous_const.add ((continuous_const.matrix_mul hinv').matrix_mul continuous_const))
        fun g => (hjinv g).symm
  let ψ : Formalism.REAL.UJ ε → Matrix (Fin m) (Fin m) ℂ × (Matrix (Fin m) (Fin m) ℂ)ᵐᵒᵖ := fun h =>
    (A' * ((h : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) * B,
      MulOpposite.op (A' * (((h : GL (Fin n) ℂ)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) * B))
  have hψc : Continuous ψ := by
    refine Continuous.prodMk ?_ ?_
    · exact (continuous_const.matrix_mul (Units.continuous_val.comp continuous_subtype_val)).matrix_mul
        continuous_const
    · exact MulOpposite.continuous_op.comp ((continuous_const.matrix_mul
        (Units.continuous_coe_inv.comp continuous_subtype_val)).matrix_mul continuous_const)
  have hψ : ∀ g, ψ (jj g) = Units.embedProduct _ (g : GL (Fin m) ℂ) := by
    intro g
    refine Prod.ext ?_ ?_
    · show A' * ((jj g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) * B = ((g : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ)
      rw [hjj, hback]
    · show MulOpposite.op (A' * ((((jj g : GL (Fin n) ℂ))⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) * B) =
        MulOpposite.op ((((g : GL (Fin m) ℂ))⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ)
      rw [hjinv, hback]
  have hind : Topology.IsInducing jj := by
    refine Topology.IsInducing.of_comp hcont hψc ?_
    have he : ψ ∘ jj = fun g : Formalism.REAL.UJ ε' => Units.embedProduct _ (g : GL (Fin m) ℂ) := funext hψ
    rw [he]
    exact Units.isInducing_embedProduct.comp Topology.IsInducing.subtypeVal
  have hinj : Function.Injective jj := by
    intro a b hab
    have hc := congrArg ψ hab
    rw [hψ, hψ] at hc
    exact Subtype.ext (Units.ext (congrArg Prod.fst hc))
  have hrng : Set.range jj = {h : Formalism.REAL.UJ ε | ((h : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) *ᵥ x₀ = x₀} := by
    ext h
    constructor
    · rintro ⟨g, rfl⟩
      exact hfix g
    · intro hh
      exact hrange h hh
  have hclosed : IsClosed (Set.range jj) := by
    rw [hrng]
    exact isClosed_eq ((Units.continuous_val.comp continuous_subtype_val).matrix_mulVec continuous_const)
      continuous_const
  exact ⟨jj, ⟨⟨hind, hinj⟩, hclosed⟩, fun g => ⟨hfix g, hcomm g⟩⟩

end GlobalTheory.StabUnfold
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsCoordinatesInverseFirstColumnInfiniteGLStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coordinates_inverseFirstColumn_infiniteGL : ∀ (E : Type) [Field E] [NumberField E] (k : ℕ), 1 ≤ k → ∃ (hh : MatInf E (k + 1) → MatInf E k) (TT : MatInf E (k + 1) → VecInf E k), Measurable hh ∧ Measurable TT ∧ (∀ g, 0 < detNorm E (k + 1) g → detNorm E k (hh g) = detNorm E (k + 1) g) ∧ (∀ g γ : MatInf E (k + 1), 0 < detNorm E (k + 1) g → 0 < detNorm E (k + 1) γ → (∀ w a, γ w a 0 = if a = 0 then 1 else 0) → ∀ β : MatInf E k, (∀ w a b, β w a b = γ w a.succ b.succ) → hh (γ * g) = β * hh g ∧ ∀ w, TT (γ * g) w ᵥ* Matrix.of (β w) = TT g w + fun b => γ w 0 b.succ) ∧ ∀ (F : MatInf E k → ENNReal) (Q : VecInf E k → ENNReal) (Φ : VecInf E (k + 1) → ENNReal), Measurable F → Measurable Q → Measurable Φ → ∫⁻ g, F (hh g) * Q (TT g) * Φ (fun u a => (Matrix.of (g u))⁻¹ a 0) ∂(haarGL E (k + 1)) = (∫⁻ x, Φ x) * (∫⁻ T, Q T) * ∫⁻ h, F h * ENNReal.ofReal (detNorm E k h) ∂(haarGL E k) := by
  first | exact @GlobalTheory.FirstColumnCoord.coordinates | exact GlobalTheory.FirstColumnCoord.coordinates | (intros; apply GlobalTheory.FirstColumnCoord.coordinates <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGramRepresentativeSizeLeHHSqStatement
section
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_gram_representative_size_le_HH_sq : ∀ Cg cb Cu cT CT C0 A : ℝ, ∃ C₀ : ℝ, ∀ C ≥ C₀, ∀ (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl : ℝ), 1 ≤ Cl → Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A → ∀ (F0 : Fb D u) (Λ : LatV D), IsBase D u F0 → IsRowLat D F0 Λ → ∀ (Z : GramM D) (F' : FlagU D u'), RelZ D Z → IsTermF D Λ (lf D F0) F' → ZEquiv (ZhatL (lf D F0) F') Z → ∃ Z₁, ZEquiv Z Z₁ ∧ QOK D u u' Z₁ (HHZ D large₂.sc.b C Z ^ 2) := by
  first | exact @GlobalTheory.LoopC.GramSize.main | exact GlobalTheory.LoopC.GramSize.main | (intros; apply GlobalTheory.LoopC.GramSize.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsFolnerSequenceBesselStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isFolnerSequenceBessel : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μS : Measure (Mt k r)), inWb k r z → 0 < Tz k r z → IsHaarOn (Sset k r z) μS → ∃ Om : ℕ → Set (Mt k r), IsFolner (Sset k r z) μS Om := by
  first | exact @GlobalTheory.SgInf.FolnerSets.exists_isFolner | exact GlobalTheory.SgInf.FolnerSets.exists_isFolner | (intros; apply GlobalTheory.SgInf.FolnerSets.exists_isFolner <;> assumption)
end

