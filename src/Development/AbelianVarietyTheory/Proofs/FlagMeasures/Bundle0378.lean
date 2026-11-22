import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0299
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0204
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0018
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0018
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0006
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0373
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.PeriodIntegrals.Bundle0015
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0374
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0376
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemColumnLevelIffMemLinkedFrameLevel
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProjectionMovesTypeVectorsModLevel
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0110
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0050
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0045
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0054
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0202
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0179
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0261
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0104

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DerivativeAlongLieAlgebraPreservesSmoothSpace
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DerClosedSmooth

open GlobalTheory.Mem.RealTranslate GlobalTheory.PointAtPlaceHom GlobalTheory.Mem.Lift

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem exists_coords {n : ℕ} (S : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :
    ∃ (m : ℕ) (e : Fin m → Matrix (Fin n) (Fin n) ℂ) (c : Fin m → Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℝ), (∀ j, e j ∈ S) ∧
      ∀ {A : Type} (L : Matrix (Fin n) (Fin n) ℂ → A → ℂ),
        (∀ (a : ℝ), ∀ X ∈ S, ∀ Y ∈ S, L (a • X + Y) = (a : ℂ) • L X + L Y) →
        ∀ Y ∈ S, ∀ x, L Y x = ∑ j, (c j Y : ℂ) * L (e j) x := by
  let b := Module.finBasis ℝ S
  choose c hc using fun j => LinearMap.exists_extend (b.coord j)
  refine ⟨_, fun j => b j, fun j => LinearMap.toContinuousLinearMap (c j), fun j => (b j).2, fun L hL Y hY x => ?_⟩
  have h0 : L 0 = 0 := by
    have := hL 1 0 S.zero_mem 0 S.zero_mem
    simpa using this
  let l : S →ₗ[ℝ] ℂ :=
    { toFun := fun Z => L Z x
      map_add' := fun Z Z' => by simpa using congrFun (hL 1 Z Z.2 Z' Z'.2) x
      map_smul' := fun a Z => by simpa [h0] using congrFun (hL a Z Z.2 0 S.zero_mem) x }
  have h1 : L Y x = l ⟨Y, hY⟩ := rfl
  rw [h1, ← b.sum_repr ⟨Y, hY⟩, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h2 : c j Y = b.repr ⟨Y, hY⟩ j := LinearMap.congr_fun (hc j) ⟨Y, hY⟩
  rw [map_smul, LinearMap.coe_toContinuousLinearMap', h2, Complex.real_smul]
  rfl

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

variable (V) in

def lieSub (τ : D.what₂.Tau) : Submodule ℝ (Matrix (Fin V.rank) (Fin V.rank) ℂ) :=
  GlobalTheory.UnitaryLieAlgebra.unitaryLie (gramAt D V τ)

variable (θ) in

def SmFam {k : ℕ} (B : (Fin k → ℝ) → GA D V) : Prop :=
  ∀ τ, (ContDiff ℝ ∞ fun t => infMat D.sp.cm.sig V.gram (θ τ) (B t)) ∧
    ContDiff ℝ ∞ fun t => infMat D.sp.cm.sig V.gram (θ τ) (B t)⁻¹

theorem SmFam.mul {k : ℕ} {A B : (Fin k → ℝ) → GA D V} (hA : SmFam θ A) (hB : SmFam θ B) :
    SmFam θ fun t => A t * B t := fun τ => by
  simp only [_root_.mul_inv_rev, infMat_mul]
  exact ⟨(hA τ).1.mul (hB τ).1, (hB τ).2.mul (hA τ).2⟩

theorem SmFam.tail {k : ℕ} {A : (Fin k → ℝ) → GA D V} (hA : SmFam θ A) :
    SmFam θ fun t : Fin (k + 1) → ℝ => A (Fin.tail t) := fun τ => by
  have h : ContDiff ℝ ∞ fun t : Fin (k + 1) → ℝ => Fin.tail t := contDiff_pi.2 fun i => contDiff_apply ℝ ℝ i.succ
  exact ⟨(hA τ).1.comp h, (hA τ).2.comp h⟩

theorem contDiff_oneP (hθ : IsInfFam θ) {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) (τ' : D.what₂.Tau) :
    ContDiff ℝ ∞ fun s : ℝ => infMat D.sp.cm.sig V.gram (θ τ') (oneP θ V τ X s) := by
  by_cases c : τ' = τ
  · subst c
    simp only [(isAtTau_oneP hθ hX _).2.1]
    have h2 : ContDiff ℝ ∞ fun t : ℝ => fun _ : Fin 1 => t := contDiff_pi.2 fun _ => contDiff_id
    simpa [Function.comp_def] using (GlobalTheory.GardingVec.contDiff_expProd fun _ : Fin 1 => X).comp h2
  · simp only [(isAtTau_oneP hθ hX _).2.2 τ' c]
    exact contDiff_const

theorem smFam_oneP (hθ : IsInfFam θ) {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) {k : ℕ} (i : Fin k) : SmFam θ fun t : Fin k → ℝ => oneP θ V τ X (t i) := fun τ' => by
  have hi : ∀ t, (oneP θ V τ X t)⁻¹ = oneP θ V τ X (-t) := fun t => inv_eq_of_mul_eq_one_right (by
    rw [← oneP_add hθ hX, add_neg_cancel, oneP_zero hθ])
  simp only [hi]
  exact ⟨(contDiff_oneP hθ hX τ').comp (contDiff_apply ℝ ℝ i),
    (contDiff_oneP hθ hX τ').comp (contDiff_apply ℝ ℝ i).neg⟩

variable (θ) in

def prodP {k : ℕ} (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ) (t : Fin k → ℝ) :
    GA D V := (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod

theorem prodP_succ {k : ℕ} (τs : Fin (k + 1) → D.what₂.Tau) (Xs : Fin (k + 1) → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (t : Fin (k + 1) → ℝ) : prodP θ τs Xs t =
      oneP θ V (τs 0) (Xs 0) (t 0) * prodP θ (Fin.tail τs) (Fin.tail Xs) (Fin.tail t) := by
  unfold prodP
  rw [List.ofFn_succ, List.prod_cons]
  rfl

theorem prodP_laws (hθ : IsInfFam θ) {k : ℕ} (τs : Fin k → D.what₂.Tau)
    (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ) (hX : ∀ i, Xs i ∈ lieAt V (τs i)) :
    SmFam θ (prodP θ τs Xs) ∧ Continuous (prodP θ τs Xs) ∧ ∀ i, ∃ B : (Fin k → ℝ) → GA D V, SmFam θ B ∧ ∀ t s,
      prodP θ τs Xs (Function.update t i (t i + s)) =
        prodP θ τs Xs t * oneP θ V (τs i) (adAt θ (B t) (τs i) (Xs i)) s := by
  have : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  induction k with
  | zero =>
    have e : prodP θ τs Xs = fun _ => 1 := funext fun t => by simp [prodP]
    rw [e]
    exact ⟨fun _ => ⟨contDiff_const, contDiff_const⟩, continuous_const, fun i => i.elim0⟩
  | succ k ih =>
    obtain ⟨h1, h2, h3⟩ := ih (Fin.tail τs) (Fin.tail Xs) fun i => hX i.succ
    rw [funext (prodP_succ (θ := θ) τs Xs)]
    refine ⟨(smFam_oneP hθ (hX 0) 0).mul h1.tail, ((continuous_oneP hθ (hX 0)).comp (continuous_apply 0)).mul
      (h2.comp (continuous_pi fun i => continuous_apply i.succ)), fun i => ?_⟩
    refine Fin.cases ⟨_, h1.tail, fun t s => ?_⟩ (fun j => ?_) i
    · simp only [Function.update_self, Fin.tail_update_zero]
      rw [oneP_add hθ (hX 0), mul_assoc, GlobalTheory.Size.oneP_mul_adelic hθ _ (hX 0) s, mul_assoc]
    · obtain ⟨B, hB, h⟩ := h3 j
      refine ⟨_, hB.tail, fun t s => ?_⟩
      simp only [Fin.tail_update_succ, Function.update_of_ne (Fin.succ_ne_zero j).symm]
      rw [mul_assoc]
      exact congrArg _ (h (Fin.tail t) s)

theorem smooth_of_closed : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D), IsInfFam θ → ∀ W : Set (GA D V → ℂ), (∀ f ∈ W, Continuous f ∧ ∀ τ, ∃ L : Matrix (Fin V.rank) (Fin V.rank) ℂ → GA D V → ℂ, (∀ X ∈ lieAt V τ, L X ∈ W ∧ ∀ x, HasDerivAt (fun t : ℝ => f (x * oneP θ V τ X t)) (L X x) 0) ∧ ∀ (a : ℝ), ∀ X ∈ lieAt V τ, ∀ Y ∈ lieAt V τ, L (a • X + Y) = (a : ℂ) • L X + L Y) → ∀ f ∈ W, ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g, ContDiff ℝ ∞ fun t : Fin k → ℝ => f (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod) := by
  intro D θ V hθ W hW f hf k τs Xs hX g
  have : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  obtain ⟨-, hc, hP⟩ := prodP_laws hθ τs Xs hX
  choose B hB hP using hP
  suffices h : ∀ n : ℕ, ∀ f ∈ W, ContDiff ℝ n fun t => f (g * prodP θ τs Xs t) from
    contDiff_infty.2 fun n => h n f hf
  intro n
  induction n with
  | zero => exact fun f hf => contDiff_zero.2 ((hW f hf).1.comp (continuous_const.mul hc))
  | succ n ih =>
    intro f hf
    choose L hL hlin using (hW f hf).2
    let d : Fin k → (Fin k → ℝ) → ℂ := fun i t => L (τs i) (adAt θ (B i t) (τs i) (Xs i)) (g * prodP θ τs Xs t)
    have hm : ∀ i t, adAt θ (B i t) (τs i) (Xs i) ∈ lieAt V (τs i) := fun i t =>
      GlobalTheory.Size.adAt_mem_lieAt hθ _ (hX i)
    have hd : ∀ i, ContDiff ℝ n (d i) := fun i => by
      obtain ⟨m, e, c, he, hs⟩ := exists_coords (lieSub V (τs i))
      have e1 : d i = fun t => ∑ j, (c j (adAt θ (B i t) (τs i) (Xs i)) : ℂ) * L (τs i) (e j) (g * prodP θ τs Xs t) :=
        funext fun t => hs _ (hlin (τs i)) _ (hm i t) _
      have e2 : ContDiff ℝ n fun t => adAt θ (B i t) (τs i) (Xs i) :=
        (((hB i (τs i)).2.mul contDiff_const).mul (hB i (τs i)).1).of_le (by exact_mod_cast le_top)
      rw [e1]
      exact ContDiff.sum fun j _ => (Complex.ofRealCLM.contDiff.comp ((c j).contDiff.comp e2)).mul
        (ih _ (hL _ _ (he j)).1)
    have hder := GlobalTheory.T.hasFDerivAt_of_continuous_coordinate_derivs k (fun t => f (g * prodP θ τs Xs t)) d (fun i t => by
      have h1 := HasDerivAt.comp_sub_const (t i) (t i) (by rw [sub_self]; exact (hL _ _ (hm i t)).2 (g * prodP θ τs Xs t))
      refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
      simp only [mul_assoc, ← hP, add_sub_cancel]) fun i => (hd i).continuous
    rw [Nat.cast_succ, contDiff_succ_iff_hasFDerivAt]
    exact ⟨_, ContDiff.sum fun i _ => contDiff_const.smulRight (hd i), hder⟩

end GlobalTheory.DerClosedSmooth

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramFibreMeasureFreeTupleNeZeroFinite
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.LocalFibreNonzero

open Topology Set Filter

section Gen

variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [T2Space V]
  [LocallyCompactSpace V] [SecondCountableTopology V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  [LocallyCompactSpace X]
  {μ : Measure V} {ν : Measure X} [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
  [ν.IsOpenPosMeasure]
  {f : V → Y} {ι : X → Y} {U : Set V} {fib : X → Measure V}

private theorem exists_continuous_compactSupport_bump_of_isOpen (hU : IsOpen U) {x : V} (hx : x ∈ U) :
    ∃ φ : V → ℝ, Continuous φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U ∧ φ x = 1 ∧
      ∀ v, 0 ≤ φ v := by
  obtain ⟨O, hO, hxO, hOU, hOc⟩ :=
    exists_open_between_and_isCompact_closure isCompact_singleton hU
      (Set.singleton_subset_iff.mpr hx)
  obtain ⟨g, hgs, hg1, hg01⟩ :=
    exists_tsupport_one_of_isOpen_isClosed hO hOc isClosed_singleton hxO
  refine ⟨g, g.continuous, ?_, hgs.trans (subset_closure.trans hOU), ?_, fun v => (hg01 v).1⟩
  · exact hOc.of_isClosed_subset (isClosed_tsupport _) (hgs.trans subset_closure)
  · simpa using hg1 (Set.mem_singleton x)

theorem fib_ne_zero_of_lb (h : IsFibreFamily μ f ι U ν univ fib) (hU : IsOpen U) {f' : V → X}
    (hf' : Continuous f') (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι)
    {x : V} (hx : x ∈ U) {b0 : X}
    (hlb : ∀ W : Set V, IsOpen W → x ∈ W → ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ⊤ ∧ ∃ N ∈ 𝓝 b0,
      ∀ S ⊆ N, MeasurableSet S → c * ν S ≤ μ (f ⁻¹' (ι '' S) ∩ W)) :
    fib b0 ≠ 0 := by
  intro h0
  obtain ⟨φ, hφc, hφs, hφU, hφx, hφ0⟩ := exists_continuous_compactSupport_bump_of_isOpen hU hx
  obtain ⟨hsupp, hdis, hcont⟩ := h
  obtain ⟨hint, hgc⟩ := hcont φ hφc hφs hφU

  set W : Set V := {v | (1 / 2 : ℝ) < φ v} with hW
  have hWo : IsOpen W := isOpen_lt continuous_const hφc
  have hxW : x ∈ W := by
    show (1 / 2 : ℝ) < φ x
    rw [hφx]; norm_num
  have hWU : W ⊆ U := fun v hv =>
    hφU (subset_tsupport _ (by
      show φ v ≠ 0
      exact ne_of_gt (lt_trans (by norm_num) hv)))
  obtain ⟨c, hc0, hctop, N, hN, hlbN⟩ := hlb W hWo hxW
  set e : ℝ≥0∞ := ENNReal.ofReal (1 / 2) * c with he
  have he0 : e ≠ 0 := mul_ne_zero (by simp) hc0.ne'
  have hetop : e ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hctop
  have hepos : 0 < e.toReal := ENNReal.toReal_pos he0 hetop
  set δ : ℝ := e.toReal / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hδe : ENNReal.ofReal δ < e := by
    rw [← ENNReal.ofReal_toReal hetop, ENNReal.ofReal_lt_ofReal_iff hepos, hδ]
    linarith

  have hgcont : Continuous (fun b => ∫ v, φ v ∂(fib b)) := continuousOn_univ.mp hgc
  have hg0 : (∫ v, φ v ∂(fib b0)) = 0 := by simp [h0]
  have hnear : {b | (∫ v, φ v ∂(fib b)) < δ} ∈ 𝓝 b0 :=
    hgcont.continuousAt.preimage_mem_nhds (Iio_mem_nhds (by rw [hg0]; exact hδpos))
  obtain ⟨K, hK, hKsub, hKc⟩ := local_compact_nhds (Filter.inter_mem hN hnear)
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have hK0 : 0 < ν K := Measure.measure_pos_of_mem_nhds ν hK
  have hKtop : ν K ≠ ⊤ := hKc.measure_lt_top.ne

  set A : Set V := f' ⁻¹' K with hA
  have hAm : MeasurableSet A := (hKc.isClosed.preimage hf').measurableSet
  set Φ : V → ℝ≥0∞ := A.indicator (fun v => ENNReal.ofReal (φ v)) with hΦ
  have hΦm : Measurable Φ := (ENNReal.measurable_ofReal.comp hφc.measurable).indicator hAm
  have hinner : ∀ b, ∫⁻ v, Φ v ∂(fib b) =
      K.indicator (fun b => ENNReal.ofReal (∫ v, φ v ∂(fib b))) b := by
    intro b
    have hon : ∀ᵐ v ∂(fib b), v ∈ f ⁻¹' {ι b} ∩ U := ae_iff.mpr (hsupp b)
    have hae : ∀ᵐ v ∂(fib b), f' v = b := by
      filter_upwards [hon] with v hv
      apply hι
      rw [← hff']
      exact hv.1
    have hcongr : Φ =ᵐ[fib b] fun v => K.indicator (fun _ => ENNReal.ofReal (φ v)) b := by
      filter_upwards [hae] with v hv
      by_cases hb : b ∈ K
      · have hvA : v ∈ A := by rw [hA, Set.mem_preimage, hv]; exact hb
        rw [hΦ, Set.indicator_of_mem hvA, Set.indicator_of_mem hb]
      · have hvA : v ∉ A := by rw [hA, Set.mem_preimage, hv]; exact hb
        rw [hΦ, Set.indicator_of_notMem hvA, Set.indicator_of_notMem hb]
    rw [lintegral_congr_ae hcongr]
    by_cases hb : b ∈ K
    · simp only [Set.indicator_of_mem hb]
      exact (ofReal_integral_eq_lintegral_ofReal (hint b (Set.mem_univ b))
        (ae_of_all _ hφ0)).symm
    · simp [Set.indicator_of_notMem hb]
  have hupper : ∫⁻ v in U, Φ v ∂μ ≤ ENNReal.ofReal δ * ν K := by
    rw [hdis Φ hΦm]
    simp_rw [hinner]
    rw [lintegral_indicator hKm]
    calc ∫⁻ b in K, ENNReal.ofReal (∫ v, φ v ∂(fib b)) ∂ν
        ≤ ∫⁻ _ in K, ENNReal.ofReal δ ∂ν :=
          setLIntegral_mono measurable_const
            (fun b hb => ENNReal.ofReal_le_ofReal (hKsub hb).2.le)
      _ = ENNReal.ofReal δ * ν K := setLIntegral_const K _
  have hpre : f ⁻¹' (ι '' K) = A := by
    ext v
    simp only [Set.mem_preimage, Set.mem_image, hff', hA]
    constructor
    · rintro ⟨b, hb, hbv⟩
      rwa [← hι hbv]
    · intro hv
      exact ⟨_, hv, rfl⟩
  have hsub : A ∩ W ⊆ {v | ENNReal.ofReal (1 / 2) ≤ Φ v} ∩ U := by
    intro v hv
    refine ⟨?_, hWU hv.2⟩
    show ENNReal.ofReal (1 / 2) ≤ Φ v
    rw [hΦ, Set.indicator_of_mem hv.1]
    exact ENNReal.ofReal_le_ofReal hv.2.le
  have hlower : e * ν K ≤ ∫⁻ v in U, Φ v ∂μ := by
    calc e * ν K = ENNReal.ofReal (1 / 2) * (c * ν K) := by rw [he, mul_assoc]
      _ ≤ ENNReal.ofReal (1 / 2) * μ (f ⁻¹' (ι '' K) ∩ W) :=
          mul_le_mul_of_nonneg_left (hlbN K (fun b hb => (hKsub hb).1) hKm) (by positivity)
      _ ≤ ENNReal.ofReal (1 / 2) * (μ.restrict U) {v | ENNReal.ofReal (1 / 2) ≤ Φ v} := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [hpre]
          exact (measure_mono hsub).trans (Measure.le_restrict_apply _ _)
      _ ≤ ∫⁻ v in U, Φ v ∂μ := mul_meas_ge_le_lintegral hΦm _
  have hle := hlower.trans hupper
  rw [mul_comm e, mul_comm (ENNReal.ofReal δ)] at hle
  exact absurd hle (not_le.mpr (ENNReal.mul_lt_mul_right hK0.ne' hKtop hδe))

end Gen

section Tens

open PI.VolStabS PI.VolStabS.TensAllW

theorem fib_tens {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (a : ℕ) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [T2Space R]
    [SecondCountableTopology R] (hU : IsOpen {r : R | IsUnit r}) (hL : LIP R)
    (μ : Measure (Fin a → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ a))
    [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    (fib : HermR R σ a → Measure (Fin a → Fin M → R ⊗[F] E))
    (h : IsFibreFamily μ (gramR R σ J) Subtype.val {X | LinearIndependent (R ⊗[F] E) X} ν
      univ fib)
    (x : Fin a → Fin M → R ⊗[F] E) (S : HermR R σ a) (hx : LinearIndependent (R ⊗[F] E) x)
    (hlb : ∀ W : Set (Fin a → Fin M → R ⊗[F] E), IsOpen W → x ∈ W →
      ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ⊤ ∧ ∃ N ∈ nhds S, ∀ T ⊆ N, MeasurableSet T →
        c * ν T ≤ μ ((gramR R σ J) ⁻¹' (Subtype.val '' T) ∩ W)) :
    fib S ≠ 0 ∧ ∀ K : Set (Fin a → Fin M → R ⊗[F] E), IsCompact K →
      K ⊆ {X | LinearIndependent (R ⊗[F] E) X} → fib S K < ⊤ := by
  have hopen : IsOpen {X : Fin a → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X} :=
    isOpen_linIndep (Module.finBasis F E) R hU hL
  refine ⟨fib_ne_zero_of_lb h hopen (f' := gramH R σ hσ J hJ) (continuous_gramH R σ hσ J hJ)
    (fun _ => rfl) Subtype.val_injective hx hlb, fun K hK hKU => ?_⟩
  exact PI.VolStabS.FibUniq.fin_cpt h hopen S K hK hKU

end Tens

theorem fibre_nonzero_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ a : ℕ, ∀ (μ : Measure (Fin a → Fin n → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ a)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∀ fib : HermR (Fv F v) σ a → Measure (Fin a → Fin n → Fv F v ⊗[F] E), IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val {X | LinearIndependent (Fv F v ⊗[F] E) X} ν Set.univ fib → ∀ (x : Fin a → Fin n → Fv F v ⊗[F] E) (S : HermR (Fv F v) σ a), LinearIndependent (Fv F v ⊗[F] E) x → gramR (Fv F v) σ J x = (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) → fib S ≠ 0 ∧ ∀ K : Set (Fin a → Fin n → Fv F v ⊗[F] E), IsCompact K → K ⊆ {X | LinearIndependent (Fv F v ⊗[F] E) X} → fib S K < ⊤ := by
  intro F E _ _ _ _ _ σ hCM n J hJ v a μ ν hμ hν fib h x S hx hS
  have := PI.VolStabS.secondCountable_Fv F v
  have := PI.VolStabS.locallyCompact_Fv F v
  have : FiniteDimensional F E :=
    Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hσ : ∀ y, σ (σ y) = y := PI.VolStabS.sigma_invol σ hCM.2.2.2
  exact fib_tens σ hσ J hJ.1 a (Fv F v) (PI.VolStabS.isOpen_units_Fv F v)
    (PI.VolStabS.TensAllW.lip_field _) μ ν fib h x S hx
    (GlobalTheory.T.gramMap_preimage_volume_lower_bound F E σ hCM n J hJ v a μ ν hμ hν x S hx hS)

end GlobalTheory.LocalFibreNonzero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.KFinDense
section
open Formalism.MainNotions.S

namespace GlobalTheory.KFinDenseDS

theorem kFin_dense : ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)),
    Formalism.QuantumDeterminants.IsHCParam lam → PI.UpqRep.IsDSHpk k r ε lam σ →
    ∀ v ∈ smoothVecs (k := k) (r := r) σ,
    ∀ Ws : List (List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)), (∀ w ∈ Ws, ∀ X ∈ w, InLieHpk k r X) →
    ∀ δ : ℝ, 0 < δ → ∃ a : H, PI.UpqRep.IsKFinHpk (k := k) (r := r) σ a ∧
      (Ws.map fun w => ‖dsigW σ w (v - a)‖).sum < δ := by
  intro k r ε lam H _ _ _ σ hl hds v hv Ws hWs δ hδ
  obtain ⟨a, ha, hs⟩ := GlobalTheory.KFinAvg.kDense k r ε lam H σ hl hds v hv Ws hWs δ hδ
  refine ⟨a, ha, ?_⟩
  simpa only [Formalism.MainNotions.BridgeCS3d.dsigW_eq] using hs

end GlobalTheory.KFinDenseDS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeInfinitesimalCharLargeGapStatement
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowestKType_infinitesimalChar_large_gap : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsHCParam lam → IsDS ε lam σ → ∀ h : ℝ, GapAtLeast ε lam h → 120 * (n : ℝ) * ((rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h → ∀ s ∈ lowKSub ε lam σ, ∀ y : H, IsZEigen ε (fun a => (lam a : ℂ)) (fun g => ⟪y, σ g s⟫_ℂ) := by
  first | exact @GlobalTheory.DSId.LowCharGap.lowChar | exact GlobalTheory.DSId.LowCharGap.lowChar | (intros; apply GlobalTheory.DSId.LowCharGap.lowChar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemColumnLevelIffMemLinkedFrameLevelStatement
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_columnLevel_iff_mem_linkedFrameLevel : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∀ (hK : X.LevelSubgroupCharacter) (Fr : FrQ D wt), FrLink X u wt ιA Fr → ∀ (h : Hfin X u) (y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F)), RepF X wt ιA (h : X.B.I.Gf) y → (h ∈ Ku X u hK ↔ Fr.InK y.1) := by
  first | exact @GlobalTheory.St.G.ColLevel.level_link | exact GlobalTheory.St.G.ColLevel.level_link | (intros; apply GlobalTheory.St.G.ColLevel.level_link <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProjectionMovesTypeVectorsModLevelStatement
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projection_moves_typeVectors_modLevel : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∀ (c : ℕ) (p : VA X.B.I →ₗ[X.B.I.E ⊗[X.B.I.F] Af X.B.I.F] VA X.B.I), (∀ y ∈ X.B.I.Lf, (∀ a, InAt X.B.I X.B.g X.B.g (hA X.B.I (incl X.B.I (X.eR a)) y • incl X.B.I (X.fR a)) ∧ InAt X.B.I X.B.g X.B.g (hA X.B.I (incl X.B.I (X.fR a)) y • incl X.B.I (X.eR a))) → InAt X.B.I X.B.g X.B.g (hA X.B.I (incl X.B.I (X.zR u)) y • incl X.B.I (X.zR u)) → (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p y - y ∈ mL X.B.I X.B.g) → (∀ i, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bw i) - X.B.I.fmat (X.xu u) *ᵥ X.bw i ∈ mL X.B.I X.B.g ∧ (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bwd i) - X.B.I.fmat (X.xu u) *ᵥ X.bwd i ∈ mL X.B.I X.B.g) := by
  first | exact @GlobalTheory.St.G.FrameClose.typeVec_close | exact GlobalTheory.St.G.FrameClose.typeVec_close | (intros; apply GlobalTheory.St.G.FrameClose.typeVec_close <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TorusCommutesWithUnipotent
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.LocalSetup

theorem exists_seq {k : ℕ} (u : Fin k → ℝ) : ∃ U : ℕ → ℝ, ∀ i : Fin k, U (i.val + 1) = u i :=
  ⟨fun n => if h : n - 1 < k then u ⟨n - 1, h⟩ else 0, fun i => by simp⟩

theorem exists_setup (hH : Hyps) {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [CompleteSpace Wp] [FiniteDimensional ℂ Wp] {lam : Fin (2 * r + k + 1) → ℝ} {u : ℕ → ℝ} {b bv ga h : ℝ} {q0 : ℕ}
    {z : Fin (2 * r + k + 1) → ℂ} {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)}
    {μW μN μG νq : Measure (Mt k r)} {R : (Fin (2 * r + k + 1) → ℤ) → Rep k r}
    (hN : Num k r lam u b bv ga h q0) (hF : IsFam lam q0 R) (hS : SideG k r z π u μW μN μG νq) {c : ℝ} (hc : 0 < c)
    (hd : ∀ (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS (PI.BesselPeriodGGP.eps48 k r) mu →
      ∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH μG R.σ w = c * fdegHC mu) :
    ∃ l : ∀ ν, (R ν).H → Wp,
      Setup lam u b bv ga h q0 z π μW μN μG νq R l (fun ν => c * fdegHC (fun a => lam a + (ν a : ℝ))) := by
  obtain ⟨⟨-, -, -, -, hG⟩, hν⟩ := GlobalTheory.NumFam.num_fam k r lam u b bv ga h q0 hN
  have h1 : ∀ ν, ∃ l : (R ν).H → Wp, n1 ν ≤ q0 → IsBeL (R ν) z π μW μN l := by
    intro ν
    by_cases hq : n1 ν ≤ q0
    · obtain ⟨l, hl⟩ := GlobalTheory.exists_normalised_bessel_map hH k r _ _ (h / 2) (R ν) Wp _ _ _ _ _ _ _ (hF ν hq)
        (hν ν hq).2.2.1 hG hS
      exact ⟨l, fun _ => hl⟩
    · exact ⟨0, fun h' => absurd h' hq⟩
  choose l hl using h1
  exact ⟨l, hN, hF, hS, fun ν hq => ⟨hl ν hq,
    mul_pos hc (GlobalTheory.FamilyDegreeRatio.degree_ratios k r lam u b bv ga h q0 hN ν hq).1, hd _ _ (hF ν hq)⟩⟩

theorem exists_setup_both : Hyps → ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), HypZ D large₂ C' Cl Cg cb Cu cT CT C0 → 1000 ≤ Cl → ∀ τ w w' θ (W : LocW D.R.k D.R.rS), HypTT D w w' → 0 < θ → GoodW D τ w w' θ W → ∀ t ∈ GG D.R.k D.R.rS, (∀ n, n ∈ Nset D.R.k D.R.rS ↔ t * n * t⁻¹ ∈ Nset D.R.k D.R.rS) → (∀ z, inWb D.R.k D.R.rS z → (∀ h ∈ UWset D.R.k D.R.rS z, t * h = h * t) ∧ ∀ n ∈ Nset D.R.k D.R.rS, psi D.R.k D.R.rS z cStd n = psiS D z (t * n * t⁻¹)) → ∀ R : (Fin (2 * D.R.rS + D.R.k + 1) → ℤ) → Rep D.R.k D.R.rS, IsFam (lamD D τ) (D.R.k * D.R.m ^ 5) R → haveI := FiniteDimensional.complete ℂ W.Wp; haveI := FiniteDimensional.complete ℂ W.Wq; ∃ (U U' : ℕ → ℝ) (l : ∀ ν, (R ν).H → W.Wp) (l' : ∀ ν, (R ν).H → W.Wq) (dg : (Fin (2 * D.R.rS + D.R.k + 1) → ℤ) → ℝ), Setup (lamD D τ) U (large₂.sc.b ^ max 2 Cu) (bOne D τ 1) ((D.R.r : ℝ) * (D.R.m : ℝ) ^ 10) ((D.R.r : ℝ) ^ 19) (D.R.k * D.R.m ^ 5) W.z W.π W.μW (W.μN.map fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j) W.μG (W.νS.map fun x => fun i j => (t⁻¹ * Matrix.of x) i j) R l dg ∧ Setup (lamD D τ) U' (large₂.sc.b ^ max 2 Cu) (bOne D τ 1) ((D.R.r : ℝ) * (D.R.m : ℝ) ^ 10) ((D.R.r : ℝ) ^ 19) (D.R.k * D.R.m ^ 5) W.z' W.π' W.μW' (W.μN.map fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j) W.μG (W.νS'.map fun x => fun i j => (t⁻¹ * Matrix.of x) i j) R l' dg := by
  intro hH D large₂ C' Cl Cg cb Cu cT CT C0 hZ hCl τ w w' θ W hTT hθ hW t ht hNt hψ R hF
  haveI := FiniteDimensional.complete ℂ W.Wp
  haveI := FiniteDimensional.complete ℂ W.Wq
  obtain ⟨c1, c2, z1, z2, t1, t2, hG, w1, -, w2, -, hN, q1, q2⟩ := hW
  have hv : 1 ≤ D.host.v := hZ.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hNH : IsHaarOn (Nset D.R.k D.R.rS) W.μN := by
    rw [hN]
    exact GlobalTheory.T.haarLie_isHaarOn_unipotentRadical _ _ _ (ENNReal.ofReal_pos.2 (by positivity)) ENNReal.ofReal_lt_top
  have hT1 : 0 < Tz D.R.k D.R.rS W.z := by
    rw [t1]; unfold Tr; exact_mod_cast hTT.1.pos
  have hT2 : 0 < Tz D.R.k D.R.rS W.z' := by
    rw [t2]; unfold Tr; exact_mod_cast hTT.2.1.pos
  obtain ⟨U, hU⟩ := exists_seq (uS D w τ)
  obtain ⟨U', hU'⟩ := exists_seq (uS D w' τ)
  have s1 : SideG D.R.k D.R.rS W.z W.π U W.μW W.μN W.μG W.νS :=
    ⟨z1, hT1, ⟨_, c1⟩, GlobalTheory.ThA.capParam_of_isHCTypeW _ _ _ _ U _ _ z1 hT1 c1 hU, w1, hNH, hG, q1⟩
  have s2 : SideG D.R.k D.R.rS W.z' W.π' U' W.μW' W.μN W.μG W.νS' :=
    ⟨z2, hT2, ⟨_, c2⟩, GlobalTheory.ThA.capParam_of_isHCTypeW _ _ _ _ U' _ _ z2 hT2 c2 hU', w2, hNH, hG, q2⟩
  have m1 := (GlobalTheory.T.torus_normaliser_bessel hH _ _ _ _ _ _ _ _ _ _ _ t ht hNt (hψ _ z1).1 (hψ _ z1).2 s1).1
  have m2 := (GlobalTheory.T.torus_normaliser_bessel hH _ _ _ _ _ _ _ _ _ _ _ t ht hNt (hψ _ z2).1 (hψ _ z2).2 s2).1
  obtain ⟨c, hc, hd⟩ := GlobalTheory.BesselDegree.schur_fdeg hH D.R.k D.R.rS (PI.BesselPeriodGGP.eps48 _ _) W.μG hG
  obtain ⟨l, hl⟩ := exists_setup hH (GlobalTheory.T.momentPieriNumerics_of_sizeHyps D large₂ C' Cl Cg cb Cu cT CT C0 hZ hCl τ w U hU).1 hF m1 hc
    fun mu R h => (hd mu R h).1
  obtain ⟨l', hl'⟩ := exists_setup hH (GlobalTheory.T.momentPieriNumerics_of_sizeHyps D large₂ C' Cl Cg cb Cu cT CT C0 hZ hCl τ w' U' hU').1 hF m2 hc
    fun mu R h => (hd mu R h).1
  exact ⟨U, U', l, l', _, hl, hl'⟩

end GlobalTheory.Amp.LocalSetup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportCoeffMapBijectiveOntoValues
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem transport_J_bijective_onto :
    ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (Tr : Transport X u F),
      Function.Injective Tr.J ∧ ∀ p ∈ Formalism.L2.Forms.ValC (Formalism.L2.Forms.gramC (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Formalism.L2.Forms.embT D)) (Formalism.L2.Forms.lamT u 0), ∃ ξ, Tr.J ξ = p := by
  intro D X u F Tr
  obtain ⟨c, -⟩ := F.cls0.y_bij.2 (Quotient.mk'' 1)
  have hinj : Function.Injective Tr.J := by
    intro ξ η h
    have h1 := Tr.J_isom c ξ η
    have h2 := Tr.J_isom c ξ ξ
    have h3 := Tr.J_isom c η ξ
    have h4 := Tr.J_isom c η η
    rw [h] at h1 h2 h3
    rw [h4] at h1 h2 h3
    have h0 : ⟪ξ - η, ξ - η⟫_ℂ = 0 := by
      rw [inner_sub_left, inner_sub_right, inner_sub_right, ← h1, ← h2, ← h3]
      ring
    exact sub_eq_zero.1 (inner_self_eq_zero.1 h0)
  refine ⟨hinj, ?_⟩
  obtain ⟨J₀, -, hJ₀⟩ := GlobalTheory.T.exists_equivariant_unitary_coefficientMap_onto D X u F Tr.wt ⟨Tr.wt_isom, Tr.wt_e, Tr.wt_f, Tr.weight_z⟩
  exact GlobalTheory.conjLinear_onto_of_injective_of_le_range (X.Vpi u) _ _ J₀ Tr.J hJ₀ hinj Tr.J_val

end GlobalTheory
end

