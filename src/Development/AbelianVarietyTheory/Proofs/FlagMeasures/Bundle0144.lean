import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0124
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
import Formalism.LocalToGlobal.HermitianForms.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MirabolicFunctionEqInducedDerivativeAddTail
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0005
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MirabolicInductionPhiPlusInductionFromBlockUni
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0049
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0126
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelRegionNormBound
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0129
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MapFnOfEqValC
section
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

namespace GlobalTheory.ValueSpaceCoordinates

theorem rowAct_mem_delSq {n : ℕ} (lam : DomWeight n) (g : Matrix (Fin n) (Fin n) ℂ)
    (p : MvPolynomial (Fin n × Fin n) ℂ) (hp : p ∈ delSq ℂ n lam) :
    Formalism.GradedWeylDivisibility.rowAct ℂ g p ∈ delSq ℂ n lam := by
  have hanti : Antitone lam.natW := by
    intro i j hij
    have h := lam.anti hij
    simp only [DomWeight.natW]
    exact Int.toNat_le_toNat (by omega)
  have hw := Formalism.L2.Col.dualWeyl_eq_weyl ℂ (le_rfl : n ≤ n) lam.natW hanti
  change p ∈ Formalism.GradedWeylDivisibility.weyl ℂ n n le_rfl lam.natW at hp
  change Formalism.GradedWeylDivisibility.rowAct ℂ g p ∈ Formalism.GradedWeylDivisibility.weyl ℂ n n le_rfl lam.natW
  rw [← hw] at hp ⊢
  exact Formalism.GradedWeylDivisibility.dualWeylRowStable ℂ n n lam.natW g p hp

theorem eval_rowAct {n : ℕ} (g x : Matrix (Fin n) (Fin n) ℂ) (p : MvPolynomial (Fin n × Fin n) ℂ) :
    MvPolynomial.eval (fun v : Fin n × Fin n => x v.1 v.2) (Formalism.GradedWeylDivisibility.rowAct ℂ g p) =
      MvPolynomial.eval (fun v : Fin n × Fin n => (g * x) v.1 v.2) p := by
  have key : (MvPolynomial.eval fun v : Fin n × Fin n => x v.1 v.2).comp
      (Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) g).toRingHom =
      MvPolynomial.eval fun v : Fin n × Fin n => (g * x) v.1 v.2 := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [Formalism.GradedWeylDivisibility.rowAct]
    · intro v
      simp [Formalism.GradedWeylDivisibility.rowAct, Matrix.mul_apply]
  simpa using RingHom.congr_fun key p

theorem eval_ten {ι : Type} [Fintype ι] {n : ℕ} (x : ι → Matrix (Fin n) (Fin n) ℂ)
    (f : ι → MvPolynomial (Fin n × Fin n) ℂ) :
    MvPolynomial.eval (fun v : ι × Fin n × Fin n => x v.1 v.2.1 v.2.2) (ten f) =
      ∏ τ, MvPolynomial.eval (fun v : Fin n × Fin n => x τ v.1 v.2) (f τ) := by
  unfold Formalism.L2.Forms.ten
  rw [map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [MvPolynomial.eval_rename]
  rfl

theorem fnOf_mul_ten {ι : Type} [Fintype ι] {n : ℕ} (G : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ)
    (A B : ι → Matrix (Fin n) (Fin n) ℂ) (f : ι → MvPolynomial (Fin n × Fin n) ℂ) :
    fnOf G s (A * B) (ten f) =
      (∏ τ, (A τ).det ^ s τ) • fnOf G s B (ten fun τ => Formalism.GradedWeylDivisibility.rowAct ℂ (A τ) (f τ)) := by
  ext y
  simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, smul_eq_mul]
  rw [eval_ten (fun τ => (A * B) τ * y.1 τ) f,
    eval_ten (fun τ => B τ * y.1 τ) (fun τ => Formalism.GradedWeylDivisibility.rowAct ℂ (A τ) (f τ))]
  simp only [eval_rowAct, Pi.mul_apply, Matrix.mul_assoc, Matrix.det_mul, mul_zpow,
    Finset.prod_mul_distrib]
  ring

theorem map_fnOf_mul_le {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (G : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ) (A B : ι → Matrix (Fin n) (Fin n) ℂ) :
    (CSpan lam).map (fnOf G s (A * B)) ≤ (CSpan lam).map (fnOf G s B) := by
  unfold CSpan
  rw [Submodule.map_span, Submodule.span_le]
  rintro _ ⟨q, ⟨f, hf, rfl⟩, rfl⟩
  rw [SetLike.mem_coe, fnOf_mul_ten]
  exact Submodule.smul_mem _ _ (Submodule.mem_map_of_mem (Submodule.subset_span
    ⟨fun τ => Formalism.GradedWeylDivisibility.rowAct ℂ (A τ) (f τ), fun τ => rowAct_mem_delSq (lam τ) (A τ) (f τ) (hf τ), rfl⟩))

theorem map_fnOf_eq_ValC :
    ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (G M : ι → Matrix (Fin n) (Fin n) ℂ), (∀ τ, IsUnit (M τ).det) → (CSpan lam).map (fnOf G (shiftOf lam) M) = ValC G lam := by
  intro ι _ n lam G M hM
  have hinv : (fun τ => (M τ)⁻¹) * M = 1 := by
    funext τ
    simp only [Pi.mul_apply, Pi.one_apply]
    exact Matrix.nonsing_inv_mul (M τ) (hM τ)
  unfold ValC
  apply le_antisymm
  · have h := map_fnOf_mul_le lam G (shiftOf lam) M 1
    rwa [mul_one] at h
  · have h := map_fnOf_mul_le lam G (shiftOf lam) (fun τ => (M τ)⁻¹) M
    rwa [hinv] at h

end GlobalTheory.ValueSpaceCoordinates
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassRatioRankFactor
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas

theorem volU_succ_eq_mul (m : ℕ) :
    volU (m + 1) = volU m * (2 * Real.pi ^ (m + 1) / (m.factorial : ℝ) * 2 ^ m) := by
  have h : (m + 1) * (m + 1 - 1) / 2 = m * (m - 1) / 2 + m := by
    have := Nat.triangle_succ m
    simpa using this
  unfold volU sphV
  rw [Finset.prod_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le m)), h, pow_add]
  simp only [Nat.add_sub_cancel]
  ring

theorem vInv_pos_of_numberField (E : Type) [Field E] [NumberField E] : 0 < Formalism.HermitianLatticesTheory.vInv E := by
  unfold Formalism.HermitianLatticesTheory.vInv
  have : (0 : ℝ) < |(discr E : ℝ)| := abs_pos.mpr (by exact_mod_cast discr_ne_zero E)
  positivity

theorem mass_ratio_mul_unitary_volume :
    ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (M : ℕ), 1 ≤ M →
      Formalism.HermitianLatticesTheory.massRatioRightSide E M * volU M ^ Formalism.HermitianLatticesTheory.fDeg E =
        rankFac E M * volU (M - 1) ^ Formalism.HermitianLatticesTheory.fDeg E := by
  intro E _ _ _ M hM
  obtain ⟨m, rfl⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
  have hv := vInv_pos_of_numberField E
  unfold Formalism.HermitianLatticesTheory.massRatioRightSide rankFac
  simp only [Nat.add_sub_cancel]
  rw [volU_succ_eq_mul]
  set v := Formalism.HermitianLatticesTheory.vInv E
  set f := Formalism.HermitianLatticesTheory.fDeg E
  have h2 : 0 < 2 * v := by positivity
  have hfac : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  have hpi := Real.pi_pos.ne'
  have key : ((m.factorial : ℝ) * (v / Real.pi) ^ (m + 1)) *
      (2 * Real.pi ^ (m + 1) / (m.factorial : ℝ) * 2 ^ m) = (2 * v) ^ (m + 1) := by
    rw [div_pow, mul_pow]
    field_simp
    ring
  have hr : (2 * v) ^ ((f : ℝ) * (((m + 1 : ℕ) : ℝ) - 1 / 2)) =
      ((2 * v) ^ (m + 1)) ^ f / Real.sqrt ((2 * v) ^ f) := by
    rw [Real.sqrt_eq_rpow, ← pow_mul, ← Real.rpow_natCast, ← Real.rpow_natCast,
      ← Real.rpow_mul h2.le, ← Real.rpow_sub h2]
    congr 1
    push_cast
    ring
  rw [hr, ← key, mul_pow (volU m), mul_pow ((m.factorial : ℝ) * (v / Real.pi) ^ (m + 1))]
  ring

end GlobalTheory.FlagMeas
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableFlagLocalSizesUnitary
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas

open MeasureTheory NumberField Matrix Finset in

theorem _root_.GlobalTheory.FlagMeas.measurable_detOn_comp {X : Type} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] {n : ℕ}
    (f : X → Matrix (Fin n) (Fin n) ℂ) (hf : Continuous f) (V : Submodule ℂ (Fin n → ℂ)) :
    Measurable fun x => _root_.GlobalTheory.FlagMeas.detOn (f x) V := by
  classical
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl V
  let P := Submodule.linearProjOfIsCompl V W hW
  let b := Module.finBasis ℂ V
  let g : X → ℂ := fun x =>
    (Matrix.of fun i k => b.repr (P (f x *ᵥ (b k : Fin n → ℂ))) i).det
  have hg : Continuous g := by
    refine Continuous.matrix_det ?_
    refine continuous_matrix fun i k => ?_
    have hL : Continuous fun v : Fin n → ℂ => b.repr (P v) i :=
      (((Finsupp.lapply i).comp b.repr.toLinearMap).comp P).continuous_of_finiteDimensional
    exact hL.comp (hf.matrix_mulVec continuous_const)
  have hS : IsClosed {x | ∀ y ∈ V, f x *ᵥ y ∈ V} := by
    simp only [Set.setOf_forall]
    refine isClosed_biInter fun y _ => ?_
    exact V.closed_of_finiteDimensional.preimage (hf.matrix_mulVec continuous_const)
  have heq : (fun x => _root_.GlobalTheory.FlagMeas.detOn (f x) V) =
      fun x => if x ∈ {x | ∀ y ∈ V, f x *ᵥ y ∈ V} then ‖g x‖ else 0 := by
    funext x
    unfold _root_.GlobalTheory.FlagMeas.detOn
    by_cases h : ∀ y ∈ V, (toLin' (f x)) y ∈ V
    · have h' : x ∈ {x | ∀ y ∈ V, f x *ᵥ y ∈ V} := fun y hy => by
        simpa [Matrix.toLin'_apply] using h y hy
      rw [dif_pos h, if_pos h', ← LinearMap.det_toMatrix b]
      congr 2
      ext i k
      rw [LinearMap.toMatrix_apply, Matrix.of_apply]
      congr 2
      have hm : f x *ᵥ (b k : Fin n → ℂ) = ((toLin' (f x)).restrict h (b k) : Fin n → ℂ) := by
        simp [LinearMap.restrict_apply, Matrix.toLin'_apply]
      rw [hm]
      exact (Submodule.projectionOnto_apply_left hW _).symm
    · have h' : x ∉ {x | ∀ y ∈ V, f x *ᵥ y ∈ V} := fun hx => h fun y hy => by
        simpa [Matrix.toLin'_apply] using hx y hy
      rw [dif_neg h, if_neg h']
  rw [heq]
  exact Measurable.ite hS.measurableSet hg.norm.measurable measurable_const

open MeasureTheory NumberField Matrix Finset in

theorem _root_.GlobalTheory.FlagMeas.measurable_locSize_uMat (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ)
    (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) (i : Fin a) :
    Measurable fun g : _root_.Formalism.REAL.UJ ε => _root_.GlobalTheory.FlagMeas.locSize j W (_root_.Formalism.MainNotions.S.uMat g) i := by
  have hc : Continuous fun g : _root_.Formalism.REAL.UJ ε => _root_.Formalism.MainNotions.S.uMat g := by
    unfold _root_.Formalism.MainNotions.S.uMat
    exact Units.continuous_val.comp continuous_subtype_val
  unfold _root_.GlobalTheory.FlagMeas.locSize
  exact ((_root_.GlobalTheory.FlagMeas.measurable_detOn_comp _ hc _).div
    (_root_.GlobalTheory.FlagMeas.measurable_detOn_comp _ hc _)).pow_const _

end GlobalTheory.FlagMeas
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableHsNormSqAmplitudeBesselUnitary
section
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.AmpMeas

theorem stronglyMeasurable_indicator_of_continuousOn {X W : Type} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W] {S : Set X}
    (hS : MeasurableSet S) {f : X → W} (hf : ContinuousOn f S) : StronglyMeasurable (S.indicator f) := by
  classical
  haveI : ProperSpace W := FiniteDimensional.proper ℂ W
  letI : MeasurableSpace W := borel W
  haveI : BorelSpace W := ⟨rfl⟩
  have := hf.measurable_piecewise (g := fun _ => (0 : W)) continuousOn_const hS
  have h2 : S.indicator f = S.piecewise f fun _ => (0 : W) := by
    funext x; by_cases hx : x ∈ S <;> simp [hx]
  rw [h2]
  exact this.stronglyMeasurable

theorem continuous_hsNormSq {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] : Continuous fun A : Wq →L[ℂ] Wp => hsNormSq A := by
  unfold hsNormSq hsInner
  refine Complex.continuous_re.comp (continuous_finset_sum _ fun i _ => ?_)
  have : Continuous fun A : Wq →L[ℂ] Wp => A (stdOrthonormalBasis ℂ Wq i) :=
    (ContinuousLinearMap.apply ℂ Wp (stdOrthonormalBasis ℂ Wq i)).continuous
  exact this.inner this

theorem measurable_hsNormSq_ampJ : ∀ (k r : ℕ) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (μG : Measure (Mt k r)) (c : ℝ) (Φ : Mat k r → Wp) (Φ' : Mat k r → Wq), IsHaarOn (GG k r) μG → ContinuousOn Φ (GG k r) → ContinuousOn Φ' (GG k r) → Measurable (Set.indicator {x : Mt k r | Matrix.of x ∈ GG k r} fun γ => hsNormSq (ampJ μG c Φ Φ' (Matrix.of γ))) := by
  intro k r Wp _ _ _ _ Wq _ _ _ μG c Φ Φ' hH hΦ hΦ'
  haveI : SigmaFinite μG := hH.1
  have hcl : IsClosed {x : Mat k r | xᴴ * Hpk k r * x = Hpk k r} :=
    isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
      continuous_id) continuous_const
  have hcl' : IsClosed {x : Mt k r | Matrix.of x ∈ GG k r} := hcl
  set S : Set (Mt k r) := {x : Mt k r | Matrix.of x ∈ GG k r} with hSdef
  have hS : MeasurableSet S := hcl'.measurableSet
  have hmul : ∀ γ x : Mat k r, γ ∈ GG k r → x ∈ GG k r → γ * x ∈ GG k r := by
    intro γ x hγ hx
    have hs' : γᴴ * Hpk k r * γ = Hpk k r := hγ
    have hx' : xᴴ * Hpk k r * x = Hpk k r := hx
    show (γ * x)ᴴ * Hpk k r * (γ * x) = Hpk k r
    rw [Matrix.conjTranspose_mul]
    calc xᴴ * γᴴ * Hpk k r * (γ * x) = xᴴ * (γᴴ * Hpk k r * γ) * x := by
          simp only [Matrix.mul_assoc]
      _ = Hpk k r := by rw [hs', hx']
  have hof : Continuous fun x : Mt k r => (Matrix.of x : Mat k r) := continuous_id
  let F : Mt k r × Mt k r → (Wq →L[ℂ] Wp) := fun p =>
    (innerSL ℂ (Φ' (Matrix.of p.2))).smulRight (Φ (Matrix.of p.1 * Matrix.of p.2))
  have hcont : Continuous fun p : Wq × Wp => (innerSL ℂ p.1).smulRight p.2 := by
    have h1 : Continuous fun p : Wq × Wp => innerSL ℂ p.1 := (innerSL ℂ).continuous.comp continuous_fst
    exact ((ContinuousLinearMap.smulRightL ℂ Wq Wp).continuous₂).comp (h1.prodMk continuous_snd)
  have h1 : ContinuousOn (fun p : Mt k r × Mt k r => Φ' (Matrix.of p.2)) (S ×ˢ S) :=
    hΦ'.comp (hof.comp continuous_snd).continuousOn fun p hp => hp.2
  have h2 : ContinuousOn (fun p : Mt k r × Mt k r => Φ (Matrix.of p.1 * Matrix.of p.2)) (S ×ˢ S) :=
    hΦ.comp ((hof.comp continuous_fst).matrix_mul (hof.comp continuous_snd)).continuousOn
      fun p hp => hmul _ _ hp.1 hp.2
  have hF : ContinuousOn F (S ×ˢ S) := hcont.comp_continuousOn (h1.prodMk h2)
  have hsm : StronglyMeasurable ((S ×ˢ S).indicator F) :=
    stronglyMeasurable_indicator_of_continuousOn (hS.prod hS) hF
  have hint : StronglyMeasurable fun γ => ∫ x, (S ×ˢ S).indicator F (γ, x) ∂μG :=
    hsm.integral_prod_right'
  have hm : Measurable fun γ => hsNormSq ((c : ℂ)⁻¹ • ∫ x, (S ×ˢ S).indicator F (γ, x) ∂μG) :=
    (continuous_hsNormSq.comp_stronglyMeasurable (hint.const_smul (c : ℂ)⁻¹)).measurable
  have hae : ∀ᵐ x ∂μG, x ∈ S := by rw [ae_iff]; exact hH.2.2.1
  have heq : (S.indicator fun γ => hsNormSq (ampJ μG c Φ Φ' (Matrix.of γ))) =
      S.indicator fun γ => hsNormSq ((c : ℂ)⁻¹ • ∫ x, (S ×ˢ S).indicator F (γ, x) ∂μG) := by
    refine Set.indicator_congr fun γ hγ => ?_
    unfold ampJ
    congr 2
    refine integral_congr_ae (hae.mono fun x hx => ?_)
    have : (γ, x) ∈ S ×ˢ S := ⟨hγ, hx⟩
    simp only [Set.indicator_of_mem this, F]
  rw [heq]
  exact hm.indicator hS

end GlobalTheory.Amp.AmpMeas
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableStarProjectionKerMatrix
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
  [CompleteSpace E] [CompleteSpace F]

theorem kerProj_re_inner_reg (T : E →L[ℂ] F) (t : ℝ) (w : E) :
    (⟪w, (ContinuousLinearMap.adjoint T ∘L T + (t : ℂ) • (1 : E →L[ℂ] E)) w⟫_ℂ).re
      = ‖T w‖ ^ 2 + t * ‖w‖ ^ 2 := by
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, inner_add_right,
    inner_smul_right, ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]

theorem kerProj_isUnit_reg (T : E →L[ℂ] F) {t : ℝ} (ht : 0 < t) :
    IsUnit (ContinuousLinearMap.adjoint T ∘L T + (t : ℂ) • (1 : E →L[ℂ] E)) := by
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  set B := ContinuousLinearMap.adjoint T ∘L T + (t : ℂ) • (1 : E →L[ℂ] E) with hB
  have hinj : Function.Injective B := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    have h := kerProj_re_inner_reg T t w
    rw [← hB, hw] at h
    simp only [inner_zero_right, Complex.zero_re] at h
    have h1 : t * ‖w‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖T w‖]
    have h2 : ‖w‖ ^ 2 ≤ 0 := by
      by_contra hc
      push_neg at hc
      nlinarith [mul_pos ht hc]
    have : ‖w‖ = 0 := by nlinarith [norm_nonneg w]
    exact norm_eq_zero.mp this
  exact ⟨hinj, (LinearMap.injective_iff_surjective (f := (B : E →ₗ[ℂ] E))).mp hinj⟩

theorem kerProj_reg_estimate (T : E →L[ℂ] F) {t : ℝ} (ht : 0 < t) (k : E) (z : F)
    (hk : T k = 0) :
    ‖(t : ℂ) • Ring.inverse (ContinuousLinearMap.adjoint T ∘L T + (t : ℂ) • (1 : E →L[ℂ] E))
      (k + ContinuousLinearMap.adjoint T z) - k‖ ^ 2 ≤ t * ‖z‖ ^ 2 := by
  have hu := kerProj_isUnit_reg T ht
  set B := ContinuousLinearMap.adjoint T ∘L T + (t : ℂ) • (1 : E →L[ℂ] E) with hB
  set w := (t : ℂ) • Ring.inverse B (k + ContinuousLinearMap.adjoint T z) - k with hw
  have hBk : B k = (t : ℂ) • k := by simp [hB, hk]
  have hBw : B w = (t : ℂ) • ContinuousLinearMap.adjoint T z := by
    have : B (Ring.inverse B (k + ContinuousLinearMap.adjoint T z))
        = k + ContinuousLinearMap.adjoint T z := by
      rw [← ContinuousLinearMap.mul_apply, Ring.mul_inverse_cancel _ hu]; rfl
    rw [hw, map_sub, map_smul, this, hBk, smul_add]; abel
  have h := kerProj_re_inner_reg T t w
  rw [← hB, hBw, inner_smul_right, ContinuousLinearMap.adjoint_inner_right,
    Complex.re_ofReal_mul] at h
  have h1 : (⟪T w, z⟫_ℂ).re ≤ ‖T w‖ * ‖z‖ :=
    (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
  have h2 : ‖T w‖ ^ 2 + t * ‖w‖ ^ 2 ≤ t * (‖T w‖ * ‖z‖) := by
    rw [← h]; exact mul_le_mul_of_nonneg_left h1 ht.le
  have h3 : t * ‖w‖ ^ 2 ≤ t * (t * ‖z‖ ^ 2) := by
    nlinarith [sq_nonneg (‖T w‖ - t * ‖z‖), sq_nonneg ‖T w‖, sq_nonneg (t * ‖z‖)]
  exact le_of_mul_le_mul_left h3 ht

theorem kerProj_reg_tendsto (T : E →L[ℂ] F) (v : E) :
    Filter.Tendsto (fun j : ℕ => (((1 / ((j : ℝ) + 1) : ℝ)) : ℂ) •
      Ring.inverse (ContinuousLinearMap.adjoint T ∘L T
        + (((1 / ((j : ℝ) + 1) : ℝ)) : ℂ) • (1 : E →L[ℂ] E)) v) Filter.atTop
      (nhds ((LinearMap.ker (T : E →ₗ[ℂ] F)).starProjection v)) := by
  set K := LinearMap.ker (T : E →ₗ[ℂ] F) with hK
  have hmem : v - K.starProjection v ∈ Kᗮ := K.sub_starProjection_mem_orthogonal v
  have horth : Kᗮ = LinearMap.range (LinearMap.adjoint (T : E →ₗ[ℂ] F)) :=
    LinearMap.orthogonal_ker _
  rw [horth] at hmem
  obtain ⟨z, hz⟩ := hmem
  have hz' : ContinuousLinearMap.adjoint T z = v - K.starProjection v := by
    rw [← hz]; rfl
  have hk : T (K.starProjection v) = 0 := K.starProjection_apply_mem v
  have hv : v = K.starProjection v + ContinuousLinearMap.adjoint T z := by rw [hz']; abel
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Filter.Tendsto (fun j : ℕ => Real.sqrt ((1 / ((j : ℝ) + 1)) * ‖z‖ ^ 2))
      Filter.atTop (nhds 0) := by
    have := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const (‖z‖ ^ 2)).sqrt
    simpa using this
  refine squeeze_zero (fun _ => norm_nonneg _) (fun j => ?_) hlim
  apply Real.le_sqrt_of_sq_le
  have := kerProj_reg_estimate T (t := 1 / ((j : ℝ) + 1)) (by positivity) _ z hk
  rwa [← hv] at this

theorem measurable_starProjection_ker_clm {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [MeasurableSpace E] [BorelSpace E] (T : X → E →L[ℂ] F) (v : X → E)
    (hT : Continuous T) (hv : Continuous v) :
    Measurable fun x => (LinearMap.ker (T x : E →ₗ[ℂ] F)).starProjection (v x) := by
  refine measurable_of_tendsto_metrizable (f := fun (j : ℕ) x => (((1 / ((j : ℝ) + 1) : ℝ)) : ℂ) •
      Ring.inverse (ContinuousLinearMap.adjoint (T x) ∘L (T x)
        + (((1 / ((j : ℝ) + 1) : ℝ)) : ℂ) • (1 : E →L[ℂ] E)) (v x)) (fun j => ?_) ?_
  · apply Continuous.measurable
    apply Continuous.const_smul
    refine Continuous.clm_apply ?_ hv
    have hc : Continuous fun x => ContinuousLinearMap.adjoint (T x) ∘L (T x)
        + (((1 / ((j : ℝ) + 1) : ℝ)) : ℂ) • (1 : E →L[ℂ] E) :=
      ((ContinuousLinearMap.adjoint.continuous.comp hT).clm_comp hT).add continuous_const
    rw [continuous_iff_continuousAt]
    intro x
    obtain ⟨u, hu⟩ := kerProj_isUnit_reg (T x) (t := 1 / ((j : ℝ) + 1)) (by positivity)
    have h1 := NormedRing.inverse_continuousAt u
    rw [hu] at h1
    exact ContinuousAt.comp (f := fun x => ContinuousLinearMap.adjoint (T x) ∘L (T x)
        + (((1 / ((j : ℝ) + 1) : ℝ)) : ℂ) • (1 : E →L[ℂ] E)) h1 hc.continuousAt
  · rw [tendsto_pi_nhds]
    intro x
    exact kerProj_reg_tendsto (T x) (v x)

end

theorem measurable_starProjection_ker_matrix : ∀ (X : Type) [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] (n p : ℕ) (L : X → Matrix (Fin p) (Fin n) ℂ) (v : X → EuclideanSpace ℂ (Fin n)), Continuous L → Continuous v → Measurable fun x => (LinearMap.ker (Matrix.toEuclideanLin (L x))).starProjection (v x) := by
  intro X _ _ _ n p L v hL hv
  let Φ : Matrix (Fin p) (Fin n) ℂ →ₗ[ℂ] (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin p)) :=
    (LinearMap.toContinuousLinearMap.toLinearMap).comp Matrix.toEuclideanLin.toLinearMap
  have hΦ : Continuous Φ := Φ.continuous_of_finiteDimensional
  exact measurable_starProjection_ker_clm (fun x => Φ (L x)) v (hΦ.comp hL) hv

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemAdelicSpanOfLatticeIffForallPlaceStatement
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_adelicSpanOfLattice_iff_forall_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), IsLat L → ∀ x : Fin n → E ⊗[F] Ad F, x ∈ hat F L ↔ ∀ v : HeightOneSpectrum (𝓞 F), prVec v x ∈ loc v L := by
  first | exact @GlobalTheory.St.G.mem_hat_iff_forall_loc | exact GlobalTheory.St.G.mem_hat_iff_forall_loc | (intros; apply GlobalTheory.St.G.mem_hat_iff_forall_loc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MirabolicFunctionEqInducedDerivativeAddTailStatement
section
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_function_eq_induced_derivative_add_tail : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) , ψ ≠ 1 → ∀ (m : ℕ) (F : Gn g (m + 1) → ℂ), 1 ≤ m → IsMirClass F → ∀ p : Gn g (m + 1), InMir (p : Mt g (m + 1)) → F p = indR ψ m (m + 1) (der ψ m F) p + indV ψ m (tail ψ m F) p := by
  first | exact @GlobalTheory.GLm.MirStep.mir_step | exact GlobalTheory.GLm.MirStep.mir_step | (intros; apply GlobalTheory.GLm.MirStep.mir_step <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MirabolicInductionPhiPlusInductionFromBlockUniStatement
section
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolicInductionPhiPlus_inductionFromBlockUni : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (i m : ℕ) (ρ : Gn g i → ℂ), i < m → ∀ x : Gn g (m + 1), InMir (x : Mt g (m + 1)) → indV ψ m (indR ψ i m ρ) x = indR ψ i (m + 1) ρ x := by
  first | exact @GlobalTheory.GLm.indV_indR | exact GlobalTheory.GLm.indV_indR | (intros; apply GlobalTheory.GLm.indV_indR <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PairingEqLeadingMinor
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.PrincipalMinorExterior

theorem pairing_eq_leading_minor : ∀ (k r l : ℕ) (hl : l ≤ r + 1) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mx k r),
    Formalism.QuantumDeterminants.herm (cmp l (Formalism.QuantumDeterminants.Hpk k r))
      (cmp l g *ᵥ (wedge (fun a : Fin l => Formalism.QuantumDeterminants.fvec k r z' (Fin.castLE hl a))))
      (wedge (fun a : Fin l => Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a))) =
      ((Formalism.QuantumDeterminants.Zhat k r z z' g).submatrix (Fin.castLE hl) (Fin.castLE hl)).det := by
  intro k r l hl z z' g
  rw [Formalism.QuantumDeterminants.herm, GlobalTheory.TopMinorWedge.cmp_mulVec_wedge, GlobalTheory.TopMinorWedge.cmp_mulVec_wedge,
    GlobalTheory.TopMinorWedge.star_wedge_dot]
  rfl

end GlobalTheory.PrincipalMinorExterior
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PatternGroupSubgroupOrderCharacterStatement
section
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.patternGroup_subgroup_order_character : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ) (Φ : Fin N → Fin N → Prop), (∀ a, ¬ Φ a a) → (∀ a b c, Φ a b → Φ b c → Φ a c) → (∃ H : Subgroup (Gn g N), (∀ x, x ∈ H ↔ InPat Φ (x : Mt g N)) ∧ Nat.card H = g ^ (Finset.univ.filter fun p : Fin N × Fin N => Φ p.1 p.2).card) ∧ (∀ M : Mt g N, InPat Φ M → IsUnit M) ∧ ∀ E : Fin N → Fin N → Prop, (∀ a b c, Φ a b → Φ b c → ¬ E a c) → (∀ a, ¬ E a a) → ∀ M M' : Mt g N, InPat Φ M → InPat Φ M' → sumAt E (M * M') = sumAt E M + sumAt E M' := by
  first | exact @GlobalTheory.GLm.Pattern.pattern_group | exact GlobalTheory.GLm.Pattern.pattern_group | (intros; apply GlobalTheory.GLm.Pattern.pattern_group <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelRegionNormBoundStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_region_norm_bound : ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (C : Set (Mat k r)), inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → IsCompact C → C ⊆ Greg k r z z' → ∃ C0 : ℝ, ∀ γ ∈ C, ∀ s ∈ Sset k r z, ∀ s' ∈ Sset k r z', ∀ b : Fin (r + 1), eucl (s *ᵥ fvec k r z b) ≤ C0 * opn (s * γ * s'⁻¹) ^ (r * (r + 1)) ∧ eucl (s' *ᵥ fvec k r z' b) ≤ C0 * opn (s * γ * s'⁻¹) ^ (r * (r + 1)) := by
  first | exact @GlobalTheory.SgInf.frame_image_bound | exact GlobalTheory.SgInf.frame_image_bound | (intros; apply GlobalTheory.SgInf.frame_image_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerHermitianLatticeOfDeepStarCongruenceStatement
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabilizer_hermitianLattice_of_deep_star_congruence : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ 𝔠 : Ideal (𝓞 K), 𝔠 ≠ ⊥ → (∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) → (∀ x ∈ 𝔠, (N.T : 𝓞 K) ∣ x) → (∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠, ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)), (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧ (x : K) * y / star (Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K)) → ∀ e : ℕ, N.Split Λ → N.Near (𝔠 ^ e) Λ → ∀ s ∈ N.Rs, (∀ x ∈ N.P0, s x - x ∈ 𝔠 ^ (3 * e + 10) • N.P0) → s • Λ = Λ := by
  first | exact @GlobalTheory.DegCnt.stab_of_deep_congruence | exact GlobalTheory.DegCnt.stab_of_deep_congruence | (intros; apply GlobalTheory.DegCnt.stab_of_deep_congruence <;> assumption)
end

