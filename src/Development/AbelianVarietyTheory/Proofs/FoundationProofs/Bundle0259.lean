import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscrB
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0240
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0239
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0245
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0233
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0210
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0092
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0404
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0299
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0234
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0247
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryHeckeCharacterValues

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarValueLeMeanSquareGenusOne
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
open MeasureTheory

noncomputable section

namespace GlobalTheory.GenusOneSup

theorem area_le (Λ : AddSubgroup ℂ) {w₁ w₂ : ℂ} (h₁ : w₁ ∈ Λ) (h₂ : w₂ ∈ Λ)
    (h : 0 < |((starRingEnd ℂ) w₁ * w₂).im|) : area Λ ≤ |((starRingEnd ℂ) w₁ * w₂).im| :=
  csInf_le ⟨0, fun _ ha => ha.1.le⟩ ⟨h, w₁, h₁, w₂, h₂, rfl⟩

theorem area_closure {w₁ w₂ : ℂ} (h : 0 < |((starRingEnd ℂ) w₁ * w₂).im|) :
    area (AddSubgroup.closure {w₁, w₂}) = |((starRingEnd ℂ) w₁ * w₂).im| := by
  have h₁ : w₁ ∈ AddSubgroup.closure ({w₁, w₂} : Set ℂ) := AddSubgroup.subset_closure (by simp)
  have h₂ : w₂ ∈ AddSubgroup.closure ({w₁, w₂} : Set ℂ) := AddSubgroup.subset_closure (by simp)
  refine le_antisymm (area_le _ h₁ h₂ h) (le_csInf ⟨_, h, w₁, h₁, w₂, h₂, rfl⟩ ?_)
  rintro a ⟨ha, x, hx, y, hy, rfl⟩
  obtain ⟨m, n, rfl⟩ := AddSubgroup.mem_closure_pair.1 hx
  obtain ⟨m', n', rfl⟩ := AddSubgroup.mem_closure_pair.1 hy
  have e : ((starRingEnd ℂ) (m • w₁ + n • w₂) * (m' • w₁ + n' • w₂)).im =
      ((m * n' - n * m' : ℤ) : ℝ) * ((starRingEnd ℂ) w₁ * w₂).im := by
    simp [Complex.mul_im]
    ring
  rw [e, abs_mul] at ha ⊢
  have hk : (m * n' - n * m' : ℤ) ≠ 0 := by
    intro h0
    rw [h0] at ha
    simp at ha
  have : (1 : ℝ) ≤ |((m * n' - n * m' : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hk
  nlinarith

theorem exists_domain {w₁ w₂ : ℂ} (hli : LinearIndependent ℝ ![w₁, w₂]) :
    ∃ F : Set ℂ, IsAddFundamentalDomain (AddSubgroup.closure ({w₁, w₂} : Set ℂ)) F volume ∧
      Bornology.IsBounded F ∧ 0 < |((starRingEnd ℂ) w₁ * w₂).im| ∧
      volume F = ENNReal.ofReal |((starRingEnd ℂ) w₁ * w₂).im| := by
  let b : Module.Basis (Fin 2) ℝ ℂ := basisOfLinearIndependentOfCardEqFinrank hli (by simp)
  have hb : ⇑b = ![w₁, w₂] := coe_basisOfLinearIndependentOfCardEqFinrank _ _
  have hdet : Complex.basisOneI.det b = ((starRingEnd ℂ) w₁ * w₂).im := by
    rw [Module.Basis.det_apply, Matrix.det_fin_two]
    simp [Module.Basis.toMatrix_apply, hb, Complex.mul_im]
    ring
  have hspan : (Submodule.span ℤ (Set.range b)).toAddSubgroup = AddSubgroup.closure ({w₁, w₂} : Set ℂ) := by
    rw [Submodule.span_int_eq_addSubgroupClosure, hb]
    congr 1
    simp [Set.pair_comm]
  refine ⟨ZSpan.fundamentalDomain b, ?_, ZSpan.fundamentalDomain_isBounded b, ?_, ?_⟩
  · rw [← hspan]; exact ZSpan.isAddFundamentalDomain' b volume
  · rw [← hdet]; exact abs_pos.2 (Complex.basisOneI.isUnit_det b).ne_zero
  · rw [ZSpan.measure_fundamentalDomain b volume Complex.basisOneI, hdet,
      measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped _ _), ← Complex.toBasis_orthonormalBasisOneI]
    have := Complex.orthonormalBasisOneI.volume_parallelepiped
    simp only [OrthonormalBasis.coe_toBasis, this, mul_one]

def lineIso : EuclideanSpace ℂ Unit ≃ₗᵢ[ℝ] ℂ where
  toFun x := x ()
  invFun z := WithLp.toLp 2 (fun _ => z)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
  norm_map' x := by
    show ‖x ()‖ = ‖x‖
    simp [EuclideanSpace.norm_eq]

theorem sup_le_mean (Λ : AddSubgroup ℂ) (a v : ℝ) (F : Set ℂ) (g : ℂ → ℂ) (ha : 0 < a) (hv : 1 ≤ v)
    (hmin : ∀ x ∈ Λ, x ≠ 0 → a / v ≤ ‖x‖ ^ 2) (hF : IsAddFundamentalDomain Λ F volume)
    (hvol : volume F = ENNReal.ofReal a) (hg : Differentiable ℂ g)
    (hper : ∀ x ∈ Λ, ∀ z, ‖g (z + x)‖ ^ 2 * Real.exp (-Real.pi * ‖z + x‖ ^ 2 / a) =
      ‖g z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / a))
    (hint : IntegrableOn (fun z => ‖g z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / a)) F) (z : ℂ) :
    ‖g z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / a) ≤
      3 * (2 * v + 1) * (a⁻¹ * ∫ z in F, ‖g z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / a)) := by
  set s : ℝ := Real.sqrt a with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 ha
  have hs2 : s ^ 2 = a := Real.sq_sqrt ha.le
  let φ : EuclideanSpace ℂ Unit ≃L[ℝ] ℂ :=
    lineIso.toContinuousLinearEquiv.trans (ContinuousLinearEquiv.smulLeft (Units.mk0 s hs0.ne'))
  have hφ : ∀ x, φ x = s • lineIso x := fun _ => rfl
  have hn : ∀ x, ‖φ x‖ ^ 2 = a * ‖x‖ ^ 2 := fun x => by
    rw [hφ, norm_smul, lineIso.norm_map, mul_pow, Real.norm_eq_abs, sq_abs, hs2]
  have hw : ∀ x, -Real.pi * ‖x‖ ^ 2 = -Real.pi * ‖φ x‖ ^ 2 / a := fun x => by
    rw [hn]; field_simp
  have hmp : MeasurePreserving φ volume (ENNReal.ofReal a⁻¹ • (volume : Measure ℂ)) := by
    have h1 : MeasurePreserving (fun z : ℂ => s • z) volume (ENNReal.ofReal a⁻¹ • (volume : Measure ℂ)) := by
      refine ⟨measurable_const_smul s, ?_⟩
      rw [Measure.map_addHaar_smul volume hs0.ne', Complex.finrank_real_complex, hs2,
        abs_of_pos (inv_pos.2 ha)]
    exact h1.comp lineIso.measurePreserving
  have hemb : MeasurableEmbedding φ := φ.toHomeomorph.measurableEmbedding
  let A : AddSubgroup (EuclideanSpace ℂ Unit) := Λ.comap (φ : EuclideanSpace ℂ Unit →+ ℂ)
  have hA : ∀ x, x ∈ A ↔ φ x ∈ Λ := fun _ => Iff.rfl
  have hF' : IsAddFundamentalDomain A (φ ⁻¹' F) volume := by
    refine hF.preimage_of_equiv (f := φ) (e := fun y : Λ => (⟨φ.symm y, (hA _).2 (by simp)⟩ : A))
      ⟨hmp.measurable, ?_⟩ ⟨?_, ?_⟩ ?_
    · rw [hmp.map_eq]; exact Measure.smul_absolutelyContinuous
    · intro x y h
      exact Subtype.ext (φ.symm.injective (congrArg Subtype.val h))
    · intro x
      exact ⟨⟨φ x, x.2⟩, Subtype.ext (by simp)⟩
    · intro y x
      show φ (φ.symm y + x) = (y : ℂ) + φ x
      simp
  have hvol' : volume (φ ⁻¹' F) = 1 := by
    rw [hmp.measure_preimage_emb hemb, Measure.smul_apply, hvol, smul_eq_mul,
      ← ENNReal.ofReal_mul (inv_pos.2 ha).le, inv_mul_cancel₀ ha.ne', ENNReal.ofReal_one]
  have hd : Differentiable ℂ (fun x : EuclideanSpace ℂ Unit => g (φ x)) := by
    have : Differentiable ℂ (fun x : EuclideanSpace ℂ Unit => (s : ℂ) * x ()) := by fun_prop
    exact hg.comp this
  have key := GlobalTheory.ThetaSupBall.sup_le_mean_square Unit A v (φ ⁻¹' F) (fun x => g (φ x)) hv ?_ hF' hvol' hd ?_ ?_ (φ.symm z)
  · simp only [hw, Fintype.card_unit, Nat.cast_one, mul_one, pow_one, ContinuousLinearEquiv.apply_symm_apply] at key
    rw [hmp.setIntegral_preimage_emb hemb (fun z => ‖g z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / a)),
      Measure.restrict_smul, integral_smul_measure, ENNReal.toReal_ofReal (inv_pos.2 ha).le, smul_eq_mul] at key
    exact key
  · intro x hx hx0
    have := hmin (φ x) hx (by simpa using hx0)
    rw [hn, div_eq_mul_one_div] at this
    exact le_of_mul_le_mul_left this ha
  · intro x hx y
    simp only [hw, map_add]
    exact hper _ hx _
  · simp only [hw]
    refine (hmp.integrableOn_comp_preimage hemb
      (f := fun z => ‖g z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / a))).2 ?_
    unfold IntegrableOn
    rw [Measure.restrict_smul]
    exact Integrable.smul_measure hint ENNReal.ofReal_ne_top

theorem thetaTranslation_weighted_normSq (Λ : AddSubgroup ℂ) (t z : ℂ) (g : ℂ → ℂ) :
    ‖U1 Λ t g z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / area Λ) =
      ‖g (z + t)‖ ^ 2 * Real.exp (-Real.pi * ‖z + t‖ ^ 2 / area Λ) := by
  unfold U1
  rw [norm_mul, mul_pow, Complex.norm_exp, mul_assoc, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 2
  have e : (2 * (area Λ : ℂ)) = ((2 * area Λ : ℝ) : ℂ) := by push_cast; ring
  rw [e, Complex.sub_re, Complex.div_ofReal_re, Complex.div_ofReal_re, ← Complex.normSq_eq_norm_sq,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.normSq_apply]
  simp
  ring

theorem lattice_sup (Λ : AddSubgroup ℂ)
    (hΛ : ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂})
    (v : ℝ) (hv : 1 ≤ v) (hmin : ∀ x ∈ Λ, x ≠ 0 → area Λ / v ≤ ‖x‖ ^ 2) (t : ℂ) :
    ‖U1 Λ t (sgStar Λ) 0‖ ^ 2 ≤ 3 * (2 * v + 1) * nrm1Sq Λ (sgStar Λ) := by
  obtain ⟨⟨hd, -, -, hU⟩, -⟩ := GlobalTheory.OddTheta.sgStar_laws Λ hΛ
  obtain ⟨w₁, w₂, hli, rfl⟩ := hΛ
  obtain ⟨F, hF, hb, hpos, hvol⟩ := exists_domain hli
  have har := area_closure hpos
  rw [← har] at hpos hvol
  set Λ : AddSubgroup ℂ := AddSubgroup.closure {w₁, w₂} with hΛ
  have hper : ∀ x ∈ Λ, ∀ z, ‖sgStar Λ (z + x)‖ ^ 2 * Real.exp (-Real.pi * ‖z + x‖ ^ 2 / area Λ) =
      ‖sgStar Λ z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / area Λ) := by
    intro x hx z
    rw [← thetaTranslation_weighted_normSq, hU x hx, norm_mul]
    split_ifs <;> simp
  have hc : Continuous fun z => ‖sgStar Λ z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / area Λ) := by
    have := hd.continuous
    fun_prop
  have hint : IntegrableOn (fun z => ‖sgStar Λ z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / area Λ)) F :=
    (hc.continuousOn.integrableOn_compact hb.isCompact_closure).mono_set subset_closure
  have key := sup_le_mean Λ (area Λ) v F (sgStar Λ) hpos hv hmin hF hvol hd hper hint t
  have h0 := thetaTranslation_weighted_normSq Λ t 0 (sgStar Λ)
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div,
    Real.exp_zero, mul_one, zero_add] at h0
  rw [h0]
  refine key.trans (le_of_eq ?_)
  congr 1
  have hF' := Classical.epsilon_spec (p := fun Fd : Set ℂ => IsAddFundamentalDomain Λ Fd volume) ⟨F, hF⟩
  have : Countable Λ := by
    have : (Λ : Set ℂ) ⊆ Set.range (fun p : ℤ × ℤ => p.1 • w₁ + p.2 • w₂) := by
      intro x hx
      obtain ⟨m, n, rfl⟩ := AddSubgroup.mem_closure_pair.1 hx
      exact ⟨(m, n), rfl⟩
    exact ((Set.countable_range _).mono this).to_subtype
  have : VAddInvariantMeasure Λ ℂ volume := ⟨fun γ s _ => measure_preimage_add volume (γ : ℂ) s⟩
  unfold nrm1Sq
  simp only
  rw [setAverage_eq, measureReal_def, hF'.measure_eq hF, hF'.setIntegral_eq hF, hvol,
    ENNReal.toReal_ofReal hpos.le, smul_eq_mul]
  intro γ z
  have := hper γ γ.2 z
  rw [add_comm] at this
  exact this

theorem value_le_mean_square : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ t, ‖U1 (lamOf D cc δ) t (sgStar (lamOf D cc δ)) 0‖ ^ 2 ≤ 3 * (2 * D.host.rdE + 1) * nrm1Sq (lamOf D cc δ) (sgStar (lamOf D cc δ)) := by
  intro D hD cc δ hc t
  obtain ⟨hΛ, -, -, -, hst⟩ := GlobalTheory.CurveLattice.lattice_of_curve D hD cc δ hc
  obtain ⟨-, hlog, hrd, -⟩ := GlobalTheory.NormSum.letters_and_sizes D hD
  refine lattice_sup _ hΛ _ hrd ?_ t
  intro x hx hx0
  have hd : (0 : ℝ) < D.host.d := by exact_mod_cast D.host.hyp.2.1.pos
  have hsq := D.host.sqd_sq
  let β : D.host.K := ⟨D.host.sqd, IntermediateField.mem_adjoin_simple_self ℚ _⟩
  have hβ : β ^ 2 = -(D.host.d : D.host.K) := Subtype.ext (by simpa [β] using hsq)
  have hi : IsIntegral ℤ β := by
    refine IsIntegral.of_pow (n := 2) two_pos ?_
    rw [hβ]
    exact (isIntegral_natCast _).neg
  have hm := hst ⟨β, hi⟩ x hx
  set c : ℂ := D.host.φ₀ (D.host.sqd) with hcdef
  have hm' : c * x ∈ lamOf D cc δ := hm
  have hc2 : c ^ 2 = -(D.host.d : ℂ) := by
    rw [hcdef, ← map_pow, hsq]; simp
  have hre : c.re * c.re - c.im * c.im = -(D.host.d : ℝ) := by
    have := congrArg Complex.re hc2
    simpa [pow_two] using this
  have him : c.re * c.im = 0 := by
    have := congrArg Complex.im hc2
    simp [pow_two] at this
    linarith
  have hre0 : c.re = 0 := by
    rcases mul_eq_zero.1 him with h | h
    · exact h
    · rw [h] at hre; nlinarith [mul_self_nonneg c.re]
  have him2 : c.im ^ 2 = D.host.d := by rw [hre0] at hre; linarith
  have e : |((starRingEnd ℂ) x * (c * x)).im| = |c.im| * ‖x‖ ^ 2 := by
    have : ((starRingEnd ℂ) x * (c * x)).im = c.im * ‖x‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp
      ring
    rw [this, abs_mul, abs_of_nonneg (sq_nonneg ‖x‖)]
  have hx2 : 0 < ‖x‖ ^ 2 := by positivity
  have hci : 0 < |c.im| := abs_pos.2 (by intro h; rw [h] at him2; linarith)
  have hle := area_le _ hx hm' (by rw [e]; positivity)
  have hrd0 : 0 < D.host.rdE := by linarith
  have hdle : (D.host.d : ℝ) ≤ D.host.rdE ^ 2 := by
    rw [← Real.log_le_log_iff hd (by positivity), Real.log_pow]
    exact_mod_cast hlog
  have hcle : |c.im| ≤ D.host.rdE := abs_le_of_sq_le_sq' (by rw [him2]; exact hdle) hrd0.le |> abs_le.2
  rw [div_le_iff₀ hrd0]
  rw [e] at hle
  nlinarith

end GlobalTheory.GenusOneSup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SummableExpNegHerm
section
open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical

namespace GlobalTheory.UnitaryTheta.GaussSumm

theorem exists_mul_norm_sq_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (H : Sesq V) (hH : IsPosHerm H) : ∃ c : ℝ, 0 < c ∧ ∀ x : V, c * ‖x‖ ^ 2 ≤ (H x x).re := by
  have hcont : Continuous fun x : V => (H x x).re := by
    let b := Module.finBasis ℂ V
    have e : (fun x : V => H x x) = fun x => ∑ i, H x (b i) * conj (b.repr x i) := by
      funext x
      conv_lhs => rw [show H x x = H x (∑ i, b.repr x i • b i) by rw [b.sum_repr]]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [LinearMap.map_smulₛₗ, smul_eq_mul, mul_comm]
    have : Continuous fun x : V => H x x := by
      rw [e]
      refine continuous_finset_sum _ fun i _ => ?_
      have h1 : Continuous fun x : V => H x (b i) :=
        (H.flip (b i)).continuous_of_finiteDimensional
      have h2 : Continuous fun x : V => b.repr x i :=
        (b.coord i).continuous_of_finiteDimensional
      exact h1.mul (continuous_conj.comp h2)
    exact continuous_re.comp this
  haveI : ProperSpace V := FiniteDimensional.proper ℂ V
  obtain ⟨c, hc, hle⟩ : ∃ c : ℝ, 0 < c ∧ ∀ x ∈ Metric.sphere (0 : V) 1, c ≤ (H x x).re := by
    refine (isCompact_sphere (0 : V) 1).exists_forall_le' hcont.continuousOn fun x hx => hH.2 x ?_
    rintro rfl
    simp at hx
  refine ⟨c, hc, fun x => ?_⟩
  by_cases hx : x = 0
  · subst hx
    simp
  have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
  have h1 := hle (((‖x‖⁻¹ : ℝ) : ℂ) • x) (by
    rw [mem_sphere_zero_iff_norm, norm_smul, Complex.norm_real, norm_inv, norm_norm,
      inv_mul_cancel₀ hn.ne'])
  have e : H (((‖x‖⁻¹ : ℝ) : ℂ) • x) (((‖x‖⁻¹ : ℝ) : ℂ) • x) = ((‖x‖⁻¹ ^ 2 : ℝ) : ℂ) * H x x := by
    rw [LinearMap.map_smulₛₗ, map_smul, LinearMap.smul_apply, conj_ofReal, smul_eq_mul, smul_eq_mul]
    push_cast
    ring
  rw [e, re_ofReal_mul] at h1
  have h2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg ‖x‖)
  have e2 : ‖x‖⁻¹ ^ 2 * (H x x).re * ‖x‖ ^ 2 = (H x x).re := by field_simp
  rwa [e2] at h2

theorem exp_le_inv_pow {a : ℝ} (ha : 0 < a) (C : ℝ) (k : ℕ) {t : ℝ} (ht : 0 < t) :
    Real.exp (-(a * t ^ 2) + C * t) ≤ (k.factorial * Real.exp ((C + 1) ^ 2 / (4 * a))) * t⁻¹ ^ k := by
  have h1 : t ^ k / k.factorial ≤ Real.exp t := Real.pow_div_factorial_le_exp t ht.le k
  have hk : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  rw [div_le_iff₀ hk] at h1
  have h2 : -(a * t ^ 2) + C * t + t ≤ (C + 1) ^ 2 / (4 * a) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (2 * a * t - (C + 1))]
  rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc Real.exp (-(a * t ^ 2) + C * t) * t ^ k
      ≤ Real.exp (-(a * t ^ 2) + C * t) * (Real.exp t * k.factorial) := by gcongr
    _ = k.factorial * Real.exp (-(a * t ^ 2) + C * t + t) := by rw [Real.exp_add _ t]; ring
    _ ≤ _ := by gcongr

theorem summable_exp_neg_herm : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (H : Sesq V), IsPosHerm H → ∀ (Λ : AddSubgroup V) [DiscreteTopology Λ] (C : ℝ), Summable (fun x : Λ => Real.exp (-(π / 2) * (H x x).re + C * ‖(x : V)‖)) := by
  intro V _ _ _ H hH Λ _ C
  obtain ⟨c, hc, hle⟩ := exists_mul_norm_sq_le H hH
  letI : NormedSpace ℝ V := NormedSpace.complexToReal
  haveI : FiniteDimensional ℝ V := FiniteDimensional.complexToReal V
  let L : Submodule ℤ V := AddSubgroup.toIntSubmodule Λ
  haveI : DiscreteTopology L := ‹DiscreteTopology Λ›
  have hs : Summable fun x : Λ => ‖(x : V)‖⁻¹ ^ (Module.finrank ℤ L + 1) :=
    ZLattice.summable_norm_pow_inv L (Module.finrank ℤ L + 1) (Nat.lt_succ_self _)
  have ha : 0 < π / 2 * c := by have := Real.pi_pos; positivity
  refine Summable.of_norm_bounded_eventually (hs.mul_left
    ((Module.finrank ℤ L + 1).factorial * Real.exp ((C + 1) ^ 2 / (4 * (π / 2 * c))))) ?_
  filter_upwards [Filter.eventually_cofinite_ne (0 : Λ)] with x hx
  have hn : 0 < ‖(x : V)‖ := norm_pos_iff.2 fun h => hx (Subtype.ext h)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine le_trans (Real.exp_le_exp.2 ?_) (exp_le_inv_pow ha C _ hn)
  have := mul_le_mul_of_nonneg_left (hle x) (by have := Real.pi_pos; positivity : 0 ≤ π / 2)
  linarith

end GlobalTheory.UnitaryTheta.GaussSumm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SurjectiveHalf
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc

namespace GlobalTheory.FundSeq

theorem ontoAt (l : ℕ) [Fact l.Prime] : OntoAt l := by
  obtain ⟨C⟩ := GlobalTheory.T.nonempty_localPeriodRingsData l
  exact ontoAt_of_core C (GlobalTheory.T.bcris_one_sub_frobenius_surjective l C) (GlobalTheory.T.fundamental_map_surjective l C)

theorem surjective_half (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.LocalSituation.adm1 D :=
  surjective_half_of_onto (fun l _ => ontoAt l) D

end GlobalTheory.FundSeq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorConjugateTangentSpacePadZeroColumns
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators

namespace GlobalTheory.ConjRestrict

theorem coeff_taylorDir_embDomain {σ σ' W : Type*} [Fintype σ] [Fintype σ'] [NormedAddCommGroup W]
    [NormedSpace ℂ W] (e : σ ↪ σ') (u : σ' → W) {f : W → ℂ} (hf : AnalyticAt ℂ f 0) (α : σ →₀ ℕ) :
    MvPowerSeries.coeff α (taylorDir (fun i => u (e i)) f) =
      MvPowerSeries.coeff (Finsupp.embDomain e α) (taylorDir u f) := by
  have h1 : ((α.toMultiset.toList : List σ) : Multiset σ) = Finsupp.toMultiset α := by simp
  have h2 : ((α.toMultiset.toList.map e : List σ') : Multiset σ') =
      Finsupp.toMultiset (Finsupp.embDomain e α) := by
    rw [← Multiset.map_coe, h1, Finsupp.toMultiset_map, Finsupp.embDomain_eq_mapDomain]
  have h3 : ∏ i, ((Finsupp.embDomain e α) i).factorial = ∏ i, (α i).factorial := by
    rw [← Finsupp.prod_fintype (Finsupp.embDomain e α) (fun _ n => n.factorial) (by simp),
      Finsupp.prod_embDomain, Finsupp.prod_fintype _ _ (by simp)]
  rw [coeff_taylorDir_eq_lineDerivList _ hf h1, coeff_taylorDir_eq_lineDerivList _ hf h2, h3,
    List.map_map]
  rfl

def colEmb (D : D7) (N N' m : ℕ) :
    D.what₂.Tau × Fin N' × Fin N ↪ D.what₂.Tau × Fin N' × Fin (N + m) :=
  ⟨fun k => (k.1, k.2.1, Fin.castAdd m k.2.2), by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
    simp only [Prod.mk.injEq, Fin.castAdd_inj] at h
    simp [h]⟩

theorem colEmb_apply (D : D7) (N N' m : ℕ) (k : D.what₂.Tau × Fin N' × Fin N) :
    colEmb D N N' m k = (k.1, k.2.1, Fin.castAdd m k.2.2) := rfl

theorem pad_coordV (D : D7) {N N' : ℕ} (m : ℕ) (k : D.what₂.Tau × Fin N' × Fin N) :
    pad D m (coordV D k) = coordV D (colEmb D N N' m k) := by
  funext τ a i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · rw [pad_left]; simp [coordV, colEmb_apply]
  · rw [pad_right]
    have : Fin.natAdd N i ≠ Fin.castAdd m k.2.2 := by
      intro h
      have := congrArg Fin.val h
      have := k.2.2.2
      simp at *
      omega
    simp [coordV, colEmb_apply, this]

theorem taylor_pad (D : D7) {N N' : ℕ} (m : ℕ) {G : VC D (N + m) N' → ℂ} (hG : Differentiable ℂ G)
    (α : Mono D N N') :
    Formalism.MainNotions.TaylorLogMetric.taylor D (fun z : VC D N N' => G (pad D m z)) α =
      Formalism.MainNotions.TaylorLogMetric.taylor D G (Finsupp.embDomain (colEmb D N N' m) α) := by
  have han : AnalyticAt ℂ G 0 :=
    SCV.analyticAt_iff_eventually_differentiableAt.2 (Filter.Eventually.of_forall hG)
  rw [ConjSeries.taylor_eq_coeff, ConjSeries.taylor_eq_coeff, ← coeff_taylorDir_embDomain _ _ han]
  have h := taylorDir_comp_clm (LinearMap.toContinuousLinearMap (padL D m (N := N) (N' := N')))
    (coordV D) han
  simp only [LinearMap.coe_toContinuousLinearMap', padL_apply, pad_coordV] at h
  rw [h]

theorem mono_pad (D : D7) {N N' : ℕ} (m : ℕ) (α : Mono D N N') (z : VC D N N') :
    mono D (Finsupp.embDomain (colEmb D N N' m) α) (pad D m z) = mono D α z := by
  rw [mono, Finsupp.prod_embDomain]
  simp [mono, colEmb_apply]

theorem mem_range_of_mono_pad (D : D7) {N N' : ℕ} (m : ℕ) (β : Mono D (N + m) N') (z : VC D N N')
    (h : mono D β (pad D m z) ≠ 0) : β ∈ Set.range (Finsupp.embDomain (colEmb D N N' m)) := by
  rw [Finsupp.mem_range_embDomain_iff]
  rintro ⟨τ, a, i⟩ hk
  revert hk
  refine Fin.addCases (fun i _ => ⟨(τ, a, i), rfl⟩) (fun i hk => ?_) i
  refine absurd (Finset.prod_eq_zero hk ?_) h
  have : β (τ, a, Fin.natAdd N i) ≠ 0 := Finsupp.mem_support_iff.1 hk
  simp [this]

theorem fnConj_pad : ∀ (D : D7) (N N' m : ℕ) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (G : VC D (N + m) N' → ℂ), Differentiable ℂ G → fnConj D M ρ (fun z : VC D N N' => G (pad D m z)) = fun z => fnConj D M ρ G (pad D m z) := by
  intro D N N' m M ρ G hG
  funext z
  simp only [fnConj]
  rw [← (Finsupp.embDomain_injective (colEmb D N N' m)).tsum_eq
    (f := fun β => ρ (TaylorLogMetric.liftM M (Formalism.MainNotions.TaylorLogMetric.taylor D G β)) * mono D β (pad D m z))
    (fun β hβ => mem_range_of_mono_pad D m β z (right_ne_zero_of_mul hβ))]
  simp only [taylor_pad D m hG, mono_pad]

end GlobalTheory.ConjRestrict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaFunctionSelfDualExistsEqSmulStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFunction_selfDual_exists_eq_smul : ∀ (D : D7) (T : Tor D) (N N' : ℕ) (A : AddSubgroup (VC D N N')), 0 < area T.abelian₂ → DiscreteTopology A → (∀ x, x ∈ A ↔ ∀ y ∈ A, ∃ m : ℤ, (Hf D T x y).im = m) → ∀ F ∈ ThSp D T A, ∀ G ∈ ThSp D T A, G ≠ 0 → ∃ c : ℂ, F = c • G := by
  first | exact @GlobalTheory.ThetaCoordLine.exists_eq_smul | exact GlobalTheory.ThetaCoordLine.exists_eq_smul | (intros; apply GlobalTheory.ThetaCoordLine.exists_eq_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceFormSpanRepNondegenerateMapRepIffStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traceForm_nondegenerate_span_mapRep_iff : ∀ (Γ K L : Type) [Group Γ] [Field K] [Field L] (f : K →+* L) (a : ℕ) (ρ : Γ →* GL (Fin a) K), (∀ x ∈ Submodule.span L (Set.range fun g => ((mapRep f ρ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L)), (∀ g, (x * ((mapRep f ρ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L)).trace = 0) → x = 0) ↔ (∀ x ∈ Submodule.span K (Set.range fun g => ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)), (∀ g, (x * ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)).trace = 0) → x = 0) := by
  first | exact @GlobalTheory.traceForm_span_rep_nondegenerate_mapRep_iff | exact GlobalTheory.traceForm_span_rep_nondegenerate_mapRep_iff | (intros; apply GlobalTheory.traceForm_span_rep_nondegenerate_mapRep_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryHeckeCharacterValuesStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryHeckeCharacter_values : ∀ (D : D7) (N : ℕ) (χ : HeckeU D N) (x : (AE D)ˣ), Mod1All ((χ.f x : ℂˣ) : ℂ) ∧ (IntU D x → ∃ m : ℕ, 0 < m ∧ χ.f x ^ m = 1) ∧ ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), (∃ y : (AE D)ˣ, IntU D y ∧ ZeroAt D p (((x * y : (AE D)ˣ) : AE D) - 1)) → ‖lamC lam ((χ.f x : ℂˣ) : ℂ)‖ = 1 := by
  first | exact @GlobalTheory.HeckeVal.hecke_values | exact GlobalTheory.HeckeVal.hecke_values | (intros; apply GlobalTheory.HeckeVal.hecke_values <;> assumption)
end

