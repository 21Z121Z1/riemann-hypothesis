import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0159
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0002
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0165
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0133
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0160
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TwoFlagsGramNumberNormalFormEqGramProjection
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0167
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentLeviRadicalCoordsHomeomorph
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0168

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiHolomorphicNearPositiveMatricesAtOne
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Dec.FormF
open scoped InnerProductSpace ComplexOrder

noncomputable section
namespace GlobalTheory.Dec

variable {n : ℕ}

theorem posDef_mem_Omega {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) : x ∈ Omega n := by
  intro i
  have hsub : (x.submatrix (Fin.castLE i.isLt) (Fin.castLE i.isLt)).PosDef :=
    hx.submatrix (Fin.castLE_injective _)
  exact hsub.det_pos.ne'

theorem posDef_mem_kConjNonzeroMinorsSet (ε : Fin n → Bool) {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) : x ∈ U1 ε := by
  intro k hk
  have hu : star k * k = 1 := Matrix.mem_unitaryGroup_iff'.mp hk.1
  rw [Matrix.inv_eq_left_inv hu, Matrix.star_eq_conjTranspose]
  apply posDef_mem_Omega
  apply hx.conjTranspose_mul_mul_same
  intro v v' h
  have h2 := congrArg (fun u => (star k).mulVec u) h
  simpa only [Matrix.mulVec_mulVec, hu, Matrix.one_mulVec] using h2

theorem continuous_leadMinor_conj (ε : Fin n → Bool) (l : ℕ) (hl : l ≤ n) :
    Continuous (fun p : KG ε × (Fin n → Fin n → ℂ) =>
      leadMinor ((toMK p.1)⁻¹ * Matrix.of p.2 * toMK p.1) l hl) := by
  have hinv : ∀ k : KG ε, (toMK k)⁻¹ = (toMK k)ᴴ := fun k =>
    Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.mp ((mem_KG ε _).1 k.2).1)
  simp_rw [hinv]
  unfold leadMinor
  have hc : Continuous (fun k : KG ε => toMK k) := toMK_cont ε
  have hz : Continuous (fun p : KG ε × (Fin n → Fin n → ℂ) => Matrix.of p.2) := continuous_snd
  exact ((((hc.comp continuous_fst).matrix_conjTranspose).matrix_mul hz).matrix_mul
    (hc.comp continuous_fst)).matrix_submatrix _ _ |>.matrix_det

theorem isOpen_kConjNonzeroMinorsSet (ε : Fin n → Bool) : IsOpen {z : Fin n → Fin n → ℂ | Matrix.of z ∈ U1 ε} := by
  have hset : {z : Fin n → Fin n → ℂ | Matrix.of z ∈ U1 ε} =
      (Prod.snd '' {p : KG ε × (Fin n → Fin n → ℂ) | ∃ i : Fin n,
        leadMinor ((toMK p.1)⁻¹ * Matrix.of p.2 * toMK p.1) (i.val + 1) i.isLt = 0})ᶜ := by
    ext z
    constructor
    · rintro hz ⟨⟨k, z'⟩, ⟨i, hi⟩, rfl⟩
      exact hz (toMK k) ((mem_KG ε _).1 k.2) i hi
    · intro hz g hg i hi
      obtain ⟨k, rfl⟩ : g ∈ Set.range (fun k : KG ε => toMK k) := by rw [range_toMK]; exact hg
      exact hz ⟨⟨k, z⟩, ⟨i, hi⟩, rfl⟩
  rw [hset, isOpen_compl_iff]
  refine isClosedMap_snd_of_compactSpace _ ?_
  have hu : {p : KG ε × (Fin n → Fin n → ℂ) | ∃ i : Fin n,
      leadMinor ((toMK p.1)⁻¹ * Matrix.of p.2 * toMK p.1) (i.val + 1) i.isLt = 0} =
      ⋃ i : Fin n, {p | leadMinor ((toMK p.1)⁻¹ * Matrix.of p.2 * toMK p.1) (i.val + 1) i.isLt = 0} := by
    ext p; simp
  rw [hu]
  exact isClosed_iUnion_of_finite fun i =>
    isClosed_eq (continuous_leadMinor_conj ε (i.val + 1) i.isLt) continuous_const

theorem differentiable_leadMinor_mul (a b : Matrix (Fin n) (Fin n) ℂ) (l : ℕ) (hl : l ≤ n) :
    Differentiable ℂ (fun z : Fin n → Fin n → ℂ => leadMinor (a * Matrix.of z * b) l hl) := by
  unfold leadMinor
  simp only [Matrix.det_apply', Matrix.submatrix_apply, Matrix.mul_apply, Matrix.of_apply]
  fun_prop

theorem IsTau.isURepOn {ε : Fin n → Bool} {abelian₂ : Fin n → ℝ} {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] {τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)} {w : W} (h : IsTau ε abelian₂ τ w) :
    IsURepOn (Kset ε) τ := by
  obtain ⟨hfd, ⟨h1, hmul⟩, hdiff, hadj, -⟩ := h
  have hsub : ∀ g ∈ Formalism.REAL.Kset ε, g ∈ KC ε := fun g hg =>
    ⟨⟨⟨g, star g, Matrix.mem_unitaryGroup_iff.mp hg.1, Matrix.mem_unitaryGroup_iff'.mp hg.1⟩, rfl⟩, hg.2⟩
  refine ⟨⟨h1, fun a ha b hb => hmul a (hsub a ha) b (hsub b hb)⟩, ?_, ?_⟩
  · intro g hg v
    have hs : star g ∈ Formalism.REAL.Kset ε := Formalism.REAL.Kset_star ε hg
    have hgg : star g * g = 1 := Matrix.mem_unitaryGroup_iff'.mp hg.1
    have hc : (τ (star g)).comp (τ g) = 1 := by
      rw [← hmul _ (hsub _ hs) _ (hsub _ hg), hgg, h1]
    have hv : τ (star g) (τ g v) = v := by
      rw [← ContinuousLinearMap.comp_apply, hc, ContinuousLinearMap.one_apply]
    have hi : ⟪τ g v, τ g v⟫_ℂ = ⟪v, v⟫_ℂ := by
      rw [hadj g (hsub g hg) v (τ g v), ← Matrix.star_eq_conjTranspose, hv]
    have h2 : ‖τ g v‖ ^ 2 = ‖v‖ ^ 2 := by
      rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ) v, hi]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2
  · intro v
    haveI := hfd
    let bs := stdOrthonormalBasis ℂ W
    have hco : ∀ u : W, ContinuousOn (fun g : Matrix (Fin n) (Fin n) ℂ => ⟪u, τ g v⟫_ℂ)
        (Formalism.REAL.Kset ε) :=
      fun u => (hdiff u v).continuousOn.mono (fun g hg => hsub g hg)
    have heq : (fun g => τ g v) = fun g => ∑ i, ⟪bs i, τ g v⟫_ℂ • bs i := by
      funext g; exact (bs.sum_repr' (τ g v)).symm
    rw [heq]
    exact continuousOn_finset_sum _ fun i _ => (hco (bs i)).smul continuousOn_const

theorem psBasic : PsBasic := by
  intro n ε lam W _ _ τ w _hlam htau
  have hrep : IsURepOn (Formalism.REAL.Kset ε) τ := htau.isURepOn
  obtain ⟨hfd, -, -, -, hirr, hw, -⟩ := htau
  haveI := hfd
  haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
  have hK : ∀ k : KG ε, toMK k ∈ Formalism.REAL.Kset ε := fun k => (mem_KG ε _).1 k.2
  have hinv : ∀ k : KG ε, (toMK k)⁻¹ = star (toMK k) := fun k =>
    Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.mp (hK k).1)
  have hτc : Continuous (fun k : KG ε => τ (toMK k) w) :=
    (hrep.2.2 w).comp_continuous (toMK_cont ε) hK
  have hPc : Continuous (fun k : KG ε => (innerSL ℂ (τ (toMK k) w)).smulRight (τ (toMK k) w)) := by
    have := (ContinuousLinearMap.smulRightL ℂ W W).continuous₂.comp₂ ((innerSL ℂ).continuous.comp hτc) hτc
    exact this
  refine ⟨isOpen_kConjNonzeroMinorsSet ε, fun x hx => posDef_mem_kConjNonzeroMinorsSet ε hx, ?_, ?_⟩
  · have hU := isOpen_kConjNonzeroMinorsSet ε
    have hmem : ∀ k : KG ε, ∀ z ∈ {z : Fin n → Fin n → ℂ | Matrix.of z ∈ U1 ε}, ∀ i : Fin n,
        leadMinor ((toMK k)⁻¹ * Matrix.of z * toMK k) (i.val + 1) i.isLt ≠ 0 :=
      fun k z hz i => hz (toMK k) (hK k) i
    have hcont : ContinuousOn (Function.uncurry fun (k : KG ε) (z : Fin n → Fin n → ℂ) =>
        Phi lam ((toMK k)⁻¹ * Matrix.of z * toMK k) •
          (innerSL ℂ (τ (toMK k) w)).smulRight (τ (toMK k) w))
        (Set.univ ×ˢ {z : Fin n → Fin n → ℂ | Matrix.of z ∈ U1 ε}) := by
      show ContinuousOn (fun q : KG ε × (Fin n → Fin n → ℂ) =>
        Phi lam ((toMK q.1)⁻¹ * Matrix.of q.2 * toMK q.1) •
          (innerSL ℂ (τ (toMK q.1) w)).smulRight (τ (toMK q.1) w)) _
      have hA : ContinuousOn (fun q : KG ε × (Fin n → Fin n → ℂ) =>
          Phi lam ((toMK q.1)⁻¹ * Matrix.of q.2 * toMK q.1))
          (Set.univ ×ˢ {z : Fin n → Fin n → ℂ | Matrix.of z ∈ U1 ε}) := by
        unfold Phi
        exact continuousOn_finset_prod _ fun i _ =>
          (continuous_leadMinor_conj ε (i.val + 1) i.isLt).continuousOn.zpow₀ _
            fun q hq => Or.inl (hmem q.1 q.2 hq.2 i)
      have hB : ContinuousOn (fun q : KG ε × (Fin n → Fin n → ℂ) =>
          (innerSL ℂ (τ (toMK q.1) w)).smulRight (τ (toMK q.1) w))
          (Set.univ ×ˢ {z : Fin n → Fin n → ℂ | Matrix.of z ∈ U1 ε}) :=
        (hPc.comp continuous_fst).continuousOn
      exact hA.smul hB
    have hdiff : ∀ k : KG ε, DifferentiableOn ℂ (fun z : Fin n → Fin n → ℂ =>
        Phi lam ((toMK k)⁻¹ * Matrix.of z * toMK k) •
          (innerSL ℂ (τ (toMK k) w)).smulRight (τ (toMK k) w))
        {z : Fin n → Fin n → ℂ | Matrix.of z ∈ U1 ε} := by
      intro k
      apply DifferentiableOn.smul_const
      unfold Phi
      have hg : ∀ i : Fin n, DifferentiableOn ℂ (fun z : Fin n → Fin n → ℂ =>
          leadMinor ((toMK k)⁻¹ * Matrix.of z * toMK k) (i.val + 1) i.isLt ^ (-(sInt lam i)))
          {z : Fin n → Fin n → ℂ | Matrix.of z ∈ U1 ε} := fun i =>
        ((differentiable_leadMinor_mul _ _ (i.val + 1) i.isLt).differentiableOn).zpow
          (Or.inl fun z hz => hmem k z hz i)
      have hprod : ∀ s : Finset (Fin n), DifferentiableOn ℂ (fun z : Fin n → Fin n → ℂ =>
          ∏ i ∈ s, leadMinor ((toMK k)⁻¹ * Matrix.of z * toMK k) (i.val + 1) i.isLt ^ (-(sInt lam i)))
          {z : Fin n → Fin n → ℂ | Matrix.of z ∈ U1 ε} := by
        intro s
        refine Finset.induction_on s ?_ ?_
        · simp only [Finset.prod_empty]
          exact differentiableOn_const _
        · intro a s ha ih
          simp only [Finset.prod_insert ha]
          exact (hg a).mul ih
      exact hprod Finset.univ
    have hint := (GlobalTheory.differentiableOn_integral_of_holomorphic_of_continuousOn (μ := muK ε) hU hcont hdiff).1
    unfold ps
    exact DifferentiableOn.congr (hint.const_smul (Module.finrank ℂ W : ℂ)) fun z _ => rfl
  · have hI : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : KG ε → E), Continuous f →
        Integrable f (muK ε) := fun f hf =>
      integrableOn_univ.mp (hf.continuousOn.integrableOn_compact isCompact_univ)
    have h1 : ∀ k : KG ε, Phi lam ((toMK k)⁻¹ * 1 * toMK k) = 1 := fun k => by
      rw [hinv, Matrix.mul_one, Matrix.mem_unitaryGroup_iff'.mp (hK k).1, Phi_at_one]
    unfold ps
    simp_rw [h1, one_smul]
    have hw0 : w ≠ 0 := by rintro rfl; simp at hw
    obtain ⟨c, -, hc⟩ := avgSchur n ε W τ w hfd hrep hirr hw0
    have hnorm : ∀ k : KG ε, ‖τ (toMK k) w‖ = 1 := fun k => by rw [hrep.2.1 _ (hK k), hw]
    let b := stdOrthonormalBasis ℂ W
    have hsum : (Module.finrank ℂ W : ℂ) * c = 1 := by
      have e1 : ∀ i, ∫ k : KG ε, ⟪τ (toMK k) w, b i⟫_ℂ * ⟪b i, τ (toMK k) w⟫_ℂ ∂(muK ε) = c := by
        intro i
        have hbi : ⟪b i, b i⟫_ℂ = 1 := by
          rw [inner_self_eq_norm_sq_to_K, b.orthonormal.1 i]; simp
        have := hc (b i) (innerSL ℂ (b i))
        simp only [show ∀ a b : W, (innerSL ℂ a) b = ⟪a, b⟫_ℂ from fun _ _ => rfl, hbi, mul_one] at this
        exact this
      have e2 : ∑ i, ∫ k : KG ε, ⟪τ (toMK k) w, b i⟫_ℂ * ⟪b i, τ (toMK k) w⟫_ℂ ∂(muK ε) = 1 := by
        rw [← integral_finset_sum _ fun i _ => hI (fun k : KG ε => ⟪τ (toMK k) w, b i⟫_ℂ * ⟪b i, τ (toMK k) w⟫_ℂ)
          ((hτc.inner continuous_const).mul (continuous_const.inner hτc))]
        simp_rw [b.sum_inner_mul_inner]
        have hone : ∀ k : KG ε, ⟪τ (toMK k) w, τ (toMK k) w⟫_ℂ = 1 := fun k => by
          rw [inner_self_eq_norm_sq_to_K, hnorm]; simp
        simp_rw [hone]
        simp
      simp_rw [e1] at e2
      simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using e2
    ext u
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.integral_apply (hI _ hPc),
      ContinuousLinearMap.id_apply]
    simp only [ContinuousLinearMap.smulRight_apply, show ∀ a b : W, (innerSL ℂ a) b = ⟪a, b⟫_ℂ from fun _ _ => rfl]
    apply ext_inner_left ℂ
    intro y
    rw [inner_smul_right, ← integral_inner (hI (fun k : KG ε => ⟪τ (toMK k) w, u⟫_ℂ • τ (toMK k) w)
      ((hτc.inner continuous_const).smul hτc))]
    simp_rw [inner_smul_right]
    have := hc u (innerSL ℂ y)
    simp only [show ∀ a b : W, (innerSL ℂ a) b = ⟪a, b⟫_ℂ from fun _ _ => rfl] at this
    rw [this, ← mul_assoc, hsum, one_mul]

end GlobalTheory.Dec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmallBallAsymptoticsPiWeighted
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory

theorem smallBall_pi_fin (n : ℕ) : ∀ (X : Fin n → Type) [∀ i, MeasurableSpace (X i)]
    (ν : ∀ i, Measure (X i)) [∀ i, IsFiniteMeasure (ν i)] (ρ : ∀ i, X i → ℝ) (d : Fin n → ℕ)
    (C : Fin n → ℝ), (∀ i, Measurable (ρ i)) → (∀ i x, 0 ≤ ρ i x) → (∀ i, 0 < C i) →
    (∀ i, Filter.Tendsto (fun r : ℝ => ν i {x | Real.sqrt (ρ i x) ≤ r} / ENNReal.ofReal (r ^ d i))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (ENNReal.ofReal (C i) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (d i))) 1)))) →
    Filter.Tendsto (fun r : ℝ => Measure.pi ν {x | Real.sqrt (∑ i, ρ i (x i)) ≤ r} /
        ENNReal.ofReal (r ^ ∑ i, d i)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (ENNReal.ofReal (∏ i, C i) *
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (∑ i, d i))) 1))) := by
  induction n with
  | zero =>
    intro X _ ν _ ρ d C _ _ _ _
    have hball : ∀ m : ℕ, m = 0 →
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin m)) 1) = 1 := by
      rintro m rfl
      rw [volume_euclideanSpace_eq_dirac]
      exact Measure.dirac_apply_of_mem (Metric.mem_ball_self one_pos)
    rw [hball _ (Fin.sum_univ_zero d), Fin.prod_univ_zero, ENNReal.ofReal_one, mul_one]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr' : (0 : ℝ) ≤ r := le_of_lt hr
    have hset : {x : ∀ i : Fin 0, X i | Real.sqrt (∑ i, ρ i (x i)) ≤ r} = Set.univ := by
      ext x
      simp [hr']
    rw [hset, Measure.pi_univ]
    simp
  | succ n ih =>
    intro X _ ν _ ρ d C hρm hρ0 hC h
    have hmp := measurePreserving_piFinSuccAbove ν 0
    have h2 := ih (fun j => X (Fin.succAbove 0 j)) (fun j => ν (Fin.succAbove 0 j))
      (fun j => ρ (Fin.succAbove 0 j)) (fun j => d (Fin.succAbove 0 j))
      (fun j => C (Fin.succAbove 0 j)) (fun j => hρm _) (fun j => hρ0 _) (fun j => hC _)
      (fun j => h _)
    have hmeas2 : Measurable fun y : (∀ j : Fin n, X (Fin.succAbove 0 j)) =>
        ∑ j, ρ (Fin.succAbove 0 j) (y j) :=
      Finset.measurable_sum _ fun j _ => (hρm _).comp (measurable_pi_apply j)
    have key := GlobalTheory.T.tendsto_prod_smallBall_asymptotics (X 0) (∀ j : Fin n, X (Fin.succAbove 0 j)) (ν 0)
      (Measure.pi fun j => ν (Fin.succAbove 0 j)) (ρ 0)
      (fun y => ∑ j, ρ (Fin.succAbove 0 j) (y j)) (d 0) (∑ j, d (Fin.succAbove 0 j))
      (C 0) (∏ j, C (Fin.succAbove 0 j)) (hρm 0) hmeas2 (hρ0 0)
      (fun y => Finset.sum_nonneg fun j _ => hρ0 _ _) (hC 0)
      (Finset.prod_pos fun j _ => hC _) (h 0) h2
    have hsumd : d 0 + ∑ j, d (Fin.succAbove 0 j) = ∑ i, d i :=
      (Fin.sum_univ_succAbove d 0).symm
    have hprodC : C 0 * ∏ j, C (Fin.succAbove 0 j) = ∏ i, C i :=
      (Fin.prod_univ_succAbove C 0).symm
    rw [hsumd, hprodC] at key
    refine key.congr' (Filter.Eventually.of_forall fun r => ?_)
    congr 1
    rw [← hmp.measure_preimage_equiv]
    congr 1
    ext x
    change Real.sqrt (ρ 0 (x 0) + ∑ j, ρ (Fin.succAbove 0 j) (x (Fin.succAbove 0 j))) ≤ r ↔
      Real.sqrt (∑ i, ρ i (x i)) ≤ r
    rw [Fin.sum_univ_succAbove (fun i => ρ i (x i)) 0]

theorem smallBall_weight {X : Type} [MeasurableSpace X] (ν : Measure X) (ρ : X → ℝ) (d : ℕ)
    (w : ℝ) (hw : 0 < w) (V : ENNReal)
    (h : Filter.Tendsto (fun r : ℝ => ν {x | Real.sqrt (ρ x) ≤ r} / ENNReal.ofReal (r ^ d))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds V)) :
    Filter.Tendsto (fun r : ℝ => ν {x | Real.sqrt (w * ρ x) ≤ r} / ENNReal.ofReal (r ^ d))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (ENNReal.ofReal (w ^ (-((d : ℝ) / 2))) * V)) := by
  have hs : 0 < Real.sqrt w := Real.sqrt_pos.2 hw
  have hmap : Filter.Tendsto (fun r : ℝ => r / Real.sqrt w) (nhdsWithin 0 (Set.Ioi 0))
      (nhdsWithin 0 (Set.Ioi 0)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h0 : Filter.Tendsto (fun r : ℝ => r / Real.sqrt w) (nhds 0)
          (nhds (0 / Real.sqrt w)) := (continuous_id.div_const _).tendsto 0
      rw [zero_div] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact div_pos hr hs
  have key := ENNReal.Tendsto.mul_const (h.comp hmap)
    (b := ENNReal.ofReal (w ^ (-((d : ℝ) / 2)))) (Or.inr ENNReal.ofReal_ne_top)
  rw [mul_comm]
  refine key.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr' : (0 : ℝ) < r := hr
  have hrs : 0 < r / Real.sqrt w := div_pos hr' hs
  have hset : {x | Real.sqrt (w * ρ x) ≤ r} = {x | Real.sqrt (ρ x) ≤ r / Real.sqrt w} := by
    ext x
    simp only [Set.mem_ofPred_eq, Real.sqrt_mul hw.le, le_div_iff₀' hs]
  have hc : w ^ (-((d : ℝ) / 2)) = (Real.sqrt w ^ d)⁻¹ := by
    rw [Real.rpow_neg hw.le, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hw.le]
    congr 2
    ring
  have hrd : r ^ d = (r / Real.sqrt w) ^ d * Real.sqrt w ^ d := by
    rw [div_pow, div_mul_cancel₀]
    exact pow_ne_zero _ hs.ne'
  have ha0 : ENNReal.ofReal ((r / Real.sqrt w) ^ d) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact pow_pos hrs d
  simp only [Function.comp_apply]
  rw [hset, hc, hrd, ENNReal.ofReal_mul (pow_nonneg hrs.le d),
    ENNReal.ofReal_inv_of_pos (pow_pos hs d)]
  simp only [ENNReal.div_eq_inv_mul]
  rw [ENNReal.mul_inv (Or.inl ha0) (Or.inl ENNReal.ofReal_ne_top)]
  ring

theorem smallBall_pi_weight : ∀ (ι : Type) [Fintype ι] (X : ι → Type) [∀ i, MeasurableSpace (X i)] (ν : ∀ i, Measure (X i)) [∀ i, IsFiniteMeasure (ν i)] (ρ : ∀ i, X i → ℝ) (d : ι → ℕ) (w : ι → ℝ), (∀ i, Measurable (ρ i)) → (∀ i x, 0 ≤ ρ i x) → (∀ i, 0 < w i) → (∀ i, Filter.Tendsto (fun r : ℝ => ν i {x | Real.sqrt (ρ i x) ≤ r} / ENNReal.ofReal (r ^ d i)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (d i))) 1)))) → Filter.Tendsto (fun r : ℝ => Measure.pi ν {x | Real.sqrt (∑ i, w i * ρ i (x i)) ≤ r} / ENNReal.ofReal (r ^ ∑ i, d i)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (ENNReal.ofReal (∏ i, w i ^ (-((d i : ℝ) / 2))) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (∑ i, d i))) 1))) := by
  intro ι _ X _ ν _ ρ d w hρm hρ0 hw h
  have hw' : ∀ i, Filter.Tendsto
      (fun r : ℝ => ν i {x | Real.sqrt (w i * ρ i x) ≤ r} / ENNReal.ofReal (r ^ d i))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (ENNReal.ofReal (w i ^ (-((d i : ℝ) / 2))) *
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (d i))) 1))) :=
    fun i => smallBall_weight (ν i) (ρ i) (d i) (w i) (hw i) _ (h i)
  let f : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have key := smallBall_pi_fin (Fintype.card ι) (fun j => X (f j)) (fun j => ν (f j))
    (fun j x => w (f j) * ρ (f j) x) (fun j => d (f j))
    (fun j => w (f j) ^ (-((d (f j) : ℝ) / 2))) (fun j => (hρm _).const_mul _)
    (fun j x => mul_nonneg (hw _).le (hρ0 _ x)) (fun j => Real.rpow_pos_of_pos (hw _) _)
    (fun j => hw' _)
  have hS : ∑ j, d (f j) = ∑ i, d i := Equiv.sum_comp f d
  have hP : ∏ j, w (f j) ^ (-((d (f j) : ℝ) / 2)) = ∏ i, w i ^ (-((d i : ℝ) / 2)) :=
    Equiv.prod_comp f (fun i => w i ^ (-((d i : ℝ) / 2)))
  rw [hS, hP] at key
  have hmp := measurePreserving_piCongrLeft ν f
  refine key.congr' (Filter.Eventually.of_forall fun r => ?_)
  congr 1
  rw [← hmp.measure_preimage_equiv]
  congr 1
  ext g
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  have hsum : ∑ i, w i * ρ i (MeasurableEquiv.piCongrLeft X f g i) =
      ∑ j, w (f j) * ρ (f j) (g j) := by
    rw [← Equiv.sum_comp f (fun i => w i * ρ i (MeasurableEquiv.piCongrLeft X f g i))]
    simp only [MeasurableEquiv.piCongrLeft_apply_apply]
  rw [hsum]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoBallMeanBigCellWeightStatement
section
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_ball_mean_bigCellWeight : ∀ (k r : ℕ), Tendsto (fun ρ : ℝ => (∫⁻ x in Metric.ball (fun _ => 1 : Fin r → ℂ) ρ, ENNReal.ofReal (Formalism.FourierDecayAlt.B2.cWeight k r x)) / volume (Metric.ball (0 : Fin r → ℂ) ρ)) (𝓝[>] 0) (𝓝 1) := by
  first | exact @GlobalTheory.CellDens.tendsto_mean_cWeight | exact GlobalTheory.CellDens.tendsto_mean_cWeight | (intros; apply GlobalTheory.CellDens.tendsto_mean_cWeight <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoVolumeSublevelDivPow
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory

theorem volume_sum_sq_le_sq (d : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    volume {x : Fin d → ℝ | ∑ i, x i ^ 2 ≤ s ^ 2}
      = ENNReal.ofReal (s ^ d) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) := by
  have h1 : {x : Fin d → ℝ | ∑ i, x i ^ 2 ≤ s ^ 2}
      = (WithLp.toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d)) ⁻¹' Metric.closedBall 0 s := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, mem_closedBall_zero_iff,
      EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs]
    rw [Real.sqrt_le_left hs]
  rw [h1, (PiLp.volume_preserving_toLp (Fin d)).measure_preimage
    measurableSet_closedBall.nullMeasurableSet, Measure.addHaar_closedBall _ _ hs]
  simp

theorem tendsto_volume_sublevel_div_pow (d : ℕ) (N : (Fin d → ℝ) → ℝ) (hc : ContinuousAt N 0)
    (h0 : N 0 = 0) (hl : ∀ x, ∑ i, x i ^ 2 ≤ N x) (hu : ∀ x, N x ≤ ∑ i, x i ^ 2 + N x ^ 2 / 4) :
    Filter.Tendsto (fun r : ℝ => volume {x : Fin d → ℝ | Real.sqrt (N x) ≤ r} /
        ENNReal.ofReal (r ^ d)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1))) := by
  set V := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) with hV
  have hVt : V ≠ ⊤ := measure_ball_lt_top.ne
  rw [tendsto_order]
  constructor
  · intro a ha
    have hcont : Filter.Tendsto (fun t : ℝ => ENNReal.ofReal (t ^ d) * V) (nhds 1) (nhds V) := by
      have h1 : Filter.Tendsto (fun t : ℝ => ENNReal.ofReal (t ^ d)) (nhds 1) (nhds 1) := by
        have : Continuous (fun t : ℝ => ENNReal.ofReal (t ^ d)) :=
          ENNReal.continuous_ofReal.comp (continuous_pow d)
        simpa using this.tendsto 1
      simpa using ENNReal.Tendsto.mul_const h1 (Or.inr hVt)
    have hev : ∀ᶠ t : ℝ in nhdsWithin 1 (Set.Iio 1), a < ENNReal.ofReal (t ^ d) * V ∧ 0 < t :=
      nhdsWithin_le_nhds ((hcont.eventually (lt_mem_nhds ha)).and (lt_mem_nhds one_pos))
    obtain ⟨t, ⟨hta, ht0⟩, ht1⟩ := (hev.and self_mem_nhdsWithin).exists
    have ht1 : t < 1 := ht1
    have hδ : 0 < 4 * (1 - t ^ 2) := by nlinarith
    have hN : ∀ᶠ x in nhds (0 : Fin d → ℝ), N x < 4 * (1 - t ^ 2) :=
      hc.eventually (gt_mem_nhds (by rw [h0]; exact hδ))
    obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.1 hN
    have hr : ∀ᶠ r : ℝ in nhdsWithin 0 (Set.Ioi 0), r < η :=
      nhdsWithin_le_nhds (gt_mem_nhds hη)
    filter_upwards [hr, self_mem_nhdsWithin] with r hrη hr0
    have hr0 : 0 < r := hr0
    refine hta.trans_le ?_
    have hp : ENNReal.ofReal (r ^ d) ≠ 0 := by
      simpa using pow_pos hr0 d
    rw [ENNReal.le_div_iff_mul_le (Or.inl hp) (Or.inl ENNReal.ofReal_ne_top)]
    have e : ENNReal.ofReal (t ^ d) * V * ENNReal.ofReal (r ^ d)
        = volume {x : Fin d → ℝ | ∑ i, x i ^ 2 ≤ (t * r) ^ 2} := by
      rw [volume_sum_sq_le_sq d (by positivity), mul_pow,
        ENNReal.ofReal_mul (by positivity), ← hV]
      ring
    rw [e]
    refine measure_mono fun x hx => ?_
    simp only [Set.mem_setOf_eq] at hx ⊢
    have htr : t * r < η := by nlinarith
    have hx' : dist x 0 < η := by
      rw [dist_zero_right]
      refine lt_of_le_of_lt ?_ htr
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
      have : x i ^ 2 ≤ (t * r) ^ 2 :=
        (Finset.single_le_sum (f := fun i => x i ^ 2) (fun _ _ => sq_nonneg _)
          (Finset.mem_univ i)).trans hx
      exact abs_le_of_sq_le_sq this (by positivity)
    have h1 := hball hx'
    have h2 := hu x
    have h3 : 0 ≤ N x := (Finset.sum_nonneg fun _ _ => sq_nonneg _).trans (hl x)
    rw [Real.sqrt_le_left hr0.le]
    have h4 : t ^ 2 * N x ≤ t ^ 2 * r ^ 2 := by
      have := mul_le_mul_of_nonneg_left h1.le h3
      nlinarith
    exact le_of_mul_le_mul_left h4 (by positivity)
  · intro a ha
    filter_upwards [self_mem_nhdsWithin] with r hr0
    have hr0 : 0 < r := hr0
    refine lt_of_le_of_lt ?_ ha
    refine ENNReal.div_le_of_le_mul ?_
    rw [mul_comm, ← volume_sum_sq_le_sq d hr0.le]
    refine measure_mono fun x hx => ?_
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [Real.sqrt_le_left hr0.le] at hx
    exact (hl x).trans hx

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TwoFlagsGramNumberNormalFormEqGramProjectionStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twoFlagsGramNumber_normalForm_eq_gram_projection : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (g₀ : Mat k r) (β : Fin r → ℕ), 2 ≤ k → TwoFl k r z z' g₀ → IsNormal k r β g₀ → ∀ m ∈ UH (Hb k), ∃ P₀ : Submodule ℂ (EuclideanSpace ℂ (Fin (k + 1))), (Module.finrank ℂ P₀ = k - 2 ∨ Module.finrank ℂ P₀ = k - 1) ∧ ∀ (u : UT r → ℂ) (q : PPar k r) (a : Fin r → ℝ), (∀ b, 0 < a b) → Yv k r z z' g₀ (uEmb k r (upper u) * pOf k r q * uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m) = gramProj P₀ fun b => m⁻¹ *ᵥ q.1 b := by
  first | exact @GlobalTheory.Amp.NormGram.Yv_normal | exact GlobalTheory.Amp.NormGram.Yv_normal | (intros; apply GlobalTheory.Amp.NormGram.Yv_normal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnimodularBesselSubgroupsUWNStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unimodular_besselSubgroups_UW_N : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z → ∀ μ : Measure (Mt k r), (IsHaarOn (Sset k r z) μ → IsUnimod (Sset k r z) μ) ∧ (IsHaarOn (Nset k r) μ → IsUnimod (Nset k r) μ ∧ ∀ h ∈ UWset k r z, μ.map (conjM h) = μ) ∧ (IsHaarOn (UWset k r z) μ → IsUnimod (UWset k r z) μ ∧ μ Set.univ < ⊤) := by
  first | exact @GlobalTheory.SgInf.unimodular_S_N_UW | exact GlobalTheory.SgInf.unimodular_S_N_UW | (intros; apply GlobalTheory.SgInf.unimodular_S_N_UW <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentLeviRadicalCoordsHomeomorphStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_levi_radical_coords_homeomorph : ∀ k r : ℕ, Set.BijOn (fun q : (UT r → ℂ) × PPar k r => uEmb k r (upper q.1) * pOf k r q.2) Set.univ (Nset k r) ∧ Continuous (fun q : (UT r → ℂ) × PPar k r => uEmb k r (upper q.1) * pOf k r q.2) ∧ ∃ c : Mat k r → (UT r → ℂ) × PPar k r, Continuous c ∧ ∀ q : (UT r → ℂ) × PPar k r, c (uEmb k r (upper q.1) * pOf k r q.2) = q := by
  first | exact @GlobalTheory.Amp.NCoord.coord_homeo | exact GlobalTheory.Amp.NCoord.coord_homeo | (intros; apply GlobalTheory.Amp.NCoord.coord_homeo <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentRadicalVolumeGrowthStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotentRadical_volume_growth : ∀ (n : ℕ) (ε : Fin n → Bool) (W : Submodule ℂ (Fin n → ℂ)) (ν : Measure (UJ ε)), IsIsoC ε W → IsHaarSub (NW ε W) ν → (∃ C : ℝ, ∀ r : ℝ, 0 ≤ r → ν {m | dOp (umat m) ≤ r} ≤ ENNReal.ofReal (C * Real.exp (4 * n * rkR ε * r))) ∧ ∀ b : ℝ, 4 * n * rkR ε < b → Integrable (fun m : UJ ε => Real.exp (-(b * dOp (umat m)))) ν := by
  first | exact @GlobalTheory.RadVol.radical_volume_growth | exact GlobalTheory.RadVol.radical_volume_growth | (intros; apply GlobalTheory.RadVol.radical_volume_growth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryGroupStructuresPermConjInvariantStatement
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryGroup_structures_perm_conj_invariant : ∀ (n : ℕ) (ε : Fin n → Bool) (s : Equiv.Perm (Fin n)), (∀ g : Matrix (Fin n) (Fin n) ℂ, (g ∈ UJset (ε ∘ s) ↔ g.submatrix s.symm s.symm ∈ UJset ε) ∧ (g ∈ Kset (ε ∘ s) ↔ g.submatrix s.symm s.symm ∈ Kset ε) ∧ (inP (ε ∘ s) g ↔ inP ε (g.submatrix s.symm s.symm)) ∧ NormedSpace.exp (g.submatrix s.symm s.symm) = (NormedSpace.exp g).submatrix s.symm s.symm) ∧ ∀ (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (p : ENNReal), (MemLp (fun g : UJ ε => f (umat g)) p (muG ε) ↔ MemLp (fun g : UJ (ε ∘ s) => f ((umat g).submatrix s.symm s.symm)) p (muG (ε ∘ s))) ∧ (MemLp (fun g : UJ ε => f (umat g)) p (muG ε) ↔ MemLp (fun g : UJ ε => f ((umat g).map star)) p (muG ε)) := by
  first | exact @GlobalTheory.Dec.PermGroup.permGroup | exact GlobalTheory.Dec.PermGroup.permGroup | (intros; apply GlobalTheory.Dec.PermGroup.permGroup <;> assumption)
end

