import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0086
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0109
import Formalism.LocalRingCardinality.DataCD
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0019
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MeasurePreservingGlue
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0016
import Formalism.SharpRestriction.InertJacobiLevels.Bundle0007
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0074
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0082
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0097
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0107
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0095
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0099
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0096
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0088
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0055
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0110
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NegOneZpowRound
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

noncomputable section

namespace GlobalTheory.MomT.Move

theorem finsum_eq_sum_reps {G V : Type} [AddCommGroup G] [AddCommGroup V] (φ : G →+ V) (M M' : AddSubgroup G)
    (Λ₁ Λ₂ : AddSubgroup V) (h₁ : ∀ y, φ y ∈ Λ₁ ↔ y ∈ M) (h₂ : ∀ v, v ∈ Λ₂ ↔ ∃ y ∈ M', φ y = v) (R : Finset G)
    (hR : IsReps M M' R) (F : V → ℂ) (hF : ∀ x ∈ Λ₂, ∀ l ∈ Λ₂, l ∈ Λ₁ → F (x + l) = F x) :
    (Λ₁.addSubgroupOf Λ₂).index = R.card ∧
      ∑ᶠ q : Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂, F ((Quotient.out q : Λ₂) : V) = ∑ y ∈ R, F (φ y) := by
  classical
  let f : R → Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂ := fun y => QuotientAddGroup.mk ⟨φ y, (h₂ _).2 ⟨y, hR.1 y y.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      have := QuotientAddGroup.eq.1 hxy
      rw [AddSubgroup.mem_addSubgroupOf] at this
      have h3 : φ (y.1 - x.1) ∈ Λ₁ := by simpa [map_sub, neg_add_eq_sub] using this
      exact Subtype.ext (hR.2.1 _ y.2 _ x.2 ((h₁ _).1 h3)).symm
    · intro q
      obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective q
      obtain ⟨y, hy, hv⟩ := (h₂ _).1 v.2
      obtain ⟨x, hx, hxy⟩ := hR.2.2 y hy
      refine ⟨⟨x, hx⟩, QuotientAddGroup.eq.2 ?_⟩
      rw [AddSubgroup.mem_addSubgroupOf]
      have := (h₁ _).2 hxy
      simpa [map_sub, neg_add_eq_sub, hv] using this
  let e := Equiv.ofBijective f hf
  refine ⟨?_, ?_⟩
  · rw [AddSubgroup.index, ← Nat.card_congr e]; simp
  · rw [← finsum_comp_equiv e, finsum_eq_sum_of_fintype, ← Finset.sum_coe_sort R]
    refine Finset.sum_congr rfl fun y _ => ?_
    have hq : (QuotientAddGroup.mk ⟨φ y, (h₂ _).2 ⟨y, hR.1 y y.2, rfl⟩⟩ : Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) =
        QuotientAddGroup.mk (Quotient.out (e y)) := (QuotientAddGroup.out_eq' (e y)).symm
    have h3 := QuotientAddGroup.eq.1 hq
    rw [AddSubgroup.mem_addSubgroupOf] at h3
    have := hF _ ((h₂ _).2 ⟨y, hR.1 y y.2, rfl⟩) _ (Subtype.property _) h3
    rw [← this]
    congr 1
    simp

theorem op_add {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (hH : IsHerm H) (α : V → ℂ) (Λ : AddSubgroup V)
    (hs : IsSelfDual H Λ) (hα : IsSemiChar H Λ α) (F : V → ℂ) (x l : V) (hx : x ∈ Λ) (hl : l ∈ Λ)
    (hF : ∀ z, α l * opU H l F z = F z) (z : V) : α (x + l) * opU H (x + l) F z = α x * opU H x F z := by
  have hx' : x ∈ dualLat H Λ := by rw [hs]; exact hx
  obtain ⟨m, hm⟩ := hx' l hl
  have h1 := hF (z + x)
  have h2 : H l x = H x l - 2 * Complex.I * m := by
    rw [hH x l]
    apply Complex.ext
    · simp
    · simp only [altE] at hm
      simp [hm]; ring
  rw [hα.2 x hx l hl, hm]
  simp only [opU] at h1 ⊢
  rw [← h1, ← add_assoc]
  have h3 : Complex.exp ((Real.pi : ℂ) * Complex.I * ((m : ℝ) : ℂ)) *
      Complex.exp (-(Real.pi : ℂ) * H z (x + l) - (Real.pi : ℂ) * H (x + l) (x + l) / 2) =
      Complex.exp (-(Real.pi : ℂ) * H (z + x) l - (Real.pi : ℂ) * H l l / 2) *
        Complex.exp (-(Real.pi : ℂ) * H z x - (Real.pi : ℂ) * H x x / 2) := by
    rw [← Complex.exp_add, ← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]
    refine ⟨m, ?_⟩
    simp only [map_add, LinearMap.add_apply, h2]
    push_cast
    ring
  linear_combination (α x * α l * F (z + x + l)) * h3

theorem neg_one_zpow_round (q : ℝ)
    (h : Complex.exp ((Real.pi : ℂ) * Complex.I * (q : ℂ)) = 1 ∨ Complex.exp ((Real.pi : ℂ) * Complex.I * (q : ℂ)) = -1) :
    (-1 : ℂ) ^ (round q) = Complex.exp ((Real.pi : ℂ) * Complex.I * (q : ℂ)) := by
  have h2 : Complex.exp (2 * ((Real.pi : ℂ) * Complex.I * (q : ℂ))) = 1 := by
    rw [two_mul, Complex.exp_add]
    rcases h with h | h <;> simp [h]
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h2
  have hq : (q : ℂ) = n := by
    have h0 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := Complex.two_pi_I_ne_zero
    apply mul_left_cancel₀ h0
    linear_combination hn
  have hq' : q = n := by exact_mod_cast hq
  rw [hq, hq', round_intCast, mul_comm, Complex.exp_int_mul, Complex.exp_pi_mul_I]

theorem isHerm_HV {ι : Type} [Fintype ι] {a b : ℕ} (sc : ℝ) : IsHerm (HV (ι := ι) (a := a) (b := b) sc) := by
  intro x y
  simp [Formalism.L2.Ker.HV, map_sum, mul_comm]

theorem embH_inj {E : Type} [Field E] [NumberField E] [StarRing E] {ι : Type} [Fintype ι] [Nonempty ι] {a b : ℕ}
    (emb : ι → E →+* ℂ) {δ : ℂ} (hδ : δ ≠ 0) : Function.Injective (embH (a := a) (b := b) emb δ) := by
  intro x y h
  obtain ⟨τ⟩ := ‹Nonempty ι›
  refine (Pi.basisFun E (Fin a)).ext fun j => funext fun i => ?_
  have := congrFun (congrFun (congrFun h τ) i) j
  simp only [embH, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
  simpa using (emb τ).injective (mul_left_cancel₀ hδ this)

theorem move : ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (a b : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (N'' : Submodule (𝓞 X.E) (Sp X.E b)), X.Ok → s.Ok → B.EqP χ → Even a → Even b → (ambOf s B χ cD).LaHyp a b ∅ → IsSdLat N → IsSdLat N' → IsSdLat N'' → ∀ R : Finset (HomE X.E a b), IsReps (per (ambOf s B χ cD) N N').toAddSubgroup (per (ambOf s B χ cD) N N'').toAddSubgroup R → ∀ z, (ambOf s B χ cD).e a b N N'' z = χ (TaylorLogMetric.detId D (s.lat N') (s.lat N'')) ^ (-((a / 2 : ℕ) : ℤ)) * (((Real.sqrt (R.card : ℝ) : ℝ) : ℂ)⁻¹ * ∑ y ∈ R, Wx (ambOf s B χ cD) y ((ambOf s B χ cD).e a b N N') z) := by
  intro D X s cc δ B χ cD a b N N' N'' _ hs hE ha hb hL hN hN' hN'' R hR z
  obtain ⟨hδ, hτ, -, -, -, hL⟩ := hL
  obtain ⟨t1, t2, t3, -⟩ := GlobalTheory.T.fieldIso_lattices_form_taylor_correspond D X s cc δ B χ cD a b hs
  set A := ambOf s B χ cD with hA
  letI := D.host.cmStar
  have key := congrFun (hE.2.1 a b ⟨s.lat N, (t2 N N' ha hb hN hN').2.2.1⟩ ⟨s.lat N', (t2 N N' ha hb hN hN').2.2.2⟩
    ⟨s.lat N'', (t2 N N'' ha hb hN hN'').2.2.2⟩ ha hb) fun τ => z (s.iT.symm τ)
  refine key.trans (congrArg₂ (· * ·) rfl ?_)
  let φ : HomE X.E a b →+ TaylorLogMetric.VC D a b :=
    { toFun := fun y τ => emb A y (s.iT.symm τ)
      map_zero' := by funext τ; simp [emb]
      map_add' := fun x y => by funext τ; simp [emb] }
  have hφ : ∀ y, (fun τ => φ y (s.iT τ)) = emb A y := fun y => by funext τ; simp [φ]
  have hmem : ∀ (M : Submodule (𝓞 X.E) (Sp X.E b)) v, v ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (s.lat N) (s.lat M) ↔
      ∃ y ∈ (per A N M).toAddSubgroup, φ y = v := by
    intro M v
    rw [t1]
    refine exists_congr fun y => and_congr Iff.rfl ⟨fun h => ?_, fun h => ?_⟩
    · funext τ
      have := congrFun h (s.iT.symm τ)
      simp only [Equiv.apply_symm_apply] at this
      exact this
    · rw [← h, hφ]; rfl
  have h₁ : ∀ y, φ y ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (s.lat N) (s.lat N') ↔ y ∈ (per A N N').toAddSubgroup := by
    intro y
    rw [hmem]
    refine ⟨fun ⟨x, hx, h⟩ => ?_, fun h => ⟨y, h, rfl⟩⟩
    have h' : emb A x = emb A y := by rw [← hφ, ← hφ, h]
    exact embH_inj _ hδ h' ▸ hx
  have hW : ∀ v ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (s.lat N) (s.lat N''),
      TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) v * TaylorLogMetric.U D (TaylorLogMetric.tor0 D cc δ) v (B.eNat χ a b (s.lat N) (s.lat N'))
        (fun τ => z (s.iT.symm τ)) =
      alV A.d A.sc (fun τ => v (s.iT τ)) * opU (HV A.sc) (fun τ => v (s.iT τ)) (A.e a b N N') z := by
    intro v hv
    refine congrArg₂ (· * ·) ?_ ?_
    · have h := (hL N N'' hN hN'').2.2.1 _ ((t1 N N'' v).1 hv)
      unfold TaylorLogMetric.al
      rw [t3]
      exact neg_one_zpow_round _ h
    · unfold TaylorLogMetric.U opU
      rw [t3, t3]
      simp only [Equiv.symm_apply_apply]
      refine congrArg₂ (· * ·) ?_ rfl
      refine congrArg (B.eNat χ a b (s.lat N) (s.lat N')) ?_
      funext τ
      simp
  obtain ⟨e1, e2⟩ := finsum_eq_sum_reps φ _ _ _ _ h₁ (hmem N'') R hR
    (fun v => TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) v * TaylorLogMetric.U D (TaylorLogMetric.tor0 D cc δ) v (B.eNat χ a b (s.lat N) (s.lat N'))
        (fun τ => z (s.iT.symm τ))) (by
      intro x hx l hl hl'
      rw [hW _ (add_mem hx hl), hW _ hx]
      exact op_add _ (isHerm_HV _) _ _ (hL N N'' hN hN'').2.1 (hL N N'' hN hN'').2.2 _ _ _ ((t1 N N'' x).1 hx)
        ((t1 N N'' l).1 hl) ((hL N N' hN hN').1 _ ((t1 N N' l).1 hl')) z)
  unfold TaylorLogMetric.Iop
  refine congrArg₂ (· * ·) ?_ (e2.trans (Finset.sum_congr rfl fun y hy => ?_))
  · rw [← e1]
  · rw [hW _ ((hmem N'' _).2 ⟨y, hR.1 y hy, rfl⟩), hφ]
    rfl

end GlobalTheory.MomT.Move
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PositiveDefiniteUnitSphereMassProof
section
open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot
open scoped ENNReal NNReal

namespace GlobalTheory.SphereMassProof

theorem qf_pos_eq (M : ℕ) (x : Sp M 0) : qf x = ∑ i, ‖x i‖ ^ 2 := by
  simp [qf, Fintype.sum_sum_type, Complex.normSq_eq_norm_sq]

theorem dx_ball (M : ℕ) (hM : 1 ≤ M) (b : ℝ) (hb : 0 ≤ b) :
    dx M 0 {x | qf x ≤ b} = ENNReal.ofReal ((2 * Real.pi) ^ M / (M.factorial : ℝ) * b ^ M) := by
  haveI : Nonempty (Fin M ⊕ Fin 0) := ⟨Sum.inl ⟨0, hM⟩⟩
  have h := Complex.volume_sum_rpow_le (Fin M ⊕ Fin 0) (p := 2) (by norm_num) (Real.sqrt b)
  have e : {x : Sp M 0 | qf x ≤ b} =
      {x : Fin M ⊕ Fin 0 → ℂ | (∑ i, ‖x i‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) ≤ Real.sqrt b} := by
    ext x
    simp only [Set.mem_setOf_eq, ← Real.sqrt_eq_rpow, Real.rpow_two, qf_pos_eq]
    exact (Real.sqrt_le_sqrt_iff hb).symm
  have hc : Fintype.card (Fin M ⊕ Fin 0) = M := by simp
  rw [dx, Measure.smul_apply, e, h, hc, smul_eq_mul]
  have g1 : Real.Gamma (2 / 2 + 1) = 1 := by
    rw [show (2 / 2 + 1 : ℝ) = 2 by norm_num, Real.Gamma_two]
  have g2 : Real.Gamma (2 * (M : ℝ) / 2 + 1) = M.factorial := by
    rw [show (2 * (M : ℝ) / 2 + 1) = M + 1 by ring, Real.Gamma_nat_eq_factorial]
  rw [g1, g2, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), pow_mul, Real.sq_sqrt hb,
    ← ENNReal.ofReal_mul (by positivity), show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
    ← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [mul_pow, add_zero]
  ring

theorem isCompact_shell (M : ℕ) : IsCompact {x : Sp M 0 | qf x ∈ Set.Icc (1 / 2 : ℝ) 2} := by
  refine Metric.isCompact_of_isClosed_isBounded
    (isClosed_Icc.preimage GlobalTheory.RealPlaceCompare.continuous_qf) ?_
  refine (Metric.isBounded_closedBall (x := (0 : Sp M 0)) (r := 2)).subset fun x hx => ?_
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by norm_num)]
  intro i
  have h1 : ‖x i‖ ^ 2 ≤ ∑ j, ‖x j‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => ‖x j‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have h2 : qf x ≤ 2 := hx.2
  rw [qf_pos_eq] at h2
  nlinarith [norm_nonneg (x i)]

theorem exists_mass {M : ℕ} {fib : ℝ → Measure (Sp M 0)} (h : IsDxDq fib) :
    ∃ G : ℝ → ℝ, Continuous G ∧ (∀ t, 0 ≤ G t) ∧
      ∀ t ∈ Set.Icc (1 / 2 : ℝ) 2, fib t Set.univ = ENNReal.ofReal (G t) := by
  obtain ⟨χ, h1, hc, hs, h01⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen
    (isCompact_shell M) (isOpen_ne (x := (0 : Sp M 0))) (by
      rintro x hx rfl
      have : (1 / 2 : ℝ) ≤ qf (0 : Sp M 0) := hx.1
      rw [qf_pos_eq] at this
      norm_num at this)
  obtain ⟨hi, hg⟩ := h.2.2 χ χ.continuous hc hs
  refine ⟨fun t => ∫ v, χ v ∂(fib t), continuousOn_univ.1 hg,
    fun t => integral_nonneg fun v => (h01 v).1, fun t ht => ?_⟩
  rw [ofReal_integral_eq_lintegral_ofReal (hi t trivial)
    (Filter.Eventually.of_forall fun v => (h01 v).1), ← lintegral_one]
  apply lintegral_congr_ae
  filter_upwards [GlobalTheory.RealPlaceCompare.ae_qf h t] with v hv
  have : χ v = 1 := h1 (show qf v ∈ Set.Icc (1 / 2 : ℝ) 2 from hv ▸ ht)
  simp [this]

theorem dx_shell {M : ℕ} {fib : ℝ → Measure (Sp M 0)} (h : IsDxDq fib) (a b : ℝ) (ha : 0 ≤ a) :
    dx M 0 (qf ⁻¹' Set.Ioc a b) = ∫⁻ t in Set.Ioc a b, fib t Set.univ := by
  have hq : Measurable (qf : Sp M 0 → ℝ) := GlobalTheory.RealPlaceCompare.continuous_qf.measurable
  have hO : MeasurableSet {x : Sp M 0 | x ≠ 0} := isOpen_ne.measurableSet
  have key := GlobalTheory.IsFibreFamily_lintegral_preimage hq isOpen_ne subset_rfl h
    (({x : Sp M 0 | x ≠ 0}).indicator 1) (measurable_one.indicator hO)
    (fun v hv => Set.indicator_of_notMem hv _) (Set.Ioc a b) measurableSet_Ioc
  have hsub : qf ⁻¹' Set.Ioc a b ⊆ {x : Sp M 0 | x ≠ 0} := by
    rintro x hx rfl
    have : a < qf (0 : Sp M 0) := hx.1
    rw [qf_pos_eq] at this
    norm_num at this
    linarith
  rw [Set.indicator_indicator, Set.inter_eq_left.2 hsub,
    lintegral_indicator_one (hq measurableSet_Ioc), Measure.restrict_apply (hq measurableSet_Ioc),
    Set.inter_eq_left.2 hsub] at key
  rw [key]
  refine lintegral_congr fun t => ?_
  rw [lintegral_indicator_one hO]
  refine measure_congr (Filter.eventuallyEq_univ.2 ?_)
  have h1 : ∀ᵐ y ∂(fib t), y ∈ qf ⁻¹' {id t} ∩ {x : Sp M 0 | x ≠ 0} := h.1 t
  filter_upwards [h1] with y hy using hy.2

theorem sphereMass : SphereMass := by
  intro M hM
  refine ⟨GlobalTheory.RealPlaceCompare.exists_isDxDq M 0, fun fib h => ?_⟩
  obtain ⟨G, hG, hG0, hGm⟩ := exists_mass h
  have hq : Measurable (qf : Sp M 0 → ℝ) := GlobalTheory.RealPlaceCompare.continuous_qf.measurable
  set C : ℝ := (2 * Real.pi) ^ M / (M.factorial : ℝ) with hC
  have hC0 : 0 ≤ C := by have := Real.pi_pos; positivity
  have hint : ∀ b ∈ Set.Ioo (1 / 2 : ℝ) 2,
      ∫ t in (1 / 2 : ℝ)..b, G t = C * b ^ M - C * (1 / 2) ^ M := by
    intro b hb
    have hb0 : 0 ≤ b := by linarith [hb.1]
    have e1 : qf ⁻¹' Set.Ioc (1 / 2 : ℝ) b =
        {x : Sp M 0 | qf x ≤ b} \ {x | qf x ≤ 1 / 2} := by
      ext x; simp [and_comm]
    have e2 := dx_shell h (1 / 2) b (by norm_num)
    have hfin : dx M 0 {x : Sp M 0 | qf x ≤ 1 / 2} ≠ ⊤ := by
      rw [dx_ball M hM _ (by norm_num)]; exact ENNReal.ofReal_ne_top
    rw [e1, measure_diff (s₁ := {x : Sp M 0 | qf x ≤ b}) (s₂ := {x : Sp M 0 | qf x ≤ 1 / 2})
      (fun x (hx : qf x ≤ 1 / 2) => (hx.trans hb.1.le : qf x ≤ b))
      (measurableSet_le hq measurable_const).nullMeasurableSet hfin,
      dx_ball M hM _ hb0, dx_ball M hM _ (by norm_num), ← hC,
      ← ENNReal.ofReal_sub _ (by positivity),
      setLIntegral_congr_fun measurableSet_Ioc
        (fun t ht => hGm t ⟨ht.1.le, ht.2.trans hb.2.le⟩),
      ← ofReal_integral_eq_lintegral_ofReal (hG.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
        (Filter.Eventually.of_forall hG0)] at e2
    rw [intervalIntegral.integral_of_le hb.1.le]
    refine ((ENNReal.ofReal_eq_ofReal_iff ?_ (integral_nonneg hG0)).1 e2).symm
    have : (1 / 2 : ℝ) ^ M ≤ b ^ M := pow_le_pow_left₀ (by norm_num) hb.1.le M
    nlinarith
  have d1 : HasDerivAt (fun b => ∫ t in (1 / 2 : ℝ)..b, G t) (G 1) 1 :=
    (hG.integral_hasStrictDerivAt _ _).hasDerivAt
  have d2 : HasDerivAt (fun b : ℝ => C * b ^ M - C * (1 / 2) ^ M)
      (C * ((M : ℝ) * 1 ^ (M - 1))) 1 := ((hasDerivAt_pow M 1).const_mul C).sub_const _
  have d3 : HasDerivAt (fun b => ∫ t in (1 / 2 : ℝ)..b, G t) (C * ((M : ℝ) * 1 ^ (M - 1))) 1 := by
    refine d2.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num) (show (1 : ℝ) < 2 by norm_num)]
      with b hb using hint b hb
  rw [hGm 1 ⟨by norm_num, by norm_num⟩, d1.unique d3, hC, cM]
  congr 1
  obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
  have hk : ((k.factorial : ℝ)) ≠ 0 := by positivity
  have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
  simp only [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    one_pow, mul_one]
  field_simp

end GlobalTheory.SphereMassProof
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowElevenLeSplitBound
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

private theorem szRow_eleven_le_splitBound : SzRow (fun _ D _ => 11 ≤ D.host.splitBound) := by
  intro eps heps _ C _
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨(11 : ℝ) ^ (eps / C.P.Cpde / 5)⁻¹, ?_⟩⟩⟩
  intro D L hε hx hV
  have hH := hV.host
  have hC : (0 : ℝ) < C.P.Cpde := lt_of_lt_of_le one_pos hH.one_le
  have ha : 0 < eps / C.P.Cpde / 5 := by positivity
  have h1 : (11 : ℝ) ≤ L.sc.x ^ (eps / C.P.Cpde / 5) := by
    have h2 := Real.rpow_le_rpow (by positivity) hx ha.le
    rwa [Real.rpow_inv_rpow (by norm_num) ha.ne'] at h2
  have h3 : L.sc.x ^ (eps / C.P.Cpde / 5) ≤ L.sc.x ^ (L.sc.ez / 5) := by
    refine Real.rpow_le_rpow_of_exponent_le L.sc.one_lt_alt.le ?_
    have := hH.eps_div_le_ez
    rw [hε] at this
    linarith
  have h4 : 11 ≤ ⌊L.sc.x ^ (L.sc.ez / 5)⌋₊ := Nat.le_floor (by exact_mod_cast h1.trans h3)
  exact h4.trans hH.split_tie

theorem szRow_sizesAt : SzRow (fun _ _ L => SizesAt L) := by
  have h := ((((((((((GlobalTheory.T.sizes_sizeN_sizeM_sizeK_sizeT_sizeTT_sizeDe2_sizeLw.and GlobalTheory.T.sizes_sizeKRel).and GlobalTheory.T.sizes_sizeCond_sizeQD_sizePde).and GlobalTheory.T.sizes_sizeLa_sizeRho_sizeBot).and GlobalTheory.T.explicitChoice_sizeEta).and
    GlobalTheory.T.explicitChoice_sizeNodes).and GlobalTheory.T.explicitChoice_sizeLstar).and GlobalTheory.T.sizes_sizeDel).and GlobalTheory.T.sizes_sizeW_sizeBm_sizeXpp).and GlobalTheory.T.sizes_sizeG_sizeWords).and
    szRow_eleven_le_splitBound)
  refine h.imp ?_
  rintro C cD ch D L - - ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hN, hM, hK, hT, hTT, hDe, hLw⟩, hKR⟩, hCo, hQD, hP⟩, hLa, hRho, hBot⟩, hEta⟩,
    hNo⟩, hLs⟩, hDel⟩, hW, hBm, hX⟩, hG, hWo⟩, h11⟩
  exact ⟨hN, hM, hK, hKR, hT, hCo, hQD, hTT, hLa, hRho, hBot, hDe, hLw, hEta, hNo, hLs, hDel, hW, hBm, hX, hG,
    hP, hWo, h11⟩

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TopsChoice
section
namespace GlobalTheory.EX

theorem exists_tops : TopsChoice := TopsOfHost.topsChoice_of GlobalTheory.topsChoice

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeylModuleSimpleClosedLowestAlcove
section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

namespace GlobalTheory.Alc

theorem natW_alcove_bound (p : ℕ) (N : ℕ) (lam : DomWeight N)
    (hl : ∀ i j : Fin N, i < j → lam.w i - lam.w j + ((j : ℕ) - (i : ℕ) : ℤ) ≤ (p : ℤ)) :
    ∀ h : 0 < N, lam.natW ⟨N - 1, by omega⟩ = 0 ∧ lam.natW ⟨0, h⟩ + (N - 1) ≤ p := by
  intro h
  obtain ⟨_, h2, h3⟩ := factNatW N lam
  refine ⟨h3 h, ?_⟩
  have e0 := h2 ⟨0, h⟩
  have e1 := h2 ⟨N - 1, by omega⟩
  rw [h3 h] at e1
  by_cases hN1 : N = 1
  · subst hN1
    have : (⟨0, h⟩ : Fin 1) = ⟨1 - 1, by omega⟩ := rfl
    rw [this, h3 h]
    omega
  · have hlt : (⟨0, h⟩ : Fin N) < ⟨N - 1, by omega⟩ := Fin.mk_lt_mk.mpr (by omega)
    have := hl _ _ hlt
    simp only at this
    have hc : ((N - 1 : ℕ) : ℤ) = (N : ℤ) - 1 := by omega
    push_cast at this
    omega

theorem inducedSimpleLowestAlcove : GlobalTheory.Published.InducedSimpleLowestAlcove := by
  intro p hp k _ _ N lam hl
  have hN := factNatW N lam
  have hne : nablaSq k N lam ≠ ⊥ := by
    intro h
    have hm : hw k le_rfl lam.natW ∈ nablaSq k N lam := hwMem k N N le_rfl _ hN.1
    rw [h, Submodule.mem_bot] at hm
    exact hwNe k N N le_rfl _ hm
  refine ⟨hne, fun M hM hG => ?_⟩
  by_contra hc
  push_neg at hc
  have key := GlobalTheory.T.highestWeightVector_mem_of_lt_stable_dualWeyl p hp k N lam.natW hN.1 (natW_alcove_bound p N lam hl)
  have good := GlobalTheory.T.isRowOperatorStable_dualWeyl_and_GLSubmodules k N lam
  have h1 := (key ⊥ M (good_top_bot k N N).2 (good.2 M hG) (bot_lt_iff_ne_bot.2 hc.1) hM).1
  have h2 := (key M (nablaSq k N lam) (good.2 M hG) good.1 (lt_of_le_of_ne hM hc.2) le_rfl).2
  exact h2 h1

end GlobalTheory.Alc
end

