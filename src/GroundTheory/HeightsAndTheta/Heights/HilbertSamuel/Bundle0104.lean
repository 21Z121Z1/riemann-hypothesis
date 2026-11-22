import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0026
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0045
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0041
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0012
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0087
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartNakayamaGenLocal

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ExistsLinearIndependentOfGenerates
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1

noncomputable section

theorem isProjVarF_map_of_isArithVar {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {D : ℕ} (hP : IsArithVar P (D + 1)) :
    IsProjVarF (P.map (MvPolynomial.map (Int.castRingHom ℚ))) D := by
  classical
  have h := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.isProjVarQ_of_isArithVar hP
  exact ⟨(GroundTheory.Heights₂.Heights.NumbersDVR.Objects.isMultiProjPrime_iff _).mp h.1, h.2⟩

section Basis

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

theorem isMultiHomog_aeval_linear {κ κ' : Type} [Fintype κ] [Fintype κ'] (c : κ → κ' → ℤ)
    {g : MRing (fun _ : Unit => κ)} {d : Unit → ℕ} (hg : IsMultiHomog g d) :
    IsMultiHomog (aeval (fun p : Σ _ : Unit, κ => ∑ i, C (c p.2 i) * X (⟨(), i⟩ : Σ _ : Unit, κ')) g) d := by
  have hdeg : ∀ {τ : Type} [Fintype τ] (m : (Σ _ : Unit, τ) →₀ ℕ), m.degree = ∑ i, m ⟨(), i⟩ := by
    intro τ _ m
    classical
    rw [Finsupp.degree_apply, Finset.sum_subset (Finset.subset_univ _) (fun x _ hx => by
      simpa using hx), Fintype.sum_sigma, Fintype.sum_unique]
  have hw : ∀ {τ : Type} (m : τ →₀ ℕ), Finsupp.weight 1 m = m.degree := by
    intro τ m
    rw [Finsupp.degree_eq_weight_one]
    rfl
  have hH : g.IsHomogeneous (d ()) := by
    intro m hm
    rw [hw, hdeg]
    exact hg m (mem_support_iff.mpr hm) ()
  have hL : ∀ p : Σ _ : Unit, κ,
      (∑ i, C (c p.2 i) * X (⟨(), i⟩ : Σ _ : Unit, κ') : MRing (fun _ : Unit => κ')).IsHomogeneous 1 :=
    fun p => IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_C_mul_X _ _
  have h := hH.aeval _ hL
  rw [one_mul] at h
  intro m hm k
  have := h (mem_support_iff.mp hm)
  rw [hw, hdeg] at this
  exact this

omit [∀ k, Fintype (ι k)] in

theorem exists_linearIndependent_of_generates (y : (Σ k, ι k) → Ω) (n : K → ℤ) {ι' : Type} [Fintype ι']
    (x' : ι' → Ω) (hmem : ∀ j, x' j ∈ chartLat y n 1) (hgen : KH.GeneratesOn y n x')
    (hbir : Birational (fun p : Σ _ : Unit, ι' => x' p.2)) :
    ∃ (ι'' : Type) (_ : Fintype ι'') (x'' : ι'' → Ω), (∀ j, x'' j ∈ chartLat y n 1) ∧
      LinearIndependent ℤ x'' ∧ KH.GeneratesOn y n x'' ∧ Birational (fun p : Σ _ : Unit, ι'' => x'' p.2) := by
  classical
  let L : Submodule ℤ Ω := Submodule.span ℤ (Set.range x')
  have : Module.Finite ℤ L := Module.Finite.span_of_finite ℤ (Set.finite_range x')
  let b := Module.Free.chooseBasis ℤ L
  let x'' : Module.Free.ChooseBasisIndex ℤ L → Ω := fun i => (b i : Ω)
  have hL : L ≤ (chartLat y n 1).toIntSubmodule :=
    Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hmem j)
  let cf : ι' → Module.Free.ChooseBasisIndex ℤ L → ℤ :=
    fun j => b.repr ⟨x' j, Submodule.subset_span ⟨j, rfl⟩⟩
  have hexp : ∀ j, x' j = ∑ i, (cf j i : Ω) * x'' i := by
    intro j
    have h := congrArg Subtype.val (b.sum_repr ⟨x' j, Submodule.subset_span ⟨j, rfl⟩⟩)
    rw [Submodule.coe_sum] at h
    refine h.symm.trans (Finset.sum_congr rfl fun i _ => ?_)
    rw [Submodule.coe_smul, zsmul_eq_mul]
  refine ⟨_, inferInstance, x'', fun i => hL (b i).2, b.linearIndependent.map' L.subtype L.ker_subtype,
    fun c hc => ?_, fun s => ?_⟩
  · obtain ⟨u, hu, hsum⟩ := hgen c hc
    refine ⟨fun i => ∑ j, (cf j i : Ω) * u j, fun i => ?_, ?_⟩
    · exact Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ (Subalgebra.intCast_mem _ _) (hu j)
    · rw [← hsum]
      calc ∑ i, (∑ j, (cf j i : Ω) * u j) * (x'' i * ∏ k, y ⟨k, c k⟩ ^ (-n k))
          = ∑ j, u j * ((∑ i, (cf j i : Ω) * x'' i) * ∏ k, y ⟨k, c k⟩ ^ (-n k)) := by
            simp only [Finset.sum_mul, Finset.mul_sum]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
        _ = ∑ j, u j * (x' j * ∏ k, y ⟨k, c k⟩ ^ (-n k)) :=
            Finset.sum_congr rfl fun j _ => by rw [← hexp j]
  · obtain ⟨d, g, h, hg, hh, hh0, hgh⟩ := hbir s
    let σ : MRing (fun _ : Unit => ι') →ₐ[ℤ] MRing (fun _ : Unit => Module.Free.ChooseBasisIndex ℤ L) :=
      aeval fun p => ∑ i, C (cf p.2 i) * X ⟨(), i⟩
    have hev : ∀ f, aeval (fun p : Σ _ : Unit, Module.Free.ChooseBasisIndex ℤ L => x'' p.2) (σ f) =
        aeval (fun p : Σ _ : Unit, ι' => x' p.2) f := by
      intro f
      rw [← AlgHom.comp_apply, comp_aeval]
      congr 2
      funext p
      simp [hexp p.2]
    refine ⟨d, σ g, σ h, isMultiHomog_aeval_linear cf hg, isMultiHomog_aeval_linear cf hh, ?_, ?_⟩
    · rw [hev]; exact hh0
    · rw [hev, hev]; exact hgh

end Basis

theorem Lift.proof (hKA : KH.KAmpStatement) (hNF : NefAmpleFibre.Statement) (hLM : LiftModel.Statement) :
    Lift.Statement := by
  intro K _ ι _ Ω _ _ y D α t I hI hV hbir ht hnef hnefQ
  classical
  let _ : LinearOrder K := LinearOrder.lift' _ (Fintype.equivFin K).injective
  let _ : ∀ k, LinearOrder (ι k) := fun k => LinearOrder.lift' _ (Fintype.equivFin (ι k)).injective
  have hnum : 0 < t.num := Rat.num_pos.mpr ht
  set p : ℕ := t.num.toNat with hp_def
  set q : ℕ := t.den with hq_def
  have hp : 1 ≤ p := by omega
  have hq : 1 ≤ q := t.den_pos
  have hpn : ((p : ℤ) : ℚ) = t.num := by
    rw [hp_def, Int.toNat_of_nonneg hnum.le]
  have htq : t = (p : ℚ) / q := by
    rw [hq_def, ← Int.cast_natCast, hpn]
    exact (Rat.num_div_den t).symm
  have hGen := hKA ℚ K ι I (KH.genIdeal y) D α q p hI (isProjVarF_map_of_isArithVar hV) hnefQ hq hp
  have hFib : ∀ ℓ : ℕ, ℓ.Prime → KH.AmpleV (ZMod ℓ) (fibreIdeal ℓ y) (q • α + fun _ => (p : ℤ)) := by
    intro ℓ hℓ
    have h := hNF K ι Ω y D α q p ℓ hV hnef hq hp hℓ
    rwa [natCast_zsmul] at h
  have hGen2 := hKA ℚ K ι I (KH.genIdeal y) D α (2 * q) (2 * p - 1) hI (isProjVarF_map_of_isArithVar hV) hnefQ
    (by omega) (by omega)
  have hExtra : ∃ c : ℕ, 1 ≤ c ∧
      KH.AmpleV ℚ (KH.genIdeal y) (c • (q • α + fun _ => (p : ℤ)) - fun _ => 1) := by
    refine ⟨2, by norm_num, ?_⟩
    have he : (2 • (q • α + fun _ => (p : ℤ)) - fun _ => (1 : ℤ) : K → ℤ) =
        (2 * q) • α + fun _ => ((2 * p - 1 : ℕ) : ℤ) := by
      funext k
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
      simp only [nsmul_eq_mul]
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [he]
    exact hGen2
  obtain ⟨a, ι', _, x', ha, hmem, hgen, hbir'⟩ := hLM K ι Ω y D _ hV hbir hGen hExtra hFib
  obtain ⟨ι'', _, x'', hmem'', hli, hgen'', hbir''⟩ :=
    exists_linearIndependent_of_generates y _ x' hmem hgen hbir'
  refine ⟨a * q, _, ι'', inferInstance, x'', Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)),
    fun k => ?_, hmem'', hli, hgen'', hbir''⟩
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  simp only [Pi.smul_apply, Pi.add_apply, nsmul_eq_mul, Int.cast_mul, Int.cast_add,
    Int.cast_natCast, Nat.cast_mul, htq]
  field_simp
  simp only [Pi.mul_apply, Pi.natCast_apply]
  push_cast
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockResolutionInterpIntegral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M MeasureTheory Filter Topology

noncomputable section

namespace BlockResolutionInterpIntegral

variable {D : ℕ} {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Ω : Type} [Field Ω] [CharZero Ω]

theorem locDens_interp (d : HSMBlockDatum D K ι Ω) {A' : HermLine ι} (hA' : IsSmoothHerm A')
    (t : ℝ) (j : Fin d.R.A.n) {y : Fin D → ℂ} (hy : y ∈ (d.R.A.chart j).target) :
    locDens d.R.A (fun _ => blockInterpPot d d.A A' t) j y =
      ∑ i ∈ Finset.range (D + 1), (D.choose i : ℝ) * t ^ i * (1 - t) ^ (D - i) *
        locDens d.R.A (fun k : Fin D => if k.val < i then AnResBridge.potOf d.R A'
          else AnResBridge.potOf d.R d.A) j y := by
  set x0 := (d.R.A.chart j).symm y with hx0
  set a : (Fin D → ℂ) → ℝ := fun y' => Real.log (d.A.h (d.R.lift x0 ((d.R.A.chart j).symm y'))) with ha
  set b : (Fin D → ℂ) → ℝ := fun y' => Real.log (A'.h (d.R.lift x0 ((d.R.A.chart j).symm y'))) with hb
  have hV : IsOpen ((d.R.A.chart j).target ∩ (d.R.A.chart j).symm ⁻¹' d.R.U x0) :=
    (d.R.A.chart j).isOpen_inter_preimage_symm (d.R.isOpen_U x0)
  have hyV : y ∈ (d.R.A.chart j).target ∩ (d.R.A.chart j).symm ⁻¹' d.R.U x0 := ⟨hy, d.R.mem_U x0⟩
  have hsm : ∀ {L : HermLine ι}, IsSmoothHerm L → ∀ᶠ y' in 𝓝 y,
      ContDiffAt ℝ 2 (fun y'' => Real.log (L.h (d.R.lift x0 ((d.R.A.chart j).symm y'')))) y' := by
    intro L hL
    filter_upwards [hV.mem_nhds hyV] with y' hy'
    exact_mod_cast contDiffAt_infty.mp
      ((AnResBridge.contDiffOn_potOf d.R hL x0 j).contDiffAt (hV.mem_nhds hy')) 2
  have hH := gaamix_cxHessian_comb (ψ := fun y' => (1 - t) * a y' + t * b y') (1 - t) t
    (hsm d.semipos.1) (hsm hA') (Filter.EventuallyEq.refl _ _)
  set H₀ := cxHessian a y
  set H₁ := cxHessian b y
  have hL : locDens d.R.A (fun _ => blockInterpPot d d.A A' t) j y =
      ReciprocityTheory.AnForm.maDens (fun _ y' => (1 - t) * a y' + t * b y') y := rfl
  have hR : ∀ i, locDens d.R.A (fun k : Fin D => if k.val < i then AnResBridge.potOf d.R A'
      else AnResBridge.potOf d.R d.A) j y =
      ReciprocityTheory.AnForm.maDens (fun k => if k.val < i then b else a) y := by
    intro i
    show ReciprocityTheory.AnForm.maDens _ y = _
    congr 1
    funext k y'
    by_cases hk : k.val < i
    · simp only [hk, if_true]; rfl
    · simp only [hk, if_false]; rfl
  have hpure : (fun _ : Fin D => ReciprocityTheory.AnForm.hessC (fun y' => (1 - t) * a y' + t * b y') y) =
      fun _ => (t : ℂ) • H₁ + (1 - (t : ℂ)) • H₀ := by
    funext k
    show cxHessian _ y = _
    rw [hH, add_comm]
    push_cast
    rfl
  have hmix : ∀ i, (fun k : Fin D => ReciprocityTheory.AnForm.hessC (if k.val < i then b else a) y) =
      fun k : Fin D => if k.val < i then H₁ else H₀ := by
    intro i
    funext k
    by_cases hk : k.val < i
    · simp only [hk, if_true]; rfl
    · simp only [hk, if_false]; rfl
  rw [hL]
  simp only [hR]
  unfold ReciprocityTheory.AnForm.maDens
  rw [hpure, ReciprocityTheory.AnForm.A.mdisc_const, ReciprocityTheory.AnForm.A.det_smul_add_smul_eq_sum_mdisc,
    Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hmix i]
  have e : (D.choose i : ℂ) * (t : ℂ) ^ i * (1 - (t : ℂ)) ^ (D - i) =
      ((D.choose i * t ^ i * (1 - t) ^ (D - i) : ℝ) : ℂ) := by push_cast; ring
  rw [e, Complex.re_ofReal_mul]
  ring

theorem continuous_logRatio (d : HSMBlockDatum D K ι Ω) {A' : HermLine ι} (hdeg : A'.a = unitDeg d.k₀)
    (hA' : IsSmoothHerm A') :
    Continuous fun x => Real.log (A'.h (blockPt d x) / d.A.h (blockPt d x)) := by
  have hA : IsSmoothHerm d.A := d.semipos.1
  have hE : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
    have e : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0} := by
      ext z; simp
    rw [e]
    exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
      isOpen_ne_fun (continuous_apply _) continuous_const
  have hΦ : ContinuousOn (fun z : (Σ k, ι k) → ℂ => Real.log (A'.h z / d.A.h z))
      {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
    (hA'.continuousOn.div hA.continuousOn fun z hz => (d.A.pos z hz).ne').log fun z hz =>
      (div_pos (A'.pos z hz) (d.A.pos z hz)).ne'
  have hdeg' : A'.a = d.A.a := hdeg.trans d.deg.symm
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  have hU := (d.R.isOpen_U x₀).mem_nhds (d.R.mem_U x₀)
  have hl : ContinuousAt (d.R.lift x₀) x₀ :=
    (continuousOn_pi.2 fun p => AnResBridge.continuousOn_lift d.R x₀ p).continuousAt hU
  have h0 : d.R.lift x₀ x₀ ∈ {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
    (d.R.mem x₀ x₀ (d.R.mem_U x₀)).1
  have h2 : ContinuousAt (fun x => Real.log (A'.h (d.R.lift x₀ x) / d.A.h (d.R.lift x₀ x))) x₀ :=
    (hΦ.continuousAt (hE.mem_nhds h0)).comp hl
  refine h2.congr ?_
  filter_upwards [hU] with x hx
  obtain ⟨c, hc0, he⟩ := d.R.compat x x₀ x ⟨d.R.mem_U x, hx⟩
  show _ = Real.log (A'.h (d.R.lift x x) / d.A.h (d.R.lift x x))
  have hp : (∏ k, ‖c k‖ ^ d.A.a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc0 k))
  rw [he, A'.smul c _ hc0, d.A.smul c _ hc0, hdeg', mul_div_mul_left _ _ hp]

theorem mInt_interp (d : HSMBlockDatum D K ι Ω) {A' : HermLine ι} (hdeg : A'.a = unitDeg d.k₀)
    (hA' : IsSmoothHerm A') (t : ℝ) :
    mInt d.R.A (fun _ => blockInterpPot d d.A A' t)
        (fun x => Real.log (A'.h (blockPt d x) / d.A.h (blockPt d x))) =
      ∑ i ∈ Finset.range (D + 1), (D.choose i : ℝ) * t ^ i * (1 - t) ^ (D - i) *
        mInt d.R.A (fun k : Fin D => if k.val < i then AnResBridge.potOf d.R A'
            else AnResBridge.potOf d.R d.A)
          (fun x => Real.log (A'.h (blockPt d x) / d.A.h (blockPt d x))) := by
  have hg := continuous_logRatio d hdeg hA'
  have hΦ : ∀ (i : ℕ) (k : Fin D), IsPotential d.R.A
      (if k.val < i then AnResBridge.potOf d.R A' else AnResBridge.potOf d.R d.A) := by
    intro i k
    split_ifs
    · exact AnResBridge.isPotential_potOf d.R hA'
    · exact AnResBridge.isPotential_potOf d.R d.semipos.1
  unfold mInt
  by_cases hP : Nonempty (ChartPartition d.R.A)
  · simp only [dif_pos hP]
    unfold integralWith
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hint : ∀ i ∈ Finset.range (D + 1), Integrable (fun y =>
        (D.choose i : ℝ) * t ^ i * (1 - t) ^ (D - i) *
          (hP.some.χ j ((d.R.A.chart j).symm y) *
            Real.log (A'.h (blockPt d ((d.R.A.chart j).symm y)) / d.A.h (blockPt d ((d.R.A.chart j).symm y))) *
            locDens d.R.A (fun k : Fin D => if k.val < i then AnResBridge.potOf d.R A'
              else AnResBridge.potOf d.R d.A) j y))
        (volume.restrict (d.R.A.chart j).target) := fun i _ =>
      (integrableOn_weight d.R.A hP.some _ _ (mIntegrableCont d.R.A _ (hΦ i) _ hg) j).const_mul _
    calc _ = ∫ y in (d.R.A.chart j).target, ∑ i ∈ Finset.range (D + 1),
          (D.choose i : ℝ) * t ^ i * (1 - t) ^ (D - i) *
            (hP.some.χ j ((d.R.A.chart j).symm y) *
              Real.log (A'.h (blockPt d ((d.R.A.chart j).symm y)) /
                d.A.h (blockPt d ((d.R.A.chart j).symm y))) *
              locDens d.R.A (fun k : Fin D => if k.val < i then AnResBridge.potOf d.R A'
                else AnResBridge.potOf d.R d.A) j y) := by
          refine setIntegral_congr_fun (d.R.A.chart j).open_target.measurableSet fun y hy => ?_
          rw [locDens_interp d hA' t j hy, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = _ := by
          rw [integral_finsetSum _ hint]
          exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  · simp only [dif_neg hP, mul_zero, Finset.sum_const_zero]

theorem proof : BlockResolutionInterpIntegral.Statement := by
  intro D K _ _ ι _ Ω _ _ d A' hdeg hA'
  unfold blockMetricInt
  simp only [mInt_interp d hdeg hA']
  rw [intervalIntegral.integral_finsetSum fun i _ =>
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [intervalIntegral.integral_mul_const,
    ReciprocityTheory.GeometryOfNumbersTheory.integral_bernstein D i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]
  have hD : (D : ℝ) + 1 ≠ 0 := by positivity
  field_simp

end BlockResolutionInterpIntegral

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartNakayamaGen
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace ChartNakayamaGen

set_option linter.unusedSectionVars false

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]

theorem homog_unique {p : MRingOver S ι} {a b : K → ℕ} (ha : IsMultiHomog p a) (hb : IsMultiHomog p b)
    (h0 : p ≠ 0) : a = b := by
  obtain ⟨μ, hμ⟩ := Finset.nonempty_iff_ne_empty.mpr (mt MvPolynomial.support_eq_empty.mp h0)
  funext k
  exact (ha μ hμ k).symm.trans (hb μ hμ k)

theorem chartMon_ne_zero [Nontrivial S] (c : ∀ k, ι k) (e : K → ℕ) : chartMon (S := S) c e ≠ 0 := by
  have h : chartMon (S := S) c e = monomial (∑ k, Finsupp.single (⟨k, c k⟩ : Σ k, ι k) (e k)) 1 := by
    rw [MvPolynomial.monomial_sum_one, chartMon]
    exact Finset.prod_congr rfl fun k _ => MvPolynomial.X_pow_eq_monomial
  rw [h, Ne, MvPolynomial.monomial_eq_zero]
  exact one_ne_zero

theorem chartMon_one_pow (c : ∀ k, ι k) (n : ℕ) :
    chartMon (S := S) c (fun _ => 1) ^ n = chartMon c (fun _ => n) := by
  simp only [chartMon, pow_one, ← Finset.prod_pow]

theorem smul_mk_cancel' {T : Submonoid (MRingOver S ι)} {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M]
    (w : MRingOver S ι) (y : M) {s : MRingOver S ι} (hs : s ∈ T) :
    (w * s) • LocalizedModule.mk y (⟨s, hs⟩ : T) = LocalizedModule.mk (w • y) 1 :=
  smul_mk_cancel w y ⟨s, hs⟩

theorem exists_kill_of_res_eq_zero {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] (c c' : ∀ k, ι k)
    (w : LocalizedModule (KH.cellMon S (chart c').1) M)
    (hw : KH.cellRes S M (chart c').1 (fun k => ({c k, c' k} : Finset (ι k))) w = 0) :
    ∃ e : ℕ, chartMon (S := S) c (fun _ => e) • w = 0 := by
  induction w using LocalizedModule.induction_on with
  | h m s =>
    have hsub : ∀ k, (chart c').1 k ⊆ ({c k, c' k} : Finset (ι k)) := fun k => by simp [chart]
    rw [GenTwistGenerated.cellRes_mk (GenTwistGenerated.cellMon_mono hsub)] at hw
    obtain ⟨v, hv⟩ := LocalizedModule.mk_eq.mp
      (hw.trans (LocalizedModule.zero_mk (1 : KH.cellMon S (fun k => ({c k, c' k} : Finset (ι k))))).symm)
    simp only [one_smul, smul_zero] at hv
    obtain ⟨e, w', hw'⟩ := dvd_of_mem_pair v.2
    have hz : (chartMon (S := S) c (fun _ => e) * chartMon c' (fun _ => e)) • m = 0 := by
      rw [hw', mul_comm, mul_smul, ← Submonoid.smul_def, hv, smul_zero]
    refine ⟨e, ?_⟩
    rw [LocalizedModule.smul'_mk, ← LocalizedModule.zero_mk s, LocalizedModule.mk_eq]
    refine ⟨⟨chartMon c' (fun _ => e), chartMon_mem c' _⟩, ?_⟩
    show chartMon (S := S) c' (fun _ => e) • (s : MRingOver S ι) • chartMon (S := S) c (fun _ => e) • m =
      chartMon (S := S) c' (fun _ => e) • (s : MRingOver S ι) • (0 : M)
    rw [smul_zero, smul_zero, smul_comm (chartMon c' (fun _ => e)) (s : MRingOver S ι),
      smul_smul (chartMon c' (fun _ => e)) (chartMon c (fun _ => e)) m,
      mul_comm (chartMon c' (fun _ => e)) (chartMon c (fun _ => e)), hz, smul_zero]

theorem genNear_of_chart [Nontrivial S] {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] {𝓜 : (K → ℤ) → Submodule S M} {d : K → ℤ} (h𝓜 : KH.IsMGraded S ι 𝓜)
    (c : ∀ k, ι k) {f₀ : MRingOver S ι} {δ₀ : K → ℕ} (hf₀ : IsMultiHomog f₀ δ₀)
    (hloc : ∀ x ∈ KH.locPart ι 𝓜 (KH.cellMon S (chart c).1) d, ∃ (t : MRingOver S ι) (a : K → ℕ) (r : ℕ)
        (p : Fin r → MRingOver S ι) (z : Fin r → KH.CechC S ι M 0),
        t ∈ KH.cellMon S (chart c).1 ∧ IsMultiHomog t a ∧ (∀ j, IsMultiHomog (p j) (a + δ₀)) ∧
        (∀ j, z j ∈ KH.cechZc ι 𝓜 d 0) ∧ (f₀ * t) • x = ∑ j, p j • z j (chart c)) :
    GenNear S ι 𝓜 d (f₀ * chartMon c (fun _ => 1)) (δ₀ + fun _ => 1) := by
  intro J
  obtain ⟨c', rfl⟩ : ∃ c', J = chart c' := ⟨_, eq_chart J⟩
  intro x hx
  obtain ⟨m, t, a, ht, hm, rfl⟩ := GenSESStep.locPart_normal h𝓜 hx

  have hy : LocalizedModule.mk m (⟨chartMon c a, chartMon_mem c a⟩ : KH.cellMon S (chart c).1) ∈
      KH.locPart ι 𝓜 (KH.cellMon S (chart c).1) d :=
    GenSESStep.mk_mem_locPart _ _ a (isMultiHomog_chartMon c a) hm
  obtain ⟨t₁, a₁, r, p, z, ht₁T, ht₁, hp, hz, he⟩ := hloc _ hy
  obtain ⟨α₁, rfl⟩ := exists_chartMon ht₁T
  obtain rfl : a₁ = α₁ := homog_unique ht₁ (isMultiHomog_chartMon c α₁) (chartMon_ne_zero c α₁)

  set U : ∀ k, Finset (ι k) := fun k => {c k, c' k} with hU
  have hsub : ∀ k, (chart c).1 k ⊆ U k := fun k => by simp [chart, hU]
  have hsub' : ∀ k, (chart c').1 k ⊆ U k := fun k => by simp [chart, hU]
  have hle := GenTwistGenerated.cellMon_mono (S := S) hsub
  have hle' := GenTwistGenerated.cellMon_mono (S := S) hsub'
  have hagree : ∀ j, KH.cellRes S M (chart c').1 U (z j (chart c')) =
      KH.cellRes S M (chart c).1 U (z j (chart c)) := fun j =>
    (res_agree (z j) (LinearMap.mem_ker.mp (hz j).2) c c' U (fun k => by simp [hU])
      (fun k => by simp [hU])).symm
  have hD : KH.cellRes S M (chart c').1 U ((f₀ * chartMon c a₁ * (t : MRingOver S ι)) • LocalizedModule.mk m t -
      ∑ j, (chartMon c a * p j) • z j (chart c')) = 0 := by
    have h2 : KH.cellRes S M (chart c').1 U (∑ j, (chartMon c a * p j) • z j (chart c')) =
        LocalizedModule.mk ((f₀ * chartMon c a₁) • m) 1 := by
      have e1 : KH.cellRes S M (chart c').1 U (∑ j, (chartMon c a * p j) • z j (chart c')) =
          chartMon (S := S) c a • KH.cellRes S M (chart c).1 U (∑ j, p j • z j (chart c)) := by
        rw [map_sum, map_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, hagree j, map_smul, mul_smul]
      rw [e1, ← he, map_smul, GenTwistGenerated.cellRes_mk hle, smul_smul,
        mul_comm (chartMon (S := S) c a) (f₀ * chartMon c a₁)]
      exact smul_mk_cancel' _ _ _
    rw [map_sub, h2, map_smul, GenTwistGenerated.cellRes_mk hle', sub_eq_zero]
    exact smul_mk_cancel' _ _ _
  obtain ⟨e, he0⟩ := exists_kill_of_res_eq_zero c c' _ hD
  rw [smul_sub, sub_eq_zero] at he0

  set E : ℕ := ∑ k, a₁ k with hE
  have haE : ∀ k, a₁ k ≤ E := fun k =>
    Finset.single_le_sum (f := a₁) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  have hexp : (fun _ : K => e + E + 1) = (fun _ => 1) + (fun k => E - a₁ k) + (fun _ => e) + a₁ := by
    funext k
    simp only [Pi.add_apply]
    have := haE k
    omega
  have hring : (f₀ * chartMon c (fun _ => 1)) ^ (e + E + 1) * (t : MRingOver S ι) =
      (f₀ ^ (e + E) * chartMon c (fun _ => 1) * chartMon c (fun k => E - a₁ k)) *
        (chartMon c (fun _ => e) * (f₀ * chartMon c a₁ * (t : MRingOver S ι))) := by
    rw [mul_pow, chartMon_one_pow, hexp, chartMon_add, chartMon_add, chartMon_add]
    ring
  refine ⟨e + E + 1, t, a, r, fun j => f₀ ^ (e + E) * chartMon c (fun _ => 1) * chartMon c (fun k => E - a₁ k) *
    chartMon c (fun _ => e) * chartMon c a * p j, z, t.2, ht, fun j => ?_, hz, ?_⟩
  · have h := GenSESStep.isMultiHomog_mul (GenSESStep.isMultiHomog_mul (GenSESStep.isMultiHomog_mul
      (GenSESStep.isMultiHomog_mul (GenSESStep.isMultiHomog_mul (isMultiHomog_pow hf₀ (e + E))
        (isMultiHomog_chartMon c (fun _ => 1))) (isMultiHomog_chartMon c (fun k => E - a₁ k)))
        (isMultiHomog_chartMon c (fun _ => e))) (isMultiHomog_chartMon c a)) (hp j)
    convert h using 1
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := haE k
    zify [this] at *
    ring
  · rw [hring, mul_smul, mul_smul (chartMon (S := S) c (fun _ => e)), he0, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    dsimp only
    simp only [smul_smul]
    congr 1
    ring

end ChartNakayamaGen

theorem ChartNakayamaGen.proof : ChartNakayamaGen.Statement := by
  intro S _ K _ _ ι _ _ M _ _ _ _ 𝓜 P d hS hM h𝓜 hP _ I hI hgen
  obtain ⟨c, rfl⟩ : ∃ c, I = ChartNakayamaGen.chart c := ⟨_, ChartNakayamaGen.eq_chart I⟩
  have h1 : (1 : S) ≠ 0 := fun h => hP.ne_top ((Ideal.eq_top_iff_one P).mpr (by
    have e : (1 : MRingOver S ι) = 0 := by rw [← C_1, h, C_0]
    rw [e]
    exact P.zero_mem))
  have : Nontrivial S := nontrivial_of_ne 1 0 h1
  have hc : ∀ k, (X ⟨k, c k⟩ : MRingOver S ι) ∉ P := fun k => hI k (c k) (Finset.mem_singleton_self _)
  obtain ⟨f₀, δ₀, hf₀, hf₀P, hloc⟩ := ChartNakayamaGen.chart_nakayama hS hM h𝓜 hP c hc hgen
  refine ⟨f₀ * ChartNakayamaGen.chartMon c (fun _ => 1), δ₀ + fun _ => 1,
    GenSESStep.isMultiHomog_mul hf₀ (ChartNakayamaGen.isMultiHomog_chartMon c _), fun h => ?_,
    ChartNakayamaGen.genNear_of_chart h𝓜 c hf₀ hloc⟩
  rcases hP.mem_or_mem h with h | h
  · exact hf₀P h
  · exact ChartNakayamaGen.cellMon_notMem hP hc (ChartNakayamaGen.chartMon_mem c _) h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

