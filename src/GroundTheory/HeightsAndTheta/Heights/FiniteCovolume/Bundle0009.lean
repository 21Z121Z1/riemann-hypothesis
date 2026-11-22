import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PMinkowskiVolumeForm
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Module MeasureTheory Submodule

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  (d : ℕ) [Fact (finrank ℝ V = d)]

theorem MinkowskiVolumeForm.proof : MinkowskiVolumeForm.Statement V d := by
  classical
  intro o b lam hlam hmin
  let _ : MeasurableSpace V := borel V
  have _ : BorelSpace V := ⟨rfl⟩
  have hd : finrank ℝ V = d := Fact.out

  have hcomb : ∀ x ∈ span ℤ (Set.range b), x ≠ 0 → lam ≤ ‖x‖ := by
    intro x hx hx0
    obtain ⟨z, rfl⟩ := (mem_span_range_iff_exists_fun ℤ).1 hx
    have hz : z ≠ 0 := by
      rintro rfl
      simp at hx0
    simpa [← Int.cast_smul_eq_zsmul ℝ] using hmin z hz
  have hdisc : DiscreteTopology (span ℤ (Set.range b)) :=
    DiscreteTopology.of_forall_le_norm hlam fun x hx => hcomb x x.2 (by simpa using hx)
  have hZ : LinearIndependent ℤ b := by
    rw [Fintype.linearIndependent_iff]
    intro z hz
    by_contra hne
    have hz' : z ≠ 0 := fun h => hne (fun i => by simp [h])
    have h1 := hmin z hz'
    have h2 : ∑ i, (z i : ℝ) • b i = 0 := by simpa [Int.cast_smul_eq_zsmul] using hz
    rw [h2, norm_zero] at h1
    linarith
  have hR : LinearIndependent ℝ b := by
    rw [linearIndependent_iff_card_eq_finrank_span, Real.finrank_eq_int_finrank_of_discrete hdisc,
      Set.finrank, finrank_span_eq_card hZ]
  have hcard : Fintype.card (Fin d) = finrank ℝ V := by simp [hd]
  let B : Basis (Fin d) ℝ V := Basis.mk hR (hR.span_eq_top_of_card_eq_finrank' hcard).ge
  have hB : ⇑B = b := Basis.coe_mk _ _

  have hF : volume (ZSpan.fundamentalDomain B) = ENNReal.ofReal |o.volumeForm b| := by
    rw [measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped B volume), ← o.measure_eq_volume,
      AlternatingMap.measure_parallelepiped, hB]

  let e : OrthonormalBasis (Fin d) ℝ V := (stdOrthonormalBasis ℝ V).reindex (finCongr hd)
  set σ : ℝ := lam / Real.sqrt d with hσ
  have hσ0 : 0 ≤ σ := div_nonneg hlam.le (Real.sqrt_nonneg _)
  let φ : V →ₗ[ℝ] (Fin d → ℝ) :=
    (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).toLinearMap ∘ₗ e.repr.toLinearEquiv.toLinearMap
  let P : Set (Fin d → ℝ) := Set.univ.pi fun _ => Set.Ioo (-σ) σ
  let s : Set V := φ ⁻¹' P
  have hs_mem : ∀ v, v ∈ s ↔ ∀ i, |e.repr v i| < σ := by
    intro v
    simp only [s, P, Set.mem_preimage, Set.mem_univ_pi, Set.mem_Ioo, abs_lt]
    rfl
  have hsymm : ∀ x ∈ s, -x ∈ s := by
    intro x hx
    rw [hs_mem] at hx ⊢
    intro i
    simpa using hx i
  have hconv : Convex ℝ s := (convex_pi fun _ _ => convex_Ioo _ _).linear_preimage φ
  have hvol : volume s = ENNReal.ofReal (2 * σ) ^ d := by
    have hmp : MeasurePreserving (fun v : V => WithLp.ofLp (e.repr v)) volume volume :=
      (PiLp.volume_preserving_ofLp (Fin d)).comp e.measurePreserving_repr
    rw [show s = (fun v : V => WithLp.ofLp (e.repr v)) ⁻¹' P from rfl,
      hmp.measure_preimage (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).nullMeasurableSet,
      Real.volume_pi_Ioo, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 2
    ring
  by_contra hlt
  push Not at hlt
  have hlt' : volume (ZSpan.fundamentalDomain B) * 2 ^ finrank ℝ V < volume s := by
    rw [hd]
    have h : ENNReal.ofReal (|o.volumeForm b| * 2 ^ d) < ENNReal.ofReal ((2 * σ) ^ d) := by
      rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity), mul_pow, mul_comm]
      exact mul_lt_mul_of_pos_left hlt (by positivity)
    rwa [ENNReal.ofReal_mul (abs_nonneg _), ENNReal.ofReal_pow (mul_nonneg zero_le_two hσ0),
      ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat, ← hF, ← hvol] at h
  have hcount : Countable (span ℤ (Set.range B)).toAddSubgroup := by
    change Countable (span ℤ (Set.range B))
    infer_instance
  obtain ⟨⟨x, hxL⟩, hx0, hxs⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    (ZSpan.isAddFundamentalDomain' B volume) hsymm hconv hlt'
  have hx0' : x ≠ 0 := by
    rintro rfl
    exact hx0 rfl
  have h1 : lam ≤ ‖x‖ := hcomb x (by rw [← hB]; exact hxL) hx0'
  have h2 : ‖x‖ < lam := by
    rw [hs_mem] at hxs
    rcases Nat.eq_zero_or_pos d with hd0 | hdpos
    · exact absurd (@Subsingleton.elim _ (finrank_zero_iff.1 (hd.trans hd0)) x 0) hx0'
    · have hσpos : 0 < σ := div_pos hlam (Real.sqrt_pos.2 (by exact_mod_cast hdpos))
      have hsq : (d : ℝ) * σ ^ 2 = lam ^ 2 := by
        rw [hσ, div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
        field_simp
      rw [← e.repr.norm_map, EuclideanSpace.norm_eq]
      calc Real.sqrt (∑ i, ‖e.repr x i‖ ^ 2) < Real.sqrt (∑ _i : Fin d, σ ^ 2) := by
            apply Real.sqrt_lt_sqrt (by positivity)
            apply Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.2 ⟨⟨0, hdpos⟩⟩)
            intro i _
            rw [Real.norm_eq_abs, sq_lt_sq, abs_of_pos hσpos, abs_abs]
            exact hxs i
        _ = lam := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hsq,
              Real.sqrt_sq hlam.le]
  linarith

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PPhaseOnMinus
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Matrix
open scoped ComplexOrder

noncomputable section

theorem PhaseOnMinus.proof (ι : Type*) [Fintype ι] [DecidableEq ι] :
    PhaseOnMinus.Statement ι := by
  intro H P hM c hc
  obtain ⟨hP, hH, hdet, hPHP⟩ := hM
  set A := majInvolution H P with hAdef
  have hHi : H⁻¹ * H = 1 := nonsing_inv_mul H hdet

  have hA2 : A * A = 1 := by
    simp only [hAdef, majInvolution]
    calc H⁻¹ * P * (H⁻¹ * P) = H⁻¹ * (P * H⁻¹ * P) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hPHP, hHi]

  have hPA : P * A = H := by
    simp only [hAdef, majInvolution]; rw [← Matrix.mul_assoc, hPHP]

  have hAh : Aᴴ = P * H⁻¹ := by
    simp only [hAdef, majInvolution, conjTranspose_mul, conjTranspose_nonsing_inv,
      hH.eq, hP.isHermitian.eq]

  let Dm : ℂ → Matrix ι ι ℂ := fun a => ((1 + a) / 2) • (1 : Matrix ι ι ℂ) + ((1 - a) / 2) • A
  have hD : phaseOnMinus H P c = Dm c := by
    simp only [Dm, phaseOnMinus, ← hAdef]
    module
  have hDD : ∀ a b : ℂ, a * b = 1 → Dm a * Dm b = 1 := by
    intro a b hab
    simp only [Dm, add_mul, mul_add, smul_mul_smul_comm, Matrix.one_mul, Matrix.mul_one, hA2]
    have e1 : (1 + a) / 2 * ((1 + b) / 2) + (1 - a) / 2 * ((1 - b) / 2) = 1 := by
      linear_combination (1 / 2 : ℂ) * hab
    have e2 : (1 + a) / 2 * ((1 - b) / 2) + (1 - a) / 2 * ((1 + b) / 2) = 0 := by
      linear_combination (-1 / 2 : ℂ) * hab
    calc _ = ((1 + a) / 2 * ((1 + b) / 2) + (1 - a) / 2 * ((1 - b) / 2)) • (1 : Matrix ι ι ℂ)
          + ((1 + a) / 2 * ((1 - b) / 2) + (1 - a) / 2 * ((1 + b) / 2)) • A := by module
      _ = 1 := by rw [e1, e2]; simp
  have hDA : ∀ a : ℂ, Dm a * A = A * Dm a := by
    intro a
    simp only [Dm, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, Matrix.one_mul,
      Matrix.mul_one]

  have hDP : (Dm c)ᴴ * P = P * Dm (star c) := by
    simp only [Dm, conjTranspose_add, conjTranspose_smul, conjTranspose_one, hAh, add_mul,
      mul_add, smul_mul_assoc, mul_smul_comm, Matrix.one_mul, Matrix.mul_one, hPA]
    simp only [hPHP, star_div₀, star_add, star_sub, star_one]
    norm_num
  have hcc : star c * c = 1 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hc]
    norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hD, hDP, Matrix.mul_assoc, hDD _ _ hcc, Matrix.mul_one]
  · rw [hD, ← hPA, ← Matrix.mul_assoc, hDP, Matrix.mul_assoc, ← hDA c, ← Matrix.mul_assoc,
      Matrix.mul_assoc P, hDD _ _ hcc, Matrix.mul_one]
  · intro u hu
    rw [hD]
    simp only [Dm, add_mulVec, smul_mulVec, one_mulVec, hu]
    module
  · intro u hu
    rw [hD]
    simp only [Dm, add_mulVec, smul_mulVec, one_mulVec, hu]
    module

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PScalingLaw
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped Pointwise ComplexOrder ENNReal

noncomputable section

theorem tsum_orbit_eq_tsum_quotient {G X : Type*} [Group G] [MulAction G X] (b : X) (o : Set X)
    (ho : MulAction.orbit G b = o) (K : Subgroup G) (hK : MulAction.stabilizer G b = K)
    (f : X → ℝ≥0∞) : ∑' p : o, f p = ∑' q : G ⧸ K, f ((Quotient.out q : G) • b) := by
  subst ho hK
  rw [← (MulAction.orbitEquivQuotientStabilizer G b).symm.tsum_eq]
  refine tsum_congr fun q => ?_
  conv_lhs => rw [← QuotientGroup.out_eq' q]
  rw [MulAction.orbitEquivQuotientStabilizer_symm_apply]

section Action

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [NumberField E]

@[reducible] def archMulAction (h : HermitianForm F E W) (v : Basis ι E W) :
    MulAction (archUnitary h v) (InfinitePlace E → ι → ℂ) where
  smul g y w := ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ y w
  one_smul y := by
    funext w
    change (((1 : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ y w = y w
    simp
  mul_smul g k y := by
    funext w
    change (((g * k : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ y w =
      ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ
        (((k : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ y w)
    simp [Matrix.mulVec_mulVec]

attribute [local instance] archMulAction

theorem archSmul_apply {h : HermitianForm F E W} {v : Basis ι E W} (g : archUnitary h v)
    (y : InfinitePlace E → ι → ℂ) (w : InfinitePlace E) :
    (g • y) w = ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ y w := rfl

theorem invApply_eq_smul {h : HermitianForm F E W} {v : Basis ι E W} (g : archUnitary h v)
    (y : InfinitePlace E → ι → ℂ) : invApply g y = g⁻¹ • y := rfl

theorem continuous_len_inv_smul {h : HermitianForm F E W} {v : Basis ι E W} (M : Majorant h v)
    (y : InfinitePlace E → ι → ℂ) : Continuous fun g : archUnitary h v => M.len (g⁻¹ • y) := by
  have hw : ∀ w, Continuous fun g : archUnitary h v => (g⁻¹ • y) w := fun w =>
    (Units.continuous_val.comp ((continuous_apply w).comp
      (continuous_subtype_val.comp continuous_inv))).matrix_mulVec continuous_const
  unfold Majorant.len
  refine Real.continuous_sqrt.comp (continuous_finset_sum _ fun w _ => ?_)
  exact Complex.continuous_re.comp
    (((continuous_star.comp (hw w))).dotProduct (continuous_const.matrix_mulVec (hw w)))

def belowIndicator {h : HermitianForm F E W} {v : Basis ι E W} (M : Majorant h v)
    (y : InfinitePlace E → ι → ℂ) (t : ℝ) : archUnitary h v → ℝ≥0∞ :=
  {g | M.len (g⁻¹ • y) < t}.indicator 1

theorem measurableSet_below {h : HermitianForm F E W} {v : Basis ι E W}
    (M : Majorant h v) (y : InfinitePlace E → ι → ℂ) (t : ℝ) :
    MeasurableSet {g : archUnitary h v | M.len (g⁻¹ • y) < t} :=
  (isOpen_lt (continuous_len_inv_smul M y) continuous_const).measurableSet

theorem measurable_belowIndicator {h : HermitianForm F E W} {v : Basis ι E W}
    (M : Majorant h v) (y : InfinitePlace E → ι → ℂ) (t : ℝ) :
    Measurable (belowIndicator M y t) :=
  measurable_one.indicator (measurableSet_below M y t)

omit [Fintype ι] [DecidableEq ι] in

theorem vecAt_injective (v : Basis ι E W) : Function.Injective (vecAt v) := by
  intro x y hxy
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace E))
  apply v.repr.injective
  ext i
  exact w.embedding.injective (congrFun (congrFun hxy w) i)

variable [NumberField F] [IsTotallyReal F] [IsTotallyComplex E]

theorem archEmbed_smul_vecAt (h : HermitianForm F E W) (v : Basis ι E W) (γ : h.unitaryGroup)
    (x : W) : archEmbed h v γ • vecAt v x = vecAt v (γ • x) := by
  funext w i
  rw [archSmul_apply]
  have hm : (((archEmbed h v γ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) =
      (LinearMap.toMatrix v v ((γ : W ≃ₗ[E] W) : W →ₗ[E] W)).map w.embedding := by
    rw [← unitaryGroupEquivMatrix_apply]
    rfl
  rw [hm]
  change _ = w.embedding (v.repr (((γ : W ≃ₗ[E] W) : W →ₗ[E] W) x) i)
  rw [← LinearMap.toMatrix_mulVec_repr v v, RingHom.map_mulVec]
  rfl

theorem stabilizer_vecAt (h : HermitianForm F E W) (v : Basis ι E W) (La : AddSubgroup W)
    (y : W) : MulAction.stabilizer (archLatticeGroup h v La) (vecAt v y) =
      (vecStabGroup h v La y).subgroupOf (archLatticeGroup h v La) := by
  ext ⟨γ, hγ⟩
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
  obtain ⟨δ, hδ, rfl⟩ := Subgroup.mem_map.1 hγ
  change archEmbed h v δ • vecAt v y = vecAt v y ↔ _
  constructor
  · intro he
    rw [archEmbed_smul_vecAt] at he
    exact Subgroup.mem_map.2 ⟨⟨δ, hδ⟩, MulAction.mem_stabilizer_iff.2 (vecAt_injective v he), rfl⟩
  · rintro ⟨ε, hε, he⟩
    have he' : archEmbed h v (ε : h.unitaryGroup) = archEmbed h v δ := he
    rw [← he', archEmbed_smul_vecAt]
    exact congrArg (vecAt v) (MulAction.mem_stabilizer_iff.1 hε)

theorem ScalingLaw.proof (h : HermitianForm F E W) (v : Basis ι E W) [FiniteDimensional E W]
    (h₁ : UnfoldingIntegral.Statement h v) (h₂ : VectorOrbitsFinite.Statement h)
    (h₃ : UnfoldOrbit.Statement (archUnitary h v))
    (h₄ : DiscreteFundamentalDomain.Statement (archUnitary h v))
    (h₅ : ArchLatticeDiscrete.Statement h v) : ScalingLaw.Statement h v := by
  classical
  intro M μ _ D La VV hLa hVV hiso hstab hC
  set Γ := archLatticeGroup h v La with hΓ
  have : DiscreteTopology Γ := h₅ La hLa.isLattice
  have : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hQc : ∀ K : Subgroup Γ, Countable (Γ ⧸ K) := fun K => QuotientGroup.mk_surjective.countable
  obtain ⟨FD, -, hFD⟩ := h₄ μ Γ inferInstance

  have key : ∀ y ∈ VV, ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ t : ℝ, 0 < t →
      ∫⁻ g in FD, ∑' q : Γ ⧸ (vecStabGroup h v La y).subgroupOf Γ,
        belowIndicator M (vecAt v y) t (((Quotient.out q : Γ) : archUnitary h v)⁻¹ * g) ∂μ =
        C * ENNReal.ofReal (t ^ (2 * finrank ℚ F * (finrank E W - 1))) := by
    intro y hy
    obtain ⟨FD₀, hFD₀, C, -, hCtop, hCt⟩ :=
      h₁ M μ D La y hLa (hVV hy) (hiso y hy).1 (hiso y hy).2
    refine ⟨C, hCtop, fun t ht => ?_⟩
    have hle : vecStabGroup h v La y ≤ Γ := by
      rintro _ ⟨ε, -, rfl⟩
      exact Subgroup.mem_map.2 ⟨ε.1, ε.2, rfl⟩
    have hinv : ∀ γ ∈ vecStabGroup h v La y, ∀ g,
        belowIndicator M (vecAt v y) t (γ * g) = belowIndicator M (vecAt v y) t g := by
      intro γ hγ g
      obtain ⟨ε, hε, rfl⟩ := Subgroup.mem_map.1 hγ
      have hb : ((archEmbed h v).comp (latticeStab h La).subtype ε) • vecAt v y = vecAt v y := by
        change archEmbed h v (ε : h.unitaryGroup) • vecAt v y = vecAt v y
        rw [archEmbed_smul_vecAt]
        exact congrArg (vecAt v) (MulAction.mem_stabilizer_iff.1 hε)
      have hb' := (inv_smul_eq_iff.2 hb.symm).symm
      simp only [belowIndicator, Set.indicator_apply, Set.mem_setOf_eq, _root_.mul_inv_rev, mul_smul,
        ← hb', Pi.one_apply]
    rw [h₃ μ Γ _ hle FD FD₀ hFD hFD₀ _ (measurable_belowIndicator M (vecAt v y) t) hinv,
      belowIndicator, lintegral_indicator_one (measurableSet_below M _ t),
      Measure.restrict_apply (measurableSet_below M _ t), Set.inter_comm]
    exact hCt t ht
  choose! Cf hCf hCeq using key

  obtain ⟨S, hSV, hScov⟩ := h₂ D La VV hLa hVV hiso hstab hC
  let T : Finset (Set (InfinitePlace E → ι → ℂ)) :=
    S.image fun y => MulAction.orbit Γ (vecAt v y)
  have hT : ∀ o ∈ T, ∃ y, y ∈ S ∧ MulAction.orbit Γ (vecAt v y) = o := fun o ho => by
    obtain ⟨y, hy, e⟩ := Finset.mem_image.1 ho
    exact ⟨y, hy, e⟩
  choose! Y hYS hYo using hT
  have hP : vecAt v '' VV = ⋃ o ∈ (T : Set (Set (InfinitePlace E → ι → ℂ))), o := by
    ext p
    simp only [Set.mem_iUnion, Finset.mem_coe, exists_prop]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨y, hyS, γ, hγ, rfl⟩ := hScov x hx
      refine ⟨MulAction.orbit Γ (vecAt v y), Finset.mem_image.2 ⟨y, hyS, rfl⟩, ?_⟩
      rw [← archEmbed_smul_vecAt]
      exact ⟨⟨archEmbed h v γ, Subgroup.mem_map.2 ⟨γ, hγ, rfl⟩⟩, rfl⟩
    · rintro ⟨o, ho, hp⟩
      rw [← hYo o ho] at hp
      obtain ⟨⟨γ', hγ'⟩, rfl⟩ := hp
      obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.1 hγ'
      exact ⟨γ • Y o, hstab γ hγ _ (hSV (hYS o ho)), (archEmbed_smul_vecAt h v γ (Y o)).symm⟩
  have hdisj : (T : Set (Set (InfinitePlace E → ι → ℂ))).PairwiseDisjoint fun o => o := by
    intro o₁ h₁' o₂ h₂' hne
    refine Set.disjoint_left.2 fun p hp1 hp2 => hne ?_
    rw [← hYo o₁ h₁'] at hp1 ⊢
    rw [← hYo o₂ h₂'] at hp2 ⊢
    exact (MulAction.orbit_eq_iff.2 hp1).symm.trans (MulAction.orbit_eq_iff.2 hp2)

  have hcount : ∀ g t, countBelow M VV g t = ∑ o ∈ T,
      ∑' q : Γ ⧸ (vecStabGroup h v La (Y o)).subgroupOf Γ,
        belowIndicator M (vecAt v (Y o)) t (((Quotient.out q : Γ) : archUnitary h v)⁻¹ * g) := by
    intro g t
    have hPA : vecAt v '' {x ∈ VV | M.len (invApply g (vecAt v x)) < t} =
        vecAt v '' VV ∩ {p | M.len (g⁻¹ • p) < t} := by
      ext p
      constructor
      · rintro ⟨x, ⟨hx, hxt⟩, rfl⟩
        exact ⟨⟨x, hx, rfl⟩, hxt⟩
      · rintro ⟨⟨x, hx, rfl⟩, hxt⟩
        exact ⟨x, ⟨hx, hxt⟩, rfl⟩
    have h1 : countBelow M VV g t =
        ∑' p : (vecAt v '' VV : Set _), {p | M.len (g⁻¹ • p) < t}.indicator 1 (p : _) := by
      rw [countBelow, ← (vecAt_injective v).encard_image, hPA, ← ENNReal.tsum_set_one,
        tsum_subtype (vecAt v '' VV), Set.indicator_indicator, ← tsum_subtype]
      rfl
    rw [h1, hP, ENNReal.tsum_biUnion' hdisj]
    refine (Finset.tsum_subtype' T fun o : Set (InfinitePlace E → ι → ℂ) =>
      ∑' p : o, {p | M.len (g⁻¹ • p) < t}.indicator (1 : (InfinitePlace E → ι → ℂ) → ℝ≥0∞) (p : InfinitePlace E → ι → ℂ)).trans ?_
    refine Finset.sum_congr rfl fun o ho => ?_
    rw [tsum_orbit_eq_tsum_quotient (vecAt v (Y o)) o (hYo o ho) _ (stabilizer_vecAt h v La (Y o))]
    refine tsum_congr fun q => ?_
    simp only [belowIndicator, Set.indicator_apply, Set.mem_setOf_eq, _root_.mul_inv_rev, inv_inv,
      mul_smul]
    rfl
  have hm : ∀ t : ℝ, 0 < t → massBelow M μ FD VV t =
      ∑ o ∈ T, Cf (Y o) * ENNReal.ofReal (t ^ (2 * finrank ℚ F * (finrank E W - 1))) := by
    intro t ht
    rw [massBelow, lintegral_congr fun g => hcount g t, lintegral_finset_sum]
    · exact Finset.sum_congr rfl fun o ho => hCeq (Y o) (hSV (hYS o ho)) t ht
    · exact fun o _ => @Measurable.ennreal_tsum _ _ _ (hQc _) _ fun q =>
        (measurable_belowIndicator M _ t).comp (measurable_const_mul _)
  refine ⟨FD, hFD, fun t ht => ⟨?_, fun θ hθ => ?_⟩⟩
  · rw [hm t ht]
    exact ENNReal.sum_lt_top.2 fun o ho =>
      ENNReal.mul_lt_top (hCf _ (hSV (hYS o ho))) ENNReal.ofReal_lt_top
  · rw [hm (θ * t) (mul_pos hθ ht), hm t ht, Finset.mul_sum]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [mul_pow, ENNReal.ofReal_mul (pow_nonneg hθ.le _)]
    ring

end Action

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PShortVectorIsotropic
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem ShortVectorIsotropic.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (h₁ : HermAtPlace.Statement h v) (h₂ : GramAtData.Statement h v)
    (h₃ : ArchInvariant.Statement h v) (h₄ : MajorantBound.Statement ι)
    (h₅ : LenSq.Statement h v) (h₆ : IntegerSmallAtPlaces.Statement E) :
    ShortVectorIsotropic.Statement h v := by
  intro M D La g x hLa hx hlen
  apply h₆ _ (hLa.integral x hx x hx)
  intro w
  set y := vecAt v x
  set z := invApply g y
  have hP : IsMajorantOf (gramAt h v w) (M.P w) :=
    ⟨M.posDef w, (h₂ w).1, (h₂ w).2, M.siegel w⟩
  obtain ⟨hnn, hsq⟩ := h₅ M z
  have hlen0 : 0 ≤ M.len z := Real.sqrt_nonneg _
  have hsq1 : M.len z ^ 2 < 1 := by nlinarith
  have hterm : (star (z w) ⬝ᵥ (M.P w *ᵥ z w)).re ≤ M.len z ^ 2 := by
    rw [hsq]
    exact Finset.single_le_sum (f := fun w' => (star (z w') ⬝ᵥ (M.P w' *ᵥ z w')).re)
      (fun w' _ => hnn w') (Finset.mem_univ w)
  have hform : w.embedding (h.toSesq x x) = star (z w) ⬝ᵥ (gramAt h v w *ᵥ z w) := by
    rw [h₁ w x x, h₃ g y y w]
  rw [← InfinitePlace.norm_embedding_eq, hform]
  exact lt_of_le_of_lt ((h₄ _ _ hP (z w)).trans hterm) hsq1

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PVecAtNeZero
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Module NumberField

variable {E : Type*} [Field E] {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*}

theorem VecAtNeZero.proof (v : Basis ι E W) : VecAtNeZero.Statement v := by
  intro x hx w hw
  apply hx
  apply v.repr.injective
  ext i
  have h := congrFun hw i
  simp only [vecAt, Pi.zero_apply] at h
  simpa using (map_eq_zero_iff w.embedding w.embedding.injective).mp h

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PWeightedNormSq
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField

theorem WeightedNormSq.proof (E : Type*) [Field E] [NumberField E] : WeightedNormSq.Statement E := by
  intro c hc a
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Fin.sum_univ_two]
  simp only [weightedEmbed, AddMonoidHom.coe_mk, ZeroHom.coe_mk, PiLp.toLp_apply, Real.norm_eq_abs,
    sq_abs, show ((1 : Fin 2) = 0) = False from by decide, ↓reduceIte]
  rw [mul_pow, mul_pow, Real.sq_sqrt (hc w), Complex.sq_norm, Complex.normSq_apply]
  ring

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

