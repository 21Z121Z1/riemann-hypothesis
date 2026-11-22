import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0028
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0014
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0032
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0013
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0027
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0029
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0030

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntCastTraceEqTraceQuotientOfMemStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intCast_trace_eq_trace_quotient_of_mem' : ∀ (L : Type) [Field L] [NumberField L] (l b : ℕ) [Fact l.Prime] (I Q : Ideal (𝓞 L)), I ⊔ Q = ⊤ → I * Q = Ideal.span {((l ^ b : ℕ) : 𝓞 L)} → ∀ [Algebra (ZMod (l ^ b)) (𝓞 L ⧸ I)] (x : 𝓞 L), x ∈ Q → ((Algebra.trace ℤ (𝓞 L) x : ℤ) : ZMod (l ^ b)) = Algebra.trace (ZMod (l ^ b)) (𝓞 L ⧸ I) (Ideal.Quotient.mk I x) := by
  first | exact @GlobalTheory.intCast_trace_eq_trace_quotient_of_mem | exact GlobalTheory.intCast_trace_eq_trace_quotient_of_mem | (intros; apply GlobalTheory.intCast_trace_eq_trace_quotient_of_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralSumIndicatorTranslate
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.CosetIntegral

theorem integral_sum_indicator_translate {G ι : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (m : Measure G)
    [m.IsMulRightInvariant] (H : Set G) (hH : IsOpen H) (hm : m H = 1) (T : Finset ι)
    (r : ι → G) (c : ι → ℂ) :
    ∫ x, ∑ q ∈ T, ((fun y => y * (r q)⁻¹) ⁻¹' H).indicator (fun _ => c q) x ∂m
      = ∑ q ∈ T, c q := by
  have hmeas : ∀ q, MeasurableSet ((fun y => y * (r q)⁻¹) ⁻¹' H) := fun q =>
    (hH.preimage (continuous_mul_right _)).measurableSet
  have hmq : ∀ q, m ((fun y => y * (r q)⁻¹) ⁻¹' H) = 1 := fun q => by
    rw [measure_preimage_mul_right, hm]
  rw [integral_finset_sum]
  · refine Finset.sum_congr rfl fun q _ => ?_
    rw [integral_indicator_const _ (hmeas q), measureReal_def, hmq q]
    simp
  · intro q _
    exact (integrable_indicator_iff (hmeas q)).2 (integrableOn_const (by rw [hmq q]; simp))

theorem integral_eq_of_coset_support
    (R S : Type) [Group R] [TopologicalSpace R] [IsTopologicalGroup R] [LocallyCompactSpace R]
    [T2Space R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R] [Group S]
    [TopologicalSpace S] [IsTopologicalGroup S] [MeasurableSpace S] [BorelSpace S]
    (i : S →* R) (hi : Topology.IsClosedEmbedding i) (μ : Measure R) (ν : Measure S)
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant] [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
    (R₀ : Subgroup R) (hR₀o : IsOpen (R₀ : Set R)) (_hR₀c : IsCompact (R₀ : Set R))
    (hμ : μ R₀ = 1) (hν : ν (i ⁻¹' R₀) = 1) (h : R → ℂ)
    (hinv : ∀ k ∈ R₀, ∀ g, h (k * g) = h g)
    (hsupp : ∀ g, h g ≠ 0 → ∃ k ∈ R₀, ∃ s, g = k * i s)
    (hcs : HasCompactSupport (fun s => h (i s))) :
    ∫ g, h g ∂μ = ∫ s, h (i s) ∂ν := by
  classical
  let S₀ : Subgroup S := R₀.comap i
  have hS₀o : IsOpen (i ⁻¹' (R₀ : Set R)) := hR₀o.preimage hi.continuous
  have hconst : ∀ g r, g * (i r)⁻¹ ∈ R₀ → h (i r) = h g := by
    intro g r hg
    have := hinv _ hg (i r)
    simpa using this.symm
  let U : S → Set S := fun s => (fun x => x * s⁻¹) ⁻¹' (i ⁻¹' (R₀ : Set R))
  have hUo : ∀ s, IsOpen (U s) := fun s => hS₀o.preimage (continuous_mul_right _)
  obtain ⟨t, ht⟩ := hcs.isCompact.elim_finite_subcover U hUo
    (fun x _ => Set.mem_iUnion.2 ⟨x, by simp [U, R₀.one_mem]⟩)
  let mk : S → Quotient (QuotientGroup.rightRel S₀) := fun s => Quotient.mk _ s
  let T := t.image mk
  have hrel : ∀ a b : S, mk a = mk b ↔ i b * (i a)⁻¹ ∈ R₀ := fun a b => by
    simp only [mk, Quotient.eq, QuotientGroup.rightRel_apply, S₀, Subgroup.mem_comap,
      map_mul, map_inv]
  have hout : ∀ q, mk q.out = q := fun q => Quotient.out_eq q
  have hsuppT : ∀ x, h (i x) ≠ 0 → mk x ∈ T := by
    intro x hx
    have hx' : x ∈ tsupport (fun s => h (i s)) := subset_tsupport _ hx
    obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.1 (ht hx')
    refine Finset.mem_image.2 ⟨s, hs, (hrel s x).2 ?_⟩
    simpa [U] using hxs
  have hrep : ∀ x, h (i (mk x).out) = h (i x) := by
    intro x
    apply hconst
    exact (hrel _ x).1 (hout _)

  have hR : (fun g => h g) = fun g => ∑ q ∈ T,
      ((fun y => y * (i q.out)⁻¹) ⁻¹' (R₀ : Set R)).indicator (fun _ => h (i q.out)) g := by
    funext g
    by_cases hg : h g = 0
    · rw [hg]
      symm
      refine Finset.sum_eq_zero fun q _ => ?_
      by_cases hm : g ∈ ((fun y => y * (i q.out)⁻¹) ⁻¹' (R₀ : Set R))
      · rw [Set.indicator_of_mem hm, hconst g _ hm, hg]
      · rw [Set.indicator_of_notMem hm]
    · obtain ⟨k, hk, s, rfl⟩ := hsupp g hg
      have hs : h (i s) ≠ 0 := by rwa [hinv k hk] at hg
      have hmem : ∀ q, (k * i s ∈ ((fun y => y * (i q.out)⁻¹) ⁻¹' (R₀ : Set R))) ↔ mk s = q := by
        intro q
        have e : mk s = q ↔ i s * (i q.out)⁻¹ ∈ R₀ := by rw [← hrel q.out s, hout q, eq_comm]
        rw [e]
        simp only [Set.mem_preimage, SetLike.mem_coe, mul_assoc]
        exact Subgroup.mul_mem_cancel_left R₀ hk
      simp only [Set.indicator, hmem, Finset.sum_ite_eq, if_pos (hsuppT s hs), hrep, hinv k hk]
  have hS : (fun x => h (i x)) = fun x => ∑ q ∈ T,
      ((fun y => y * q.out⁻¹) ⁻¹' (i ⁻¹' (R₀ : Set R))).indicator (fun _ => h (i q.out)) x := by
    funext x
    have hmem : ∀ q, x ∈ ((fun y => y * q.out⁻¹) ⁻¹' (i ⁻¹' (R₀ : Set R))) ↔ mk x = q := by
      intro q
      have e : mk x = q ↔ i x * (i q.out)⁻¹ ∈ R₀ := by rw [← hrel q.out x, hout q, eq_comm]
      rw [e]
      simp
    simp only [Set.indicator, hmem, Finset.sum_ite_eq]
    split_ifs with hx
    · rw [hrep]
    · by_contra hne
      exact hx (hsuppT x hne)
  rw [hR, hS, integral_sum_indicator_translate μ _ hR₀o hμ,
    integral_sum_indicator_translate ν _ hS₀o hν]

end GlobalTheory.CosetIntegral
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvariantRightInverseOfRightInverse
section
open Matrix

namespace GlobalTheory

theorem invariant_right_inverse_of_right_inverse :
    ∀ (L : Type) [CommRing L], IsField L → ∀ (G : Type) (act : G → L →+* L) (N b : Type)
      [Fintype N] [DecidableEq N] [Fintype b] [DecidableEq b] (κ : Matrix b N L)
      (Y : Matrix N b L), κ * Y = 1 → (∀ g, κ.map (act g) = κ) →
      ∃ Λ : Matrix N b L, κ * Λ = 1 ∧ ∀ g, Λ.map (act g) = Λ := by
  first
  | exact @_root_.GlobalTheory.InvariantRightInverse.exists_invariant_rightInverse
  | exact _root_.GlobalTheory.InvariantRightInverse.exists_invariant_rightInverse
  | (apply _root_.GlobalTheory.InvariantRightInverse.exists_invariant_rightInverse <;> assumption)
  | (intros; apply _root_.GlobalTheory.InvariantRightInverse.exists_invariant_rightInverse <;> assumption)
  | (intros; apply @_root_.GlobalTheory.InvariantRightInverse.exists_invariant_rightInverse <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.InvariantRightInverse.exists_invariant_rightInverse ..)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvariantSchwartzMemSpanLatticeIndicators
section
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory.GenUnr

variable {O : Type} [CommRing O]

noncomputable def red (I : Ideal O) (r : ℕ) : (Fin r → O) →ₗ[O] (Fin r → O ⧸ I) :=
  ((Ideal.Quotient.mkₐ O I).toLinearMap).compLeft (Fin r)

noncomputable def rowSpan {n r : ℕ} (I : Ideal O) (z : Matrix (Fin n) (Fin r) O) :
    Submodule O (Fin r → O ⧸ I) :=
  Submodule.span O (Set.range fun i => red I r (z i))

end GlobalTheory.GenUnr

namespace GlobalTheory.GenUnr
open Matrix
variable {O : Type} [CommRing O]

end GlobalTheory.GenUnr

namespace GlobalTheory.GenUnr
open Matrix

end GlobalTheory.GenUnr

namespace GlobalTheory.GenUnr
open Matrix

end GlobalTheory.GenUnr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBaseChangeLatticeOfBasisAfterExtensionStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isBaseChange_lattice_of_basis_after_extension : ∀ (S A EE O W RW D Y : Type) [CommRing S] [CommRing A] [CommRing EE] [CommRing O] [CommRing W] [CommRing RW] [Algebra O A] [Algebra A EE] [Algebra O EE] [IsScalarTower O A EE] [Algebra O RW] [AddCommGroup D] [Module EE D] [Module A D] [IsScalarTower A EE D] [AddCommGroup Y] [Module RW Y] (a : S →+* A) (ι : EE →ₐ[O] RW) (c : W →+* RW) (jD : D →+ Y), Function.Injective ι → (∀ e, IsUnit (ι e) → IsUnit e) → (∀ (e : EE) (x : D), jD (e • x) = ι e • jD x) → (∀ s, ι (algebraMap A EE (a s)) ∈ Set.range c) → ∀ (d r : ℕ) (o : Fin d → O), (∀ e : EE, ∃ e' : Fin d → EE, (∀ j, ι (e' j) ∈ Set.range c) ∧ e = ∑ j, o j • e' j) → Nonempty (Module.Basis (Fin r) EE D) → ∀ (q : ℕ) (x : Fin q → D), q = d * r → (∀ y : Y, ∃! w : Fin q → W, y = ∑ i, c (w i) • jD (x i)) → ∀ N : Submodule A D, (∀ y, y ∈ N ↔ ∃ s : Fin q → S, y = ∑ i, a (s i) • x i) → IsBaseChange EE N.subtype := by
  first | exact @GlobalTheory.isBaseChange_subtype_of_basis_after_extension | exact GlobalTheory.isBaseChange_subtype_of_basis_after_extension | (intros; apply GlobalTheory.isBaseChange_subtype_of_basis_after_extension <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCompactIntMatrix
section
open Matrix MeasureTheory Topology

noncomputable section

namespace GlobalTheory.JR.MeasExist

theorem isOpen_intMatrix (r : ℕ) (k : Type) [NontriviallyNormedField k] [IsUltrametricDist k] :
    IsOpen {A : Matrix (Fin r) (Fin r) k | ∀ i j, ‖A i j‖ ≤ 1} := by
  simp only [Set.setOf_forall]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  have h : IsOpen (Metric.closedBall (0 : k) 1) := IsUltrametricDist.isOpen_closedBall _ one_ne_zero
  have hc : Continuous fun A : Matrix (Fin r) (Fin r) k => A i j := by fun_prop
  convert h.preimage hc using 1
  ext A; simp

theorem isCompact_intMatrix (r : ℕ) (k : Type) [NontriviallyNormedField k] [LocallyCompactSpace k] :
    IsCompact {A : Matrix (Fin r) (Fin r) k | ∀ i j, ‖A i j‖ ≤ 1} := by
  haveI : ProperSpace k := ProperSpace.of_locallyCompactSpace k
  have h : IsCompact (Set.pi Set.univ fun _ : Fin r => Set.pi Set.univ fun _ : Fin r =>
      Metric.closedBall (0 : k) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have e : {A : Matrix (Fin r) (Fin r) k | ∀ i j, ‖A i j‖ ≤ 1} = (Set.pi Set.univ fun _ : Fin r =>
      Set.pi Set.univ fun _ : Fin r => Metric.closedBall (0 : k) 1) := by
    ext A
    exact ⟨fun H i _ j _ => mem_closedBall_zero_iff.2 (H i j),
      fun H i j => mem_closedBall_zero_iff.1 (H i trivial j trivial)⟩
  rw [e]; exact h

theorem isOpen_glO (r : ℕ) (k : Type) [NontriviallyNormedField k] [IsUltrametricDist k] :
    IsOpen (glO r k) := by
  have h1 := (isOpen_intMatrix r k).preimage (Units.continuous_val (M := Matrix (Fin r) (Fin r) k))
  have h2 := (isOpen_intMatrix r k).preimage (Units.continuous_coe_inv (M := Matrix (Fin r) (Fin r) k))
  convert h1.inter h2 using 1
  ext g
  simp only [glO, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, forall_and]

theorem isCompact_glO (r : ℕ) (k : Type) [NontriviallyNormedField k] [LocallyCompactSpace k] :
    IsCompact (glO r k) := by
  have hK := isCompact_intMatrix r k
  have h := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin r) (Fin r) k)).isCompact_preimage
    (hK.prod (hK.image MulOpposite.continuous_op))
  convert h using 1
  ext g
  simp only [glO, Set.mem_setOf_eq, Set.mem_preimage, forall_and, Units.embedProduct_apply, Set.mem_prod,
    (MulOpposite.op_injective).mem_set_image]

theorem one_mem_intMatrix (r : ℕ) (k : Type) [NormedField k] (i j : Fin r) :
    ‖(1 : Matrix (Fin r) (Fin r) k) i j‖ ≤ 1 := by
  rw [Matrix.one_apply]; split_ifs <;> simp

theorem isOpen_uO (r : ℕ) (k : Type) [NontriviallyNormedField k] [IsUltrametricDist k] [StarRing k] :
    IsOpen (uO r k) :=
  (isOpen_intMatrix r k).preimage continuous_subtype_val

theorem isCompact_uO (r : ℕ) (k : Type) [NontriviallyNormedField k] [LocallyCompactSpace k] [StarRing k]
    [ContinuousStar k] : IsCompact (uO r k) :=
  (isClosed_unitary (R := Matrix (Fin r) (Fin r) k)).isClosedEmbedding_subtypeVal.isCompact_preimage
    (isCompact_intMatrix r k)

@[to_additive exists_addHaar_eq_one  ]
theorem exists_haar_eq_one {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] {K : Set G} (hc : IsCompact K) (ho : IsOpen K) (hne : K.Nonempty) :
    ∃ μ : Measure G, μ.IsHaarMeasure ∧ μ K = 1 := by
  let K₀ : TopologicalSpace.PositiveCompacts G := ⟨⟨K, hc⟩, by rwa [TopologicalSpace.Compacts.carrier_eq_coe, TopologicalSpace.Compacts.coe_mk, ho.interior_eq]⟩
  exact ⟨Measure.haarMeasure K₀, inferInstance, Measure.haarMeasure_self (K₀ := K₀)⟩

theorem nonempty_meas (r : ℕ) (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [h : Unram F E] : Nonempty (Meas r F E) := by
  haveI := h.ultraF
  haveI := h.ultraE
  haveI := h.lcF
  haveI := h.lcE
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : NormedStarGroup E := ⟨fun y => (h.norm_star y).le⟩
  borelize (GL (Fin r) F) (↥(Matrix.unitaryGroup (Fin r) E)) F E
  obtain ⟨μG, hG, vG⟩ := exists_haar_eq_one (isCompact_glO r F) (isOpen_glO r F)
    ⟨1, fun i j => ⟨one_mem_intMatrix r F i j, by simpa using one_mem_intMatrix r F i j⟩⟩
  obtain ⟨μU, hU, vU⟩ := exists_haar_eq_one (isCompact_uO r E) (isOpen_uO r E)
    ⟨1, fun i j => one_mem_intMatrix r E i j⟩
  obtain ⟨μF, hF, vF⟩ := exists_addHaar_eq_one (isCompact_closedBall (0 : F) 1)
    (IsUltrametricDist.isOpen_closedBall _ one_ne_zero) ⟨0, by simp⟩
  obtain ⟨μE, hE, vE⟩ := exists_addHaar_eq_one (isCompact_closedBall (0 : E) 1)
    (IsUltrametricDist.isOpen_closedBall _ one_ne_zero) ⟨0, by simp⟩
  exact ⟨Meas.mk μG μU μF μE hG hU hF hE vG vU vF vE⟩

end GlobalTheory.JR.MeasExist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDomainClosedDiscGaugeCompletionOfEquivNorm
section
open scoped NNReal

namespace GlobalTheory.BSP.DiscDomain

variable {l : ℕ} [hl : Fact l.Prime] {A : Type} [CommRing A] {u : A} {ρ : ℝ≥0}

private theorem gauge_mul_le_of_mem_ball (y z : PreDisc l u ρ) {s : ℝ} (hs : 0 < s) (hz : z ∈ ball l u ρ s) :
    gauge l u ρ (y * z) ≤ gauge l u ρ y * s := by
  have key : ∀ r, gauge l u ρ y < r → gauge l u ρ (y * z) / s ≤ r := by
    intro r hr
    have hr0 : 0 < r := (gauge_nonneg l u ρ y).trans_lt hr
    rw [div_le_iff₀ hs]
    exact gauge_le l u ρ (mul_pos hr0 hs)
      (mul_mem_ball l u ρ hr0.le (mem_ball_of_gauge_lt l u ρ hr) hz)
  rw [← div_le_iff₀ hs]
  exact le_of_forall_gt_imp_ge_of_dense key

private theorem algebraMap_natCast_mem_ball_inv (hl0 : (0 : ℝ) < l) :
    algebraMap A (PreDisc l u ρ) (l : A) ∈ ball l u ρ ((l : ℝ)⁻¹) := by
  refine Submodule.subset_span ?_
  rw [monos, Set.mem_setOf_eq]
  refine ⟨1, 0, 0, ?_, ?_⟩
  · rw [pow_zero, pow_zero, pow_one, one_mul, inv_mul_cancel₀ hl0.ne']
  · simp

private theorem invSelf_mem_ball :
    (IsLocalization.Away.invSelf (l : A) : PreDisc l u ρ) ∈ ball l u ρ (l : ℝ) := by
  refine Submodule.subset_span ?_
  rw [monos, Set.mem_setOf_eq]
  refine ⟨0, 0, 1, ?_, ?_⟩
  · simp
  · simp

theorem norm_mul_l (y : PreDisc l u ρ) :
    ‖y * algebraMap A (PreDisc l u ρ) (l : A)‖ * l = ‖y‖ := by
  have hl0 : (0 : ℝ) < l := by exact_mod_cast hl.out.pos
  rw [norm_preDisc, norm_preDisc]
  apply le_antisymm
  · have h := gauge_mul_le_of_mem_ball y _ (inv_pos.mpr hl0) (algebraMap_natCast_mem_ball_inv (u := u) (ρ := ρ) hl0)
    calc gauge l u ρ (y * algebraMap A (PreDisc l u ρ) (l : A)) * l
        ≤ gauge l u ρ y * (l : ℝ)⁻¹ * l := mul_le_mul_of_nonneg_right h hl0.le
      _ = gauge l u ρ y := by rw [mul_assoc, inv_mul_cancel₀ hl0.ne', mul_one]
  · have h := gauge_mul_le_of_mem_ball (y * algebraMap A (PreDisc l u ρ) (l : A)) _ hl0
      (invSelf_mem_ball (u := u) (ρ := ρ))
    rwa [mul_assoc, IsLocalization.Away.mul_invSelf, mul_one] at h

theorem norm_mul_l_pow (n : ℕ) (y : PreDisc l u ρ) :
    ‖y * algebraMap A (PreDisc l u ρ) (l : A) ^ n‖ * (l : ℝ) ^ n = ‖y‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := norm_mul_l (y * algebraMap A (PreDisc l u ρ) (l : A) ^ n)
    calc ‖y * algebraMap A (PreDisc l u ρ) (l : A) ^ (n + 1)‖ * (l : ℝ) ^ (n + 1)
        = ‖y * algebraMap A (PreDisc l u ρ) (l : A) ^ n * algebraMap A (PreDisc l u ρ) (l : A)‖ * l
            * (l : ℝ) ^ n := by
          rw [pow_succ, pow_succ, mul_assoc y]; ring
      _ = ‖y‖ := by rw [h, ih]

private theorem exists_mul_pow_eq_algebraMap (p : PreDisc l u ρ) :
    ∃ (a : A) (k : ℕ), p * algebraMap A (PreDisc l u ρ) (l : A) ^ k = algebraMap A (PreDisc l u ρ) a := by
  obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj (Submonoid.powers (l : A)) p
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
  refine ⟨a, k, ?_⟩
  rw [← map_pow, hk]
  exact h

private theorem norm_ofPre_eq_mul_pow {p : PreDisc l u ρ} {a : A} {k : ℕ}
    (h : p * algebraMap A (PreDisc l u ρ) (l : A) ^ k = algebraMap A (PreDisc l u ρ) a) :
    ‖ofPre l u ρ p‖ = ‖toDisc l u ρ a‖ * (l : ℝ) ^ k := by
  have e : ‖toDisc l u ρ a‖ = ‖algebraMap A (PreDisc l u ρ) a‖ := by
    rw [toDisc, RingHom.comp_apply, norm_ofPre, norm_preDisc]
  rw [e, ← h, norm_mul_l_pow, norm_ofPre, norm_preDisc]

private theorem sq_mul_norm_mul_norm_le_norm_mul (N : A → ℝ) (c : ℝ) (hc : 0 < c) (hmul : ∀ x y, N (x * y) = N x * N y)
    (hle : ∀ x, N x ≤ ‖toDisc l u ρ x‖) (hge : ∀ x, c * ‖toDisc l u ρ x‖ ≤ N x) (p q : PreDisc l u ρ) :
    c ^ 2 * (‖ofPre l u ρ p‖ * ‖ofPre l u ρ q‖) ≤ ‖ofPre l u ρ p * ofPre l u ρ q‖ := by
  obtain ⟨a, k, hp⟩ := exists_mul_pow_eq_algebraMap p
  obtain ⟨b, m, hq⟩ := exists_mul_pow_eq_algebraMap q
  have hpq : p * q * algebraMap A (PreDisc l u ρ) (l : A) ^ (k + m) =
      algebraMap A (PreDisc l u ρ) (a * b) := by
    rw [map_mul, ← hp, ← hq, pow_add]; ring
  rw [← map_mul, norm_ofPre_eq_mul_pow hp, norm_ofPre_eq_mul_pow hq, norm_ofPre_eq_mul_pow hpq, pow_add]
  have hab : N a * N b ≤ ‖toDisc l u ρ (a * b)‖ := by rw [← hmul]; exact hle _
  have h0 : 0 ≤ c * ‖toDisc l u ρ a‖ := mul_nonneg hc.le (norm_nonneg _)
  have h1 : 0 ≤ c * ‖toDisc l u ρ b‖ := mul_nonneg hc.le (norm_nonneg _)
  have key : c * ‖toDisc l u ρ a‖ * (c * ‖toDisc l u ρ b‖) ≤ ‖toDisc l u ρ (a * b)‖ :=
    (mul_le_mul (hge a) (hge b) h1 (h0.trans (hge a))).trans hab
  have hpow : 0 ≤ (l : ℝ) ^ k * (l : ℝ) ^ m := by positivity
  calc c ^ 2 * (‖toDisc l u ρ a‖ * (l : ℝ) ^ k * (‖toDisc l u ρ b‖ * (l : ℝ) ^ m))
      = c * ‖toDisc l u ρ a‖ * (c * ‖toDisc l u ρ b‖) * ((l : ℝ) ^ k * (l : ℝ) ^ m) := by ring
    _ ≤ ‖toDisc l u ρ (a * b)‖ * ((l : ℝ) ^ k * (l : ℝ) ^ m) := mul_le_mul_of_nonneg_right key hpow

theorem isDomain_disc (l : ℕ) [hl : Fact l.Prime] (A : Type) [CommRing A] (u : A) (ρ : ℝ≥0) (N : A → ℝ) (c : ℝ)
    (hc : 0 < c) (hmul : ∀ x y, N (x * y) = N x * N y) (_hadd : ∀ x y, N (x + y) ≤ max (N x) (N y))
    (hNl : N (l : A) = (l : ℝ)⁻¹) (hle : ∀ x, N x ≤ ‖toDisc l u ρ x‖) (hge : ∀ x, c * ‖toDisc l u ρ x‖ ≤ N x) :
    IsDomain (Disc l u ρ) ∧ ∀ x y : Disc l u ρ, c ^ 2 * (‖x‖ * ‖y‖) ≤ ‖x * y‖ := by
  have hmain : ∀ x y : Disc l u ρ, c ^ 2 * (‖x‖ * ‖y‖) ≤ ‖x * y‖ := by
    intro x y
    refine (denseRange_ofPre l u ρ).induction_on₂
      (p := fun x y : Disc l u ρ => c ^ 2 * (‖x‖ * ‖y‖) ≤ ‖x * y‖) ?_ ?_ x y
    · exact isClosed_le (by fun_prop) (by fun_prop)
    · intro p q
      exact sq_mul_norm_mul_norm_le_norm_mul N c hc hmul hle hge p q
  have hlinv : (0 : ℝ) < (l : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hl.out.pos)
  have hne : toDisc l u ρ (l : A) ≠ 0 := by
    intro h
    have h' := hle (l : A)
    rw [h, norm_zero, hNl] at h'
    linarith
  haveI : Nontrivial (Disc l u ρ) := ⟨⟨_, _, hne⟩⟩
  haveI : NoZeroDivisors (Disc l u ρ) := by
    refine ⟨fun {x y} hxy => ?_⟩
    have h := hmain x y
    rw [hxy, norm_zero] at h
    have hc2 : 0 < c ^ 2 := by positivity
    have hn : ‖x‖ * ‖y‖ ≤ 0 := by nlinarith [mul_nonneg (norm_nonneg x) (norm_nonneg y)]
    rcases mul_eq_zero.mp (le_antisymm hn (mul_nonneg (norm_nonneg _) (norm_nonneg _))) with h | h
    · exact Or.inl (norm_eq_zero.mp h)
    · exact Or.inr (norm_eq_zero.mp h)
  exact ⟨NoZeroDivisors.to_isDomain (α := Disc l u ρ), hmain⟩

end GlobalTheory.BSP.DiscDomain
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLatComap
section
noncomputable section
namespace GlobalTheory.LatticeComap
open GlobalTheory.PhiGam

section
variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module (LaurentSeries k) V]
  [Module (PowerSeries k) V] [IsScalarTower (PowerSeries k) (LaurentSeries k) V]

theorem exists_pow_smul_mem {N : Submodule (PowerSeries k) V}
    (hN : Submodule.span (LaurentSeries k) (N : Set V) = ⊤) (x : V) :
    ∃ m : ℕ, ((PowerSeries.X : PowerSeries k) ^ m) • x ∈ N := by
  have hx : x ∈ Submodule.span (LaurentSeries k) (N : Set V) := by rw [hN]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨0, by simpa using hy⟩
  | zero => exact ⟨0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨m1, h1⟩ := hy
    obtain ⟨m2, h2⟩ := hz
    refine ⟨m1 + m2, ?_⟩
    rw [smul_add]
    refine N.add_mem ?_ ?_
    · rw [pow_add, mul_comm, mul_smul]; exact N.smul_mem _ h1
    · rw [pow_add, mul_smul]; exact N.smul_mem _ h2
  | smul a y _ hy =>
    obtain ⟨m, hm⟩ := hy
    obtain ⟨⟨p, s⟩, hps⟩ := IsLocalization.surj (Submonoid.powers (PowerSeries.X : PowerSeries k)) a
    obtain ⟨j, hj⟩ := s.2
    have hj' : (PowerSeries.X : PowerSeries k) ^ j = (s : PowerSeries k) := hj
    have hps' : a * algebraMap (PowerSeries k) (LaurentSeries k) (s : PowerSeries k) =
        algebraMap (PowerSeries k) (LaurentSeries k) p := hps
    have key : ((PowerSeries.X : PowerSeries k) ^ j) • a • y = p • y := by
      rw [← algebraMap_smul (LaurentSeries k) ((PowerSeries.X : PowerSeries k) ^ j) (a • y), smul_smul, hj',
        mul_comm, hps', algebraMap_smul]
    refine ⟨m + j, ?_⟩
    rw [pow_add, mul_smul, key, smul_comm]
    exact N.smul_mem _ hm

variable {W : Type} [AddCommGroup W] [Module (LaurentSeries k) W]
  [Module (PowerSeries k) W] [IsScalarTower (PowerSeries k) (LaurentSeries k) W]

theorem isLat_comap (f : W →ₗ[LaurentSeries k] V) (hf : Function.Injective f)
    {N : Submodule (PowerSeries k) V} (hN : IsLat N) :
    IsLat (N.comap (f.restrictScalars (PowerSeries k))) := by
  refine ⟨?_, ?_⟩
  · refine Submodule.fg_of_fg_map_injective (f.restrictScalars (PowerSeries k)) hf ?_
    haveI : IsNoetherian (PowerSeries k) N := isNoetherian_of_fg_of_noetherian N hN.1
    exact isNoetherian_submodule.1 this _ (Submodule.map_comap_le _ _)
  · refine eq_top_iff.2 fun w _ => ?_
    obtain ⟨m, hm⟩ := exists_pow_smul_mem hN.2 (f w)
    have hmem : ((PowerSeries.X : PowerSeries k) ^ m) • w ∈ N.comap (f.restrictScalars (PowerSeries k)) := by
      rw [Submodule.mem_comap, LinearMap.restrictScalars_apply, LinearMap.map_smul_of_tower]
      exact hm
    have hne : algebraMap (PowerSeries k) (LaurentSeries k) ((PowerSeries.X : PowerSeries k) ^ m) ≠ 0 := by
      rw [map_pow]
      refine pow_ne_zero _ ?_
      intro h
      have hX : (PowerSeries.X : PowerSeries k) ≠ 0 := PowerSeries.X_ne_zero
      exact hX (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := k) (by rw [map_zero]; exact h))
    rw [← Submodule.smul_mem_iff _ hne, algebraMap_smul]
    exact Submodule.subset_span hmem

end

theorem main : ∀ {k : Type} [inst : Field k] {V : Type} [inst_1 : AddCommGroup V]
    [inst_2 : Module (LaurentSeries k) V] [inst_3 : Module (PowerSeries k) V]
    [inst_4 : IsScalarTower (PowerSeries k) (LaurentSeries k) V] {W : Type} [inst_5 : AddCommGroup W]
    [inst_6 : Module (LaurentSeries k) W] [inst_7 : Module (PowerSeries k) W]
    [inst_8 : IsScalarTower (PowerSeries k) (LaurentSeries k) W] (f : LinearMap (RingHom.id (LaurentSeries k)) W V),
    Function.Injective (DFunLike.coe f) → ∀ {N : Submodule (PowerSeries k) V}, GlobalTheory.PhiGam.IsLat N →
      GlobalTheory.PhiGam.IsLat (Submodule.comap (LinearMap.restrictScalars (PowerSeries k) f) N) :=
  fun f hf _ hN => isLat_comap f hf hN

end GlobalTheory.LatticeComap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNilpotentResidueToMatrixMulLeftStatement
section
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNilpotent_residue_toMatrix_mulLeft' : ∀ (R S : Type) [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S] [Algebra R S] (n : ℕ) (b : Module.Basis (Fin n) R S) (t : S), t ∈ IsLocalRing.maximalIdeal S → IsNilpotent ((LinearMap.toMatrix b b (LinearMap.mulLeft R t)).map (IsLocalRing.residue R)) := by
  first | exact @GlobalTheory.isNilpotent_residue_toMatrix_mulLeft | exact GlobalTheory.isNilpotent_residue_toMatrix_mulLeft | (intros; apply GlobalTheory.isNilpotent_residue_toMatrix_mulLeft <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsTotallyComplexOfPrimitiveRootThreeLeStatement
section
open NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTotallyComplex_of_primitiveRoot_three_le : ∀ (K : Type) [Field K] [NumberField K] (ζ : K) (m : ℕ), IsPrimitiveRoot ζ m → 3 ≤ m →
    NumberField.IsTotallyComplex K := by
  first | exact @GlobalTheory.tcroot | exact GlobalTheory.tcroot | (intros; apply GlobalTheory.tcroot <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeCosetTranslateMemOfCoverStatement
section
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_coset_translate_mem_of_cover : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r t : ℕ) (ϖ : O), Irreducible ϖ → ∀ (N : ℕ) (x : Matrix (Fin r ⊕ Fin t) (Fin r) K) (g : GL (Fin r) K) (z₀ : Matrix (Fin r ⊕ Fin t) (Fin r) O), x * (g : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z₀).map (algebraMap O K) → (∀ z : Matrix (Fin r ⊕ Fin t) (Fin r) O, ∃ (g' : GL (Fin r) K) (z' : Matrix (Fin r ⊕ Fin t) (Fin r) O), (x + (ϖ ^ N • z).map (algebraMap O K)) * (g' : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z').map (algebraMap O K)) → ∀ z : Matrix (Fin r ⊕ Fin t) (Fin r) O, ∃ z' : Matrix (Fin r ⊕ Fin t) (Fin r) O, (x + (ϖ ^ N • z).map (algebraMap O K)) * (g : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z').map (algebraMap O K) := by
  first | exact @GlobalTheory.coset_translate_mem_of_cover | exact GlobalTheory.coset_translate_mem_of_cover | (intros; apply GlobalTheory.coset_translate_mem_of_cover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LaurentDegenerationFirstOrderKernelStatement
section
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurent_degeneration_first_order_kernel : ∀ (k : Type) [Field k], ∃ (K : Type) (_ : Field K) (_ : Algebra k K) (σ : K), ∀ (a e : ℕ) (V : Submodule k (Fin a → k)) (U : Type) [AddCommGroup U] [Module k U] (t u : V →ₗ[k] U), e ≤ 1 → (∀ x0 x1 : Fin (e + 1) → V, (∀ j, t (x0 j) = 0 ∧ t (x1 j) = u (x0 j)) → ¬ LinearIndependent k x0) → ∀ y : Fin (e + 1) → Fin a → K, (∀ j (π : K →ₗ[k] k), ∃ x x' : V, (∀ c, x.1 c = π (y j c)) ∧ (∀ c, x'.1 c = π (σ * y j c)) ∧ t x = u x') → ¬ LinearIndependent K y := by
  first | exact @GlobalTheory.laurent_degeneration | exact GlobalTheory.laurent_degeneration | (intros; apply GlobalTheory.laurent_degeneration <;> assumption)
end

