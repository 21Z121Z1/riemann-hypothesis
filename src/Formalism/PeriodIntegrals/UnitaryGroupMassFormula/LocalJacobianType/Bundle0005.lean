import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.Bundle0004
import Formalism.PeriodIntegrals.Bundle0019
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.Bundle0002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.BoxMul

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.ComponentsOfD1EqZero
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.LocJacTyp.Sd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain Topology Filter PI.LocJacTyp
open PI.VolStabSW.SdUniqW
open scoped TensorProduct

attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv finDim

theorem piu_inv_not_mem {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    (piu v)⁻¹ ∉ v.adicCompletionIntegers F := by
  intro h
  have hU : {x : Fv F v | x ≠ 1} ∈ 𝓝 (0 : Fv F v) := isOpen_ne.mem_nhds zero_ne_one
  obtain ⟨k, hk⟩ := (tube v (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v) hU).exists
  have hm : (piu v)⁻¹ ^ k ∈ v.adicCompletionIntegers F := pow_mem h k
  apply hk _ hm
  simp [smul_eq_mul, mul_inv_cancel₀ (pow_ne_zero k (piu_ne v))]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) (ψ : AddChar (AF F) ℂ)

theorem finrank_pos' : 0 < Module.finrank F E := Module.finrank_pos

theorem exists_not_mem_oev : ∃ t0 : Fv F v ⊗[F] E, t0 ∉ OEv (E := E) v := by
  classical
  set i0 : Fin (Module.finrank F E) := ⟨0, finrank_pos'⟩
  set P : Set (Fv F v) := (fun y => trE (E := E) v y i0) '' OEv (E := E) v
  have hP : IsCompact P :=
    (isCompact_oev v).image ((continuous_apply i0).comp (continuous_trE v))
  have hU : (v.adicCompletionIntegers F : Set (Fv F v)) ∈ 𝓝 (0 : Fv F v) :=
    (Valued.isOpen_valuationSubring _).mem_nhds (zero_mem _)
  obtain ⟨k, hk⟩ := (tube v hP hU).exists
  refine ⟨(trE (E := E) v).symm (Pi.single i0 (piu v ^ (k + 1))⁻¹), fun h => ?_⟩
  have hp : (piu v ^ (k + 1))⁻¹ ∈ P :=
    ⟨_, h, by simp⟩
  have h2 := hk _ hp
  have e : piu v ^ k • (piu v ^ (k + 1))⁻¹ = (piu v)⁻¹ := by
    have := piu_ne v
    rw [smul_eq_mul, pow_succ]
    field_simp
  rw [e] at h2
  exact piu_inv_not_mem v h2

variable [SecondCountableTopology (Fv F v ⊗[F] E)]

theorem no_sd_triv (ι : Type) [Fintype ι] [Nonempty ι] (htriv : ∀ r, psiV F ψ v r = 1) :
    ¬ ∃ μ : Measure (ι → Fv F v ⊗[F] E), SelfDual μ (chi (E := E) v ψ ι) := by
  classical
  rintro ⟨μ, hμ⟩
  have := hμ.1
  obtain ⟨t0, ht0⟩ := exists_not_mem_oev (E := E) v
  obtain ⟨i0⟩ := ‹Nonempty ι›
  set t : ι → Fv F v ⊗[F] E := Pi.single i0 t0
  set L := ObS (E := E) v ι
  have hLo : IsOpen (L : Set (ι → Fv F v ⊗[F] E)) := by rw [coe_ObS]; exact isOpen_obox v ι
  have hLc : IsCompact (L : Set (ι → Fv F v ⊗[F] E)) := by rw [coe_ObS]; exact isCompact_obox v ι
  have hcl : IsClopen (L : Set (ι → Fv F v ⊗[F] E)) := ⟨AddSubgroup.isClosed_of_isOpen L hLo, hLo⟩
  have hnt : -t ∉ L := by
    intro h
    have h2 : t ∈ L := by simpa using L.neg_mem h
    rw [← SetLike.mem_coe, coe_ObS] at h2
    exact ht0 (by simpa [t] using h2 i0 trivial)
  set f : (ι → Fv F v ⊗[F] E) → ℂ := (L : Set (ι → Fv F v ⊗[F] E)).indicator (fun _ => (1 : ℂ))
  have hfc : Continuous f := by
    rw [show f = (L : Set _).piecewise (fun _ => (1 : ℂ)) (fun _ => 0) from
      (Set.piecewise_eq_indicator).symm]
    exact continuous_const.piecewise (by simp [hcl.frontier_eq]) continuous_const
  have hfs : HasCompactSupport f := HasCompactSupport.intro hLc fun x hx => Set.indicator_of_notMem hx _
  have hfi : Integrable f μ := hfc.integrable_of_hasCompactSupport hfs
  have hχ1 : ∀ x y, chi (E := E) v ψ ι x y = 1 := fun x y => htriv _
  have hT : ∀ y, ∫ x, (f x - f (x - t)) * chi (E := E) v ψ ι x y ∂μ = 0 := by
    intro y
    simp only [hχ1, mul_one]
    rw [integral_sub hfi (hfi.comp_sub_right t), integral_sub_right_eq_self, sub_self]
  have hI : Integrable (fun y => ∫ x, (f x - f (x - t)) * chi (E := E) v ψ ι x y ∂μ) μ := by
    simp only [hT]; exact integrable_zero _ _ _
  have h := hμ.2 (fun x => f x - f (x - t)) (hfc.sub (hfc.comp (continuous_id.sub continuous_const)))
    (hfs.sub (hfs.comp_homeomorph (Homeomorph.subRight t))) hI 0
  simp only [hT, zero_mul, integral_zero, neg_zero, zero_sub] at h
  have h1 : f 0 = 1 := by simp [f, L.zero_mem]
  have h2 : f (-t) = 0 := Set.indicator_of_notMem hnt _
  rw [h1, h2] at h
  norm_num at h

theorem components_of_D1_eq_zero (h : ¬ OpenKer v ψ) : D1 (E := E) v ψ = {0} := by
  ext y
  constructor
  · intro hy
    by_contra hne
    have h1 : trE (E := E) v y ≠ 0 := by
      rw [Ne, LinearEquiv.map_eq_zero_iff]; exact hne
    obtain ⟨j, hj⟩ := Function.ne_iff.1 h1
    apply h (openKer_of v ψ (trE (E := E) v y j) hj fun c hc => ?_)
    have e : c * trE (E := E) v y j =
        Algebra.trace (Fv F v) (Fv F v ⊗[F] E) ((c • bas (E := E) v j) * y) := by
      rw [trE_apply, trC_apply, smul_mul_assoc, map_smul, smul_eq_mul]
    rw [e]
    exact hy _ (smul_bas_mem v hc j)
  · intro hy
    rw [Set.mem_singleton_iff.1 hy]
    intro x _
    simp [psiV_zero]

theorem no_sd_noKer (ι : Type) [Fintype ι] [Nonempty ι] (h : ¬ OpenKer v ψ) :
    ¬ ∃ μ : Measure (ι → Fv F v ⊗[F] E), SelfDual μ (chi (E := E) v ψ ι) := by
  classical
  rintro ⟨μ, hμ⟩
  have := hμ.1
  have hD : Dbox (E := E) v ψ ι = {0} := by
    ext y
    simp only [Dbox, components_of_D1_eq_zero v ψ h, Set.mem_pi, Set.mem_univ, Set.mem_singleton_iff,
      true_implies]
    exact ⟨fun hy => funext hy, fun hy i => by rw [hy]; rfl⟩
  have h1 := sd_test v ψ ι μ hμ (by rw [hD]; exact measurableSet_singleton 0)
    (by rw [hD]; exact measure_singleton_lt_top)
  rw [hD] at h1
  have h0 : μ {0} ≠ 0 := by
    intro h0
    simp [Measure.real, h0] at h1
  obtain ⟨i0⟩ := ‹Nonempty ι›
  set j0 : Fin (Module.finrank F E) := ⟨0, finrank_pos'⟩
  set x1 : ι → Fv F v ⊗[F] E := Pi.single i0 (bas (E := E) v j0)
  have hx1 : x1 ≠ 0 := by
    intro hx
    have := congrFun hx i0
    simp [x1] at this
    exact (bas (E := E) v).ne_zero j0 this
  have hx1m : ∀ n : ℕ, n • x1 ∈ Obox (E := E) v ι := by
    intro n
    have hm : x1 ∈ ObS (E := E) v ι := by
      rw [← SetLike.mem_coe, coe_ObS]
      intro i _
      by_cases hi : i = i0
      · subst hi; simpa [x1] using bas_mem v j0
      · simpa [x1, hi] using oev_zero v
    have := (ObS (E := E) v ι).nsmul_mem hm n
    rwa [← SetLike.mem_coe, coe_ObS] at this
  have : CharZero (Fv F v) := charZero_of_injective_algebraMap (algebraMap F (Fv F v)).injective
  have hinj : ∀ n m : ℕ, n • x1 = m • x1 → n = m := by
    intro n m hnm
    rw [← Nat.cast_smul_eq_nsmul (Fv F v), ← Nat.cast_smul_eq_nsmul (Fv F v), ← sub_eq_zero,
      ← sub_smul, smul_eq_zero] at hnm
    rcases hnm with h' | h'
    · exact Nat.cast_injective (R := Fv F v) (sub_eq_zero.1 h')
    · exact absurd h' hx1
  have hpt : ∀ a : ι → Fv F v ⊗[F] E, μ {a} = μ {0} := by
    intro a
    have e : ({a} : Set (ι → Fv F v ⊗[F] E)) = (fun h => -a + h) ⁻¹' {0} := by
      ext y; simp [eq_comm]
    rw [e, measure_preimage_add]
  have hfin : μ (Obox (E := E) v ι) ≠ ⊤ := (isCompact_obox v ι).measure_lt_top.ne
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_mul_gt h0 hfin
  have hS : μ (⋃ n ∈ Finset.range N, {n • x1}) = N * μ {0} := by
    rw [measure_biUnion_finset]
    · rw [Finset.sum_congr rfl (fun n _ => hpt (n • x1)), Finset.sum_const, Finset.card_range,
        nsmul_eq_mul]
    · intro n _ m _ hnm
      exact Set.disjoint_singleton.2 fun h' => hnm (hinj n m h')
    · intro n _; exact measurableSet_singleton _
  have hsub : (⋃ n ∈ Finset.range N, ({n • x1} : Set (ι → Fv F v ⊗[F] E))) ⊆ Obox (E := E) v ι := by
    intro y hy
    simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hy
    obtain ⟨n, _, rfl⟩ := hy
    exact hx1m n
  have := measure_mono (μ := μ) hsub
  rw [hS] at this
  exact absurd (lt_of_lt_of_le hN this) (lt_irrefl _)

end PI.UnitaryGroupMassFormula.LocJacTyp.Sd
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.KitShear
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.LocJacTyp

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacTyp
open scoped TensorProduct

attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv
attribute [local instance] Sd.finDim

section Gen

variable {W : Type} [AddCommGroup W] [TopologicalSpace W] [IsTopologicalAddGroup W]
  [LocallyCompactSpace W] [SecondCountableTopology W] [T2Space W] [MeasurableSpace W] [BorelSpace W]

theorem haar_shear (μ : Measure W) [μ.IsAddHaarMeasure] (Φ : W ≃ₜ+ W) (K : Set W)
    (hK : IsCompact K) (hKo : IsOpen K) (hK0 : K.Nonempty) (hΦ : Φ ⁻¹' K = K) (S : Set W) :
    μ (Φ ⁻¹' S) = μ S := by
  have hmap : ∀ T, (μ.map Φ) T = μ (Φ ⁻¹' T) := fun T =>
    (Φ.toHomeomorph.toMeasurableEquiv).map_apply (μ := μ) T
  have e := Measure.isAddLeftInvariant_eq_smul (μ.map Φ) μ
  have hpos : μ K ≠ 0 := hKo.measure_ne_zero μ hK0
  have hfin : μ K ≠ ⊤ := hK.measure_lt_top.ne
  have h1 := congrArg (fun ν : Measure W => ν K) e
  simp only [hmap, hΦ, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h1
  have hc : ((Measure.addHaarScalarFactor (μ.map Φ) μ : NNReal) : ENNReal) = 1 := by
    have h2 : (1 : ENNReal) * μ K = (Measure.addHaarScalarFactor (μ.map Φ) μ : ENNReal) * μ K := by
      rw [one_mul]; exact h1
    exact ((ENNReal.mul_left_inj hpos hfin).1 h2).symm
  rw [← hmap, e, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, hc, one_mul]

end Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)}

theorem continuous_sigR' (σ : E →ₐ[F] E) : Continuous (sigR (Fv F v) σ) := by
  have : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  have h : ∀ x : Fv F v ⊗[F] E, sigR (Fv F v) σ x = (σ.toLinearMap.baseChange (Fv F v)) x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r e => simp [sigR]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have : (sigR (Fv F v) σ : Fv F v ⊗[F] E → Fv F v ⊗[F] E) = (σ.toLinearMap.baseChange (Fv F v)) :=
    funext h
  rw [this]
  exact IsModuleTopology.continuous_of_linearMap _

namespace SD

variable (D : SD σ v)

theorem e_mul_f : D.e * (1 - D.e) = 0 := by
  rw [mul_sub, mul_one, D.he.eq, sub_self]

def shear {ι : Type} (τ : ι → ι) : (ι → Fv F v ⊗[F] E) ≃ₜ+ (ι → Fv F v ⊗[F] E) where
  toFun z k := z k + D.e * sigR (Fv F v) σ (z (τ k))
  invFun w k := w k - D.e * sigR (Fv F v) σ (w (τ k))
  left_inv z := by
    funext k
    simp only [map_add, map_mul, D.hσ]
    linear_combination (-(sigR (Fv F v) σ (sigR (Fv F v) σ (z (τ (τ k)))))) * D.e_mul_f
  right_inv w := by
    funext k
    simp only [map_sub, map_mul, D.hσ]
    linear_combination (-(sigR (Fv F v) σ (sigR (Fv F v) σ (w (τ (τ k)))))) * D.e_mul_f
  map_add' x y := by
    funext k
    simp only [Pi.add_apply, map_add]
    ring
  continuous_toFun := continuous_pi fun k =>
    (continuous_apply k).add (continuous_const.mul ((continuous_sigR' σ).comp (continuous_apply (τ k))))
  continuous_invFun := continuous_pi fun k =>
    (continuous_apply k).sub (continuous_const.mul ((continuous_sigR' σ).comp (continuous_apply (τ k))))

theorem shear_apply {ι : Type} (τ : ι → ι) (z : ι → Fv F v ⊗[F] E) (k : ι) :
    D.shear τ z k = z k + D.e * sigR (Fv F v) σ (z (τ k)) := rfl

theorem shear_first_coordinate {ι : Type} (τ : ι → ι) (z : ι → Fv F v ⊗[F] E) (k : ι) :
    D.p 0 (D.shear τ z k) = D.p 0 (z k) + D.p 1 (z (τ k)) := by
  rw [shear_apply, map_add, map_mul, D.p_e.1, (D.p_sig _).1, one_mul]

theorem shear_second_coordinate {ι : Type} (τ : ι → ι) (z : ι → Fv F v ⊗[F] E) (k : ι) :
    D.p 1 (D.shear τ z k) = D.p 1 (z k) := by
  rw [shear_apply, map_add, map_mul, D.p_e.2, zero_mul, add_zero]

theorem mem_box_iff {ι : Type} (z : ι → Fv F v ⊗[F] E) :
    z ∈ Obox (E := E) v ι ↔ ∀ k, D.p 0 (z k) ∈ v.adicCompletionIntegers F ∧
      D.p 1 (z k) ∈ v.adicCompletionIntegers F := by
  simp only [Obox, Set.mem_pi, Set.mem_univ, true_implies, D.mem_iff]

theorem shear_box {ι : Type} (τ : ι → ι) : D.shear τ ⁻¹' Obox (E := E) v ι = Obox (E := E) v ι := by
  ext z
  rw [Set.mem_preimage, D.mem_box_iff, D.mem_box_iff]
  simp only [D.shear_first_coordinate, D.shear_second_coordinate]
  constructor
  · intro h k
    refine ⟨?_, (h k).2⟩
    have := sub_mem (h k).1 (h (τ k)).2
    simpa using this
  · intro h k
    exact ⟨add_mem (h k).1 (h (τ k)).2, (h k).2⟩

theorem mem_sc_mul (t : Fv F v) (c : Fv F v ⊗[F] E) :
    sc (E := E) v t * c ∈ OEv (E := E) v ↔
      t * D.p 0 c ∈ v.adicCompletionIntegers F ∧ t * D.p 1 c ∈ v.adicCompletionIntegers F := by
  rw [D.mem_iff, map_mul, map_mul, D.p_sc, D.p_sc]

def pt (s t : Fv F v) : Fv F v ⊗[F] E := s • D.e + t • (1 - D.e)

theorem p_pt (s t : Fv F v) : D.p 0 (D.pt s t) = s ∧ D.p 1 (D.pt s t) = t := D.p_pair s t

theorem isUnit_pt {s t : Fv F v} (hs : s ≠ 0) (ht : t ≠ 0) : IsUnit (D.pt s t) := by
  refine IsUnit.of_mul_eq_one (D.pt s⁻¹ t⁻¹) (D.ext ?_ ?_)
  · rw [map_mul, (D.p_pt _ _).1, (D.p_pt _ _).1, map_one, mul_inv_cancel₀ hs]
  · rw [map_mul, (D.p_pt _ _).2, (D.p_pt _ _).2, map_one, mul_inv_cancel₀ ht]

theorem mem_pt_mul (s t : Fv F v) (c : Fv F v ⊗[F] E) :
    D.pt s t * c ∈ OEv (E := E) v ↔
      s * D.p 0 c ∈ v.adicCompletionIntegers F ∧ t * D.p 1 c ∈ v.adicCompletionIntegers F := by
  rw [D.mem_iff, map_mul, map_mul, (D.p_pt _ _).1, (D.p_pt _ _).2]

theorem norm_pt (s t : Fv F v) : Algebra.norm (Fv F v) (D.pt s t) = s * t := by
  rw [D.norm_eq, (D.p_pt _ _).1, (D.p_pt _ _).2]

end SD

theorem obox_compact (ι : Type) [Finite ι] : IsCompact (Obox (E := E) v ι) :=
  isCompact_univ_pi fun _ => (integer_ring_topology (E := E) v).1

theorem obox_open (ι : Type) [Finite ι] : IsOpen (Obox (E := E) v ι) :=
  isOpen_set_pi Set.finite_univ fun _ _ => (integer_ring_topology (E := E) v).2.1

theorem obox_nonempty (ι : Type) : (Obox (E := E) v ι).Nonempty :=
  ⟨0, fun _ _ => Sd.oev_zero v⟩

end PI.UnitaryGroupMassFormula.LocJacTyp
end
end

