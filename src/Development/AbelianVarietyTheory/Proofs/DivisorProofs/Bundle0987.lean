import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0961
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0901
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0960
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0978
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0005
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SmoothInExponentialCoordsIffFirstSecondKind
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0007
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0081
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0964
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0825

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermCenterActionSmoothForm
section
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep Topology

namespace GlobalTheory.ConstTermZalg

open GlobalTheory.ConstTermSmooth

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem good_add {φ ψ : Sm E a} (hφ : Good φ) (hψ : Good ψ) : Good (φ + ψ) := by
  refine ⟨fun γ g => ?_, ?_⟩
  · simp [hφ.1, hψ.1]
  · refine isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset
      (Filter.inter_mem (hφ.2.mem_nhds (by simp)) (hψ.2.mem_nhds (by simp))) fun k hk => ?_)
    obtain ⟨h1, h2⟩ := hk
    have h1' : finRep E a k φ = φ := h1
    have h2' : finRep E a k ψ = ψ := h2
    show finRep E a k (φ + ψ) = φ + ψ
    rw [map_add, h1', h2']

theorem good_smul {φ : Sm E a} (hφ : Good φ) (s : ℂ) : Good (s • φ) := by
  refine ⟨fun γ g => ?_, ?_⟩
  · simp [hφ.1]
  · refine isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset (hφ.2.mem_nhds (by simp)) fun k hk => ?_)
    have h1' : finRep E a k φ = φ := hk
    show finRep E a k (s • φ) = s • φ
    rw [map_smul, h1']

theorem good_integrable {r : ℕ} [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)]
    (ν : Measure (BlockIx a r → Ad E)) [IsFiniteMeasure ν] {φ : Sm E a} (h : Good φ) (g : GA E a) :
    Integrable (fun x => φ.1 (unip x * g)) ν := by
  have hc : Continuous φ.1 := ContAut.continuous_of_isOpen_stab E a φ h.2
  exact integrable_unip ν (Ψ := fun g (_ : Lie E a) => φ.1 g) (hc.comp continuous_fst).continuousOn
    (fun γ g => funext fun _ => h.1 γ g) g (y := oneL E a) isUnit_one

theorem constTerm_zalg : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ)
    [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E))
    (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 →
    ∀ φ : Sm E a, (∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g) → IsOpen {k | finRep E a k φ = φ} →
    ∀ z ∈ Zalg E a, ∀ c : Sm E a, c.1 = (fun g : GA E a => ∫ x in 𝓕, φ.1 (unip x * g) ∂μ) →
      (z c).1 = fun g : GA E a => ∫ x in 𝓕, (z φ).1 (unip x * g) ∂μ := by
  intro E _ _ _ a r _ _ μ 𝓕 hH hF h1 φ hl ho z hz c hc
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by simp [h1]⟩
  let CT : Sm E a → GA E a → ℂ := fun ψ g => ∫ x, ψ.1 (unip x * g) ∂(μ.restrict 𝓕)
  let S : Subalgebra ℂ (Module.End ℂ (Sm E a)) :=
    { carrier := {z | ∀ ψ, Good ψ → Good (z ψ) ∧ ∀ c : Sm E a, c.1 = CT ψ → (z c).1 = CT (z ψ)}
      mul_mem' := by
        intro z w hz hw ψ h
        exact ⟨(hz _ (hw ψ h).1).1, fun c hc => (hz _ (hw ψ h).1).2 _ ((hw ψ h).2 c hc)⟩
      add_mem' := by
        intro z w hz hw ψ h
        refine ⟨good_add (hz ψ h).1 (hw ψ h).1, fun c hc => ?_⟩
        have e1 := (hz ψ h).2 c hc
        have e2 := (hw ψ h).2 c hc
        funext g
        simp only [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply, e1, e2, CT]
        rw [integral_add (good_integrable _ (hz ψ h).1 g) (good_integrable _ (hw ψ h).1 g)]
      algebraMap_mem' := by
        intro s ψ h
        simp only [Module.algebraMap_end_apply]
        refine ⟨good_smul h s, fun c hc => ?_⟩
        funext g
        simp only [Submodule.coe_smul, Pi.smul_apply, hc, CT, smul_eq_mul]
        rw [integral_const_mul] }
  have hlie : ∀ X, lie E a X ∈ S := fun X ψ h => ⟨h.lie X, fun c hc => funext fun g => by
    rw [lie_apply, hc]
    exact (constTerm_mem_Sm E a r μ 𝓕 hH hF h1 ψ h.1 h.2).2 X g⟩
  have hE : ∀ τ i j, Eop τ i j ∈ S := fun τ i j =>
    S.smul_mem (S.sub_mem (hlie _) (S.smul_mem (hlie _) _)) _
  have hzS : z ∈ S := by
    refine (Algebra.adjoin_le (S := S) ?_) hz
    rintro _ ⟨τ, u, rfl⟩
    refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
    refine S.add_mem ?_ (hE _ _ _)
    split_ifs
    · exact S.algebraMap_mem _
    · exact S.zero_mem
  exact (hzS φ ⟨hl, ho⟩).2 c hc

end GlobalTheory.ConstTermZalg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormModerateGrowthCompact
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Topology Filter Matrix

namespace GlobalTheory.JSW.MirSemi

open GlobalTheory.CuspRep GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def IsLocModerate (F : GA E a → ℂ) : Prop :=
  ∀ g₀ : GA E a, ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ᶠ g in 𝓝 g₀, ∀ y, ‖F (g * infGL E a y)‖ ≤ C * height y ^ N

theorem continuous_mapGL {R S : Type} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
    [IsTopologicalRing R] [IsTopologicalRing S] {p : R →+* S} (hp : Continuous p) :
    Continuous (GeneralLinearGroup.map (n := Fin a) p) :=
  Continuous.units_map _ (continuous_id.matrix_map hp)

theorem continuous_pInf_ad : Continuous (pInf E) := by
  have h : Continuous (infEq E).symm := by
    refine continuous_pi fun w => ?_
    exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)
  exact h.comp continuous_fst

theorem continuous_pFin_ad : Continuous (pFin E) := continuous_snd

theorem continuous_height_inf : Continuous (height : GL (Fin a) (Cinf E) → ℝ) := by
  have ht : Continuous fun x : Matrix (Fin a) (Fin a) (Cinf E) => toL x := continuous_id
  show Continuous fun y : GL (Fin a) (Cinf E) => 1 + ‖toL y.val‖ + ‖toL (y⁻¹).val‖
  exact (continuous_const.add (ht.comp Units.continuous_val).norm).add (ht.comp Units.continuous_coe_inv).norm

theorem isAutForm_continuous_locModerate {φ : Sm E a} (hA : IsAutForm φ) : Continuous φ.1 ∧ IsLocModerate φ.1 := by
  have cI : Continuous fun g : GA E a => GeneralLinearGroup.map (pInf E) g := continuous_mapGL continuous_pInf_ad
  have cF : Continuous fun g : GA E a => GeneralLinearGroup.map (pFin E) g := continuous_mapGL continuous_pFin_ad
  have dec : ∀ g₀ g : GA E a, finRep E a (GeneralLinearGroup.map (pFin E) (g₀⁻¹ * g)) φ = φ → ∀ y,
      φ.1 (g * infGL E a y) = φ.1 (g₀ * infGL E a (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g) * y)) := by
    intro g₀ g hk y
    have hu : g = g₀ * (infGL E a (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)) *
        finGL E a (GeneralLinearGroup.map (pFin E) (g₀⁻¹ * g))) := by
      rw [infGL_mul_finGL, mul_inv_cancel_left]
    have e : g * infGL E a y = g₀ * infGL E a (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g) * y) *
        finGL E a (GeneralLinearGroup.map (pFin E) (g₀⁻¹ * g)) := by
      conv_lhs => rw [hu]
      rw [map_mul (infGL E a) (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)) y]
      simp only [mul_assoc]
      rw [← infGL_comm]
    rw [e]
    exact congrArg (fun ψ : Sm E a => ψ.1 (g₀ * infGL E a (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g) * y))) hk
  have nb : ∀ g₀ : GA E a, ∀ᶠ g in 𝓝 g₀, finRep E a (GeneralLinearGroup.map (pFin E) (g₀⁻¹ * g)) φ = φ := by
    intro g₀
    have hc : Continuous fun g : GA E a => GeneralLinearGroup.map (pFin E) (g₀⁻¹ * g) :=
      cF.comp (continuous_const.mul continuous_id)
    refine hc.continuousAt.preimage_mem_nhds (hA.level.mem_nhds ?_)
    simp
  refine ⟨continuous_iff_continuousAt.2 fun g₀ => ?_, fun g₀ => ?_⟩
  · have e : (fun g => φ.1 g) =ᶠ[𝓝 g₀]
        fun g => chart φ.1 g₀ (toL (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)).val) := by
      filter_upwards [nb g₀] with g hg
      rw [chart_val]
      have := dec g₀ g hg 1
      simp only [map_one, mul_one] at this
      exact this
    refine ContinuousAt.congr ?_ e.symm
    refine ContinuousAt.comp_of_eq (contDiffAt_chart (x := oneL E a) φ.2 g₀ isUnit_one).continuousAt ?_
      (by simp [oneL])
    have ht : Continuous fun x : Matrix (Fin a) (Fin a) (Cinf E) => toL x := continuous_id
    exact ((ht.comp Units.continuous_val).comp (cI.comp (continuous_const.mul continuous_id))).continuousAt
  · obtain ⟨C, N, hC⟩ := hA.growth g₀
    have ha : (0 : ℝ) ≤ 1 + 2 * a := by positivity
    have h1' := one_le_height (1 : GL (Fin a) (Cinf E))
    refine ⟨|C| * ((1 + 2 * a) * (height (1 : GL (Fin a) (Cinf E)) + 1)) ^ N, N,
      mul_nonneg (abs_nonneg C) (pow_nonneg (mul_nonneg ha (by linarith)) N), ?_⟩
    have hh : ∀ᶠ g in 𝓝 g₀, height (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)) <
        height (1 : GL (Fin a) (Cinf E)) + 1 := by
      have hc : Continuous fun g : GA E a => height (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)) :=
        continuous_height_inf.comp (cI.comp (continuous_const.mul continuous_id))
      exact hc.continuousAt.eventually_lt continuousAt_const (by simp)
    filter_upwards [nb g₀, hh] with g hg hg' y
    rw [dec g₀ g hg y]
    have h1 := one_le_height (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g))
    have h2 := one_le_height y
    have h3 := one_le_height (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g) * y)
    calc ‖φ.1 (g₀ * infGL E a (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g) * y))‖
        ≤ C * height (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g) * y) ^ N := hC _
      _ ≤ |C| * height (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g) * y) ^ N :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (by linarith) N)
      _ ≤ |C| * ((1 + 2 * a) * (height (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)) * height y)) ^ N :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (RapidModel.height_mul_le _ y) N) (abs_nonneg C)
      _ ≤ |C| * (((1 + 2 * a) * (height (1 : GL (Fin a) (Cinf E)) + 1)) * height y) ^ N := by
          refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀
            (mul_nonneg ha (mul_nonneg (by linarith) (by linarith))) ?_ N) (abs_nonneg C)
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg'.le ha) (by linarith)
      _ = _ := by rw [mul_pow]; ring

variable (π : CuspSub E a) in

def regSpan : Submodule ℂ (GA E a → ℂ) where
  carrier := {F | F ∈ rspan π ∧ Continuous F ∧ IsLocModerate F}
  add_mem' := fun {F G} hF hG => by
    refine ⟨add_mem hF.1 hG.1, hF.2.1.add hG.2.1, fun g₀ => ?_⟩
    obtain ⟨C, N, h0, e1⟩ := hF.2.2 g₀
    obtain ⟨C', N', h0', e2⟩ := hG.2.2 g₀
    refine ⟨C + C', N + N', add_nonneg h0 h0', ?_⟩
    filter_upwards [e1, e2] with g h1 h2 y
    have hy := one_le_height y
    have p1 : height y ^ N ≤ height y ^ (N + N') := pow_le_pow_right₀ hy (by omega)
    have p2 : height y ^ N' ≤ height y ^ (N + N') := pow_le_pow_right₀ hy (by omega)
    refine (norm_add_le _ _).trans ?_
    nlinarith [h1 y, h2 y, mul_le_mul_of_nonneg_left p1 h0, mul_le_mul_of_nonneg_left p2 h0']
  zero_mem' := ⟨zero_mem _, continuous_zero, fun _ => ⟨0, 0, le_rfl, Eventually.of_forall fun _ _ => by simp⟩⟩
  smul_mem' c F hF := by
    refine ⟨Submodule.smul_mem _ c hF.1, hF.2.1.const_smul c, fun g₀ => ?_⟩
    obtain ⟨C, N, h0, e⟩ := hF.2.2 g₀
    refine ⟨‖c‖ * C, N, mul_nonneg (norm_nonneg _) h0, ?_⟩
    filter_upwards [e] with g h y
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h y) (norm_nonneg _)

theorem mem_regSpan {π : CuspSub E a} {F : GA E a → ℂ} :
    F ∈ regSpan π ↔ F ∈ rspan π ∧ Continuous F ∧ IsLocModerate F := Iff.rfl

theorem rt_mem_regSpan {π : CuspSub E a} {F : GA E a → ℂ} (hF : F ∈ regSpan π) (h : GA E a) :
    (fun g => F (g * h)) ∈ regSpan π := by
  refine ⟨rt_mem_rspan hF.1 h, hF.2.1.comp (continuous_mul_right h), fun g₀ => ?_⟩
  obtain ⟨y₀, k, rfl⟩ : ∃ y₀ k, h = infGL E a y₀ * finGL E a k := ⟨_, _, (infGL_mul_finGL h).symm⟩
  obtain ⟨C, N, h0, e⟩ := hF.2.2 (g₀ * finGL E a k)
  have hy₀ := one_le_height y₀
  refine ⟨C * ((1 + 2 * a) * height y₀) ^ N, N, mul_nonneg h0 (pow_nonneg (mul_nonneg (by positivity)
    (by linarith)) N), ?_⟩
  have ht : Tendsto (fun g => g * finGL E a k) (𝓝 g₀) (𝓝 (g₀ * finGL E a k)) := (continuous_mul_right _).tendsto g₀
  filter_upwards [ht.eventually e] with g hg z
  have ex : g * infGL E a z * (infGL E a y₀ * finGL E a k) = g * finGL E a k * infGL E a (z * y₀) := by
    rw [mul_assoc g (finGL E a k), ← infGL_comm, map_mul]; simp only [mul_assoc]
  change ‖F (g * infGL E a z * (infGL E a y₀ * finGL E a k))‖ ≤ _
  rw [ex]
  refine (hg _).trans ?_
  rw [mul_assoc C, ← mul_pow]
  refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith [one_le_height (z * y₀)]) ?_ N) h0
  exact (RapidModel.height_mul_le z y₀).trans_eq (by ring)

theorem kerInf_mem_regSpan {π : CuspSub E a} {F : GA E a → ℂ} (hF : F ∈ regSpan π) {X : Type} [MeasurableSpace X]
    (ν : Measure X) [SFinite ν] {k : X → ℂ} {γ : X → GL (Fin a) (Cinf E)} (hk : IsRapidInf ν k γ) :
    kerInf ν k γ F ∈ regSpan π := by
  have hM := RapidModel.rspan_le_modGr π hF.1
  refine ⟨kerInf_mem_rspan hF.1 ν hk, continuous_iff_continuousAt.2 fun g₀ => ?_, fun g₀ => ?_⟩
  · obtain ⟨C, N, h0, e⟩ := hF.2.2 g₀
    show ContinuousAt (fun g => ∫ x, k x * F (g * infGL E a (γ x)) ∂ν) g₀
    refine continuousAt_of_dominated (bound := fun x => C * (‖k x‖ * height (γ x) ^ N))
      (Eventually.of_forall fun g => (RapidModel.integrable_of_modGr hM hk g).aestronglyMeasurable) ?_
      ((hk.2.2 N).const_mul C)
      (Eventually.of_forall fun x => (continuous_const.mul (hF.2.1.comp (continuous_mul_right _))).continuousAt)
    filter_upwards [e] with g hg
    refine Eventually.of_forall fun x => ?_
    rw [norm_mul]
    calc ‖k x‖ * ‖F (g * infGL E a (γ x))‖ ≤ ‖k x‖ * (C * height (γ x) ^ N) :=
          mul_le_mul_of_nonneg_left (hg _) (norm_nonneg _)
      _ = C * (‖k x‖ * height (γ x) ^ N) := by ring
  · obtain ⟨C, N, h0, e⟩ := hF.2.2 g₀
    refine ⟨C * (1 + 2 * a) ^ N * ∫ x, ‖k x‖ * height (γ x) ^ N ∂ν, N, ?_, ?_⟩
    · refine mul_nonneg (by positivity) (integral_nonneg fun x => ?_)
      have := one_le_height (γ x)
      positivity
    · filter_upwards [e] with g hC z
      rw [kerInf]
      calc _ ≤ ∫ x, (C * (1 + 2 * a) ^ N * height z ^ N) * (‖k x‖ * height (γ x) ^ N) ∂ν := by
            refine norm_integral_le_of_norm_le ((hk.2.2 N).const_mul _) (Eventually.of_forall fun x => ?_)
            rw [norm_mul, mul_assoc g, ← map_mul]
            have h1 := (hC (z * γ x)).trans (mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (by linarith [one_le_height (z * γ x)]) (RapidModel.height_mul_le z (γ x)) N) h0)
            refine (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)).trans_eq ?_
            rw [mul_pow, mul_pow]; ring
        _ = _ := by rw [integral_const_mul]; ring

theorem IsLocModerate.bound_of_isCompact {F : GA E a → ℂ} (hF : IsLocModerate F) {K : Set (GA E a)}
    (hK : IsCompact K) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ g ∈ K, ∀ y, ‖F (g * infGL E a y)‖ ≤ C * height y ^ N := by
  first
  | exact @_root_.GlobalTheory.CompactUniformHeightBound.compact_uniform_bound
  | exact _root_.GlobalTheory.CompactUniformHeightBound.compact_uniform_bound
  | (apply _root_.GlobalTheory.CompactUniformHeightBound.compact_uniform_bound <;> assumption)
  | (intros; apply _root_.GlobalTheory.CompactUniformHeightBound.compact_uniform_bound <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CompactUniformHeightBound.compact_uniform_bound <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CompactUniformHeightBound.compact_uniform_bound ..)

theorem locSpan_le_regSpan {π : CuspSub E a} {φ : Sm E a} (hφ : φ ∈ π.V) (S : Finset (HeightOneSpectrum (𝓞 E))) :
    locSpan S φ.1 ≤ regSpan π :=
  locSpan_le (mem_regSpan.2 ⟨mem_rspan hφ, isAutForm_continuous_locModerate (π.cusp φ hφ).1⟩)
    (fun _ hF h _ => rt_mem_regSpan hF h) fun _ hF _ _ ν _ _ _ hk => kerInf_mem_regSpan hF ν hk

end GlobalTheory.JSW.MirSemi

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory in

theorem GlobalTheory.JSW.MirSemi.locSpan_continuous_moderate :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
      (π : CuspSub E a) (φ : Sm E a), φ ∈ π.V → ∀ F ∈ GlobalTheory.JSW.MirSemi.locSpan S φ.1, Continuous F ∧
        ∀ K : Set (GA E a), IsCompact K → ∃ (C : ℝ) (N : ℕ), ∀ g ∈ K, ∀ y : GL (Fin a) (Cinf E),
          ‖F (g * infGL E a y)‖ ≤ C * height y ^ N := by
  intro E _ _ _ a S π φ hφ F hF
  have hG := GlobalTheory.JSW.MirSemi.locSpan_le_regSpan hφ S hF
  refine ⟨hG.2.1, fun K hK => ?_⟩
  obtain ⟨C, N, -, h⟩ := hG.2.2.bound_of_isCompact hK
  exact ⟨C, N, h⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DRepAddAndBracket
section
noncomputable section

open GlobalTheory.SmoothForms NormedSpace
open scoped ContDiff Topology InnerProductSpace

namespace GlobalTheory.DerivedAction

variable {𝔸 H : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]

def dOp (π : 𝔸 → (H →L[ℂ] H)) (X : 𝔸) (v : H) : H := deriv (fun t : ℝ => π (exp (t • X)) v) 0

theorem abstract (σ : 𝔸 →ₗ[ℝ] 𝔸) (anti : ∀ a b, σ (a * b) = σ b * σ a) (one : σ 1 = 1) (invol : ∀ a, σ (σ a) = a)
    (π : 𝔸 → (H →L[ℂ] H)) (π1 : π 1 = 1) (πm : ∀ a b, σ a * a = 1 → σ b * b = 1 → π (a * b) = π a * π b) (v : H)
    (hv : ∀ (k : ℕ) (Xs : Fin k → 𝔸), (∀ i, σ (Xs i) = -Xs i) →
      ContDiff ℝ ∞ fun t : Fin k → ℝ => π ((List.ofFn fun i => exp (t i • Xs i)).prod) v)
    (X : 𝔸) (hX : σ X = -X) (Y : 𝔸) (hY : σ Y = -Y) :
    dOp π (X + Y) v = dOp π X v + dOp π Y v ∧
      dOp π (X * Y - Y * X) v = dOp π X (dOp π Y v) - dOp π Y (dOp π X v) := by
  classical
  let L : Submodule ℝ 𝔸 := LinearMap.ker (σ + LinearMap.id)
  have hL : ∀ Z, Z ∈ L ↔ σ Z = -Z := fun Z => by
    simp only [L, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply, add_eq_zero_iff_eq_neg]
  have hunit : ∀ a, σ a * a = 1 → IsUnit (π a) := fun a ha => by
    have hr : a * σ a = 1 := by
      have : IsArtinianRing 𝔸 := IsArtinianRing.of_finite ℝ 𝔸
      exact mul_eq_one_comm.1 ha
    have hs : σ (σ a) * σ a = 1 := by rw [invol, hr]
    exact ⟨⟨π a, π (σ a), by rw [← πm _ _ ha hs, hr, π1], by rw [← πm _ _ hs ha, ha, π1]⟩, rfl⟩
  have hmul : ∀ a b, σ a * a = 1 → σ b * b = 1 → σ (a * b) * (a * b) = 1 := fun a b ha hb => by
    rw [anti, mul_assoc, ← mul_assoc (σ a), ha, one_mul, hb]
  let s : 𝔸 → (H →L[ℂ] H)ˣ := fun a => if h : IsUnit (π a) then h.unit else 1
  have hs : ∀ a, σ a * a = 1 → (s a : H →L[ℂ] H) = π a := fun a ha => by
    simp only [s, dif_pos (hunit a ha), IsUnit.unit_spec]
  have hD : IsLieData σ L.subtype s :=
    ⟨anti, one, invol, L.injective_subtype,
      fun Z => ⟨fun h => ⟨⟨Z, (hL Z).2 h⟩, rfl⟩, by rintro ⟨Z, rfl⟩; exact (hL _).1 Z.2⟩,
      fun a b ha hb => Units.ext (by rw [Units.val_mul, hs _ ha, hs _ hb, hs _ (hmul a b ha hb), πm _ _ ha hb])⟩
  have hl := hasLog_of_isLieData _ _ _ _ _ _ hD
  have hu : ∀ Z : L, σ (exp Z.1) * exp Z.1 = 1 := fun Z => SecondKind.exp_unitary hD Z
  have he : ∀ Z : L, ((expMap L.subtype s Z : (H →L[ℂ] H)ˣ) : H →L[ℂ] H) = π (exp Z.1) := fun Z => hs _ (hu Z)
  have hprod : ∀ l : List L, σ (l.map fun Z => exp Z.1).prod * (l.map fun Z => exp Z.1).prod = 1 ∧
      (((l.map (expMap L.subtype s)).prod : (H →L[ℂ] H)ˣ) : H →L[ℂ] H) = π (l.map fun Z => exp Z.1).prod := fun l => by
    induction l with
    | nil => simp [one, π1]
    | cons Z l ih =>
      simp only [List.map_cons, List.prod_cons, Units.val_mul]
      exact ⟨hmul _ _ (hu Z) ih.1, by rw [he, ih.2, πm _ _ (hu Z) ih.1]⟩

  have d1 : ∀ Z : L, DifferentiableAt ℝ (fun t : ℝ => π (exp (t • Z.1)) v) 0 := fun Z => by
    have h := (hv 1 (fun _ => Z.1) fun _ => (hL _).1 Z.2).comp
      (contDiff_pi.2 fun _ => contDiff_id : ContDiff ℝ ∞ fun (t : ℝ) (_ : Fin 1) => t)
    have := (h.differentiable (by simp)).differentiableAt (x := 0)
    simpa [Function.comp_def] using this
  have hlin : ∀ (A : H →L[ℂ] H) (Z : L) (u : H), DifferentiableAt ℝ (fun t : ℝ => π (exp (t • Z.1)) u) 0 →
      HasDerivAt (fun t : ℝ => A (π (exp (t • Z.1)) u)) (A (dOp π Z.1 u)) 0 := fun A Z u h =>
    (A.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 h.hasDerivAt
  have d2 : ∀ Z Z' : L, DifferentiableAt ℝ (fun t : ℝ => π (exp (t • Z.1)) (dOp π Z'.1 v)) 0 := fun Z Z' => by
    have h := (hv 2 ![Z.1, Z'.1] (by
      intro i; fin_cases i
      · exact (hL _).1 Z.2
      · exact (hL _).1 Z'.2)).comp
      (contDiff_pi.2 (by
        intro i; fin_cases i
        · exact contDiff_fst
        · exact contDiff_snd) : ContDiff ℝ ∞ fun (p : ℝ × ℝ) => ![p.1, p.2])
    have h' : ContDiff ℝ ∞ (Function.uncurry fun (t r : ℝ) => π (exp (t • Z.1)) (π (exp (r • Z'.1)) v)) := by
      convert h using 1
      funext p
      have := πm _ _ (hu (p.1 • Z)) (hu (p.2 • Z'))
      simp only [Submodule.coe_smul] at this
      simp [Function.uncurry, this]
    have h3 : ContDiff ℝ ∞ fun t : ℝ =>
        fderiv ℝ (fun r : ℝ => π (exp (t • Z.1)) (π (exp (r • Z'.1)) v)) 0 (1 : ℝ) :=
      (ContDiff.fderiv (m := ∞) h' contDiff_const (by simp)).clm_apply contDiff_const
    have h4 := (h3.differentiable (by simp)).differentiableAt (x := 0)
    exact h4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => (hlin _ Z' v (d1 Z')).deriv.symm)

  let φ : H → H → (H →L[ℂ] H)ˣ → ℂ := fun w u g => ⟪w, (g : H →L[ℂ] H) u⟫_ℂ
  have hder : ∀ (w : H) (Z : L) (u : H), DifferentiableAt ℝ (fun t : ℝ => π (exp (t • Z.1)) u) 0 →
      Der (expMap L.subtype s) Z (φ w u) = φ w (dOp π Z.1 u) := fun w Z u h => by
    funext g
    have h1 := ((innerSL ℂ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 (hlin g Z u h)
    refine Eq.trans ?_ h1.deriv
    simp only [Der, φ, Units.val_mul, he]
    rfl
  have hsm : ∀ w, Sm (expMap L.subtype s) (φ w v) := fun w => by
    refine (SecondKind.main _ _ _ _ _ _ hD hl Set.univ Submodule.span_univ _).2 fun k Z _ g => ?_
    have h1 := (((innerSL ℂ w).comp (g : H →L[ℂ] H)).restrictScalars ℝ).contDiff.comp
      (hv k (fun i => (Z i).1) fun i => (hL _).1 (Z i).2)
    convert h1 using 1
    funext t
    have h2 := (hprod (List.ofFn fun i => t i • Z i)).2
    rw [List.map_ofFn, List.map_ofFn] at h2
    simp only [φ, Units.val_mul]
    exact congrArg (fun A : H →L[ℂ] H => ⟪w, (g : H →L[ℂ] H) (A v)⟫_ℂ) h2
  let X' : L := ⟨X, (hL _).2 hX⟩
  let Y' : L := ⟨Y, (hL _).2 hY⟩
  let Z' : L := ⟨X * Y - Y * X, (hL _).2 (by rw [map_sub, anti, anti, hX, hY]; noncomm_ring)⟩
  refine ⟨ext_inner_left ℂ fun w => ?_, ext_inner_left ℂ fun w => ?_⟩
  · have h := (der_smooth_and_linear _ _ _ _ _ _ hD hl _ (hsm w)).2.1 X' Y'
    rw [hder w _ _ (d1 _), hder w _ _ (d1 _), hder w _ _ (d1 _)] at h
    rw [inner_add_right]
    exact congrFun h 1
  · have h := Bracket.der_bracket _ _ _ _ _ _ hD hl _ (hsm w) X' Y' Z' rfl
    rw [hder w _ _ (d1 _), hder w _ _ (d1 _), hder w _ _ (d1 _), hder w _ _ (d2 _ _), hder w _ _ (d2 _ _)] at h
    rw [inner_sub_right]
    exact (congrFun h 1).symm

open Matrix Formalism.MainNotions.S Formalism.L2.Theta

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in

theorem dRep_add_and_bracket : ∀ (n : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (J : Matrix (Fin n) (Fin n) ℂ) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Jᴴ = J → IsUnit J.det → IsURepOn (Formalism.QuantumDeterminants.UH J) π → ∀ v, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0} π v → ∀ X ∈ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0}, ∀ Y ∈ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0}, dRep π (X + Y) v = dRep π X v + dRep π Y v ∧ dRep π (X * Y - Y * X) v = dRep π X (dRep π Y v) - dRep π Y (dRep π X v) := by
  intro n H _ _ J π hJ hd hπ v hv X hX Y hY
  let σ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun X => J⁻¹ * Xᴴ * J
      map_add' := fun X Y => by rw [conjTranspose_add, mul_add, add_mul]
      map_smul' := fun c X => by
        rw [conjTranspose_smul, star_trivial, mul_smul_comm, smul_mul_assoc]; rfl }
  have hσ : ∀ Z, σ Z = J⁻¹ * Zᴴ * J := fun _ => rfl
  have hskew : ∀ Z, σ Z = -Z ↔ Zᴴ * J + J * Z = 0 := fun Z => by
    rw [hσ]
    constructor
    · intro h1
      rw [← mul_nonsing_inv_cancel_left _ (Zᴴ * J) hd, ← mul_assoc J⁻¹, h1, mul_neg, neg_add_cancel]
    · intro h1
      rw [mul_assoc, eq_neg_of_add_eq_zero_left h1, mul_neg, nonsing_inv_mul_cancel_left _ _ hd]
  have hun : ∀ u, σ u * u = 1 → u ∈ Formalism.QuantumDeterminants.UH J := fun u h1 => by
    change uᴴ * J * u = J
    have := congrArg (J * ·) h1
    simpa only [hσ, ← mul_assoc, mul_nonsing_inv _ hd, one_mul, mul_one] using this
  refine abstract σ (fun a b => ?_) ?_ (fun a => ?_) π hπ.1.1 (fun a b ha hb => hπ.1.2 _ (hun a ha) _ (hun b hb)) v
    (fun k Xs h => hv k Xs fun i => (hskew _).1 (h i)) X ((hskew _).2 hX) Y ((hskew _).2 hY)
  · simp only [hσ, conjTranspose_mul, mul_assoc]
    rw [mul_nonsing_inv_cancel_left _ _ hd]
  · rw [hσ, conjTranspose_one, mul_one, nonsing_inv_mul _ hd]
  · rw [hσ, hσ, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_nonsing_inv, hJ]
    simp only [mul_assoc]
    rw [nonsing_inv_mul_cancel_left _ _ hd, nonsing_inv_mul _ hd, mul_one]

end GlobalTheory.DerivedAction

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefinitePairUnitVacuumRealPointNeZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VacRealForm

open GlobalTheory.FockCompare

theorem vacuum_real_ne_zero : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (W : G.Weil) {U : Set T} (N : GlobalTheory.FunObj.Std G U) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart W.θ σ → ∀ (t : T) (j : ℕ), j + 1 ≤ D.R.m → ∀ f, IsVacO W.ψ W.θ _ _ (G.cartS W.cart (.top t j)) (G.onT W.cart (.top t j)) (N.latS (.top t j) : Set _) (N.latT (.top t j) : Set _) f → ∃ z : GlobalTheory.FockCompare.RW (G.pT (.top t j)) (G.pS (.top t j)), f (GlobalTheory.FockCompare.iotaW σ (G.pT (.top t j)) (G.pS (.top t j)) z) ≠ 0 := by
  classical
  intro D T L sc G W U N σ h t j hj f hf
  by_contra hcon
  push_neg at hcon
  have hψ := hf.1
  have hS : IsSelfDualC (G.pS (.top t j)) (N.latS (.top t j)) :=
    N.selfDual (X := .top j) (show j ≤ D.R.m by omega)
  have hT : IsSelfDualC (G.pT (.top t j)) (N.latT (.top t j)) :=
    N.selfDual (X := .top (j + 1)) (show j + 1 ≤ D.R.m by omega)
  obtain ⟨-, h2, h3⟩ := GlobalTheory.T.self_dual_lattice_pairing_dual D W.ψ _ _ _ _ hψ hS hT
  have hinf := fun u => GlobalTheory.VacUnique.latO_inf (u := u) (G.pS (.top t j)) (G.pT (.top t j))
    ((N.latS (.top t j) : Set _)) ((N.latT (.top t j) : Set _)) fun _ => True
  choose ε _ hε2 using h3 f hf.2.lat
  have e : f = 0 := by
    funext w
    obtain ⟨γ, z, u, hu, rfl⟩ := GlobalTheory.VacUnique.exists_decomp h h2 w
    rw [hf.2.theta.quasi, GlobalTheory.VacUnique.apply_real_add h hψ (hinf u hu) (hε2 u hu f hf.2.lat), hcon z]
    simp
  obtain ⟨⟨p, hp⟩, hn⟩ := hf.2.norm
  have n1 := hn p hp
  rw [e] at n1
  simp [nrm2] at n1

end GlobalTheory.VacRealForm

end
end

