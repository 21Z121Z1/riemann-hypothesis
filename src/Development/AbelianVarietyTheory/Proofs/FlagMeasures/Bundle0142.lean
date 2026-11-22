import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommutantScalar
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0125
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
import Formalism.LocalToGlobal.HermitianForms.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsRiemannianHaarOnSubgroupMapMulRightUnitary
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.GaugeRightInv

open Topology

theorem map_mul_right_of_conj_nhds {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (ν : Measure G) [ν.IsMulLeftInvariant] (B : Set G) (hBm : MeasurableSet B) (hB : B ∈ 𝓝 (1 : G))
    (h0 : ν B ≠ 0) (ht : ν B ≠ ⊤) (l : G) (hl : ∀ g, g * l ∈ B ↔ l * g ∈ B) :
    ν.map (fun g => g * l) = ν := by
  have hU : (interior B).Nonempty := ⟨1, mem_interior_iff_mem_nhds.2 hB⟩
  have hmeas : Measurable (fun g : G => g * l) := measurable_mul_const l
  haveI : IsFiniteMeasureOnCompacts ν :=
    ⟨fun K hK => measure_lt_top_of_isCompact_of_isMulLeftInvariant' hU ht hK⟩

  have hVo : IsOpen ((fun g : G => g * l⁻¹) ⁻¹' interior B) :=
    isOpen_interior.preimage (continuous_mul_right l⁻¹)
  have hV : ν.map (fun g => g * l) ((fun g : G => g * l⁻¹) ⁻¹' interior B) = ν (interior B) := by
    rw [Measure.map_apply hmeas hVo.measurableSet]
    congr 1
    ext g
    simp [mul_assoc]
  haveI : IsFiniteMeasureOnCompacts (ν.map (fun g => g * l)) :=
    ⟨fun K hK => measure_lt_top_of_isCompact_of_isMulLeftInvariant _ hVo
      ⟨l, by simpa using mem_interior_iff_mem_nhds.2 hB⟩
      (by rw [hV]; exact ((measure_mono interior_subset).trans_lt ht.lt_top).ne) hK⟩

  obtain ⟨c₁, e₁⟩ : ∃ c : NNReal, ν = c • (Measure.haar : Measure G) :=
    ⟨_, Measure.isMulLeftInvariant_eq_smul ν Measure.haar⟩
  obtain ⟨c₂, e₂⟩ : ∃ c : NNReal, ν.map (fun g => g * l) = c • (Measure.haar : Measure G) :=
    ⟨_, Measure.isMulLeftInvariant_eq_smul _ Measure.haar⟩

  have hBB : ν.map (fun g => g * l) B = ν B := by
    rw [Measure.map_apply hmeas hBm,
      show (fun g => g * l) ⁻¹' B = (fun g => l * g) ⁻¹' B from Set.ext hl]
    exact measure_preimage_mul ν l B
  have hpos : (Measure.haar : Measure G) B ≠ 0 := (Measure.measure_pos_of_mem_nhds _ hB).ne'
  have hc₁ : (c₁ : ENNReal) ≠ 0 := by
    rintro h
    apply h0
    rw [e₁, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, h, zero_mul]
  have hfin : (Measure.haar : Measure G) B ≠ ⊤ := by
    intro h
    apply ht
    rw [e₁, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, h, ENNReal.mul_top hc₁]
  rw [e₂, e₁, Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def, ENNReal.smul_def,
    smul_eq_mul, smul_eq_mul, ENNReal.mul_left_inj hpos hfin] at hBB
  rw [e₂, e₁, ENNReal.coe_injective hBB]

theorem map_mul_right_of_conj_nhds_subgroup {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (M : Subgroup G) (hM : IsClosed (M : Set G)) (μ : Measure G) (hμ : μ (M : Set G)ᶜ = 0)
    (hinv : ∀ s ∈ M, μ.map (fun g => s * g) = μ) (B : Set G) (hBm : MeasurableSet B) (hB : B ∈ 𝓝 (1 : G))
    (h0 : μ B ≠ 0) (ht : μ B ≠ ⊤) (l : G) (hlM : l ∈ M) (hl : ∀ g, g * l ∈ B ↔ l * g ∈ B) :
    μ.map (fun g => g * l) = μ := by
  haveI : LocallyCompactSpace M := hM.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology M := inferInstanceAs (SecondCountableTopology (M : Set G))
  haveI : BorelSpace M := inferInstanceAs (BorelSpace (M : Set G))
  have emb : MeasurableEmbedding (Subtype.val : M → G) :=
    MeasurableEmbedding.subtype_coe hM.measurableSet

  set ν : Measure M := μ.comap Subtype.val with hν
  have hμν : ν.map Subtype.val = μ := by
    rw [hν, emb.map_comap, Subtype.range_coe]
    exact Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact hμ)
  haveI : ν.IsMulLeftInvariant := ⟨fun s => by
    ext A hA
    rw [Measure.map_apply (measurable_const_mul s) hA, hν, emb.comap_apply, emb.comap_apply]
    have himg : Subtype.val '' ((fun x => s * x) ⁻¹' A) =
        (fun x : G => (s : G) * x) ⁻¹' (Subtype.val '' A) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨s * y, hy, rfl⟩
      · rintro ⟨y, hy, hyx⟩
        have hx : x ∈ M := by
          have : x = (s : G)⁻¹ * y := by rw [hyx, ← mul_assoc, inv_mul_cancel, one_mul]
          rw [this]
          exact M.mul_mem (M.inv_mem s.2) y.2
        refine ⟨⟨x, hx⟩, ?_, rfl⟩
        show s * (⟨x, hx⟩ : M) ∈ A
        rw [show s * (⟨x, hx⟩ : M) = y from Subtype.ext hyx.symm]
        exact hy
    rw [himg, ← Measure.map_apply (measurable_const_mul (s : G)) (emb.measurableSet_image' hA),
      hinv s s.2]⟩
  have hνB : ν (Subtype.val ⁻¹' B) = μ B := by
    conv_rhs => rw [← hμν]
    rw [Measure.map_apply measurable_subtype_coe hBm]
  have key := map_mul_right_of_conj_nhds ν (Subtype.val ⁻¹' B)
    (hBm.preimage measurable_subtype_coe)
    (continuous_subtype_val.continuousAt.preimage_mem_nhds hB)
    (by rwa [hνB]) (by rwa [hνB]) ⟨l, hlM⟩ (fun g => hl g)
  rw [← hμν, Measure.map_map (measurable_mul_const l) measurable_subtype_coe,
    show (fun g : G => g * l) ∘ Subtype.val = Subtype.val ∘ (fun g : M => g * ⟨l, hlM⟩) from rfl,
    ← Measure.map_map measurable_subtype_coe (measurable_mul_const _), key]

theorem hs_eq_re_trace {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) : Formalism.REAL.hs X = (trace (X * Xᴴ)).re := by
  simp only [Formalism.REAL.hs, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [RCLike.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

private theorem hs_mul_mul_conjTranspose_of_unitary {n : ℕ} (L M : Matrix (Fin n) (Fin n) ℂ) (hL : Lᴴ * L = 1) :
    Formalism.REAL.hs (L * M * Lᴴ) = Formalism.REAL.hs M := by
  rw [hs_eq_re_trace, hs_eq_re_trace, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  congr 1
  calc trace (L * M * Lᴴ * (L * (Mᴴ * Lᴴ))) = trace (L * (M * Mᴴ) * Lᴴ) := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc Lᴴ L, hL, Matrix.one_mul]
    _ = trace (Lᴴ * (L * (M * Mᴴ))) := Matrix.trace_mul_comm _ _
    _ = trace (M * Mᴴ) := by rw [← Matrix.mul_assoc, hL, Matrix.one_mul]

theorem hs_conj {n : ℕ} (L X : Matrix (Fin n) (Fin n) ℂ) (hL : Lᴴ * L = 1) :
    Formalism.REAL.hs (L * X - 1) = Formalism.REAL.hs (X * L - 1) := by
  have hL' : L * Lᴴ = 1 := mul_eq_one_comm.mp hL

  have h : L * X - 1 = L * (X * L - 1) * Lᴴ := by
    simp only [mul_sub, sub_mul, mul_one, mul_assoc, hL']
  rw [h, hs_mul_mul_conjTranspose_of_unitary L _ hL]

theorem isGaugeSub_map_mul_right (n : ℕ) (ε : Fin n → Bool) (M : Subgroup (Formalism.REAL.UJ ε)) (d : ℕ)
    (μ : Measure (Formalism.REAL.UJ ε)) (hM : IsClosed (M : Set (Formalism.REAL.UJ ε)))
    (hμ : IsGaugeSub (M : Set (Formalism.REAL.UJ ε)) d μ) (l : Formalism.REAL.UJ ε) (hlM : l ∈ M) (hlK : l ∈ maxK ε) :
    μ.map (fun g => g * l) = μ := by
  unfold IsGaugeSub at hμ
  obtain ⟨hμc, hinv, hlim⟩ := hμ
  have hlU : (uMat l)ᴴ * uMat l = 1 := by unfold maxK at hlK; exact hlK

  obtain ⟨r, ⟨h1, h2⟩, hr⟩ : ∃ r : ℝ,
      μ {g | √(Formalism.REAL.hs (uMat g - 1)) ≤ r} / ENNReal.ofReal (r ^ d) ∈ Set.Ioo 0 ⊤ ∧ 0 < r := by
    refine ((hlim.eventually (Ioo_mem_nhds ?_ ?_)).and self_mem_nhdsWithin).exists
    · exact Metric.measure_ball_pos _ _ one_pos
    · exact measure_ball_lt_top
  have hB0 : μ {g | √(Formalism.REAL.hs (uMat g - 1)) ≤ r} ≠ 0 := by
    intro h
    rw [h, ENNReal.zero_div] at h1
    exact lt_irrefl _ h1
  have hBt : μ {g | √(Formalism.REAL.hs (uMat g - 1)) ≤ r} ≠ ⊤ := by
    intro h
    rw [h, ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top] at h2
    exact lt_irrefl _ h2
  have hu : Continuous fun g : Formalism.REAL.UJ ε => uMat g := by
    unfold uMat
    fun_prop
  have hc : Continuous fun g : Formalism.REAL.UJ ε => √(Formalism.REAL.hs (uMat g - 1)) := by
    unfold Formalism.REAL.hs
    fun_prop
  have hBn : {g | √(Formalism.REAL.hs (uMat g - 1)) ≤ r} ∈ 𝓝 (1 : Formalism.REAL.UJ ε) := by
    have h1' : √(Formalism.REAL.hs (uMat (1 : Formalism.REAL.UJ ε) - 1)) < r := by
      rw [show uMat (1 : Formalism.REAL.UJ ε) = 1 from rfl, sub_self]
      simp [Formalism.REAL.hs, hr]
    exact Filter.mem_of_superset ((isOpen_lt hc continuous_const).mem_nhds h1') fun g hg =>
      show √(Formalism.REAL.hs (uMat g - 1)) ≤ r from le_of_lt hg

  have hcomm : ∀ g, g * l ∈ {g | √(Formalism.REAL.hs (uMat g - 1)) ≤ r} ↔
      l * g ∈ {g | √(Formalism.REAL.hs (uMat g - 1)) ≤ r} := by
    intro g
    show √(Formalism.REAL.hs (uMat (g * l) - 1)) ≤ r ↔ √(Formalism.REAL.hs (uMat (l * g) - 1)) ≤ r
    rw [show uMat (g * l) = uMat g * uMat l from rfl, show uMat (l * g) = uMat l * uMat g from rfl,
      hs_conj (uMat l) (uMat g) hlU]
  exact map_mul_right_of_conj_nhds_subgroup M hM μ hμc hinv _
    (isClosed_le hc continuous_const).measurableSet hBn hB0 hBt l hlM hcomm

end GlobalTheory.GaugeRightInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsURepTensor
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.HilbTensorUnitary

open GlobalTheory.HilbTensorRep

theorem isURep_tensor {ι : Type} [Fintype ι] {H : ι → Type} [∀ i, NormedAddCommGroup (H i)]
    [∀ i, InnerProductSpace ℂ (H i)] {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
    {tens : (∀ i, H i) → Hs} {G : ι → Type} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
    {π : ∀ i, G i →* (H i →L[ℂ] H i)} {σs : (∀ i, G i) → (Hs →L[ℂ] Hs)}
    (hi : ∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ i, ⟪x i, y i⟫_ℂ)
    (hd : Dense (Submodule.span ℂ (Set.range tens) : Set Hs))
    (hs : ∀ g x, σs g (tens x) = tens fun i => π i (g i) (x i))
    (hn : ∀ i g a, ‖π i g a‖ = ‖a‖) (hc : ∀ i a, Continuous fun g => π i g a) :
    IsURep σs := by
  classical
  have h1 : σs 1 = 1 := by
    apply ext_op hd
    intro x
    rw [hs]
    simp
  have hmul : ∀ a b, σs (a * b) = (σs a).comp (σs b) := by
    intro a b
    apply ext_op hd
    intro x
    rw [ContinuousLinearMap.comp_apply, hs, hs, hs]
    simp [Pi.mul_apply, map_mul, ContinuousLinearMap.mul_apply]
  have hnorm : ∀ g u, ‖σs g u‖ = ‖u‖ := by
    intro g u
    have key : ⟪σs g u, σs g u⟫_ℂ = ⟪u, u⟫_ℂ := by
      rw [← inner_inv hi hd hs hn g (σs g u) u, ← ContinuousLinearMap.comp_apply, ← hmul,
        inv_mul_cancel, h1, ContinuousLinearMap.one_apply]
    have h2 : ‖σs g u‖ ^ 2 = ‖u‖ ^ 2 := by
      rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ), key]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2
  let S : Submodule ℂ Hs :=
    { carrier := {u | Continuous fun g => σs g u}
      add_mem' := fun {a b} ha hb => by
        show Continuous fun g => σs g (a + b)
        simp only [map_add]
        exact ha.add hb
      zero_mem' := by
        show Continuous fun g => σs g 0
        simp only [map_zero]
        exact continuous_const
      smul_mem' := fun c a ha => by
        show Continuous fun g => σs g (c • a)
        simp only [map_smul]
        exact ha.const_smul c }
  have hmemS : ∀ u, u ∈ S ↔ Continuous fun g => σs g u := fun u => Iff.rfl
  have htens : ∀ x, tens x ∈ S := by
    intro x
    rw [hmemS]
    have e : (fun g => σs g (tens x)) = fun g => tens fun i => π i (g i) (x i) := by
      funext g
      exact hs g x
    rw [e]
    exact (continuous_tens hi).comp (continuous_pi fun i => (hc i (x i)).comp (continuous_apply i))
  have hclosed : IsClosed (S : Set Hs) := by
    apply isClosed_of_closure_subset
    intro u hu
    show Continuous fun g => σs g u
    rw [continuous_iff_continuousAt]
    intro g0
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨b, hb, hub⟩ := Metric.mem_closure_iff.1 hu (ε / 3) (by positivity)
    have hbc : Continuous fun g => σs g b := hb
    filter_upwards [Metric.tendsto_nhds.1 hbc.continuousAt (ε / 3) (by positivity)] with g hg
    have d1 : dist (σs g u) (σs g b) = dist u b := by
      rw [dist_eq_norm, ← map_sub, hnorm, ← dist_eq_norm]
    have d2 : dist (σs g0 b) (σs g0 u) = dist u b := by
      rw [dist_eq_norm, ← map_sub, hnorm, ← dist_eq_norm, dist_comm]
    calc dist (σs g u) (σs g0 u)
        ≤ dist (σs g u) (σs g b) + dist (σs g b) (σs g0 b) + dist (σs g0 b) (σs g0 u) :=
          dist_triangle4 _ _ _ _
      _ < ε / 3 + ε / 3 + ε / 3 := by rw [d1, d2]; linarith
      _ = ε := by ring
  have hall : ∀ u, u ∈ S := by
    intro u
    have hle : (Submodule.span ℂ (Set.range tens) : Set Hs) ⊆ S :=
      Submodule.span_le.2 (by rintro _ ⟨x, rfl⟩; exact htens x)
    have hcl := closure_minimal hle hclosed
    rw [hd.closure_eq] at hcl
    exact hcl (Set.mem_univ u)
  exact ⟨h1, hmul, hnorm, fun u => hall u⟩

theorem isURep_rows :
    ∀ B : RowsAut, (∀ v, IsURepOn (UJset (B.I.ε v)) (B.σ v)) → IsURep B.σs := by
  intro B hB
  have hmem : ∀ v (g : Formalism.REAL.UJ (B.I.ε v)), uMat g ∈ UJset (B.I.ε v) := fun v g => g.2
  have hcu : ∀ v, Continuous fun g : Formalism.REAL.UJ (B.I.ε v) => uMat g :=
    fun v => Units.continuous_val.comp continuous_subtype_val
  exact isURep_tensor (H := B.H) (tens := B.tens)
    (π := fun v =>
      { toFun := fun g => B.σ v (uMat g)
        map_one' := (hB v).1.1
        map_mul' := fun a b => (hB v).1.2 _ (hmem v a) _ (hmem v b) })
    B.tens_spec.1 B.tens_spec.2.2 (fun g x => B.tens_spec.2.1 g x)
    (fun v g a => (hB v).2.1 _ (hmem v g) a)
    (fun v a => ((hB v).2.2 a).comp_continuous (hcu v) (hmem v))

end GlobalTheory.HilbTensorUnitary
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagLeviMaxCompactClosedSubgroups
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

noncomputable section

namespace GlobalTheory.FlagLeviGroup

variable {n : ℕ} {ε : Fin n → Bool}

theorem uMat_mul (g h : Formalism.REAL.UJ ε) : uMat (g * h) = uMat g * uMat h := rfl

theorem uMat_one : uMat (1 : Formalism.REAL.UJ ε) = 1 := rfl

theorem uMat_mul_inv (g : Formalism.REAL.UJ ε) : uMat g * uMat g⁻¹ = 1 := by
  rw [← uMat_mul, mul_inv_cancel, uMat_one]

theorem uMat_inv_mul (g : Formalism.REAL.UJ ε) : uMat g⁻¹ * uMat g = 1 := by
  rw [← uMat_mul, inv_mul_cancel, uMat_one]

theorem continuous_uMat : Continuous (fun g : Formalism.REAL.UJ ε => uMat g) :=
  Units.continuous_val.comp continuous_subtype_val

theorem inv_keeps {A B : Matrix (Fin n) (Fin n) ℂ} (hBA : B * A = 1) (V : Submodule ℂ (Fin n → ℂ))
    (hA : ∀ y ∈ V, A *ᵥ y ∈ V) : ∀ y ∈ V, B *ᵥ y ∈ V := by
  have hA' : ∀ y ∈ V, Matrix.toLin' A y ∈ V := fun y hy => by simpa using hA y hy
  have hinj : Function.Injective ((Matrix.toLin' A).restrict hA') := by
    intro x y hxy
    have h1 : A *ᵥ (x : Fin n → ℂ) = A *ᵥ (y : Fin n → ℂ) := by
      simpa using congrArg Subtype.val hxy
    have h2 := congrArg (fun z => B *ᵥ z) h1
    simp only [Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec] at h2
    exact Subtype.ext h2
  have hsurj := LinearMap.injective_iff_surjective.mp hinj
  intro y hy
  obtain ⟨x, hx⟩ := hsurj ⟨y, hy⟩
  have h1 : A *ᵥ (x : Fin n → ℂ) = y := by
    simpa using congrArg Subtype.val hx
  rw [← h1, Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec]
  exact x.2

variable (ε) in

def leviSub {a : ℕ} (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) : Subgroup (Formalism.REAL.UJ ε) where
  carrier := flagM ε W
  one_mem' := by
    intro i y hy
    simpa [uMat_one] using hy
  mul_mem' := by
    intro g h hg hh i y hy
    rw [uMat_mul, Matrix.conjTranspose_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact ⟨(hg i _ (hh i y hy).1).1, (hh i _ (hg i y hy).2).2⟩
  inv_mem' := by
    intro g hg i y hy
    refine ⟨inv_keeps (uMat_inv_mul g) (W i) (fun z hz => (hg i z hz).1) y hy,
      inv_keeps (A := (uMat g)ᴴ) ?_ (W i) (fun z hz => (hg i z hz).2) y hy⟩
    rw [← Matrix.conjTranspose_mul, uMat_mul_inv, Matrix.conjTranspose_one]

variable (ε) in

def compactSub : Subgroup (Formalism.REAL.UJ ε) where
  carrier := maxK ε
  one_mem' := by
    show (uMat (1 : Formalism.REAL.UJ ε))ᴴ * uMat (1 : Formalism.REAL.UJ ε) = 1
    simp [uMat_one]
  mul_mem' := by
    intro g h hg hh
    have hg' : (uMat g)ᴴ * uMat g = 1 := hg
    have hh' : (uMat h)ᴴ * uMat h = 1 := hh
    show (uMat (g * h))ᴴ * uMat (g * h) = 1
    rw [uMat_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (uMat g)ᴴ, hg',
      Matrix.one_mul, hh']
  inv_mem' := by
    intro g hg
    have hg' : (uMat g)ᴴ * uMat g = 1 := hg
    have h1 : uMat g⁻¹ = (uMat g)ᴴ := by
      calc uMat g⁻¹ = ((uMat g)ᴴ * uMat g) * uMat g⁻¹ := by rw [hg', Matrix.one_mul]
        _ = (uMat g)ᴴ := by rw [Matrix.mul_assoc, uMat_mul_inv, Matrix.mul_one]
    show (uMat g⁻¹)ᴴ * uMat g⁻¹ = 1
    conv_lhs => enter [1]; rw [h1, Matrix.conjTranspose_conjTranspose]
    exact uMat_mul_inv g

theorem isClosed_flagM {a : ℕ} (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) : IsClosed (flagM ε W) := by
  have h : flagM ε W = ⋂ i, ⋂ y ∈ W i,
      ((fun g : Formalism.REAL.UJ ε => uMat g *ᵥ y) ⁻¹' (W i : Set (Fin n → ℂ)) ∩
        (fun g : Formalism.REAL.UJ ε => (uMat g)ᴴ *ᵥ y) ⁻¹' (W i : Set (Fin n → ℂ))) := by
    ext g
    simp only [flagM, Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe]
    rfl
  rw [h]
  refine isClosed_iInter fun i => isClosed_iInter fun y => isClosed_iInter fun _ => ?_
  exact ((W i).closed_of_finiteDimensional.preimage
      (continuous_uMat.matrix_mulVec continuous_const)).inter
    ((W i).closed_of_finiteDimensional.preimage
      (continuous_uMat.matrix_conjTranspose.matrix_mulVec continuous_const))

theorem isClosed_maxK : IsClosed (maxK ε) :=
  isClosed_eq (continuous_uMat.matrix_conjTranspose.matrix_mul continuous_uMat) continuous_const

theorem conj_sub (m u : Formalism.REAL.UJ ε) (y : Fin n → ℂ) :
    uMat (m * u * m⁻¹) *ᵥ y - y = uMat m *ᵥ (uMat u *ᵥ (uMat m⁻¹ *ᵥ y) - uMat m⁻¹ *ᵥ y) := by
  rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec y (uMat m) (uMat m⁻¹), uMat_mul_inv, Matrix.one_mulVec,
    uMat_mul, uMat_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

theorem form_inv (m : Formalism.REAL.UJ ε) (x y : Fin n → ℂ) :
    star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ (uMat m⁻¹ *ᵥ y)) = star (uMat m *ᵥ x) ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) := by
  have hm : (uMat m)ᴴ * Formalism.REAL.Jm ε * uMat m = Formalism.REAL.Jm ε := m.2
  have h1 : Formalism.REAL.Jm ε * uMat m⁻¹ = (uMat m)ᴴ * Formalism.REAL.Jm ε := by
    calc Formalism.REAL.Jm ε * uMat m⁻¹ = ((uMat m)ᴴ * Formalism.REAL.Jm ε * uMat m) * uMat m⁻¹ := by rw [hm]
      _ = _ := by rw [Matrix.mul_assoc, uMat_mul_inv, Matrix.mul_one]
  rw [Matrix.mulVec_mulVec, h1, ← Matrix.mulVec_mulVec, Matrix.star_mulVec, Matrix.dotProduct_mulVec]

theorem conj_mem_flagN {a : ℕ} (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) {m u : Formalism.REAL.UJ ε}
    (hm : m ∈ flagM ε W) (hu : u ∈ flagN ε W) : m * u * m⁻¹ ∈ flagN ε W := by
  have hm' : m⁻¹ ∈ flagM ε W := (leviSub ε W).inv_mem hm
  refine ⟨fun i y hy => ?_, fun y hy => ?_⟩
  · rw [conj_sub]
    exact (hm _ _ (hu.1 i _ (hm' _ y hy).1)).1
  · rw [conj_sub]
    refine (hm _ _ (hu.2 _ fun x hx => ?_)).1
    rw [form_inv]
    exact hy _ (hm _ x hx).1

theorem levi_compact_subgroups : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ)
    (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)),
    (∃ M : Subgroup (Formalism.REAL.UJ ε), (M : Set (Formalism.REAL.UJ ε)) = flagM ε W) ∧ IsClosed (flagM ε W) ∧
    (∃ K : Subgroup (Formalism.REAL.UJ ε), (K : Set (Formalism.REAL.UJ ε)) = maxK ε) ∧ IsClosed (maxK ε) ∧
    ∀ m ∈ flagM ε W, ∀ u ∈ flagN ε W, m * u * m⁻¹ ∈ flagN ε W :=
  fun _ ε _ W => ⟨⟨leviSub ε W, rfl⟩, isClosed_flagM W, ⟨compactSub ε, rfl⟩, isClosed_maxK,
    fun _ hm _ hu => conj_mem_flagN W hm hu⟩

end GlobalTheory.FlagLeviGroup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatUnipMapMulVec
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.PointLattice

section General

variable {E A n : Type} [Field E] [CommRing A] [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
theorem latUnip_map_mulVec (ι : E →+* A) (M : Matrix n n E) (y : n → E) :
    (fun i => ι ((M *ᵥ y) i)) = M.map ι *ᵥ fun i => ι (y i) := by
  funext i
  exact RingHom.map_mulVec ι M y i

theorem latUnip_conj_pow (X Y G : Matrix n n A) (h : X * Y = 1) (m : ℕ) :
    (Y * G * X - 1) ^ m * Y = Y * (G - 1) ^ m := by
  have h1 : (Y * G * X - 1) * Y = Y * (G - 1) := by
    rw [sub_mul, one_mul, mul_assoc (Y * G), h, mul_one, mul_sub, mul_one]
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, mul_assoc, h1, ← mul_assoc, ih, mul_assoc, ← pow_succ]

end General

theorem lamX_unipMod : ∀ (I : AutInst) (x a : I.GA) (γ : GL (Fin I.n) I.E) (l : ℕ), 1 ≤ l → I.fmat a.2 = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) → (x⁻¹ * a * x).2 ∈ I.Kset → I.UnipMod l (x⁻¹ * a * x).2 → (∀ y ∈ lamX I x, (γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ y ∈ lamX I x) ∧ ∀ y ∈ lamX I x, ∃ z ∈ lamX I x, (((γ : Matrix (Fin I.n) (Fin I.n) I.E) - 1) ^ I.n) *ᵥ y = (l : I.E) • z := by
  intro I x a γ l hl hfa hk hu
  have hK : ∀ w, w ∈ I.Lf ↔ I.fmat (x⁻¹ * a * x).2 *ᵥ w ∈ I.Lf := hk
  have hmem : ∀ y, y ∈ lamX I x ↔
      I.fmat x.2⁻¹ *ᵥ (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (y i)) ∈ I.Lf := (lamX_selfDual I x).1
  have hconj : I.fmat (x⁻¹ * a * x).2 = I.fmat x.2⁻¹ * I.fmat a.2 * I.fmat x.2 := rfl
  have hXY : I.fmat x.2 * I.fmat x.2⁻¹ = 1 := by
    show I.fmat (x.2 * x.2⁻¹) = 1
    rw [mul_inv_cancel]
    rfl
  have key : ∀ y, I.fmat x.2⁻¹ *ᵥ (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (((γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ y) i)) =
      I.fmat (x⁻¹ * a * x).2 *ᵥ (I.fmat x.2⁻¹ *ᵥ fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (y i)) := by
    intro y
    rw [latUnip_map_mulVec (Formalism.UG.inclE (F := I.F) (Af I.F)) (γ : Matrix (Fin I.n) (Fin I.n) I.E) y, ← hfa, hconj, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, mul_assoc (I.fmat x.2⁻¹ * I.fmat a.2), hXY, mul_one]
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · rw [hmem, key]
    exact (hK _).1 ((hmem y).1 hy)
  · obtain ⟨w, hw, hwe⟩ := hu _ ((hmem y).1 hy)
    have hl0 : (l : I.E) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    refine ⟨(l : I.E)⁻¹ • ((((γ : Matrix (Fin I.n) (Fin I.n) I.E) - 1) ^ I.n) *ᵥ y), ?_, ?_⟩
    · rw [hmem]
      have hpow : (((γ : Matrix (Fin I.n) (Fin I.n) I.E) - 1) ^ I.n).map (Formalism.UG.inclE (F := I.F) (Af I.F)) = (I.fmat a.2 - 1) ^ I.n := by
        rw [hfa, ← RingHom.mapMatrix_apply, map_pow, map_sub, map_one, RingHom.mapMatrix_apply]
      have hcp := latUnip_conj_pow (I.fmat x.2) (I.fmat x.2⁻¹) (I.fmat a.2) hXY I.n
      have e1 : (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (((l : I.E)⁻¹ • ((((γ : Matrix (Fin I.n) (Fin I.n) I.E) - 1) ^ I.n) *ᵥ y)) i)) =
          Formalism.UG.inclE (F := I.F) (Af I.F) ((l : I.E)⁻¹) • fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (((((γ : Matrix (Fin I.n) (Fin I.n) I.E) - 1) ^ I.n) *ᵥ y) i) := by
        funext i
        simp only [Pi.smul_apply, smul_eq_mul, map_mul]
      have e2 : I.fmat x.2⁻¹ *ᵥ (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (((((γ : Matrix (Fin I.n) (Fin I.n) I.E) - 1) ^ I.n) *ᵥ y) i)) =
          (l : TensorProduct I.F I.E (Af I.F)) • w := by
        rw [latUnip_map_mulVec (Formalism.UG.inclE (F := I.F) (Af I.F)) (((γ : Matrix (Fin I.n) (Fin I.n) I.E) - 1) ^ I.n) y, hpow, Matrix.mulVec_mulVec, ← hcp,
          ← Matrix.mulVec_mulVec, ← hconj, hwe]
      rw [e1, Matrix.mulVec_smul, e2, smul_smul, ← map_natCast (Formalism.UG.inclE (F := I.F) (Af I.F)) l, ← map_mul,
        inv_mul_cancel₀ hl0, map_one, one_smul]
      exact hw
    · rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]

end GlobalTheory.PointLattice
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalSpanOfLatticeAtPlaceEqForAlmostAllPlacesStatement
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localSpanOfLatticeAtPlace_eq_for_almost_all_places : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L M : Submodule (𝓞 E) (Fin n → E)), IsLat L → IsLat M → {v : HeightOneSpectrum (𝓞 F) | loc v L ≠ loc v M}.Finite := by
  first | exact @GlobalTheory.St.G.loc_eq_almost_all | exact GlobalTheory.St.G.loc_eq_almost_all | (intros; apply GlobalTheory.St.G.loc_eq_almost_all <;> assumption)
end

