import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1097
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1129
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1122
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1117
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0008
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1119
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1086
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedUnip
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.UnipDom

noncomputable section

namespace GlobalTheory.ThK.UnipClosed

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def carrierSet (σ : E →ₐ[F] E) {d d₁ : ℕ} (W : Spc F E d) (H' : Plane E d d₁) : Set (UA σ W.J) :=
  {u | mat u *ᵥ incV F H'.x = incV F H'.x ∧
    ∀ z, ∃ a : AE F E, mat u *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + a • incV F H'.x}

theorem mat_mul {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g h : UA σ J) :
    mat (g * h) = mat g * mat h := rfl

theorem mat_inv_mul {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) :
    mat g⁻¹ * mat g = 1 := by
  show ((g⁻¹ : UA σ J).1.1) * g.1.1 = 1
  rw [← Units.val_mul]
  show (((g⁻¹ * g : UA σ J) : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) = 1
  simp

theorem mat_one {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} :
    mat (1 : UA σ J) = 1 := rfl

def carrierSub (σ : E →ₐ[F] E) {d d₁ : ℕ} (W : Spc F E d) (H' : Plane E d d₁) : Subgroup (UA σ W.J) where
  carrier := carrierSet σ W H'
  one_mem' := ⟨by rw [mat_one, Matrix.one_mulVec], fun z => ⟨0, by rw [mat_one, Matrix.one_mulVec, zero_smul, add_zero]⟩⟩
  mul_mem' := by
    rintro u v ⟨hu1, hu2⟩ ⟨hv1, hv2⟩
    refine ⟨by rw [mat_mul, ← Matrix.mulVec_mulVec, hv1, hu1], fun z => ?_⟩
    obtain ⟨a, ha⟩ := hu2 z
    obtain ⟨b, hb⟩ := hv2 z
    refine ⟨a + b, ?_⟩
    rw [mat_mul, ← Matrix.mulVec_mulVec, hb, Matrix.mulVec_add, ha, Matrix.mulVec_smul, hu1, add_smul, add_assoc]
  inv_mem' := by
    rintro u ⟨hu1, hu2⟩
    have hx : mat u⁻¹ *ᵥ incV F H'.x = incV F H'.x := by
      conv_lhs => rw [← hu1]
      rw [Matrix.mulVec_mulVec, mat_inv_mul, Matrix.one_mulVec]
    refine ⟨hx, fun z => ?_⟩
    obtain ⟨a, ha⟩ := hu2 z
    refine ⟨-a, ?_⟩
    have h1 : mat u⁻¹ *ᵥ (mat u *ᵥ (incM F H'.ι *ᵥ z)) = incM F H'.ι *ᵥ z := by
      rw [Matrix.mulVec_mulVec, mat_inv_mul, Matrix.one_mulVec]
    rw [ha, Matrix.mulVec_add, Matrix.mulVec_smul, hx] at h1
    rw [neg_smul, ← sub_eq_add_neg, eq_sub_iff_add_eq]
    exact h1

theorem unip_eq (σ : E →ₐ[F] E) {d d₁ : ℕ} (W : Spc F E d) (H' : Plane E d d₁) :
    unip σ W H' = carrierSub σ W H' := by
  apply le_antisymm
  · exact (Subgroup.closure_le _).2 fun u hu => hu
  · intro u hu
    exact Subgroup.subset_closure hu

section Top

variable [T2Space (AE F E)] [IsTopologicalRing (AE F E)]

theorem isClosed_line {d : ℕ} (x : Fin d → E) : IsClosed {w : Fin d → AE F E | ∃ a : AE F E, w = a • incV F x} := by
  by_cases hx : x = 0
  · have : {w : Fin d → AE F E | ∃ a : AE F E, w = a • incV F x} = {0} := by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      have h0 : incV F x = 0 := by
        funext i
        simp [incV, hx]
      simp [h0]
    rw [this]
    exact isClosed_singleton
  · obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hx (funext h)
    have hinv : incV F x i * inclR (F := F) (AF F) (x i)⁻¹ = 1 := by
      simp only [incV, ← map_mul, mul_inv_cancel₀ hi, map_one]
    have : {w : Fin d → AE F E | ∃ a : AE F E, w = a • incV F x} =
        {w | w = (w i * inclR (F := F) (AF F) (x i)⁻¹) • incV F x} := by
      ext w
      simp only [Set.mem_setOf_eq]
      constructor
      · rintro ⟨a, rfl⟩
        congr 1
        simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, hinv, mul_one]
      · intro h
        exact ⟨_, h⟩
    rw [this]
    exact isClosed_eq continuous_id
      (((continuous_apply i).mul continuous_const).smul continuous_const)

end Top

variable [T2Space (AE F E)] [IsTopologicalRing (AE F E)] in
theorem isClosed_carrierSet (σ : E →ₐ[F] E) {d d₁ : ℕ} (W : Spc F E d) (H' : Plane E d d₁) :
    IsClosed (carrierSet σ W H') := by
  have hm : Continuous fun u : UA σ W.J => mat u := Units.continuous_val.comp continuous_subtype_val
  have h1 : IsClosed {u : UA σ W.J | mat u *ᵥ incV F H'.x = incV F H'.x} :=
    isClosed_eq (hm.matrix_mulVec continuous_const) continuous_const
  have h2 : ∀ z : Fin d₁ → AE F E, IsClosed {u : UA σ W.J | ∃ a : AE F E,
      mat u *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + a • incV F H'.x} := by
    intro z
    have : {u : UA σ W.J | ∃ a : AE F E, mat u *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + a • incV F H'.x} =
        (fun u : UA σ W.J => mat u *ᵥ (incM F H'.ι *ᵥ z) - incM F H'.ι *ᵥ z) ⁻¹'
          {w | ∃ a : AE F E, w = a • incV F H'.x} := by
      ext u
      simp only [Set.mem_setOf_eq, Set.mem_preimage, sub_eq_iff_eq_add']
    rw [this]
    exact (isClosed_line H'.x).preimage ((hm.matrix_mulVec continuous_const).sub continuous_const)
  have : carrierSet σ W H' = {u : UA σ W.J | mat u *ᵥ incV F H'.x = incV F H'.x} ∩
      ⋂ z : Fin d₁ → AE F E, {u : UA σ W.J | ∃ a : AE F E,
        mat u *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + a • incV F H'.x} := by
    ext u
    simp [carrierSet]
  rw [this]
  exact h1.inter (isClosed_iInter h2)

theorem isClosed_unip : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (d d₁ : ℕ) (W : Spc F E d) (H' : Plane E d d₁), IsClosed ((unip σ W H' : Subgroup (UA σ W.J)) : Set (UA σ W.J)) := by
  intro F E _ _ _ _ _ σ d d₁ W H'
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  rw [unip_eq]
  exact isClosed_carrierSet σ W H'

end GlobalTheory.ThK.UnipClosed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspFunOfTransvectionConstantTermsZero
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TransvCusp

section Abstract

variable {N : Type} [Group N] [TopologicalSpace N] [IsTopologicalGroup N] [MeasurableSpace N] [BorelSpace N]
  {Γ : Subgroup N} [Countable Γ] {μ : Measure N} [μ.IsMulLeftInvariant] {𝓕 : Set N}

theorem fd_preimage (h : IsFundamentalDomain Γ 𝓕 μ) {z : N} (hz : ∀ n, z * n = n * z) :
    IsFundamentalDomain Γ ((fun n => z * n) ⁻¹' 𝓕) μ :=
  h.preimage_of_equiv (measurePreserving_mul_left μ z).quasiMeasurePreserving (e := id) Function.bijective_id
    fun γ n => by
      change z * ((γ : N) * n) = (γ : N) * (z * n)
      rw [← mul_assoc, hz, mul_assoc]

theorem inv_shift {B : Type} {z : N} (hz : ∀ n, z * n = n * z) {F : N → B} (hF : ∀ (γ : Γ) n, F ((γ : N) * n) = F n)
    (γ : Γ) (n : N) : F (z * (γ • n)) = F (z * n) := by
  change F (z * ((γ : N) * n)) = _
  rw [← mul_assoc, hz, mul_assoc, hF]

theorem setIntegral_shift {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B] (h : IsFundamentalDomain Γ 𝓕 μ)
    {z : N} (hz : ∀ n, z * n = n * z) {F : N → B} (hF : ∀ (γ : Γ) n, F ((γ : N) * n) = F n) :
    ∫ n in 𝓕, F (z * n) ∂μ = ∫ n in 𝓕, F n ∂μ := by
  rw [h.setIntegral_eq (fd_preimage h hz) (f := fun n => F (z * n)) (inv_shift hz hF)]
  exact (measurePreserving_mul_left μ z).setIntegral_preimage_emb (MeasurableEquiv.mulLeft z).measurableEmbedding F 𝓕

theorem integrableOn_shift {B : Type} [NormedAddCommGroup B] (h : IsFundamentalDomain Γ 𝓕 μ)
    {z : N} (hz : ∀ n, z * n = n * z) {F : N → B} (hF : ∀ (γ : Γ) n, F ((γ : N) * n) = F n)
    (hi : IntegrableOn F 𝓕 μ) : IntegrableOn (fun n => F (z * n)) 𝓕 μ := by
  rw [h.integrableOn_iff (fd_preimage h hz) (f := fun n => F (z * n)) (inv_shift hz hF)]
  exact ((measurePreserving_mul_left μ z).integrableOn_comp_preimage
    (MeasurableEquiv.mulLeft z).measurableEmbedding).2 hi

theorem setIntegral_eq_zero [SecondCountableTopology N] [SFinite μ] {Z : Type} [TopologicalSpace Z] [MeasurableSpace Z]
    [OpensMeasurableSpace Z] (ν : Measure Z) [IsFiniteMeasure ν] (hν : ν ≠ 0) (i : Z → N) (hi : Continuous i)
    (hz : ∀ z n, i z * n = n * i z) (h : IsFundamentalDomain Γ 𝓕 μ) {F : N → ℂ} (hc : Continuous F)
    (hF : ∀ (γ : Γ) n, F ((γ : N) * n) = F n) (h0 : ∀ n, ∫ z, F (i z * n) ∂ν = 0) : ∫ n in 𝓕, F n ∂μ = 0 := by
  by_cases hI : IntegrableOn F 𝓕 μ
  swap
  · exact integral_undef hI
  have hm : AEStronglyMeasurable (Function.uncurry fun (z : Z) (n : N) => F (i z * n)) (ν.prod (μ.restrict 𝓕)) :=
    (hc.comp ((hi.comp continuous_fst).mul continuous_snd)).aestronglyMeasurable
  have hp : Integrable (Function.uncurry fun (z : Z) (n : N) => F (i z * n)) (ν.prod (μ.restrict 𝓕)) := by
    refine (integrable_prod_iff hm).2 ⟨Filter.Eventually.of_forall fun z => integrableOn_shift h (hz z) hF hI, ?_⟩
    have e : (fun z : Z => ∫ n in 𝓕, ‖F (i z * n)‖ ∂μ) = fun _ => ∫ n in 𝓕, ‖F n‖ ∂μ :=
      funext fun z => setIntegral_shift h (hz z) (F := fun n => ‖F n‖) fun γ n => by rw [hF]
    exact e ▸ integrable_const _
  have key := integral_integral_swap hp
  simp only [h0, integral_zero, setIntegral_shift h (hz _) hF, integral_const, smul_eq_zero] at key
  exact key.resolve_left (by simpa [measureReal_eq_zero_iff] using hν)

end Abstract

section Mat

variable {R : Type} [CommRing R] {n r : ℕ} {m m' : Matrix (Fin n) (Fin n) R} {a : R} {C : Matrix (Fin n) (Fin r) R}
  {E : Matrix (Fin r) (Fin r) R} {P : Matrix (Fin r) (Fin n) R}

theorem mat_kill (ha : m = a • (C * E * P)) (h0 : P * C = 0) :
    m * C = 0 ∧ P * m = 0 ∧ ∀ x, P *ᵥ x = 0 → m *ᵥ x = C *ᵥ 0 := by
  refine ⟨?_, ?_, fun x hx => ?_⟩
  · rw [ha, Matrix.smul_mul, Matrix.mul_assoc, h0, Matrix.mul_zero, smul_zero]
  · rw [ha, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h0, Matrix.zero_mul, Matrix.zero_mul, smul_zero]
  · rw [ha, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero, smul_zero, Matrix.mulVec_zero]

theorem mat_comm (ha : m - 1 = a • (C * E * P)) (h1 : (m' - 1) * C = 0) (h2 : P * (m' - 1) = 0) :
    m * m' = m' * m := by
  have e : Commute (m - 1) (m' - 1) := by
    rw [Commute, SemiconjBy, ha, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc, h2, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, h1, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_mul]
  have := (e.add_left (Commute.one_left _)).add_right (Commute.one_right _)
  rw [sub_add_cancel, sub_add_cancel] at this
  exact this

theorem commute_closure {G : Type} [Group G] {s t : Set G} (h : ∀ x ∈ s, ∀ y ∈ t, Commute x y) {x y : G}
    (hx : x ∈ Subgroup.closure s) (hy : y ∈ Subgroup.closure t) : Commute x y := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    induction hy using Subgroup.closure_induction with
    | mem y hy => exact h x hx y hy
    | one => exact Commute.one_right _
    | mul _ _ _ _ k k' => exact k.mul_right k'
    | inv _ _ k => exact k.inv_right
  | one => exact Commute.one_left _
  | mul _ _ _ _ k k' => exact k.mul_left k'
  | inv _ _ k => exact k.inv_left

end Mat

section Algebra

variable {D : D7} (V : HSp D) {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}

theorem vecMulVec_col (j : Fin r) :
    vecMulVec (fun i => C i j) ((fun i => (D.sp.cm.sig : D.host.E →+* D.host.E) (C i j)) ᵥ* V.gram) =
      C * Matrix.single j j (1 : D.host.E) * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram) := by
  ext a b
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · rw [Matrix.mul_single_apply_same, mul_one]
    rfl
  · intro k _ hk
    rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hk, zero_mul]
  · exact fun h => absurd (Finset.mem_univ j) h

theorem isoVec_col (hC : IsIsoFrame V C) (j : Fin r) : IsoVec V fun i => C i j := by
  refine ⟨hC.2.1.ne_zero j, ?_⟩
  have := congrFun (congrFun hC.2.2 j) j
  rw [Matrix.mul_assoc] at this
  exact this

theorem ZI_le (hC : IsIsoFrame V C) (j : Fin r) : ZI V (fun i => C i j) ≤ NI V C := by
  refine Subgroup.closure_mono ?_
  rintro g ⟨a, ha⟩
  have h0 : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram).map (incA D) * C.map (incA D) = 0 := by
    rw [← Matrix.map_mul, hC.2.2, Matrix.map_zero _ (map_zero _)]
  rw [vecMulVec_col, Matrix.map_mul, Matrix.map_mul] at ha
  obtain ⟨k1, k2, k3⟩ := mat_kill ha h0
  refine ⟨k1, k2, fun x hx => ⟨0, k3 _ (funext fun i => ?_)⟩⟩
  have := RingHom.map_mulVec (incA D) (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram) x i
  rw [hx, Pi.zero_apply, map_zero] at this
  exact this.symm

theorem ZI_comm (j : Fin r) {z n : GA D V} (hz : z ∈ ZI V fun i => C i j) (hn : n ∈ NI V C) : Commute z n := by
  refine commute_closure ?_ hz hn
  rintro z ⟨a, ha⟩ n ⟨h1, h2, -⟩
  rw [vecMulVec_col, Matrix.map_mul, Matrix.map_mul] at ha
  exact Subtype.ext (Units.ext (mat_comm ha h1 h2))

end Algebra

theorem isCuspFun_of_zCusp : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ φ : GA D V → ℂ, IsAutFun V φ →
    ZCusp V φ → IsCuspFun V φ := by
  intro D θ V hθ φ hφ hZ r C hC μ 𝓕 hμ h𝓕 g
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  let j : Fin r := ⟨0, hC.1⟩
  have hξ := isoVec_col V hC j
  obtain ⟨⟨ν, 𝓖, hν, h𝓖, -⟩, hm, -⟩ := GlobalTheory.T.transvectionSubgroup_cocompact_haar_fundamentalDomain D θ V hθ _ hξ
  obtain ⟨m0, m1⟩ := hm ν 𝓖 hν h𝓖
  have : LocallyCompactSpace (NI V C) := (GlobalTheory.CuspDecay.Model.isClosed_NI V hC).locallyCompactSpace
  let i : NIQ V C → GQ V := fun x => ⟨x.1.1, x.2⟩
  have hi : Function.Injective i := fun x y h => Subtype.ext (Subtype.ext (congrArg (fun z : GQ V => z.1) h))
  have : Countable (NIQ V C) := hi.countable
  have : SecondCountableTopology (NI V C) := TopologicalSpace.Subtype.secondCountableTopology _
  have : IsFiniteMeasure (ν.restrict 𝓖) := isFiniteMeasure_restrict.2 m1
  refine setIntegral_eq_zero (ν.restrict 𝓖) (fun h => m0 (Measure.restrict_eq_zero.1 h))
    (Subgroup.inclusion (ZI_le V hC j)) (continuous_subtype_val.subtype_mk _)
    (fun z n => Subtype.ext (ZI_comm V j z.2 n.2)) h𝓕 (F := fun n => φ ((n : GA D V) * g))
    (hφ.cont.comp (continuous_subtype_val.mul continuous_const)) (fun γ n => ?_) fun n => ?_
  · rw [Subgroup.coe_mul, mul_assoc]
    exact hφ.left _ γ.2 _
  · simpa only [Subgroup.coe_mul, mul_assoc, Subgroup.coe_inclusion] using hZ _ hξ ν 𝓖 hν h𝓖 ((n : GA D V) * g)

end GlobalTheory.TransvCusp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatticeSublatticePullbackAlongEmbedding
section
open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew

namespace GlobalTheory.PlaneSkew

theorem exists_ne_zero_smul_mem_of_mem_span {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (x : Fin n → E)
    (hx : x ∈ Submodule.span E (L : Set (Fin n → E))) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ d • x ∈ L := by
  first
  | exact @_root_.GlobalTheory.HermitianEigenvalueInequality.main
  | exact _root_.GlobalTheory.HermitianEigenvalueInequality.main
  | (apply _root_.GlobalTheory.HermitianEigenvalueInequality.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.HermitianEigenvalueInequality.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.HermitianEigenvalueInequality.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.HermitianEigenvalueInequality.main ..)

theorem isLattice_lowLat : ∀ (E : Type) [Field E] [NumberField E] (n n₁ : ℕ) (L : Submodule (𝓞 E) (Fin n → E))
    (ι : Matrix (Fin n) (Fin n₁) E), L.IsLattice E → Function.Injective ι.mulVec → (lowLat ι L).IsLattice E := by
  intro E _ _ n n₁ L ι hL hι
  have hfg : L.FG := Submodule.IsLattice.fg (self := hL)
  have hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤ := Submodule.IsLattice.span_eq_top (self := hL)
  refine ⟨?_, ?_⟩
  · let f : (Fin n₁ → E) →ₗ[𝓞 E] (Fin n → E) := (Matrix.mulVecLin ι).restrictScalars (𝓞 E)
    have hf : Function.Injective f := hι
    have hle : (lowLat ι L).map f ≤ L := Submodule.map_comap_le f L
    have hN : IsNoetherian (𝓞 E) L := isNoetherian_of_fg_of_noetherian L hfg
    have hm : ((lowLat ι L).map f).FG := (isNoetherian_submodule.mp hN) _ hle
    exact Submodule.fg_of_fg_map_injective f hf hm
  · rw [eq_top_iff]
    intro u _
    obtain ⟨d, hd, hdu⟩ := exists_ne_zero_smul_mem_of_mem_span L (ι *ᵥ u) (by rw [hsp]; trivial)
    have hd1 : algebraMap (𝓞 E) E d ≠ 0 := by
      intro h
      exact hd (IsFractionRing.injective (𝓞 E) E (by simpa using h))
    have hmem : (algebraMap (𝓞 E) E d) • u ∈ lowLat ι L := by
      rw [mem_lowLat, Matrix.mulVec_smul, algebraMap_smul]
      exact hdu
    have : u = (algebraMap (𝓞 E) E d)⁻¹ • ((algebraMap (𝓞 E) E d) • u) := by
      rw [smul_smul, inv_mul_cancel₀ hd1, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

end GlobalTheory.PlaneSkew
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenIntegralTensorAdeleMultiples
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF GlobalTheory.HeckeExtend

noncomputable section

namespace GlobalTheory.HeckeExtend

variable {F : Type} [Field F] [NumberField F]

variable (F) in

theorem intF_isOpen (M : ℕ) (hM : 0 < M) : IsOpen (intF F M) := by
  let S : AddSubgroup (Af F) :=
    { carrier := {c | ∃ a : Af F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ c = M • a}
      zero_mem' := ⟨0, fun v => zero_mem _, (smul_zero M).symm⟩
      add_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a + b, fun v => add_mem (ha v) (hb v), (smul_add M a b).symm⟩
      neg_mem' := by
        rintro _ ⟨a, ha, rfl⟩
        exact ⟨-a, fun v => neg_mem (ha v), (smul_neg M a).symm⟩ }
  have hS : IsOpen (S : Set (Af F)) :=
    S.isOpen_of_mem_nhds (g := 0) (GlobalTheory.AdLat.OpenLat.nsmul_integral_mem_nhds F M hM)
  have e : intF F M = Prod.snd ⁻¹' (S : Set (Af F)) := by
    ext x
    constructor
    · rintro ⟨c, hc, e⟩
      exact ⟨c, hc, e⟩
    · rintro ⟨c, hc, e⟩
      exact ⟨c, hc, e⟩
  rw [e]
  exact hS.preimage continuous_snd

theorem exists_intF_one_mul (M : ℕ) (hM : 0 < M) {x : AF F} (hx : x ∈ intF F M) :
    ∃ s ∈ intF F 1, (M : AF F) * s = x := by
  obtain ⟨c, hc, e⟩ := hx
  have hM' : (M : F) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  refine ⟨algebraMap F (AF F) ((M : F)⁻¹) * x, ⟨c, hc, ?_⟩, ?_⟩
  · show (algebraMap F (AF F) ((M : F)⁻¹)).2 * x.2 = 1 • c
    rw [e, one_smul, nsmul_eq_mul]
    have h2 : (algebraMap F (AF F) ((M : F)⁻¹)).2 = algebraMap F (Af F) ((M : F)⁻¹) := rfl
    rw [h2, ← mul_assoc, ← map_natCast (algebraMap F (Af F)) M, ← map_mul, inv_mul_cancel₀ hM', map_one, one_mul]
  · rw [← mul_assoc, ← map_natCast (algebraMap F (AF F)) M, ← map_mul, mul_inv_cancel₀ hM', map_one, one_mul]

end GlobalTheory.HeckeExtend

theorem GlobalTheory.HeckeExtend.CE_isOpen : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (N : ℕ), 0 < N → IsOpen (CE F E N : Set (AF F ⊗[F] E)) := by
  intro F E _ _ _ _ _ N hN
  haveI : IsTopologicalAddGroup (AF F ⊗[F] E) := IsModuleTopology.topologicalAddGroup (AF F) _
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  let b₀ := Module.finBasis F E
  have hint : ∀ i, ∃ d : ℕ, 0 < d ∧ IsIntegral ℤ ((d : E) * b₀ i) := by
    intro i
    have : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
    have : Algebra.IsAlgebraic ℤ E := Algebra.IsAlgebraic.trans ℤ ℚ E
    obtain ⟨y, hy, h⟩ := IsAlgebraic.exists_integral_multiple (R := ℤ) (z := b₀ i) (Algebra.IsAlgebraic.isAlgebraic _)
    refine ⟨(y * y).natAbs, Int.natAbs_pos.2 (mul_ne_zero hy hy), ?_⟩
    have h1 : (((y * y).natAbs : ℕ) : E) = (y : E) * (y : E) := by
      rw [← Int.cast_natCast, Int.natAbs_of_nonneg (mul_self_nonneg y), Int.cast_mul]
    rw [h1, mul_assoc]
    rw [zsmul_eq_mul] at h
    exact (isIntegral_algebraMap (x := y)).mul h
  choose d hd hdint using hint
  let B := Algebra.TensorProduct.basis (AF F) b₀
  let U : Set (AF F ⊗[F] E) := ⋂ i, (fun z => B.repr z i) ⁻¹' intF F (N * d i)
  have hU : IsOpen U := by
    refine isOpen_iInter_of_finite fun i => (intF_isOpen F _ (Nat.mul_pos hN (hd i))).preimage ?_
    exact IsModuleTopology.continuous_of_linearMap (B.coord i)
  have h0 : (0 : AF F ⊗[F] E) ∈ U := by
    refine Set.mem_iInter.2 fun i => ⟨0, fun v => zero_mem _, ?_⟩
    show (B.repr 0 i).2 = (N * d i) • 0
    rw [map_zero, smul_zero]
    rfl
  have hsub : U ⊆ (CE F E N : Set (AF F ⊗[F] E)) := by
    intro z hz
    have hz' : ∀ i, B.repr z i ∈ intF F (N * d i) := fun i => Set.mem_iInter.1 hz i
    choose s hs hsx using fun i => exists_intF_one_mul (N * d i) (Nat.mul_pos hN (hd i)) (hz' i)
    refine mem_CE.2 ⟨∑ i, algebraMap (AF F) (AF F ⊗[F] E) (s i) * incAF F E ((⟨(d i : E) * b₀ i, hdint i⟩ : 𝓞 E) : E),
      sum_mem fun i _ => AddSubgroup.subset_closure ⟨s i, hs i, ⟨(d i : E) * b₀ i, hdint i⟩, rfl⟩, ?_⟩
    rw [Finset.smul_sum]
    conv_rhs => rw [← B.sum_repr z]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hsx i, Algebra.TensorProduct.basis_apply, nsmul_eq_mul, Algebra.smul_def]
    have h1 : incAF F E ((d i : E) * b₀ i) = (d i : AF F ⊗[F] E) * (1 ⊗ₜ b₀ i) := by
      rw [map_mul, map_natCast]
      rfl
    have hc : ((⟨(d i : E) * b₀ i, hdint i⟩ : 𝓞 E) : E) = (d i : E) * b₀ i := rfl
    rw [hc, h1, map_mul, map_natCast]
    push_cast
    ring
  exact (CE F E N).isOpen_of_mem_nhds (g := 0) (Filter.mem_of_superset (hU.mem_nhds h0) hsub)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenOffCoordinateHyperplanes
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in

theorem _root_.GlobalTheory.GoodTop.isOpen_offHyp_of_isOpen {n : ℕ} (S : Finset (Fin n)) (U : Set (_root_.ReciprocityTheory.L2DbarEstimates.V n)) (hU : IsOpen U) :
    IsOpen (_root_.GlobalTheory.GoodTop.offHyp S U) := by
  unfold _root_.GlobalTheory.GoodTop.offHyp
  have hset : {v : _root_.ReciprocityTheory.L2DbarEstimates.V n | v ∈ U ∧ ∀ a ∈ S, v.ofLp a ≠ 0} =
      U ∩ ⋂ a ∈ S, {v : _root_.ReciprocityTheory.L2DbarEstimates.V n | v.ofLp a ≠ 0} := by
    ext v
    simp
  rw [hset]
  refine hU.inter (isOpen_biInter_finset fun a _ => isOpen_ne_fun ?_ continuous_const)
  unfold _root_.ReciprocityTheory.L2DbarEstimates.V
  fun_prop

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitaryTActStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnitary_tAct_formT_of_isUnitary : ∀ (R S k : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (actW : Mat R S →ₗ[ℂ] Module.End ℂ W)
    (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ), IsUnitary actW B → IsUnitary (tAct k actW) (formT k B) := by
  first | exact @GlobalTheory.SteepMult.isUnitary_tAct | exact GlobalTheory.SteepMult.isUnitary_tAct | (intros; apply GlobalTheory.SteepMult.isUnitary_tAct <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KTypeLeKFiniteVectorsFiniteDimensionalStatement
section
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kType_le_kFiniteVectors_finiteDimensional : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D), CompleteSpace H → IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → IsKMod ε σ D E → ∀ (μ : Fin n → ℝ) (S : Submodule ℂ H), IsKTypeOf ε σ μ S → S ≤ D ∧ FiniteDimensional ℂ (S.comap D.subtype) ∧ KStab ε E (S.comap D.subtype) ∧ (∀ ν : Fin n → ℝ, ∀ x ∈ S.comap D.subtype, x ≠ 0 → KHighest ε E ν x → ν = μ) := by
  first | exact @GlobalTheory.kTypeInKFinite | exact GlobalTheory.kTypeInKFinite | (intros; apply GlobalTheory.kTypeInKFinite <;> assumption)
end

