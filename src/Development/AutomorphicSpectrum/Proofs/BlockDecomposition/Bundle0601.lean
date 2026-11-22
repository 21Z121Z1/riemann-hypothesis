import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0563
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0041
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.SSmoothW
import GroundTheory.AutomorphicForms.GL2.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1369
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1414
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetGramRatOneNeZero
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLemmas.ToComplBijective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0577

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFibreMeasureUnramifiedFormula
section
open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory

namespace GlobalTheory.CompanionTheory.AvgFree.FibMass

theorem sig_inv {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) (e : E) : σ (σ e) = e := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [hCM.2.2.2 τ, hCM.2.2.2 τ]
  simp

theorem gram_mem {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} (R : Type) [CommRing R]
    [Algebra F R] (hs : ∀ x, σ (σ x) = x) {M n : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (hJ : ∀ i j, σ (J j i) = J i j) (X : Fin n → Fin M → R ⊗[F] E) :
    gramR R σ J X ∈ HermR R σ n := by
  intro a c
  have hi : ∀ y : E, sigR R σ (inclR R y) = inclR R (σ y) := fun y => by simp [sigR, inclR]
  change sigR R σ (hR R σ J (X c) (X a)) = hR R σ J (X a) (X c)
  simp only [hR, hform, JR, map_sum, map_mul, Matrix.map_apply, sigR_sigR R σ hs, hi, hJ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

end GlobalTheory.CompanionTheory.AvgFree.FibMass

theorem GlobalTheory.CompanionTheory.AvgFree.free_fibre_masses : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ J → ∀ (n : ℕ) (mv : (HermR (Fv F v) σ n) → Measure (Fin n → Fin M → (Fv F v ⊗[F] E))), IsGramFibFree (Fv F v) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) mv → ∀ Tt : Set (Fin n → Fin M → (Fv F v ⊗[F] E)), IsCompact Tt → IsOpen Tt → Tt ⊆ {X : (Fin n → Fin M → (Fv F v ⊗[F] E)) | LinearIndependent (Fv F v ⊗[F] E) X} → (∀ Y : Set (HermR (Fv F v) σ n), MeasurableSet Y → (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) (Tt ∩ gramIn (Fv F v) σ J Y) = ∫⁻ y in Y, mv y Tt ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n)) ∧ Continuous (fun y => (mv y Tt).toReal) ∧ (∀ y, mv y Tt ≠ ⊤) ∧ ∃ C : ℝ≥0, ∀ y, mv y Tt ≤ C := by
  intro F E _ _ _ _ _ σ hσ d b v lv hlv M J hJ n mv hmv Tt hTc hTo hTf
  obtain ⟨r1, r2, r3, r4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨a1, a2, a3, a4, -, -, -, a8, -, a10⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)
  haveI := a1
  haveI := a2
  haveI := a3
  haveI := a4
  haveI := a8 n M
  haveI hBH : BorelSpace (HermR (Fv F v) σ n) := ⟨rfl⟩
  obtain ⟨h1, h2, h3⟩ := hmv
  have hinv : ∀ e, σ (σ e) = e := GlobalTheory.CompanionTheory.AvgFree.FibMass.sig_inv hσ
  have hgc : Continuous (gramR (Fv F v) σ J : (Fin n → Fin M → Fv F v ⊗[F] E) → _) := a10 n M J

  let q : (Fin n → Fin M → Fv F v ⊗[F] E) → HermR (Fv F v) σ n := fun X =>
    ⟨gramR (Fv F v) σ J X, GlobalTheory.CompanionTheory.AvgFree.FibMass.gram_mem (Fv F v) hinv hJ.1 X⟩
  have hqc : Continuous q := hgc.subtype_mk _
  have hTm : MeasurableSet Tt := hTo.measurableSet

  have hae : ∀ y, ∀ᵐ x ∂(mv y), q x = y := fun y => by
    refine measure_mono_null ?_ (h1 y)
    intro x hx hx'
    exact hx (Subtype.ext hx'.1)

  let φ : (Fin n → Fin M → Fv F v ⊗[F] E) → ℝ := Tt.indicator fun _ => 1
  have hφc : Continuous φ := by
    refine continuous_indicator ?_ continuous_const.continuousOn
    simp [hTo.frontier_eq, hTc.isClosed.closure_eq]
  have hφs : HasCompactSupport φ :=
    HasCompactSupport.intro hTc fun x hx => Set.indicator_of_notMem hx _
  have hφt : tsupport φ ⊆ {X : Fin n → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} := by
    refine subset_trans (closure_minimal ?_ hTc.isClosed) hTf
    intro x hx
    by_contra h
    exact hx (Set.indicator_of_notMem h _)
  obtain ⟨hI, hC⟩ := h3 φ hφc hφs hφt
  have hint : ∀ y, ∫ X, φ X ∂(mv y) = (mv y Tt).toReal := fun y => by
    simp [φ, integral_indicator hTm, Measure.real]
  have hfin : ∀ y, mv y Tt ≠ ⊤ := fun y => by
    have h := hI y (Set.mem_univ y)
    rw [integrable_indicator_iff hTm] at h
    rcases (integrableOn_const_iff (C := (1 : ℝ)) (by simp)).1 h with h | h
    · simp at h
    · exact h.ne
  have hcont : Continuous fun y => (mv y Tt).toReal := by
    have h := continuousOn_univ.1 hC
    simpa only [hint] using h
  refine ⟨fun Y hY => ?_, hcont, hfin, ?_⟩
  · have hG : gramIn (Fv F v) σ J Y = q ⁻¹' Y := by
      ext X
      constructor
      · rintro ⟨y, hy, e⟩
        have : q X = y := Subtype.ext e
        show q X ∈ Y
        rwa [this]
      · intro hX
        exact ⟨q X, hX, rfl⟩
    rw [hG]
    have hqY : MeasurableSet (q ⁻¹' Y) := hqc.measurable hY
    have hT : MeasurableSet (Tt ∩ q ⁻¹' Y) := hTm.inter hqY
    have e := h2 ((Tt ∩ q ⁻¹' Y).indicator 1) (measurable_one.indicator hT)
    rw [lintegral_indicator_one hT, Measure.restrict_apply hT,
      Set.inter_eq_left.2 (Set.inter_subset_left.trans hTf)] at e
    rw [e, ← lintegral_indicator hY]
    refine lintegral_congr fun y => ?_
    rw [lintegral_indicator_one hT]
    by_cases hy : y ∈ Y
    · rw [Set.indicator_of_mem hy]
      refine measure_congr ?_
      filter_upwards [hae y] with x hx
      refine propext ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
      show q x ∈ Y
      rwa [hx]
    · rw [Set.indicator_of_notMem hy]
      refine measure_mono_null (t := {x | ¬ q x = y}) ?_ (hae y)
      intro x hx hxy
      apply hy
      rw [← hxy]
      exact hx.2
  · obtain ⟨C, hC'⟩ := (hTc.image hqc).exists_bound_of_continuousOn hcont.continuousOn
    refine ⟨Real.toNNReal C, fun y => ?_⟩
    by_cases hy : y ∈ q '' Tt
    · have h := hC' y hy
      rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] at h
      show mv y Tt ≤ ENNReal.ofReal C
      exact (ENNReal.le_ofReal_iff_toReal_le (hfin y) (ENNReal.toReal_nonneg.trans h)).2 h
    · have h0 : mv y Tt = 0 := by
        refine measure_mono_null ?_ (h1 y)
        intro x hx hx'
        exact hy ⟨x, hx, Subtype.ext hx'.1⟩
      rw [h0]
      exact bot_le
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalSectionInvariance
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.LocalChar

theorem sInv : Ad3.LFS.SInv := by
  intro F _ _ _ _ _ _ ν hν
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact continuous_inv.comp hν.1
  · intro x
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, hν.2 x, inv_one]
  · intro hu x hx
    have h : ν x = 1 := hu hx
    rw [MonoidHom.mem_ker, MonoidHom.inv_apply, h, inv_one]

end GlobalTheory.CompanionTheory.LocalChar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalSectionNonvanishing
section
noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel Topology

namespace GlobalTheory.CompanionTheory.LFNe

open Ad3 Ad3.LFS

section

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

def lev (m : ℕ) : Fin 3 → ℤ := ![(m : ℤ), (m : ℤ), 0]

variable (F) in

def tBox (m : ℕ) : Set (Matrix (Fin 2) (Fin 3) F) :=
  {X | ∀ i j, X i j - blk (0 : Fin 2 → F) i j ∈ valBall F (lev m j)}

omit [MeasurableSpace F] [BorelSpace F] in
theorem mp_det_eq_one {h : GL (Fin 2) F} (hh : h ∈ GLnLocal.integralGL F 2) (s : ℂ) :
    mp (GeneralLinearGroup.det h) s = 1 := by
  have : modulus ((GeneralLinearGroup.det h : Fˣ) : F) = 1 :=
    modulus_eq_one_iff.2 ⟨Units.ne_zero _, GodementSectionLocal.ord_det_eq_zero hh⟩
  unfold mp
  rw [this]
  simp

variable (F) in

def cong (m : ℕ) : Set (GL (Fin 2) F) :=
  {h | ∀ i j, (h : Matrix (Fin 2) (Fin 2) F) i j - (1 : Matrix (Fin 2) (Fin 2) F) i j ∈ valBall F m}

theorem volume_unit_box_ne_zero (ψ : AddChar F Circle) :
    (vol2 ψ).real (GodementSectionLocal.box F 0 : Set (Fin 2 → F)) ≠ 0 := by
  have : (vol2 ψ).IsAddHaarMeasure := by unfold vol2; infer_instance
  refine (ENNReal.toReal_ne_zero).2 ⟨?_, (GodementSectionLocal.isCompact_box 0).measure_lt_top.ne⟩
  exact (GodementSectionLocal.isClopen_box 0).isOpen.measure_ne_zero _ ⟨0, zero_mem _⟩

end

end GlobalTheory.CompanionTheory.LFNe
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalSectionSupport
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.LFSupp

open ValuativeRel NNReal

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem dg_mul_uni (a b : Fˣ) (x z : F) :
    Ad3.dg (a * b) b 1 * Ad3.uni x 0 z =
      Ad3.uni ((a : F) * x) 0 ((b : F) * z) * Ad3.dg (a * b) b 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Ad3.dg, Ad3.uni, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem uni_mem_congruenceSubgroup {m : ℕ} {x z : F}
    (hx : valuation F x ≤ valuation F (GLnLocal.uniformizer F : F) ^ m)
    (hz : valuation F z ≤ valuation F (GLnLocal.uniformizer F : F) ^ m) :
    Ad3.uni x 0 z ∈ GLnLocal.congruenceSubgroup F 3 m := by
  have h1 : valuation F (GLnLocal.uniformizer F : F) ^ m ≤ 1 :=
    pow_le_one' (GLnLocal.valuation_uniformizer_lt_one F).le m
  have hxO : x ∈ 𝒪[F] := (Valuation.mem_integer_iff _ _).mpr (hx.trans h1)
  have hzO : z ∈ 𝒪[F] := (Valuation.mem_integer_iff _ _).mpr (hz.trans h1)
  have hnx : -x ∈ 𝒪[F] := neg_mem hxO
  have hnz : -z ∈ 𝒪[F] := neg_mem hzO
  have hxz : x * z ∈ 𝒪[F] := mul_mem hxO hzO
  have hinv : (((Ad3.uni x 0 z)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![1, -x, x * z - 0; 0, 1, -z; 0, 0, 1] := rfl
  have hval : (((Ad3.uni x 0 z) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![1, x, 0; 0, 1, z; 0, 0, 1] := rfl
  rw [GLnLocal.mem_congruenceSubgroup_iff]
  refine ⟨(GLnLocal.mem_integralGL_iff F 3).mpr ⟨fun i j => ?_, fun i j => ?_⟩, fun i j => ?_⟩
  · rw [hval]
    fin_cases i <;> fin_cases j <;> simp [hxO, hzO, zero_mem, one_mem]
  · rw [hinv]
    fin_cases i <;> fin_cases j <;> simp [hnx, hnz, hxz, zero_mem, one_mem]
  · rw [hval]
    fin_cases i <;> fin_cases j <;> simp [hx, hz]

theorem valuation_le_of_mem_valBall {m : ℕ} {x : F}
    (hx : x ∈ valBall F (ord ((GLnLocal.uniformizer F : F) ^ m))) :
    valuation F x ≤ valuation F (GLnLocal.uniformizer F : F) ^ m := by
  have h0 : (GLnLocal.uniformizer F : F) ≠ 0 := fun h =>
    GLnLocal.valuation_uniformizer_ne_zero F (by rw [h, map_zero])
  obtain ⟨y, rfl⟩ := exists_mul_of_mem_valBall (pow_ne_zero m h0) hx
  rw [map_mul, map_pow]
  exact mul_le_of_le_one_right' ((Valuation.mem_integer_iff _ _).mp y.2)

theorem psi_eq_one {ψ : AddChar F Circle} {W : GL (Fin 3) F → ℂ}
    (hW : ∀ x y z g, W (Ad3.uni x y z * g) = (ψ (x + z) : ℂ) * W g)
    {U : Set (GL (Fin 3) F)} (hU : ∀ g, ∀ u ∈ U, W (g * u) = W g) {m : ℕ}
    (hm : (GLnLocal.congruenceSubgroup F 3 m : Set (GL (Fin 3) F)) ⊆ U) (a b : Fˣ)
    {k : GL (Fin 3) F} (hk : k ∈ GLnLocal.integralGL F 3) {x z : F}
    (hx : valuation F x ≤ valuation F (GLnLocal.uniformizer F : F) ^ m)
    (hz : valuation F z ≤ valuation F (GLnLocal.uniformizer F : F) ^ m)
    (h : W (Ad3.dg (a * b) b 1 * k) ≠ 0) : ψ ((a : F) * x + (b : F) * z) = 1 := by
  have hc : k⁻¹ * Ad3.uni x 0 z * k ∈ GLnLocal.congruenceSubgroup F 3 m := by
    simpa using GLnLocal.conj_mem_congruenceSubgroup F 3 (inv_mem hk)
      (uni_mem_congruenceSubgroup hx hz)
  have e1 := hU (Ad3.dg (a * b) b 1 * k) _ (hm hc)
  have e2 : Ad3.dg (a * b) b 1 * k * (k⁻¹ * Ad3.uni x 0 z * k) =
      Ad3.uni ((a : F) * x) 0 ((b : F) * z) * (Ad3.dg (a * b) b 1 * k) := by
    calc Ad3.dg (a * b) b 1 * k * (k⁻¹ * Ad3.uni x 0 z * k)
        = Ad3.dg (a * b) b 1 * Ad3.uni x 0 z * k := by group
      _ = _ := by rw [dg_mul_uni, mul_assoc]
  rw [e2, hW] at e1
  have e3 : (ψ ((a : F) * x + (b : F) * z) : ℂ) = 1 :=
    mul_right_cancel₀ h (by rw [e1, one_mul])
  exact Circle.coe_eq_one.mp e3

theorem modulus_le_of_trivial {ψ : AddChar F Circle} {y : F} (hy : y ∈ valBall F (-1))
    (hy1 : ψ y ≠ 1) {n : ℤ} (c : Fˣ) (h : ∀ x ∈ valBall F n, ψ ((c : F) * x) = 1) :
    GroundTheory.LocalField.modulus (c : F) ≤ (residueCard F : ℝ≥0) ^ (n + 1) := by
  by_contra hlt
  rw [not_le, GroundTheory.LocalField.modulus_of_ne_zero c.ne_zero,
    (zpow_right_strictMono₀ one_lt_residueCard_nnreal).lt_iff_lt] at hlt
  have h1 : (c : F)⁻¹ ∈ valBall F (-ord (c : F)) := by
    rw [← ord_inv c.ne_zero]
    exact mem_valBall_ord
  have h2 : (c : F)⁻¹ * y ∈ valBall F n :=
    valBall_antitone (by omega) (mul_mem_valBall h1 hy)
  apply hy1
  simpa [c.ne_zero] using h _ h2

end GlobalTheory.CompanionTheory.LFSupp

open GlobalTheory.CompanionTheory.LFSupp in

theorem GlobalTheory.CompanionTheory.LFSupp.sSupp : Ad3.LFS.SSupp := by
  intro F _ _ _ _ _ _ ψ hψ W hW hsm
  obtain ⟨U, hU⟩ := hsm
  obtain ⟨m, -, hm⟩ := (GLnLocal.hasBasis_nhds_one F 3).mem_iff.mp
    (U.isOpen.mem_nhds (one_mem U))
  obtain ⟨hc, h1, h0⟩ := hψ
  have hnot := not_isTrivialOn_addCharConductor_sub_one hc h1
  rw [h0] at hnot
  simp only [IsTrivialOn, not_forall] at hnot
  obtain ⟨y, hy, hy1⟩ := hnot
  have hy' : y ∈ valBall F (-1) := by simpa using hy
  refine ⟨(((residueCard F : NNReal) ^ (ord ((GLnLocal.uniformizer F : F) ^ m) + 1) : NNReal) : ℝ),
    fun a b k hk h => ⟨?_, ?_⟩⟩
  · refine NNReal.coe_le_coe.mpr (modulus_le_of_trivial hy' hy1 a fun x hx => ?_)
    have := psi_eq_one hW (U := (U : Set _)) hU hm a b hk (valuation_le_of_mem_valBall hx)
      (z := 0) (by simp) h
    simpa using this
  · refine NNReal.coe_le_coe.mpr (modulus_le_of_trivial hy' hy1 b fun z hz => ?_)
    have := psi_eq_one hW (U := (U : Set _)) hU hm a b hk (x := 0) (by simp)
      (valuation_le_of_mem_valBall hz) h
    simpa using this
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalSectionTranslation
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.LFTrans

open Ad3 Ad3.LFS

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

noncomputable def rightMulHomeo (h : GL (Fin 3) F) :
    Matrix (Fin 2) (Fin 3) F ≃ₜ Matrix (Fin 2) (Fin 3) F where
  toFun X := X * (h : Matrix (Fin 3) (Fin 3) F)
  invFun X := X * ((h⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
  left_inv X := by
    show X * (h : Matrix (Fin 3) (Fin 3) F) * ((h⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = X
    rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  right_inv X := by
    show X * ((h⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (h : Matrix (Fin 3) (Fin 3) F) = X
    rw [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
  continuous_toFun := Continuous.matrix_mul continuous_id continuous_const
  continuous_invFun := Continuous.matrix_mul continuous_id continuous_const

theorem mp_mul_one (x y : Fˣ) : mp (x * y) 1 = mp x 1 * mp y 1 := by
  simp [mp, modulus_mul]

theorem rtr_mem_SB (h : GL (Fin 3) F) {Φ : Matrix (Fin 2) (Fin 3) F → ℂ} (hΦ : Φ ∈ SB F) :
    rtr h Φ ∈ SB F := by
  obtain ⟨hl, hc⟩ := hΦ
  have hc' : HasCompactSupport (Φ ∘ rightMulHomeo h) :=
    hc.comp_homeomorph (rightMulHomeo h)
  refine ⟨?_, ?_⟩
  · have h1 : IsLocallyConstant (fun X : Matrix (Fin 2) (Fin 3) F =>
        Φ (X * (h : Matrix (Fin 3) (Fin 3) F))) :=
      hl.comp_continuous (Continuous.matrix_mul continuous_id continuous_const)
    exact h1.comp (fun z => mp (GeneralLinearGroup.det h) 1 * z)
  · exact HasCompactSupport.mul_left (f := fun _ => mp (GeneralLinearGroup.det h) 1) hc'

theorem inn_rtr (ψ : AddChar F Circle) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ)
    (h : GL (Fin 3) F) (k : GL (Fin 2) F) (g : GL (Fin 3) F) :
    inn ψ (rtr h Φ) k g = mp (GeneralLinearGroup.det h) 1 * inn ψ Φ k (g * h) := by
  unfold inn rtr
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [Units.val_mul, Matrix.mul_assoc, mul_assoc]

theorem Wp_mul_right (ψ : AddChar F Circle) (W' : GL (Fin 2) F → ℂ)
    (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (h g : GL (Fin 3) F) :
    Wp ψ W' Φ (g * h) = Wp ψ W' (rtr h Φ) g := by
  unfold Wp
  have h1 : (fun k : GL (Fin 2) F => W' k⁻¹ * mp (GeneralLinearGroup.det k) (3 / 2) * inn ψ (rtr h Φ) k g)
      = fun k => mp (GeneralLinearGroup.det h) 1 *
        (W' k⁻¹ * mp (GeneralLinearGroup.det k) (3 / 2) * inn ψ Φ k (g * h)) := by
    funext k
    rw [inn_rtr]
    ring
  rw [h1, integral_const_mul, map_mul, mp_mul_one]
  ring

theorem sTrans : Ad3.LFS.STrans := by
  intro F _ _ _ _ _ _ ψ W' Φ h hΦ
  exact ⟨rtr_mem_SB h hΦ, funext fun g => Wp_mul_right ψ W' Φ h g⟩

end GlobalTheory.CompanionTheory.LFTrans
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalWhittakerCentral
section
noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.LFCen

open Ad3 Ad3.LFS

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem mp_mul (x y : Fˣ) (s : ℂ) : mp (x * y) s = mp x s * mp y s := by
  unfold mp
  rw [Units.val_mul, GroundTheory.LocalField.modulus_mul, NNReal.coe_mul, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)]

theorem mp_scale (a : Fˣ) : mp (a * a * a) 1 * mp (a⁻¹ * a⁻¹) (3 / 2) = 1 := by
  have ht : 0 < (modulus (a : F) : ℝ) := by
    exact_mod_cast GroundTheory.LocalField.modulus_pos a.ne_zero
  unfold mp
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, GroundTheory.LocalField.modulus_mul,
    GroundTheory.LocalField.modulus_inv, NNReal.coe_mul, NNReal.coe_inv]
  generalize (modulus (a : F) : ℝ) = t at ht
  have e : ((t⁻¹ * t⁻¹ : ℝ) : ℂ) ^ (3 / 2 : ℂ) = (((t⁻¹ * t⁻¹) ^ (3 / 2 : ℝ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (by positivity)]
    push_cast
    rfl
  have e2 : (t⁻¹ * t⁻¹) ^ (3 / 2 : ℝ) * (t * t * t) = 1 := by
    have : t⁻¹ * t⁻¹ = t ^ (-2 : ℝ) := by
      rw [Real.rpow_neg ht.le, Real.rpow_two]
      field_simp
    rw [this, ← Real.rpow_mul ht.le]
    have : t * t * t = t ^ (3 : ℝ) := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      ring
    rw [this, ← Real.rpow_add ht]
    norm_num
  push_cast at e ⊢
  rw [Complex.cpow_one, e]
  have := congrArg (fun r : ℝ => (r : ℂ)) e2
  push_cast at this
  rw [mul_comm]
  exact this

theorem blk_scalar (a : Fˣ) (x : Fin 2 → F) :
    blk x * ((dg a a a : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((dg2 a a : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * blk x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk, dg, dg2, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, mul_comm]

theorem inn_scalar (ψ : AddChar F Circle) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (h : GL (Fin 2) F)
    (g : GL (Fin 3) F) (a : Fˣ) : inn ψ Φ h (dg a a a * g) = inn ψ Φ (h * dg2 a a) g := by
  unfold inn
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have : (h : Matrix (Fin 2) (Fin 2) F) * blk x * ((dg a a a * g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((h * dg2 a a : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * blk x * (g : Matrix (Fin 3) (Fin 3) F) := by
    rw [Units.val_mul, Units.val_mul, ← Matrix.mul_assoc, Matrix.mul_assoc _ (blk x), blk_scalar,
      Matrix.mul_assoc _ _ (blk x)]
  simp only [this]

theorem det_dg (a : Fˣ) : GeneralLinearGroup.det (dg a a a) = a * a * a := by
  ext
  simp [dg, Matrix.det_fin_three]

theorem det_diagonal_two (a : Fˣ) : GeneralLinearGroup.det (dg2 a a) = a * a := by
  ext
  simp [dg2, Matrix.det_fin_two]

theorem scenW : Ad3.LFS.SCenW := by
  intro F _ _ _ _ _ _ ψ ν W' Φ hyp a g
  obtain ⟨-, -, ⟨V', hV, hW⟩, -⟩ := hyp
  have hc : ∀ g, W' (dg2 a a * g) = W' g := fun g => by
    rw [hV.cen W' hW a g]
    simp
  have hI : ∫ h, W' h⁻¹ * mp (GeneralLinearGroup.det h) (3 / 2) * inn ψ Φ h (dg a a a * g) ∂hG ψ =
      mp (a⁻¹ * a⁻¹) (3 / 2) * ∫ h, W' h⁻¹ * mp (GeneralLinearGroup.det h) (3 / 2) * inn ψ Φ h g ∂hG ψ := by
    rw [← integral_const_mul]
    haveI : (hG ψ).IsMulRightInvariant := by
      unfold hG
      infer_instance
    rw [← integral_mul_right_eq_self (μ := hG ψ)
      (fun h => mp (a⁻¹ * a⁻¹) (3 / 2) * (W' h⁻¹ * mp (GeneralLinearGroup.det h) (3 / 2) * inn ψ Φ h g)) (dg2 a a)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
    have hw : W' (h * dg2 a a)⁻¹ = W' h⁻¹ := by
      rw [← hc (h * dg2 a a)⁻¹, _root_.mul_inv_rev, mul_inv_cancel_left]
    have hm : mp (a⁻¹ * a⁻¹) (3 / 2) * mp (GeneralLinearGroup.det (h * dg2 a a)) (3 / 2) =
        mp (GeneralLinearGroup.det h) (3 / 2) := by
      rw [map_mul, det_diagonal_two, ← mp_mul]
      congr 1
      rw [mul_comm, mul_assoc, show a * a * (a⁻¹ * a⁻¹) = (1 : Fˣ) by group, mul_one]
    simp only
    rw [inn_scalar, hw, ← hm]
    ring
  unfold Wp
  rw [hI, map_mul, det_dg, mp_mul, ← mul_assoc, mul_right_comm (mp _ 1), mp_scale, one_mul]

end GlobalTheory.CompanionTheory.LFCen
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHermitianClassThird
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField PositivityTheory.BCUSide.HermitianLocalForms

noncomputable section

namespace GlobalTheory.CompanionTheory.NormCongr

theorem mem_norms_locPhi : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (hv : w.under (𝓞 (maximalRealSubfield E)) = v), ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ → ∀ (m : (w.adicCompletion E)[X]) (c : GL (Fin n) (w.adicCompletion E)), c.val * (γ₀.val.map (algebraMap E (w.adicCompletion E))) = (γ₀.val.map (algebraMap E (w.adicCompletion E))) * c.val → (H₀.map (algebraMap E (w.adicCompletion E))) * aeval (γ₀.val.map (algebraMap E (w.adicCompletion E))) m = cT (cj w) c.val * (H₀.map (algebraMap E (w.adicCompletion E))) * c.val → ∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly → ∀ x : ((v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q)ˣ, inclPlus Q (v.adicCompletion (maximalRealSubfield E)) (x : (v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q) = locPhi hU w hw v hv Q m → x ∈ norms Q (v.adicCompletion (maximalRealSubfield E)) := by
  intro E _ _ _ hU w hw v hv n γ₀ hell H₀ _ hdet hinv m c hc1 hc2 r Q hQ x hx
  exact mem_norms_of_congr_equiv hU w hw (v.adicCompletion (maximalRealSubfield E)) (locJ hU w hw v hv)
    (locJ_algebraMap hU w hw v hv) (locJ_cj hU w hw v hv) n γ₀ hell H₀ hdet hinv m c hc1 hc2 r Q hQ x hx

end GlobalTheory.CompanionTheory.NormCongr
end
end

