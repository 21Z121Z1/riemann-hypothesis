import Mathlib
import GroundTheory.LocalFields.LubinTateReciprocity.Descent
import GroundTheory.LocalFields.Different
import GroundTheory.LocalFields.Bundle0010
import GroundTheory.LocalFields.LocalZetaShell

-- bundled from GroundTheory.LocalFields.ConductorFormalGroup
section
noncomputable section

open MvPowerSeries ValuativeRel

namespace GroundTheory.LocalField

section Coeff

variable {R : Type*} [CommRing R] (F : FormalGroup R)

theorem coeff_formalGroup_Xzero (j : ℕ) :
    PowerSeries.coeff j F.Xzero = coeff (Finsupp.single 0 j) F.toPowerSeries := by
  rw [PowerSeries.coeff, coeff_subst, finsum_eq_single _ (Finsupp.single 0 j)]
  · simp [PowerSeries.coeff_X_pow]
  · intro d hd
    by_cases hd₁ : d 1 = 0
    · simp [hd₁, PowerSeries.coeff_X_pow]
      intro h
      exact absurd (by ext i; fin_cases i <;> simp [h, hd₁]) hd
    · simp [hd₁]
  · exact HasSubst.X_zero

theorem exists_sub_X_eq_X_mul :
    ∃ G : MvPowerSeries (Fin 2) R, constantCoeff G = 1 ∧ F.toPowerSeries - X 0 = X 1 * G := by
  have hdvd : (X 1 : MvPowerSeries (Fin 2) R) ∣ F.toPowerSeries - X 0 := by
    rw [X_dvd_iff]
    intro m hm
    have hm' : m = Finsupp.single 0 (m 0) := by
      ext i; fin_cases i <;> simp [hm]
    rw [map_sub, hm', ← coeff_formalGroup_Xzero, F.Xzero_eq_X, PowerSeries.coeff_X, coeff_X]
    by_cases h : m 0 = 1
    · simp [h]
    · have : Finsupp.single (0 : Fin 2) (m 0) ≠ Finsupp.single 0 1 := by
        intro e; exact h (by simpa using congrArg (fun d => d 0) e)
      simp [h, this]
  obtain ⟨G, hG⟩ := hdvd
  refine ⟨G, ?_, hG⟩
  have h := congrArg (coeff (Finsupp.single 1 1)) hG
  rw [map_sub, F.lin_coeff_Y, coeff_X, if_neg (by
    intro e; simpa using congrArg (fun d => d 1) e)] at h
  have e := coeff_add_monomial_mul (m := Finsupp.single (1 : Fin 2) 1) (n := 0) (φ := G) (1 : R)
  rw [add_zero, one_mul, ← X_def] at e
  rw [e, sub_zero] at h
  rw [← coeff_zero_eq_constantCoeff_apply, ← h]

end Coeff

section Valuation

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel Ω] [IsValuativeTopology Ω]
  [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] in

theorem psEval_one {σ : Type*} (x : σ → Ω) : psEval (1 : MvPowerSeries σ 𝒪[K]) x = 1 := by
  classical
  rw [psEval, tsum_eq_single 0]
  · simp [psTerm]
  · intro d hd
    simp [psTerm, coeff_one, hd]

theorem valuation_psEval_sub_left (F : FormalGroup 𝒪[K]) {a b : Ω} (ha : valuation Ω a < 1)
    (hb : valuation Ω b < 1) :
    valuation Ω (psEval F.toPowerSeries ![a, b] - a) = valuation Ω b := by
  obtain ⟨G, hG1, hG⟩ := exists_sub_X_eq_X_mul F
  have hx : ∀ i, valuation Ω ((![a, b] : Fin 2 → Ω) i) < 1 := by
    intro i; fin_cases i
    exacts [ha, hb]
  have h1 : psEval F.toPowerSeries ![a, b] - a = b * psEval G ![a, b] := by
    have e : F.toPowerSeries = X 0 + X 1 * G := by rw [← hG]; ring
    rw [e, psEval_add' _ _ _ hx, psEval_mul' _ _ _ hx, psEval_X, psEval_X]
    simp
  have h2 : valuation Ω (psEval G ![a, b]) = 1 := by
    have hG' : G = 1 + (G - 1) := by ring
    have hc : constantCoeff (G - 1) = 0 := by simp [hG1]
    rw [hG', psEval_add' _ _ _ hx, psEval_one]
    exact Valuation.map_one_add_of_lt _ (valuation_psEval_lt_one' hc _ hx)
  rw [h1, map_mul, h2, mul_one]

end Valuation

end GroundTheory.LocalField
end
end

-- bundled from GroundTheory.LocalFields.LocalFourierTrace
section
noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel
open scoped nonZeroDivisors

attribute [local instance high] FaithfulSMul.to_isTorsionFree

section Dual

variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]

theorem mem_valBall_ord_iff {c : L} (hc : c ≠ 0) {x : L} :
    x ∈ valBall L (ord c) ↔ ∃ y : 𝒪[L], x = c * y := by
  refine ⟨exists_mul_of_mem_valBall hc, ?_⟩
  rintro ⟨y, rfl⟩
  have := mul_mem_valBall (mem_valBall_ord (x := c)) (mem_valBall_zero_iff.mpr y.2)
  rwa [add_zero] at this

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]

theorem forall_trace_mul_mem_iff (x : L) :
    (∀ z : 𝒪[L], Algebra.trace K L (x * z) ∈ 𝒪[K]) ↔
      x ∈ valBall L (-(differentExponent K L : ℤ)) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  have hϖ0 : (ϖ : L) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hD : ((differentIdeal 𝒪[K] 𝒪[L] : Ideal 𝒪[L]) : FractionalIdeal 𝒪[L]⁰ L) =
      FractionalIdeal.spanSingleton 𝒪[L]⁰ ((ϖ : L) ^ differentExponent K L) := by
    rw [differentIdeal_eq_maximalIdeal_pow, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow,
      FractionalIdeal.coeIdeal_span_singleton]
    rfl
  have hdual : FractionalIdeal.dual 𝒪[K] K (1 : FractionalIdeal 𝒪[L]⁰ L) =
      FractionalIdeal.spanSingleton 𝒪[L]⁰ ((ϖ : L) ^ differentExponent K L)⁻¹ := by
    rw [← FractionalIdeal.spanSingleton_inv, ← hD, coeIdeal_differentIdeal 𝒪[K] K L 𝒪[L], inv_inv]
  have hc0 : ((ϖ : L) ^ differentExponent K L)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hϖ0)
  have hc : ord ((ϖ : L) ^ differentExponent K L)⁻¹ = -(differentExponent K L : ℤ) := by
    rw [ord_inv (pow_ne_zero _ hϖ0), ord_pow hϖ0, ord_uniformizer hϖ, mul_one]
  have key : x ∈ FractionalIdeal.dual 𝒪[K] K (1 : FractionalIdeal 𝒪[L]⁰ L) ↔
      ∀ z : 𝒪[L], Algebra.trace K L (x * z) ∈ 𝒪[K] := by
    rw [FractionalIdeal.mem_dual (@one_ne_zero (FractionalIdeal 𝒪[L]⁰ L) _ _ _)]
    constructor
    · intro h z
      obtain ⟨a, ha⟩ := h (z : L) (FractionalIdeal.mem_one_iff _ |>.mpr ⟨z, rfl⟩)
      rw [Algebra.traceForm_apply] at ha
      rw [← ha]
      exact a.2
    · intro h a ha
      obtain ⟨z, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp ha
      exact ⟨⟨_, h z⟩, by rw [Algebra.traceForm_apply]; rfl⟩
  rw [← key, hdual, FractionalIdeal.mem_spanSingleton, ← hc, mem_valBall_ord_iff hc0]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, by rw [Algebra.smul_def, mul_comm]; rfl⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, by rw [Algebra.smul_def, mul_comm]; rfl⟩

end Dual

section TraceChar

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

variable (L) in

def traceChar (ψ : AddChar K Circle) : AddChar L Circle :=
  ψ.compAddMonoidHom (Algebra.trace K L).toAddMonoidHom

theorem traceChar_apply (ψ : AddChar K Circle) (x : L) :
    traceChar L ψ x = ψ (Algebra.trace K L x) := rfl

theorem trace_algebraMap_mul (a : K) (x : L) :
    Algebra.trace K L (algebraMap K L a * x) = a * Algebra.trace K L x := by
  rw [← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]

variable [ValuativeRel K] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension K L]

theorem mem_valBall_algebraMap_mul {m : ℤ} {x : L} (hx : x ∈ valBall L m) {a : K}
    (ha : a ∈ 𝒪[K]) : algebraMap K L a * x ∈ valBall L m := by
  have := mul_mem_valBall (mem_valBall_zero_iff.mpr ((algebraMap_mem_integer_iff K L a).mpr ha)) hx
  rwa [zero_add] at this

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K] [FiniteDimensional K L]

variable {ψ : AddChar K Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
include hψ hψ1

omit [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] in

theorem forall_integer_mul_eq_one_iff (t : K) :
    (∀ a ∈ 𝒪[K], ψ (a * t) = 1) ↔ t ∈ valBall K (addCharConductor ψ) := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp only [mul_zero, AddChar.map_zero_eq_one, implies_true, true_iff]
    exact zero_mem _
  rw [mem_valBall_iff_le_ord ht, ← isTrivialOn_iff hψ hψ1]
  constructor
  · intro h x hx
    obtain ⟨y, rfl⟩ := (mem_valBall_ord_iff ht).mp hx
    rw [mul_comm]
    exact h y y.2
  · intro h a ha
    apply h
    rw [mem_valBall_ord_iff ht]
    exact ⟨⟨a, ha⟩, mul_comm _ _⟩

variable [Algebra.IsSeparable K L]

theorem isTrivialOn_traceChar_iff (m : ℤ) :
    IsTrivialOn (traceChar L ψ) m ↔
      (ramificationIndex K L : ℤ) * addCharConductor ψ - differentExponent K L ≤ m := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hϖ0 : (ϖ : K) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  obtain ⟨c, hcdef⟩ : ∃ c : K, c = (ϖ : K) ^ addCharConductor ψ := ⟨_, rfl⟩
  have hc0 : c ≠ 0 := hcdef ▸ zpow_ne_zero _ hϖ0
  have hcK : ord c = addCharConductor ψ := by rw [hcdef, ord_zpow hϖ0, ord_uniformizer hϖ, mul_one]
  have hcL : ord (algebraMap K L c) = ramificationIndex K L * addCharConductor ψ := by
    rw [ord_algebraMap, hcK]
  have step1 : IsTrivialOn (traceChar L ψ) m ↔
      ∀ x ∈ valBall L m, Algebra.trace K L x ∈ valBall K (addCharConductor ψ) := by
    constructor
    · intro h x hx
      rw [← forall_integer_mul_eq_one_iff hψ hψ1]
      intro a ha
      rw [← trace_algebraMap_mul]
      exact h _ (mem_valBall_algebraMap_mul hx ha)
    · intro h x hx
      rw [traceChar_apply]
      exact isTrivialOn_addCharConductor hψ hψ1 _ (h x hx)
  rw [step1]
  constructor
  · intro h
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
    have hπ0 : (π : L) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
    obtain ⟨w, hwdef⟩ : ∃ w : L,
        w = (π : L) ^ (m - ramificationIndex K L * addCharConductor ψ) := ⟨_, rfl⟩
    have hw0 : w ≠ 0 := hwdef ▸ zpow_ne_zero _ hπ0
    have hwk : ord w = m - ramificationIndex K L * addCharConductor ψ := by
      rw [hwdef, ord_zpow hπ0, ord_uniformizer hπ, mul_one]
    have hw : w ∈ valBall L (-(differentExponent K L : ℤ)) := by
      rw [← forall_trace_mul_mem_iff K]
      intro z
      have hx : algebraMap K L c * (w * z) ∈ valBall L m := by
        have h1 := mul_mem_valBall (mem_valBall_ord (x := algebraMap K L c))
          (mul_mem_valBall (mem_valBall_ord (x := w)) (mem_valBall_zero_iff.mpr z.2))
        rw [hcL, hwk] at h1
        convert h1 using 2
        ring
      have h2 := h _ hx
      rw [trace_algebraMap_mul] at h2
      have h3 := mul_mem_valBall (mem_valBall_ord (x := c⁻¹)) h2
      rw [ord_inv hc0, hcK, neg_add_cancel, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul] at h3
      exact mem_valBall_zero_iff.mp h3
    rw [mem_valBall_iff_le_ord hw0, hwk] at hw
    linarith
  · intro hm x hx
    obtain ⟨w, hwdef⟩ : ∃ w : L, w = algebraMap K L c⁻¹ * x := ⟨_, rfl⟩
    have hw : w ∈ valBall L (-(differentExponent K L : ℤ)) := by
      have h1 := mul_mem_valBall (mem_valBall_ord (x := algebraMap K L c⁻¹)) hx
      rw [ord_algebraMap, ord_inv hc0, hcK] at h1
      rw [hwdef]
      exact valBall_antitone (by linarith) h1
    have h2 := (forall_trace_mul_mem_iff K w).mpr hw 1
    rw [OneMemClass.coe_one, mul_one] at h2
    have hx' : x = algebraMap K L c * w := by
      rw [hwdef, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hc0, map_one, one_mul]
    rw [hx', trace_algebraMap_mul]
    have := mul_mem_valBall (mem_valBall_ord (x := c)) (mem_valBall_zero_iff.mpr h2)
    rwa [hcK, add_zero] at this

theorem continuous_traceChar : Continuous (traceChar L ψ) :=
  continuous_of_isTrivialOn ((isTrivialOn_traceChar_iff hψ hψ1 _).mpr le_rfl)

theorem traceChar_ne_one : traceChar L ψ ≠ 1 := by
  intro h
  have ht : IsTrivialOn (traceChar L ψ)
      ((ramificationIndex K L : ℤ) * addCharConductor ψ - differentExponent K L - 1) := by
    rw [h]
    intro x _
    exact AddChar.one_apply x
  have := (isTrivialOn_traceChar_iff hψ hψ1 _).mp ht
  linarith

theorem addCharConductor_traceChar :
    addCharConductor (traceChar L ψ) =
      (ramificationIndex K L : ℤ) * addCharConductor ψ - differentExponent K L := by
  have hc := continuous_traceChar (L := L) hψ hψ1
  have hne := traceChar_ne_one (L := L) hψ hψ1
  apply le_antisymm
  · exact (isTrivialOn_iff hc hne _).mp ((isTrivialOn_traceChar_iff hψ hψ1 _).mpr le_rfl)
  · exact (isTrivialOn_traceChar_iff hψ hψ1 _).mp (isTrivialOn_addCharConductor hc hne)

theorem addCharConductor_traceChar_of_eq_zero (h0 : addCharConductor ψ = 0) :
    addCharConductor (traceChar L ψ) = -(differentExponent K L : ℤ) := by
  rw [addCharConductor_traceChar hψ hψ1, h0, mul_zero, zero_sub]

end TraceChar

end GroundTheory.LocalField
end
end

-- bundled from GroundTheory.LocalFields.LocalZetaChar
section
noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel MeasureTheory Measure Topology Filter
open scoped WithZero NNReal ENNReal Pointwise

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

section Decomposition

theorem unifUnit_zpow_neg_mul_mem (u : Kˣ) :
    unifUnit K ^ (-ord (u : K)) * u ∈ unitFiltrationUnits K 0 := by
  rw [mem_unitFiltrationUnits_zero_iff_ord, ord_units_mul, ord_unifUnit_zpow]
  ring

theorem eq_unifUnit_zpow_mul (u : Kˣ) :
    u = unifUnit K ^ ord (u : K) * (unifUnit K ^ (-ord (u : K)) * u) := by
  rw [← mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]

theorem isCompact_unitFiltrationUnits_zero :
    IsCompact (unitFiltrationUnits K 0 : Set Kˣ) := by
  have hS : IsCompact ((valBall K 0 : Set K) \ valBall K 1) :=
    (isCompact_valBall 0).diff (isOpen_valBall 1)
  have heq : (unitFiltrationUnits K 0 : Set Kˣ) =
      Units.val ⁻¹' ((valBall K 0 : Set K) \ valBall K 1) := by
    rw [← ordShell_zero]
    ext u
    simp only [mem_ordShell, Set.mem_preimage, Set.mem_sdiff, SetLike.mem_coe,
      mem_valBall_iff_le_ord u.ne_zero]
    omega
  rw [heq]
  refine Units.isEmbedding_val₀.isInducing.isCompact_preimage' hS ?_
  rintro x ⟨-, hx⟩
  have hx0 : x ≠ 0 := fun h => hx (h ▸ zero_mem _)
  exact ⟨Units.mk0 x hx0, rfl⟩

end Decomposition

section QuasiCharacter

variable (χ : Kˣ →* ℂˣ)

def IsUnramifiedChar : Prop := unitFiltrationUnits K 0 ≤ χ.ker

def quasiCharConductor : ℕ := sInf {n : ℕ | unitFiltrationUnits K n ≤ χ.ker}

def quasiCharExponent : ℝ := -Real.logb (residueCard K) ‖((χ (unifUnit K) : ℂˣ) : ℂ)‖

variable {χ}

theorem isUnramifiedChar_iff : IsUnramifiedChar χ ↔ ∀ u : Kˣ, ord (u : K) = 0 → χ u = 1 := by
  refine ⟨fun h u hu => h (mem_unitFiltrationUnits_zero_iff_ord.mpr hu), fun h u hu => ?_⟩
  exact h u (mem_unitFiltrationUnits_zero_iff_ord.mp hu)

theorem quasiChar_apply_of_isUnramified (h : IsUnramifiedChar χ) (u : Kˣ) :
    χ u = χ (unifUnit K) ^ ord (u : K) := by
  conv_lhs => rw [eq_unifUnit_zpow_mul u]
  rw [map_mul, MonoidHom.mem_ker.mp (h (unifUnit_zpow_neg_mul_mem u)), mul_one, map_zpow]

theorem quasiChar_apply_eq_of_isUnramified (h : IsUnramifiedChar χ) {π : Kˣ}
    (hπ : ord (π : K) = 1) : χ π = χ (unifUnit K) := by
  rw [quasiChar_apply_of_isUnramified h, hπ, zpow_one]

variable (hχ : Continuous χ)
include hχ

theorem exists_unitFiltrationUnits_le_ker : ∃ n, unitFiltrationUnits K n ≤ χ.ker := by
  refine exists_unitFiltrationUnits_le (GroundTheory.Global.isOpen_ker_of_noSmallSubgroups (fun W hW => ?_)
    GroundTheory.Global.Complex.units_noSmallSubgroups χ hχ)
  obtain ⟨n, -, hn⟩ := hasBasis_nhds_one_unitFiltrationUnits.mem_iff.mp hW
  exact ⟨⟨unitFiltrationUnits K n, isOpen_unitFiltrationUnits n⟩, hn⟩

theorem unitFiltrationUnits_quasiCharConductor_le_ker :
    unitFiltrationUnits K (quasiCharConductor χ) ≤ χ.ker :=
  Nat.sInf_mem (exists_unitFiltrationUnits_le_ker hχ)

theorem quasiCharConductor_eq_zero_iff : quasiCharConductor χ = 0 ↔ IsUnramifiedChar χ := by
  constructor
  · intro h
    have := unitFiltrationUnits_quasiCharConductor_le_ker hχ
    rwa [h] at this
  · intro h
    exact Nat.eq_zero_of_le_zero (Nat.sInf_le h)

theorem exists_apply_ne_one_of_not_isUnramified (h : ¬ IsUnramifiedChar χ) :
    ∃ v ∈ unitFiltrationUnits K (quasiCharConductor χ - 1), χ v ≠ 1 := by
  have hc : quasiCharConductor χ ≠ 0 := mt (quasiCharConductor_eq_zero_iff hχ).mp h
  have hlt : quasiCharConductor χ - 1 < quasiCharConductor χ := by omega
  have hnot := Nat.notMem_of_lt_sInf hlt
  by_contra hcon
  push_neg at hcon
  exact hnot fun v hv => MonoidHom.mem_ker.mpr (hcon v hv)

omit hχ in
theorem quasiCharConductor_pos (hχ : Continuous χ) (h : ¬ IsUnramifiedChar χ) :
    0 < quasiCharConductor χ :=
  Nat.pos_of_ne_zero (mt (quasiCharConductor_eq_zero_iff hχ).mp h)

theorem norm_quasiChar_apply_eq_one {u : Kˣ} (hu : u ∈ unitFiltrationUnits K 0) :
    ‖((χ u : ℂˣ) : ℂ)‖ = 1 := by
  have hcont : Continuous fun v : Kˣ => ‖((χ v : ℂˣ) : ℂ)‖ :=
    (Units.continuous_val.comp hχ).norm
  obtain ⟨C, hC⟩ := isCompact_unitFiltrationUnits_zero.exists_bound_of_continuousOn
    hcont.continuousOn
  have key : ∀ v ∈ unitFiltrationUnits K 0, ‖((χ v : ℂˣ) : ℂ)‖ ≤ 1 := by
    intro v hv
    by_contra hlt
    push_neg at hlt
    obtain ⟨n, hn⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hlt).eventually_gt_atTop C).exists
    have := hC (v ^ n) (pow_mem hv n)
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), map_pow, Units.val_pow_eq_pow_val,
      norm_pow] at this
    linarith
  have h1 := key u hu
  have h2 := key u⁻¹ (inv_mem hu)
  rw [map_inv, Units.val_inv_eq_inv_val, norm_inv] at h2
  have hpos : 0 < ‖((χ u : ℂˣ) : ℂ)‖ := norm_pos_iff.mpr (χ u).ne_zero
  have : 1 ≤ ‖((χ u : ℂˣ) : ℂ)‖ := by rwa [inv_le_one₀ hpos] at h2
  linarith

theorem norm_quasiChar_apply (u : Kˣ) :
    ‖((χ u : ℂˣ) : ℂ)‖ = (modulus (u : K) : ℝ) ^ quasiCharExponent χ := by
  have hq := residueCard_pos_real (K := K)
  have hq1 : (residueCard K : ℝ) ≠ 1 := by exact_mod_cast (one_lt_residueCard (K := K)).ne'
  have hr : 0 < ‖((χ (unifUnit K) : ℂˣ) : ℂ)‖ := norm_pos_iff.mpr (χ _).ne_zero
  conv_lhs => rw [eq_unifUnit_zpow_mul u]
  rw [map_mul, Units.val_mul, norm_mul,
    norm_quasiChar_apply_eq_one hχ (unifUnit_zpow_neg_mul_mem u), mul_one, map_zpow,
    Units.val_zpow_eq_zpow_val, norm_zpow, modulus_of_ne_zero u.ne_zero, NNReal.coe_zpow,
    NNReal.coe_natCast, ← Real.rpow_intCast, ← Real.rpow_intCast, ← Real.rpow_mul hq.le,
    quasiCharExponent]
  rw [show ((-ord (u : K) : ℤ) : ℝ) * -Real.logb (residueCard K) ‖((χ (unifUnit K) : ℂˣ) : ℂ)‖ =
      Real.logb (residueCard K) ‖((χ (unifUnit K) : ℂˣ) : ℂ)‖ * (ord (u : K) : ℝ) by push_cast; ring,
    Real.rpow_mul hq.le, Real.rpow_logb hq hq1 hr]

omit hχ in
theorem continuous_quasiChar_inv (hχ : Continuous χ) : Continuous (χ⁻¹ : Kˣ →* ℂˣ) := by
  have : ((χ⁻¹ : Kˣ →* ℂˣ) : Kˣ → ℂˣ) = fun u => (χ u)⁻¹ := by
    funext u
    rfl
  rw [this]
  exact hχ.inv

omit hχ in

theorem quasiCharExponent_inv : quasiCharExponent χ⁻¹ = -quasiCharExponent χ := by
  simp only [quasiCharExponent, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv,
    Real.logb_inv, neg_neg]

end QuasiCharacter

section ShellIntegral

variable [MeasurableSpace K] [BorelSpace K] {χ : Kˣ →* ℂˣ}

open scoped Classical in

theorem setIntegral_ordShell_quasiChar (hχ : Continuous χ) (k : ℤ) :
    ∫ u in ordShell K k, ((χ u : ℂˣ) : ℂ) ∂multHaar K =
      if IsUnramifiedChar χ then ((χ (unifUnit K) : ℂˣ) : ℂ) ^ k else 0 := by
  have hk : ord ((unifUnit K ^ k : Kˣ) : K) + 0 = k := by rw [ord_unifUnit_zpow, add_zero]
  have e := setIntegral_ordShell_mul (fun u : Kˣ => ((χ u : ℂˣ) : ℂ)) (unifUnit K ^ k) 0
  rw [hk] at e
  rw [e]
  simp only [map_mul, Units.val_mul, map_zpow, Units.val_zpow_eq_zpow_val]
  rw [integral_const_mul]
  split_ifs with h
  · have hone : ∀ u ∈ ordShell K 0, ((χ u : ℂˣ) : ℂ) = 1 := fun u hu => by
      rw [(isUnramifiedChar_iff.mp h) u hu, Units.val_one]
    rw [setIntegral_congr_fun (measurableSet_ordShell 0) hone, setIntegral_const,
      measureReal_def, multHaar_ordShell, ENNReal.toReal_one, one_smul, mul_one]
  · obtain ⟨v, hv, hv1⟩ : ∃ v ∈ unitFiltrationUnits K 0, χ v ≠ 1 := by
      by_contra hcon
      push_neg at hcon
      exact h fun v hv => MonoidHom.mem_ker.mpr (hcon v hv)
    rw [setIntegral_ordShell_eq_zero (fun u => ((χ u : ℂˣ) : ℂ))
      (mem_unitFiltrationUnits_zero_iff_ord.mp hv) (a := ((χ v : ℂˣ) : ℂ))
      (fun h1 => hv1 (Units.val_eq_one.mp h1)) 0 (fun u _ => by simp), mul_zero]

end ShellIntegral

end GroundTheory.LocalField
end
end

