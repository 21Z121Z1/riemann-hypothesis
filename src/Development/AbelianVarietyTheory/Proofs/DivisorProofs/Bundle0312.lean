import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Formalism.SatakeDualWeyl.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0227
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0289
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0003
import Formalism.GradedWeylDivisibility.StatementA
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0287
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUniMat
section
open MeasureTheory GlobalTheory.PRep GlobalTheory.LGrp Matrix
open scoped NNReal

noncomputable section
namespace GlobalTheory.BorelModulus

abbrev Pos (n : ℕ) : Type := {p : Fin n × Fin n // p.1 < p.2}

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem mem_U_iff (g : GL (Fin n) k) :
    g ∈ (borelGL k (Fin n)).U ↔ (∀ i j, j < i → g.val i j = 0) ∧ ∀ i, g.val i i = 1 := by
  rw [LeviDatum.mem_U]
  constructor
  · rintro ⟨h, e⟩
    exact ⟨fun _ _ hij => h hij, fun i => congrArg (fun t : Fin n → kˣ => (t i : k)) e⟩
  · rintro ⟨h, e⟩
    exact ⟨fun _ _ hij => h _ _ hij, funext fun i => Units.ext (e i)⟩

def uniMat (x : Pos n → k) : Matrix (Fin n) (Fin n) k :=
  fun i j => if h : i < j then x ⟨(i, j), h⟩ else if i = j then 1 else 0

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem uniMat_low (x : Pos n → k) (i j : Fin n) (h : j < i) : uniMat x i j = 0 := by
  simp [uniMat, h.not_gt, h.ne']

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem uniMat_diag (x : Pos n → k) (i : Fin n) : uniMat x i i = 1 := by
  simp [uniMat]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem uniMat_det (x : Pos n → k) : (uniMat x).det = 1 := by
  rw [det_of_upperTriangular (fun i j h => uniMat_low x i j h)]
  simp [uniMat_diag]

theorem continuous_uniMat : Continuous (uniMat : (Pos n → k) → _) := by
  refine continuous_matrix fun i j => ?_
  unfold uniMat
  split_ifs
  · exact continuous_apply _
  · exact continuous_const
  · exact continuous_const

def uniGL (x : Pos n → k) : GL (Fin n) k :=
  ⟨uniMat x, (uniMat x).adjugate, by rw [mul_adjugate, uniMat_det, one_smul],
    by rw [adjugate_mul, uniMat_det, one_smul]⟩

theorem continuous_uniGL : Continuous (uniGL : (Pos n → k) → _) :=
  Units.continuous_iff.2 ⟨continuous_uniMat, continuous_uniMat.matrix_adjugate⟩

def coord (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) :
    (borelGL k (Fin n)).U ≃ₜ (Pos n → k) where
  toFun u p := u.1.val p.1.1 p.1.2
  invFun x := ⟨uniGL x, (mem_U_iff _).2 ⟨uniMat_low x, uniMat_diag x⟩⟩
  left_inv u := by
    obtain ⟨h1, h2⟩ := (mem_U_iff _).1 u.2
    refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
    show uniMat (fun p : Pos n => u.1.val p.1.1 p.1.2) i j = u.1.val i j
    rcases lt_trichotomy i j with h | rfl | h
    · simp [uniMat, h]
    · rw [uniMat_diag, h2]
    · rw [uniMat_low _ _ _ h, h1 _ _ h]
  right_inv x := by
    funext p
    show uniMat x _ _ = _
    simp [uniMat, p.2]
  continuous_toFun := continuous_pi fun p => (continuous_entry _ _).comp continuous_subtype_val
  continuous_invFun := continuous_uniGL.subtype_mk _

theorem coord_apply (u : (borelGL k (Fin n)).U) (p : Pos n) : coord k n u p = u.1.val p.1.1 p.1.2 := rfl

def leftMat (A : Matrix (Fin n) (Fin n) k) : Matrix (Pos n) (Pos n) k :=
  fun p q => if q.1.2 = p.1.2 then A p.1.1 q.1.1 else 0

theorem leftMat_det (u : (borelGL k (Fin n)).U) : (leftMat u.1.val).det = 1 := by
  obtain ⟨h1, h2⟩ := (mem_U_iff _).1 u.2
  have hb : (leftMat u.1.val).BlockTriangular (fun p => p.1.1) := fun p q h => by
    simp [leftMat, h1 _ _ h]
  rw [hb.det_fintype]
  refine Finset.prod_eq_one fun a _ => ?_
  have : (leftMat u.1.val).toSquareBlock (fun p => p.1.1) a = 1 := by
    ext ⟨⟨⟨i, j⟩, hp⟩, rfl⟩ ⟨⟨⟨i', j'⟩, hq⟩, e⟩
    obtain rfl : i' = i := e
    simp [toSquareBlock_def, leftMat, h2, Matrix.one_apply, eq_comm]
  rw [this, det_one]

theorem coord_mul (u x : (borelGL k (Fin n)).U) :
    coord k n (u * x) = (leftMat u.1.val).mulVec (coord k n x) + coord k n u := by
  obtain ⟨h1, h2⟩ := (mem_U_iff _).1 x.2
  funext ⟨⟨i, j⟩, hp⟩
  show (u.1.val * x.1.val) i j = ∑ q : Pos n, (if q.1.2 = j then u.1.val i q.1.1 else 0) * x.1.val q.1.1 q.1.2 +
    u.1.val i j
  rw [← Finset.sum_subtype (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2) (by simp)
    (fun q : Fin n × Fin n => (if q.2 = j then u.1.val i q.1 else 0) * x.1.val q.1 q.2),
    Finset.sum_filter, Fintype.sum_prod_type, mul_apply]
  have : u.1.val i j = ∑ l, if l = j then u.1.val i l else 0 := by simp
  rw [this, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (by simp)]
  rcases lt_trichotomy l j with h | rfl | h
  · simp [h, h.ne]
  · simp [h2]
  · simp [h.not_gt, h.ne', h1 _ _ h]

theorem coord_conj (t : Fin n → kˣ) (ht) (x : (borelGL k (Fin n)).U) :
    coord k n (conjAut _ ⟨(borelGL k (Fin n)).s t, ht⟩ x) =
      (diagonal fun p : Pos n => ((t p.1.1 * (t p.1.2)⁻¹ : kˣ) : k)).mulVec (coord k n x) := by
  funext p
  rw [mulVec_diagonal, coord_apply, conjAut_coe, coord_apply]
  show ((diagHom k (Fin n) t) * x.1 * (diagHom k (Fin n) t)⁻¹).val _ _ = _
  rw [← map_inv, Units.val_mul, Units.val_mul, diagHom_val, diagHom_val, mul_diagonal, diagonal_mul]
  simp only [Pi.inv_apply, Units.val_mul]
  ring

theorem prod_pos_eq {G : Type} [CommGroup G] (t : Fin n → G) :
    ∏ p : Pos n, (t p.1.1 * (t p.1.2)⁻¹) = ∏ i : Fin n, t i ^ ((n : ℤ) - 1 - 2 * (i.val : ℤ)) := by
  rw [← Finset.prod_subtype (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2) (by simp)
    (fun q : Fin n × Fin n => t q.1 * (t q.2)⁻¹), Finset.prod_mul_distrib, Finset.prod_filter, Finset.prod_filter,
    Fintype.prod_prod_type, Fintype.prod_prod_type_right, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [← Finset.prod_filter, Finset.prod_const]
  rw [Finset.filter_lt_eq_Ioi, Finset.filter_gt_eq_Iio, Fin.card_Ioi, Fin.card_Iio, inv_pow, ← zpow_natCast,
    ← zpow_natCast, ← _root_.zpow_sub]
  congr 1
  have := i.2
  omega

theorem delta_eq (q : (borelGL k (Fin n)).Q) :
    (borelGL k (Fin n)).delta q =
      distribHaarChar k (∏ p : Pos n, ((borelGL k (Fin n)).p q p.1.1 * ((borelGL k (Fin n)).p q p.1.2)⁻¹)) := by
  haveI := SplitWeil.secondCountable k
  borelize k
  borelize ↥(borelGL k (Fin n)).U
  let ν : Measure k := Measure.addHaar
  let π : Measure (Pos n → k) := Measure.pi fun _ => ν
  let e := coord k n
  let μ : Measure (borelGL k (Fin n)).U := Measure.map e.symm π
  have hm : ∀ A : Matrix (Pos n) (Pos n) k, Measurable A.mulVec := fun A =>
    (continuous_const.matrix_mulVec continuous_id).measurable
  have hes : Measurable e.symm := e.symm.continuous.measurable
  haveI : μ.Regular := Measure.Regular.map e.symm
  haveI : μ.IsOpenPosMeasure := e.symm.continuous.isOpenPosMeasure_map e.symm.surjective
  haveI : μ.IsMulLeftInvariant := ⟨fun u => by
    have h1 : (fun x => u * x) ∘ e.symm = e.symm ∘ (fun y => y + e u) ∘ (leftMat u.1.val).mulVec := by
      funext y
      apply e.injective
      simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
      rw [coord_mul, Homeomorph.apply_symm_apply]
    have h2 := WeilM.smul_map_mulVec_pi ν (leftMat u.1.val) 1 (by rw [leftMat_det]; rfl)
    rw [map_one, ENNReal.coe_one, one_smul] at h2
    rw [Measure.map_map (measurable_const_mul u) hes, h1,
      ← Measure.map_map hes ((measurable_add_const _).comp (hm _)),
      ← Measure.map_map (measurable_add_const _) (hm _), h2, map_add_right_eq_self]⟩
  haveI : μ.IsHaarMeasure := {}
  set t := (borelGL k (Fin n)).p q
  rw [LeviDatum.delta_apply]
  set g : Subgroup.normalizer ((borelGL k (Fin n)).U : Set (GL (Fin n) k)) := ⟨(borelGL k (Fin n)).s t, _⟩
  set c := distribHaarChar k (∏ p : Pos n, (t p.1.1 * (t p.1.2)⁻¹))
  have hc : Continuous (conjAut (borelGL k (Fin n)).U g) := (conjAut _ g).continuous
  have h3 : (c : ENNReal) • Measure.map (conjAut _ g) μ = μ := by
    have h1 : (conjAut _ g) ∘ e.symm =
        e.symm ∘ (diagonal fun p : Pos n => ((t p.1.1 * (t p.1.2)⁻¹ : kˣ) : k)).mulVec := by
      funext y
      apply e.injective
      simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
      rw [coord_conj, Homeomorph.apply_symm_apply]
    have h2 := WeilM.smul_map_mulVec_pi ν (diagonal fun p : Pos n => ((t p.1.1 * (t p.1.2)⁻¹ : kˣ) : k))
      (∏ p : Pos n, (t p.1.1 * (t p.1.2)⁻¹)) (by rw [det_diagonal, Units.coe_prod])
    rw [Measure.map_map hc.measurable hes, h1, ← Measure.map_map hes (hm _),
      ← Measure.map_smul, h2]
  haveI : LocallyCompactSpace (borelGL k (Fin n)).U := (borelGL k (Fin n)).closed_U.locallyCompactSpace
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : (borelGL k (Fin n)).U)
  have h4 := modulus_measure _ (borelGL k (Fin n)).closed_U μ g K
  have h5 := congrArg (fun m : Measure _ => m (conjAut _ g '' K)) h3
  simp only [Measure.smul_apply, smul_eq_mul] at h5
  rw [Measure.map_apply hc.measurable
    (hK.image hc).isClosed.measurableSet,
    Set.preimage_image_eq _ (conjAut _ g).injective, h4] at h5
  exact (ENNReal.coe_injective ((ENNReal.mul_left_inj (Measure.measure_pos_of_mem_nhds μ hK1).ne'
    hK.measure_lt_top.ne).1 h5)).symm

theorem delta_borelGL : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (q : (borelGL k (Fin n)).Q), (((borelGL k (Fin n)).delta q : ℝ≥0) : ℝ) =
      ∏ i : Fin n, GlobalTheory.SplitWeil.nabs k ((borelGL k (Fin n)).p q i) ^ ((n : ℤ) - 1 - 2 * (i.val : ℤ)) := by
  intro k _ _ _ _ n q
  rw [delta_eq, prod_pos_eq, map_prod, NNReal.coe_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h : ∀ (x : kˣ) (m : ℤ), distribHaarChar k (x ^ m) = distribHaarChar k x ^ m := fun x m =>
    (congrArg Units.val (map_zpow (distribHaarChar k (G := kˣ)).toHomUnits x m)).trans
      (Units.val_zpow_eq_zpow_val _ _)
  rw [h, NNReal.coe_zpow]
  rfl

end GlobalTheory.BorelModulus
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetRestrictScalarsTwoSidedMatrixMul
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

noncomputable section

namespace GlobalTheory.KSp

def twoSidedMulLin {E : Type} [Field E] {α ν : Type} [Fintype α] [Fintype ν]
    (u : Matrix α α E) (a : Matrix ν ν E) : Matrix α ν E →ₗ[E] Matrix α ν E where
  toFun x := u * x * a
  map_add' x y := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c x := by rw [Matrix.mul_smul, Matrix.smul_mul]; rfl

theorem det_twoSidedMulLin {E : Type} [Field E] {α ν : Type} [Fintype α] [DecidableEq α]
    [Fintype ν] [DecidableEq ν] (u : Matrix α α E) (a : Matrix ν ν E) :
    LinearMap.det (twoSidedMulLin u a) = u.det ^ Fintype.card ν * a.det ^ Fintype.card α := by
  let e : (α × ν → E) ≃ₗ[E] Matrix α ν E := LinearEquiv.curry E E α ν
  have h : twoSidedMulLin u a =
      (e : _ →ₗ[E] _) ∘ₗ (Matrix.toLin' (Matrix.kroneckerMap (· * ·) u a.transpose)) ∘ₗ
        (e.symm : _ →ₗ[E] _) := by
    refine LinearMap.ext fun z => ?_
    funext i j
    change (u * z * a) i j = (Matrix.kroneckerMap (· * ·) u a.transpose).mulVec (Function.uncurry z) (i, j)
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
      Matrix.transpose_apply, Function.uncurry_apply_pair, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
    rw [show Function.uncurry z (b, c) = z b c from rfl]
    ring
  rw [h, LinearMap.det_conj, LinearMap.det_toLin', Matrix.det_kronecker, Matrix.det_transpose]

theorem det_restrictScalars_twoSidedMul : ∀ (F : Type) [Field F] (E : Type) [Field E] [Algebra F E]
    [FiniteDimensional F E] (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν]
    [DecidableEq ν] (u : Matrix α α E) (a : Matrix ν ν E) (T : Matrix α ν E →ₗ[F] Matrix α ν E),
    (∀ x, T x = u * x * a) →
      LinearMap.det T = Algebra.norm F u.det ^ Fintype.card ν * Algebra.norm F a.det ^ Fintype.card α := by
  intro F _ E _ _ _ α _ _ ν _ _ u a T hT
  have hT' : T = (twoSidedMulLin u a).restrictScalars F := by
    refine LinearMap.ext fun x => ?_
    rw [hT]; rfl
  rw [hT', LinearMap.det_restrictScalars, det_twoSidedMulLin, map_mul, map_pow, map_pow]

end GlobalTheory.KSp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantElementProductStatement
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.determinant_element_product : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (C : Type) [Field C] [Algebra O C] (ε : PreTilt O p) (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (ψ : RL p O Λ →+* RL p O Λ) (N N' : ℕ) (Δ Δ' : RL p O Λ) (a a' : (Λ →+* O) → ℕ) (c c' : (Λ →+* O) → C), IsDetElt ε ψ N Δ → IsDetElt ε ψ N' Δ' → HasOrders C ε N Δ a c → HasOrders C ε N' Δ' a' c' → IsDetElt ε ψ (N + N') (Δ * Δ') ∧ HasOrders C ε (N + N') (Δ * Δ') (a + a') (c * c') := by
  first | exact @GlobalTheory.DetInv.detData_mul | exact GlobalTheory.DetInv.detData_mul | (intros; apply GlobalTheory.DetInv.detData_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantLatticePrincipalStatement
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.determinant_lattice_principal : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (Λ : Type) [CommRing Λ] (h N : ℕ), v.Integers O → ∀ (ρ : Λ → Matrix (Fin h) (Fin h) O) (τ : Λ →+* O), iSupIndep (fun σ : Λ →+* O => eig C ρ σ) → (⨆ σ : Λ →+* O, eig C ρ σ) = ⊤ → Module.finrank C (eig C ρ τ) = N → Module.finrank C (detLine C ρ τ N) = 1 ∧ ∃ w : detLine C ρ τ N, w ≠ 0 ∧ detLattice C ρ τ N = Submodule.span O {w} := by
  first | exact @GlobalTheory.detLattice_eq_span_singleton | exact GlobalTheory.detLattice_eq_span_singleton | (intros; apply GlobalTheory.detLattice_eq_span_singleton <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantOrdersIndependentOfRootStatement
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.determinant_orders_independent_of_root : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε ε' : PreTilt O p) (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (ψ : RL p O Λ →+* RL p O Λ) (N : ℕ) (Δ : RL p O Λ) (a : (Λ →+* O) → ℕ) (c : (Λ →+* O) → C), Associated (xi ε) (xi ε') → Associated (mu ε) (mu ε') → IsDetElt ε ψ N Δ → HasOrders C ε N Δ a c → ∃ c' : (Λ →+* O) → C, IsDetElt ε' ψ N Δ ∧ HasOrders C ε' N Δ a c' ∧ ∀ σ, v (c' σ) = v (c σ) := by
  first | exact @GlobalTheory.detData_indep_eps | exact GlobalTheory.detData_indep_eps | (intros; apply GlobalTheory.detData_indep_eps <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylEqBotOfNotAntitone
section
namespace GlobalTheory.NonDomZero

theorem exists_lt_lt_of_not_antitone {N : ℕ} {ν : Fin N → ℕ} (hν : ¬ Antitone ν) :
    ∃ a b : Fin N, a < b ∧ ν a < ν b := by
  simp only [Antitone, not_forall] at hν
  obtain ⟨a, b, hab, hlt⟩ := hν
  refine ⟨a, b, lt_of_le_of_ne hab ?_, lt_of_not_ge hlt⟩
  rintro rfl
  exact hlt le_rfl

theorem dualWeyl_eq_bot_of_not_antitone :
    ∀ (O : Type) [CommRing O] [IsDomain O] [CharZero O] (N : ℕ) (ν : Fin N → ℕ),
      ¬ Antitone ν → Formalism.GradedWeylDivisibility.dualWeyl O N N ν = ⊥ := by
  intro O _ _ _ N ν hν
  exact Formalism.GradedWeylDivisibility.dualWeylModuleNonDominant O N N ν (exists_lt_lt_of_not_antitone hν)

end GlobalTheory.NonDomZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfLeadOrdersEq
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem dvd_of_lead_orders_eq : ∀ (R C ι : Type) [CommRing R] [Field C] (f : ι → (R →+* C))
    (ξ : R) (N : ℕ) (a : ι → ℕ) (c c' : ι → C) (Δ Δ' u u' g g' g₁ : R),
    ξ ∈ nonZeroDivisors R → (∀ i, f i ξ = 0) → (∀ r : R, (∀ i, f i r = 0) → ξ ∣ r) →
    (∀ i, a i ≤ N) → (∀ i, c i ≠ 0) → (∀ i, Lead (f i) ξ Δ (a i) (c i)) →
    (∀ i, Lead (f i) ξ Δ' (a i) (c' i)) → Δ = g * u → Δ' = g' * u' → (∀ i, f i u' ≠ 0) →
    g * g₁ = ξ ^ N → g ∣ g' := by
  intro R C ι _ _ f ξ N a c c' Δ Δ' u u' g g' g₁ hξ hf0 hker haN hc hL hL' hΔ hΔ' hu' hgg
  have hpow : ∀ n : ℕ, ξ ^ n ∈ nonZeroDivisors R := fun n => pow_mem hξ n
  have hloc : ∀ i, ∃ s : R, f i s ≠ 0 ∧ ξ ^ N ∣ s * (g' * g₁) := by
    intro i
    obtain ⟨s, t, hs, hst, hft⟩ := hL i
    obtain ⟨s', t', hs', hst', -⟩ := hL' i
    have ht : f i t ≠ 0 := by rw [hft]; exact mul_ne_zero (hc i) hs
    have hsplit : ξ ^ a i * ξ ^ (N - a i) = ξ ^ N := pow_mul_pow_sub ξ (haN i)
    have key : t * g₁ = s * u * ξ ^ (N - a i) := by
      have h1 : (t * g₁ - s * u * ξ ^ (N - a i)) * ξ ^ a i = 0 := by
        have e1 : ξ ^ a i * t * g₁ = s * u * ξ ^ N := by
          calc ξ ^ a i * t * g₁ = (s * Δ) * g₁ := by rw [hst]
            _ = s * u * (g * g₁) := by rw [hΔ]; ring
            _ = s * u * ξ ^ N := by rw [hgg]
        rw [← hsplit] at e1
        linear_combination e1
      have := (mul_right_mem_nonZeroDivisors_eq_zero_iff (hpow (a i))).mp h1
      exact sub_eq_zero.mp this
    refine ⟨s' * u' * t, ?_, ⟨t' * s * u, ?_⟩⟩
    · simp only [map_mul]
      exact mul_ne_zero (mul_ne_zero hs' (hu' i)) ht
    · calc s' * u' * t * (g' * g₁) = (s' * Δ') * (t * g₁) := by rw [hΔ']; ring
        _ = ξ ^ a i * t' * (s * u * ξ ^ (N - a i)) := by rw [hst', key]
        _ = (ξ ^ a i * ξ ^ (N - a i)) * (t' * s * u) := by ring
        _ = ξ ^ N * (t' * s * u) := by rw [hsplit]
  obtain ⟨b, hb⟩ := GlobalTheory.T.divisibility_of_vanishing_powers R C ι f ξ hξ hf0 hker N (g' * g₁) hloc
  have hg₁ : g₁ ∈ nonZeroDivisors R := by
    rw [mem_nonZeroDivisors_iff_right]
    intro x hx
    have : x * ξ ^ N = 0 := by rw [← hgg, ← mul_assoc, mul_comm x g, mul_assoc, hx, mul_zero]
    exact (mul_right_mem_nonZeroDivisors_eq_zero_iff (hpow N)).mp this
  refine ⟨b, ?_⟩
  have h2 : (g' - g * b) * g₁ = 0 := by
    rw [sub_mul, hb, ← hgg]; ring
  exact sub_eq_zero.mp ((mul_right_mem_nonZeroDivisors_eq_zero_iff hg₁).mp h2)

end GlobalTheory.DetInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrDeterminantProductOrders
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

noncomputable section
namespace GlobalTheory.ShiftBasis

section Lat
variable {O : Type} [CommRing O] (C : Type) [Field C] [Algebra O C] {Λ : Type} [CommRing Λ] {h : ℕ}

theorem mem_quotLattice_iff (ρ : Λ → Matrix (Fin h) (Fin h) O) (τ : Λ →+* O) (z : eig C ρ τ) :
    z ∈ quotLattice C ρ τ ↔ (z : Fin h → C) ∈ eigPart C ρ τ ⊤ := by
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨z.2, ?_⟩
    refine Submodule.mem_sup.2 ⟨incl C h t, Submodule.mem_map_of_mem Submodule.mem_top,
      -((fun i => algebraMap O C (t i)) - (z : Fin h → C)), ?_, ?_⟩
    · exact (Submodule.restrictScalars_mem _ _ _).2 (Submodule.neg_mem _ ht)
    · ext i; simp [incl]
  · rintro ⟨-, hz⟩
    obtain ⟨y, hy, u, hu, hyu⟩ := Submodule.mem_sup.1 hz
    obtain ⟨t, -, rfl⟩ := Submodule.mem_map.1 hy
    refine ⟨t, ?_⟩
    have : (fun i => algebraMap O C (t i)) - (z : Fin h → C) = -u := by
      rw [← hyu]; ext i; simp [incl]
    rw [this]
    exact Submodule.neg_mem _ ((Submodule.restrictScalars_mem _ _ _).1 hu)
end Lat

section Wedge
variable (C : Type) [Field C]

theorem iotaMulti_comb {M : Type} [AddCommGroup M] [Module C M] (N : ℕ) (x : Fin N → M)
    (c : Matrix (Fin N) (Fin N) C) :
    exteriorPower.ιMulti C N (fun i => ∑ j, c i j • x j) = c.det • exteriorPower.ιMulti C N x := by
  set f := (exteriorPower.ιMulti C N (M := M)).compLinearMap (Fintype.linearCombination C x)
  have h3 : f (fun i => c i) = exteriorPower.ιMulti C N (fun i => ∑ j, c i j • x j) := by
    simp only [f, AlternatingMap.compLinearMap_apply, Fintype.linearCombination_apply]
  have h4 : f (Pi.basisFun C (Fin N)) = exteriorPower.ιMulti C N x := by
    simp only [f, AlternatingMap.compLinearMap_apply]
    congr 1; funext i
    simp [Fintype.linearCombination_apply, Pi.single_apply]
  have key : ∀ ψ : Module.Dual C (⋀[C]^N M), ψ (f (fun i => c i)) =
      ψ (c.det • f (Pi.basisFun C (Fin N))) := by
    intro ψ
    have h := AlternatingMap.eq_smul_basis_det (Pi.basisFun C (Fin N)) (ψ.compAlternatingMap f)
    have := congrArg (fun g => g (fun i => c i)) h
    simp only [LinearMap.compAlternatingMap_apply, AlternatingMap.smul_apply, smul_eq_mul,
      Pi.basisFun_det_apply] at this
    rw [this, map_smul, smul_eq_mul, mul_comm]
    rfl
  have : f (fun i => c i) - c.det • f (Pi.basisFun C (Fin N)) = 0 := by
    rw [← Module.forall_dual_apply_eq_zero_iff C]
    intro ψ; rw [map_sub, key, sub_self]
  rw [← h3, ← h4]
  exact sub_eq_zero.mp this

end Wedge

theorem shift_basis : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (a b h : ℕ) (D : Datum ε h Λ) (τ : Λ →+* O) (w : Fin a → Fin h → C) (n : Fin b → Fin h → C), IsBasisOf C (wQuot C D τ) w → IsBasisOf C (alQuot C D τ) n → ∃ x : Fin (a + b) → eig C (actT D) τ, (∀ i, (x (Fin.castAdd b i) : Fin h → C) = w i) ∧ (∀ i, alC C D (x (Fin.natAdd a i)) = n i) ∧ IsBasisOf C (eigPart C (actT D) τ ⊤) (fun i => (x i : Fin h → C)) ∧ detLattice C (actT D) τ (a + b) = Submodule.span O {exteriorPower.ιMulti C (a + b) x} := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ a b h D τ w n hw hn
  set E := eigPart C (actT D) τ ⊤ with hE
  have hwQ : ∀ i, w i ∈ E ∧ alC C D (w i) = 0 := by
    intro i
    have : w i ∈ wQuot C D τ := hw.2 ▸ Submodule.subset_span ⟨i, rfl⟩
    exact ⟨this.1, this.2⟩
  have hnQ : ∀ j, ∃ y, y ∈ E ∧ alC C D y = n j := by
    intro j
    have : n j ∈ alQuot C D τ := hn.2 ▸ Submodule.subset_span ⟨j, rfl⟩
    obtain ⟨y, hy, hyj⟩ := Submodule.mem_map.1 this
    exact ⟨y, hy, hyj⟩
  choose t htE htn using hnQ
  set vec : Fin (a + b) → Fin h → C := Fin.append w t with hvec
  have hvecE : ∀ i, vec i ∈ E := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa [vec] using (hwQ j).1
    · simpa [vec] using htE j
  have hEeig : ∀ y ∈ E, y ∈ eig C (actT D) τ := fun y hy => hy.1
  let x : Fin (a + b) → eig C (actT D) τ := fun i => ⟨vec i, hEeig _ (hvecE i)⟩
  have hxv : ∀ i, (x i : Fin h → C) = vec i := fun i => rfl
  have hspan : Submodule.span O (Set.range vec) = E := by
    apply le_antisymm
    · rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; exact hvecE i
    · intro y hy
      have h1 : alC C D y ∈ alQuot C D τ := Submodule.mem_map_of_mem (f := (alC C D).restrictScalars O) hy
      rw [← hn.2] at h1
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 h1
      have h2 : y - ∑ j, c j • t j ∈ wQuot C D τ := by
        refine ⟨E.sub_mem hy (E.sum_mem fun j _ => E.smul_mem _ (htE j)), ?_⟩
        show alC C D (y - ∑ j, c j • t j) = 0
        rw [map_sub, map_sum, ← hc]
        simp only [LinearMap.map_smul_of_tower, htn, sub_self]
      rw [← hw.2] at h2
      obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 h2
      have : y = ∑ i, d i • vec (Fin.castAdd b i) + ∑ j, c j • vec (Fin.natAdd a j) := by
        simp only [vec, Fin.append_left, Fin.append_right]
        rw [hd]; abel
      rw [this]
      refine Submodule.add_mem _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_)
        (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_) <;>
        exact Submodule.subset_span ⟨_, rfl⟩
  have hind : LinearIndependent C vec := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_add] at hg
    simp only [vec, Fin.append_left, Fin.append_right] at hg
    have h1 := congrArg (alC C D) hg
    simp only [map_add, map_sum, map_smul, (hwQ _).2, smul_zero, Finset.sum_const_zero, zero_add,
      htn, map_zero] at h1
    have hb : ∀ j, g (Fin.natAdd a j) = 0 :=
      (Fintype.linearIndependent_iff.1 hn.1) (fun j => g (Fin.natAdd a j)) h1
    simp only [hb, zero_smul, Finset.sum_const_zero, add_zero] at hg
    have ha : ∀ i, g (Fin.castAdd b i) = 0 :=
      (Fintype.linearIndependent_iff.1 hw.1) (fun i => g (Fin.castAdd b i)) hg
    intro i
    exact Fin.addCases ha hb i
  refine ⟨x, fun i => by simp [x, vec], fun i => by simp [x, vec, htn], ⟨hind, hspan⟩, ?_⟩
  apply le_antisymm
  · rw [detLattice, Submodule.span_le]
    rintro _ ⟨z, hz, rfl⟩
    have hzE : ∀ i, (z i : Fin h → C) ∈ Submodule.span O (Set.range vec) := fun i => by
      rw [hspan]; exact (mem_quotLattice_iff C _ _ _).1 (hz i)
    choose c hc using fun i => (Submodule.mem_span_range_iff_exists_fun O).1 (hzE i)
    have hzc : z = fun i => ∑ j, (Matrix.of fun i j => algebraMap O C (c i j)) i j • x j := by
      funext i; apply Subtype.ext
      rw [← hc i, Submodule.coe_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Submodule.coe_smul, hxv, Matrix.of_apply, algebraMap_smul]
    have hdet : (Matrix.of fun i j => algebraMap O C (c i j)).det
        = algebraMap O C (Matrix.of c).det := by
      rw [RingHom.map_det]; rfl
    rw [hzc, iotaMulti_comb, hdet, algebraMap_smul]
    exact Submodule.mem_span_singleton.2 ⟨_, rfl⟩
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact Submodule.subset_span ⟨x, fun i => (mem_quotLattice_iff C _ _ _).2 (hvecE i), rfl⟩

end GlobalTheory.ShiftBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenDecompositionTraceMultipleStatement
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_decomposition_trace_multiple : ∀ (C : Type) [Field C] [CharZero C] (O : Type) [CommRing O] [Algebra O C] (Λ : Type) [CommRing Λ] (h h' m : ℕ) (ρ : Λ → Matrix (Fin h) (Fin h) O) (ρ' : Λ → Matrix (Fin h') (Fin h') O), Function.Injective (algebraMap O C) → iSupIndep (fun σ : Λ →+* O => eig C ρ σ) → (⨆ σ : Λ →+* O, eig C ρ σ) = ⊤ → iSupIndep (fun σ : Λ →+* O => eig C ρ' σ) → (⨆ σ : Λ →+* O, eig C ρ' σ) = ⊤ → (∀ a, (ρ a).trace = (m : O) * (ρ' a).trace) → ∀ τ : Λ →+* O, Module.finrank C (eig C ρ τ) = m * Module.finrank C (eig C ρ' τ) := by
  first | exact @GlobalTheory.finrank_eig_eq_mul_of_trace_eq_mul | exact GlobalTheory.finrank_eig_eq_mul_of_trace_eq_mul | (intros; apply GlobalTheory.finrank_eig_eq_mul_of_trace_eq_mul <;> assumption)
end

