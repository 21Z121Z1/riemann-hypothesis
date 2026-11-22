import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Counterexample.StatementsMuMetric
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0013
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitDegree
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0017
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0016
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0018
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0017
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0013

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Counterexample
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo Line

section Curve

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem inter_constLine_eq [Nonempty K] (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → Geo.HermLine ι) → ℝ)
    (hI : IsIntersectionFamily I) {W : Ideal (MRing ι)} (hW : IsArithVar W 1)
    (hH : IsMultiHomogIdeal W) (hdeg : 0 < degC W) (M : ℝ) (hM : 0 < M) :
    I W 1 ![constLine M hM] = Real.log M * degC W := by
  obtain ⟨c, hc⟩ := exists_chartMon_notMem hW
  rw [inter_eq_recR I hI hW (isSmoothHerm_constLine M hM) (d := 0) (fun k ↦ rfl)
    (isMultiHomog_chartMon c 0) (hc 0), chartMon_zero, recR_one]
  have h : logNorm (constLine (ι := ι) M hM) 1 = fun _ ↦ -Real.log M := by
    funext z
    simp [logNorm, constLine, Real.log_inv]
  have hfin : Finite (projPts W) := by
    rw [degC_eq_card_projPts] at hdeg
    exact (Nat.card_pos_iff.mp hdeg).2
  have key : ∀ φ : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ, ptsIntegral W φ (fun _ ↦ (1 : ℝ)) = degC W := by
    intro φ
    obtain rfl : φ = Fin.elim0 := funext fun j ↦ j.elim0
    rw [PtsIntegralPoints.homogProof K ι W (fun _ ↦ 1) hH hfin (fun _ _ _ _ ↦ rfl),
      degC_eq_card_projPts]
    have := Fintype.ofFinite (projPts W)
    rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      Nat.card_eq_fintype_card]
  unfold arInt
  rw [h, Inter.Conservation.ptsIntegral_const, key]
  ring

end Curve

section Point

def ptIdeal : Ideal (MRing (PBlk 2)) := orbitIdeal samplePoint

theorem isArithVar_ptIdeal : IsArithVar ptIdeal 1 :=
  OrbitCurve.full Unit (fun _ ↦ 1) samplePoint samplePoint_blockNonzero

theorem isMultiHomogIdeal_ptIdeal : IsMultiHomogIdeal ptIdeal :=
  OrbitCurve.isMultiHomogIdeal_orbitIdeal samplePoint

theorem degC_ptIdeal_pos : 0 < degC ptIdeal :=
  OrbitDegree.full Unit (fun _ ↦ 1) samplePoint samplePoint_blockNonzero

end Point

section Shift

theorem muLine_scaled_h (hMu : MuMetricLine.Statement) (II : IntersectionSystem)
    (hII : ∀ W : Ideal (MRing (PBlk 2)), IsArithVar W 1 → 0 ≤ II Unit (PBlk 2) W 1 ![fsLine 2])
    (c : ℝ) (hc : 0 < c) (z : (Σ _ : Unit, Fin 2) → ℂ) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    (muLine (lineHodgeScaled II hII c hc)).h z = Real.sqrt c := by
  obtain ⟨a, ha, hza⟩ := exists_eq_smul_orbitRep z
  have hw : ∀ k, ∃ i, orbitRep z ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := hz k
    refine ⟨i, fun h0 ↦ hi ?_⟩
    rw [hza]
    simp [torusSmul, h0]
  show refNorm 0 z * Real.exp (Real.log (muMetric (lineHodgeScaled II hII c hc) (orbitRep z) /
    refNorm 0 (orbitRep z))) = Real.sqrt c
  rw [hMu II hII c hc _ hw]
  simp only [refNorm, Pi.zero_apply, Int.cast_zero, zero_div, Real.rpow_zero, Finset.prod_const_one,
    div_one, one_mul]
  exact Real.exp_log (Real.sqrt_pos.mpr hc)

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet in

theorem heightMU_scaled (hMu : MuMetricLine.Statement) (II : IntersectionSystem)
    (hII : IsIntersectionSystem II) (R : WeightReg (PBlk 2)) (eps t' : ℝ) {W : Ideal (MRing (PBlk 2))}
    (hW : IsArithVar W 1) (hH : IsMultiHomogIdeal W) (hdeg : 0 < degC W) (c : ℝ) (hc : 0 < c) :
    heightMU (lineDataScaled II (fsHeight_nonneg II hII) c hc)
        (lineHodgeScaled II (fsHeight_nonneg II hII) c hc) R eps t' W =
      heightMU (lineDataScaled II (fsHeight_nonneg II hII) 1 one_pos)
        (lineHodgeScaled II (fsHeight_nonneg II hII) 1 one_pos) R eps t' W + Real.log (Real.sqrt c) := by
  set h1 := fsHeight_nonneg II hII
  set μc := muLine (lineHodgeScaled II h1 c hc)
  set μ1 := muLine (lineHodgeScaled II h1 1 one_pos)
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hμc : ∀ z : (Σ _ : Unit, Fin 2) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → μc.h z = Real.sqrt c :=
    muLine_scaled_h hMu II h1 c hc
  have hμ1 : ∀ z : (Σ _ : Unit, Fin 2) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → μ1.h z = 1 := fun z hz ↦ by
    rw [muLine_scaled_h hMu II h1 1 one_pos z hz, Real.sqrt_one]
  have hsm : ∀ (μ : Geo.HermLine (PBlk 2)) (v : ℝ),
      (∀ z : (Σ _ : Unit, Fin 2) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → μ.h z = v) → IsSmoothHerm μ :=
    fun μ v h ↦ contDiffOn_const.congr fun z hz ↦ h z hz
  have hshift := R.shift t' μ1 μc (Real.sqrt c) hsc rfl fun z hz ↦ by rw [hμc z hz, hμ1 z hz, mul_one]
  have hrc := R.smooth t' μc (hsm μc _ hμc)
  have hr1 := R.smooth t' μ1 (hsm μ1 _ hμ1)
  have hI := hII Unit (PBlk 2)
  have hcongr : II Unit (PBlk 2) W 1 ![R.reg t' μc] =
      II Unit (PBlk 2) W 1 ![(R.reg t' μ1).tensor (constLine (Real.sqrt c) hsc)] :=
    inter_congr (II Unit (PBlk 2)) hI hW hrc (IndefiniteRowSideFullHecke.HeightsSet.isSmoothHerm_tensor hr1 (isSmoothHerm_constLine _ _))
      (d := 0) (fun k ↦ by rw [R.deg]; rfl)
      (fun k ↦ by
        show (R.reg t' μ1).a k + (0 : Unit → ℤ) k = _
        rw [R.deg]
        rfl)
      (fun z hz ↦ by
        rw [hshift z hz.1]
        show _ = (R.reg t' μ1).h z * Real.sqrt c
        ring)
  have hA : ∀ (c' : ℝ) (hc' : 0 < c'), (lineDataScaled II h1 c' hc').A' = fsLine 2 := fun _ _ ↦ rfl
  have hd : (degC W : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hdeg.ne'
  simp only [heightMU, hA]
  rw [hcongr, inter_tensor (II Unit (PBlk 2)) hI hW hr1 (isSmoothHerm_constLine _ _),
    inter_constLine_eq (II Unit (PBlk 2)) hI hW hH hdeg]
  field_simp
  ring

end Shift

section Main

def HtInteriorNotUniversal.Statement : Prop :=
  ∀ (II : IntersectionSystem) (hII : IsIntersectionSystem II) (R : WeightReg (PBlk 2)) (Ch rd Lval : ℝ),
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ (c : ℝ) (hc : 0 < c), c ≤ c₀ →
      ¬ HtInteriorArch (lineDataScaled II (fsHeight_nonneg II hII) c hc)
        (lineHodgeScaled II (fsHeight_nonneg II hII) c hc) R Ch rd Lval

example : WeightReg (PBlk 2) := weightRegRef

theorem HtInteriorNotUniversal.proof (hMu : MuMetricLine.Statement) : HtInteriorNotUniversal.Statement := by
  intro II hII R Ch rd Lval
  set h1 := fsHeight_nonneg II hII
  set X := heightMU (lineDataScaled II h1 1 one_pos) (lineHodgeScaled II h1 1 one_pos) R 1 1 ptIdeal
  set β := -Ch * abelian₂ 16 rd Lval
  refine ⟨Real.exp (2 * (β - X - 1)), Real.exp_pos _, fun c hc hcle hN ↦ ?_⟩
  have hPX : (lineDataScaled II h1 c hc).PX ≤ ptIdeal := by
    show mCoordIdeal yLine ≤ _
    rw [mCoordIdeal_yLine]
    exact bot_le
  have h := hN 16 (by rw [lineDataScaled_f, lineDataScaled_N]; norm_num) 1 1 one_pos le_rfl one_pos le_rfl
    ptIdeal isArithVar_ptIdeal hPX (fun z _ hz ↦ Set.notMem_empty z hz)
  rw [heightMU_scaled hMu II hII R 1 1 isArithVar_ptIdeal isMultiHomogIdeal_ptIdeal degC_ptIdeal_pos c hc,
    Real.log_sqrt hc.le] at h
  have hK : (lineDataScaled II h1 c hc).KA = 0 := rfl
  rw [lineDataScaled_f, lineDataScaled_j', hK] at h
  have hlog : Real.log c ≤ 2 * (β - X - 1) := by
    rw [← Real.log_exp (2 * (β - X - 1))]
    exact Real.log_le_log hc hcle
  push_cast at h
  linarith

end Main

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagSectionNeZero
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.Nine

open MvPolynomial Filter Topology Matrix ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

namespace ComponentData

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]

def CuspBundlePos (D : ComponentData Ψ K ι) : Prop :=
  ∀ B : ℕ, 4 * D.f + 2 ≤ B → ∀ eps t' : ℝ, 0 < eps → eps ≤ 1 → 0 < t' → t' ≤ 1 →
    (D.MU B eps t').IsSemipos D.P ∧ (D.MU B eps t').IsNefFibres D.P ∧ (D.MU B eps t').IsAmpleGen D.P

def HtInterior (D : ComponentData Ψ K ι) (II : IntersectionSystem) (Ch : ℝ) : Prop :=
  ∀ B : ℕ, 4 * D.f * D.N ^ 2 ≤ B → ∀ eps t' : ℝ, 0 < eps → eps ≤ 1 → 0 < t' → t' ≤ 1 →
    ∀ W, IsAlgPt D.P W → ¬ OnBd D.Bd W →
      -Ch * D.f * D.jp * D.abelian₂ B - eps * D.Kamp ≤ (D.MU B eps t').ht II W

def HtBoundary (D : ComponentData Ψ K ι) (II : IntersectionSystem) (Ch : ℝ) : Prop :=
  ∀ B : ℕ, 4 * D.f * D.N ^ 2 ≤ B → ∀ eps t' : ℝ, 0 < eps → eps ≤ 1 → 0 < t' → t' ≤ 1 →
    ∀ W, IsAlgPt D.P W → OnBd D.Bd W →
      -Ch * D.f * D.jp * D.abelian₂ B - eps * D.Kamp ≤ (D.MU B eps t').ht II W

def CuspMean (D : ComponentData Ψ K ι) (Cu : ℝ) : Prop :=
  1 ≤ D.jp → 3 * D.jp + 1 ≤ D.N → ∀ B : ℕ, 4 * D.f * D.N ^ 2 ≤ B → D.meanU ≤ Cu * D.f * D.jp * D.abelian₂ B

end ComponentData

open ComponentData

def ZhangLowerX.Statement : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (D : ComponentData Ψ K ι) (II : IntersectionSystem) (A : RLine ι) (e : ℝ),
    IsIntersectionSystem II → A.IsSemipos D.P → A.IsNefFibres D.P → A.IsAmpleGen D.P → A.IsConjInv →
    (∀ W, IsAlgPt D.P W → e ≤ A.ht II W) →
    ((D.n + 1 : ℕ) : ℝ) * e * A.geomDeg D.P D.n ≤ A.top II D.P (D.n + 1)

def DimX.Statement : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (D : ComponentData Ψ K ι),
    ringKrullDim (MRingOver ℚ ι ⧸ Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) D.P) =
      ((D.n + Fintype.card K : ℕ) : WithBot ℕ∞)

def StokesLimit.Statement : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (D : ComponentData Ψ K ι) (II : IntersectionSystem),
    D.Clauses → IsIntersectionSystem II → D.KBound II →
    ∀ B : ℕ, 4 * D.f + 2 ≤ B → ∀ a : ℝ,
      (∀ eps t' : ℝ, 0 < eps → eps ≤ 1 → 0 < t' → t' ≤ 1 →
        ((D.n + 1 : ℕ) : ℝ) * (a - eps * D.Kamp) * (D.MU B eps t').geomDeg D.P D.n ≤
          (D.MU B eps t').top II D.P (D.n + 1)) →
      ((D.n + 1 : ℕ) : ℝ) * (a - D.meanU / 2) * D.degMu ≤ D.arLim II B

def PushDown.Statement : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (D : ComponentData Ψ K ι) (II : IntersectionSystem),
    D.Clauses → IsIntersectionSystem II → ∀ B : ℕ,
      D.PPB II B = ((cf D.n : ℚ) : ℝ) * (D.fdeg' : ℝ) * D.arLim II B ∧
      (∃ vol : ℝ, 0 < vol ∧ ((cf D.n : ℚ) : ℝ) * (D.fdeg' : ℝ) * D.degMu = vol * (D.J' : ℝ)) ∧
      0 < D.degMu

def GrassmannianHeightZTwo.Statement : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (hj : j ≤ N) (II : IntersectionSystem) (e : ℝ),
    IsIntersectionSystem II → 2 ≤ N → 1 ≤ j → j < N →
    0 < Jint (Ψ := Ψ) j hj (Fintype.card Ψ * j * (N - j)) →
    (∀ Z : Matrix (Fin (N - j)) (Fin j) ℂ, (∀ a b, ‖Z a b‖ = 1) → (1 / 2) * Real.log ((1 + Z * Zᴴ).det.re) ≤ e) →
    hFl II (FA (Ψ := Ψ) j hj (Fintype.card Ψ * j * (N - j))) ≤
      ((Fintype.card Ψ * j * (N - j) + 1 : ℕ) : ℝ) * (Jint (Ψ := Ψ) j hj (Fintype.card Ψ * j * (N - j)) : ℝ) *
        (Fintype.card Ψ : ℝ) * e

def LowerBoundComponent.Statement : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (D : ComponentData Ψ K ι) (II : IntersectionSystem) (Ch Cu : ℝ) (B : ℕ),
    D.Clauses → IsIntersectionSystem II → D.KBound II →
    ZhangLowerX.Statement → DimX.Statement → D.CuspBundlePos → D.HtInterior II Ch → D.HtBoundary II Ch →
    StokesLimit.Statement → D.CuspMean Cu → PushDown.Statement → GrassmannianHeightZTwo.Statement →
    1 ≤ D.jp → 3 * D.jp + 1 ≤ D.N → 4 * D.f * D.N ^ 2 ≤ B → 4 * D.f + 2 ≤ B →
    ∀ vol : ℝ, ((cf D.n : ℚ) : ℝ) * (D.fdeg' : ℝ) * D.degMu = vol * (D.J' : ℝ) →
      -(Ch + Cu / 2) * D.f * D.jp * D.abelian₂ B ≤ D.PPB II B / (((D.n + 1 : ℕ) : ℝ) * vol * (D.J' : ℝ))

section Example

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (GlobalTheory isArithVar_bot noRows isQuotRows_noRows)

abbrev ιE : Unit → Type := GlobalTheory 2

theorem isMultiHomog_zero' (d : Unit → ℕ) : IsMultiHomog (0 : MRing ιE) d := by
  intro m hm
  simp at hm

theorem isMultiHomog_one' : IsMultiHomog (1 : MRing ιE) 0 := by
  intro m hm k
  rw [support_one, Finset.mem_singleton] at hm
  subst hm
  simp

theorem isMultiHomog_Xpow (i : Fin 2) (e : ℕ) : IsMultiHomog ((X ⟨(), i⟩ : MRing ιE) ^ e) (fun _ => e) := by
  intro m hm k
  rw [support_X_pow, Finset.mem_singleton] at hm
  subst hm
  cases k
  rw [Fin.sum_univ_two]
  fin_cases i <;> simp

theorem X_notMem_bot (i : Fin 2) : (X ⟨(), i⟩ : MRing ιE) ∉ (⊥ : Ideal (MRing ιE)) := by
  rw [Ideal.mem_bot]
  exact X_ne_zero _

theorem cls_ne_zero {f : MRing ιE} (hf : f ≠ 0) : cls ⊥ f ≠ 0 := by
  intro h
  apply hf
  have h' := IsFractionRing.injective (MRing ιE ⧸ (⊥ : Ideal (MRing ιE))) (FnField (⊥ : Ideal (MRing ιE)))
    (h.trans (map_zero _).symm)
  rwa [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_bot] at h'

def y0E : FnField (⊥ : Ideal (MRing ιE)) := cls ⊥ (X ⟨(), 0⟩)

theorem flagSection_ne_zero : y0E ≠ 0 := cls_ne_zero (X_ne_zero _)

theorem isHomogOf_y0E : IsHomogOf ⊥ y0E (fun _ => 1) :=
  ⟨X ⟨(), 0⟩, 1, fun _ => 1, 0, by simpa using isMultiHomog_Xpow 0 1, isMultiHomog_one',
    by rw [Ideal.mem_bot]; exact one_ne_zero, by intro k; simp, by simp [y0E, cls]⟩

theorem isHomogOf_y0E_sq : IsHomogOf (⊥ : Ideal (MRing ιE)) (y0E * y0E) (fun _ => 2) := by
  have h1 : IsMultiHomog ((X ⟨(), 0⟩ : MRing ιE) ^ 2) (fun _ => 2) := isMultiHomog_Xpow 0 2
  have h3 : (1 : MRing ιE) ∉ (⊥ : Ideal (MRing ιE)) := by rw [Ideal.mem_bot]; exact one_ne_zero
  have h4 : ∀ k : Unit, (((fun _ => 2 : Unit → ℕ) k : ℕ) : ℤ) - (((0 : Unit → ℕ) k : ℕ) : ℤ) = 2 := fun _ => rfl
  have h5 : y0E * y0E * cls ⊥ (1 : MRing ιE) = cls ⊥ ((X ⟨(), 0⟩ : MRing ιE) ^ 2) := by
    simp only [y0E, cls, map_one, mul_one, pow_two, map_mul]
  exact ⟨_, _, _, _, h1, isMultiHomog_one', h3, h4, h5⟩

theorem isHomogOf_zeroE (d : Unit → ℕ) : IsHomogOf (⊥ : Ideal (MRing ιE)) 0 (fun k => (d k : ℤ)) :=
  ⟨0, 1, d, 0, isMultiHomog_zero' d, isMultiHomog_one', by rw [Ideal.mem_bot]; exact one_ne_zero,
    by intro k; simp, by simp [cls]⟩

def basisE : Module.Basis (Fin 2) (FnField (⊥ : Ideal (MRing ιE))) (Fin 2 → FnField (⊥ : Ideal (MRing ιE))) :=
  (Pi.basisFun _ (Fin 2)).unitsSMul fun _ => Units.mk0 y0E flagSection_ne_zero

theorem basisE_apply (a l : Fin 2) : basisE a l = if l = a then y0E else 0 := by
  simp [basisE, Module.Basis.unitsSMul_apply, Pi.single_apply]

def exData : ComponentData Unit Unit ιE where
  N := 2
  j := 1
  two_le_N := le_refl 2
  one_le_j := le_refl 1
  j_lt_N := by norm_num
  P := ⊥
  arith := by simpa using isArithVar_bot 1
  Bd := ∅
  bd_comp := by simp
  bdEq := fun _ => 0
  bdDeg := fun _ => 0
  bdEq_spec := by simp
  N1 := 2
  t := 0
  what₂ := fun _ => noRows 2
  rowDeg := fun _ => 0
  quot := fun _ => isQuotRows_noRows 2
  twist := fun _ _ => 1
  basis := fun _ => ⇑basisE
  ker_basis := fun _ => by
    refine ⟨basisE.linearIndependent, ?_⟩
    rw [basisE.span_eq]
    symm
    rw [LinearMap.ker_eq_top]
    exact LinearMap.ext fun _ => Subsingleton.elim _ _
  basis_homog := fun _ a l => by
    rw [basisE_apply]
    split_ifs
    · exact isHomogOf_y0E
    · simpa using isHomogOf_zeroE (fun _ => 1)
  hodge := fun _ => Matrix.of fun _ l => if l = 0 then y0E else 0
  hodge_homog := fun _ a l => by
    simp only [Matrix.of_apply]
    split_ifs
    · exact isHomogOf_y0E
    · simpa using isHomogOf_zeroE (fun _ => 1)
  hodge_indep := fun _ => by
    have : Unique (Fin (2 - 1)) := inferInstanceAs (Unique (Fin 1))
    show LinearIndependent (FnField ⊥) (fun (_ : Fin (2 - 1)) (l : Fin 2) => if l = 0 then y0E else 0)
    rw [linearIndependent_unique_iff]
    intro h
    have := congrFun h 0
    simp [flagSection_ne_zero] at this
  hodge_sub := fun _ a => Submodule.subset_span ⟨0, by
    funext l
    rw [basisE_apply]
    simp⟩
  metric := fun _ z => ((‖z ⟨(), 0⟩‖ ^ 2 + ‖z ⟨(), 1⟩‖ ^ 2 : ℝ)⁻¹ : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
  detLine := fun _ => fsLine (fun _ => 2)
  detCoord := fun _ => y0E * y0E
  detCoord_homog := fun _ => isHomogOf_y0E_sq
  kMu := ()
  k0 := 1
  one_le_k0 := le_refl 1
  muCoord := fun i => cls ⊥ (X ⟨(), i⟩) / y0E
  muCoord_homog := fun i =>
    ⟨X ⟨(), i⟩, X ⟨(), 0⟩, fun _ => 1, fun _ => 1, by simpa using isMultiHomog_Xpow i 1,
      by simpa using isMultiHomog_Xpow 0 1, X_notMem_bot 0, by intro k; simp,
      by show cls ⊥ (X ⟨(), i⟩) / y0E * y0E = _; rw [div_mul_cancel₀ _ flagSection_ne_zero]⟩
  muCoord_ratio := fun i i' => by
    show cls ⊥ (X ⟨(), i⟩) * (cls ⊥ (X ⟨(), i'⟩) / y0E) = cls ⊥ (X ⟨(), i'⟩) * (cls ⊥ (X ⟨(), i⟩) / y0E)
    ring
  muCoord_ne := ⟨0, by rw [show cls ⊥ (X ⟨(), (0 : Fin 2)⟩) = y0E from rfl, div_self flagSection_ne_zero]; exact one_ne_zero⟩
  muLine := fsLine (Pi.single () 1)
  muLine_a := rfl
  muRef := fsLine (Pi.single () 1)
  muRef_a := rfl
  ample := fsLine (fun _ => 1)
  Kamp := 0
  S := ∅
  S_prime := by simp
  latNum := fun _ _ _ => 1
  latDen := fun _ _ _ => 1
  latFl := fun _ _ _ => oneLine
  cuspNorm := fun _ _ => 1
  rd := 1
  Lchi := 0
  one_le_rd := le_refl 1
  regMu := fun _ _ => 0
  regMu_inv := fun _ _ _ _ => rfl
  regCusp := fun _ _ => 0
  regCusp_inv := fun _ _ _ _ => rfl
  regFl := fun _ _ _ _ => 0
  regFl_inv := fun _ _ _ _ _ _ => rfl

end Example

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.Nine
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.JointExample
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology Metric
open scoped ContDiff

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

namespace Line

open GroundTheory.Heights₂.Heights (CP)
open GroundTheory.Heights₂.Heights.Regular.ProjectiveLine
open GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi (phi sqSum)

def lineBW (t : ℝ) : CP 1 → ℝ :=
  cpBounded.regularised (ReciprocityTheory.AnForm.A.mollifierInhabit_thm 1).some t t cpEta

def lineMUFun (t : ℝ) (p q : ℕ) (z : (Σ _ : Unit, Fin 2) → ℂ) : ℝ :=
  Real.exp (lineBW t (projL z)) ^ q * (fsLine 2).h z ^ p

variable (II : IntersectionSystem)
  (hII : ∀ W : Ideal (MRing (PBlk 2)), IsArithVar W 1 → 0 ≤ II Unit (PBlk 2) W 1 ![fsLine 2])

omit II hII in
theorem two_le_infty : (2 : WithTop ℕ∞) ≤ ∞ := by
  exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)

omit II hII in

def chartQ (k : Fin 2) (y : (Σ _ : Unit, Fin 2) → ℂ) : Fin 1 → ℂ :=
  fun j => (2 : ℂ)⁻¹ * (y ⟨(), k.succAbove j⟩ * (y ⟨(), k⟩)⁻¹)

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.ObjectsTied
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

def GenLeadMinor0NeZero.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ψ : Type) (n j : ℕ) (τ : Ψ) (a : Fin (n - 1)), leadMinor (genMat0Fr F Ψ n j τ) a ≠ 0

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PPivotMinorFlag
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

theorem PivotMinorFlag.full : PivotMinorFlag.Statement := by
  intro R _ n M a b hab
  exact ⟨⟨Finset.univ.image (pivotCols a b), card_image_pivotCols a b hab⟩, pivotMinor_eq_flagMinor M a b hab⟩

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHodgeFlagRatioFieldEq
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

def HodgeFlagRatioFieldEq.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (Pl : PlueckerData D) (H : HodgeData D)
    (B : AdaptedBasis H) (c : ∀ k, Pl.ιY k), (∀ k, Pl.flagGenericPoint B ⟨k, c k⟩ ≠ 0) →
    IntermediateField.adjoin Ω (coneRatios (Pl.flagGenericPoint B) c) =
      IntermediateField.adjoin Ω (Set.range (flagMinorRatio0 Ω Ψ D.N D.j))

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

