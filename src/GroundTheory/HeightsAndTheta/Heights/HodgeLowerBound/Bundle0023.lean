import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Assembly
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0086
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0021
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHodgeFlag
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0027
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0038

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PPlueckerArith
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.CoordinateConeArithVar

theorem PlueckerArith.proof (hNe : PlueckerNeZero.Statement) (hTr : PlueckerRatioTrdeg.Statement) :
    PlueckerArith.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D Pl
  choose cX hcX using D.arith.2.1.2.2
  choose cP hcP using hNe II Ψ K ι Ω E D Pl
  let c : ∀ k, Pl.ιY k := fun
    | Sum.inl k => cX k
    | Sum.inr q => cP q.1 q.2
  have hc : ∀ k, Pl.yY ⟨k, c k⟩ ≠ 0 := by
    rintro (k | q)
    · intro h
      have h0 : D.y ⟨k, cX k⟩ = 0 := by
        have h' : Pl.ofΩ (D.y ⟨k, cX k⟩) = 0 := h
        have h2 : (C (D.y ⟨k, cX k⟩) : MvPolynomial (Ψ × Fin D.N × Fin D.N) Ω) = 0 :=
          IsFractionRing.injective (MvPolynomial (Ψ × Fin D.N × Fin D.N) Ω) Pl.ΩY (by rw [map_zero]; exact h')
        exact C_injective _ _ (h2.trans C_0.symm)
      apply hcX k
      rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, map_zero, zero_mul]
    · exact hcP q.1 q.2
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have : CharZero Pl.ΩY :=
    charZero_of_injective_algebraMap (IsFractionRing.injective (MvPolynomial (Ψ × Fin D.N × Fin D.N) Ω) Pl.ΩY)
  have hhor : IsHorizontal Pl.PY := horizontal Pl.yY
  refine ⟨⟨Sum.inl D.arith.1.some⟩, ⟨RingHom.ker_isPrime _, isMultiHomogIdeal Pl.yY, relevant Pl.yY c hc⟩,
    hhor, ?_⟩
  have htr := ConeTrdeg.full _ Pl.ιY (ratioField Pl.yY c) (ratioPtL Pl.yY c) (birational Pl.yY c hc)
    (fun k ↦ ⟨c k, fun h0 ↦ by
      have h1 := congrArg Subtype.val h0
      simp [ratioPtL, ratioPt, hc] at h1⟩)
    (by rw [mCoordIdeal_ratioPtL Pl.yY c hc]; exact hhor)
  have hL : Algebra.trdeg ℤ (ratioField Pl.yY c) = ((D.n + D.flagDim : ℕ) : Cardinal) := by
    rw [← hTr II Ψ K ι Ω E D Pl c hc]
    have hsub : (ratioField Pl.yY c).toSubfield = Subfield.closure (coneRatios Pl.yY c) := by
      simp only [IntermediateField.adjoin_toSubfield]
      refine le_antisymm (Subfield.closure_le.2 (Set.union_subset ?_ Subfield.subset_closure))
        (Subfield.closure_mono Set.subset_union_right)
      rintro _ ⟨q, rfl⟩
      rw [eq_ratCast]
      exact SubfieldClass.ratCast_mem _ q
    rw [← (RingEquiv.subfieldCongr hsub).toIntAlgEquiv.trdeg_eq]
    exact AlgEquiv.trdeg_eq (RingEquiv.refl _).toIntAlgEquiv
  rw [mCoordIdeal_ratioPtL Pl.yY c hc, hL] at htr
  have : (mCoordIdeal Pl.yY).IsPrime := RingHom.ker_isPrime _
  have hA := IntDomainDim.full (MRing Pl.ιY ⧸ mCoordIdeal Pl.yY) (algebraMap_injective _ hhor)
  show ringKrullDim (MRing Pl.ιY ⧸ mCoordIdeal Pl.yY) = _
  rw [hA, htr]
  rw [← Nat.cast_add, Cardinal.toENat_nat,
    show D.n + 1 + D.flagDim + Fintype.card (K ⊕ Ψ × Fin (D.N - 1)) =
      D.n + D.flagDim + Fintype.card (K ⊕ Ψ × Fin (D.N - 1)) + 1 by omega]
  push_cast
  rfl

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PZhangLowerX
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open ReciprocityTheory.ChartRestriction.G.Geo HilbertSamuel.CurvePointsFinite

theorem degC_pos_of_isArithVar_one {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {W : Ideal (MRing ι)} (hW : IsArithVar W 1) : 0 < degC W := by
  have : W.IsPrime := hW.2.1.1
  have := charZero_fractionRing W hW.2.2.1
  have hEq := mCoordIdeal_genericPt W hW.2.1.2.1
  have hP : IsArithVar (mCoordIdeal (genericPt W)) 1 := by rw [hEq]; exact hW
  have hdeg := IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.degC_eq hP
  rw [hEq] at hdeg
  have := IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.isAlgebraic_blockFnField hP
  set L := ReciprocityTheory.ChartRestriction.G.AI.I4.blockFnField (genericPt W)
  set S : Set (FractionRing (MRing ι ⧸ W)) :=
    {t | ∃ p q : Σ k, ι k, p.1 = q.1 ∧ t = genericPt W p / genericPt W q}
  have hSfin : S.Finite := (Set.finite_range fun pq : (Σ k, ι k) × (Σ k, ι k) ↦
      genericPt W pq.1 / genericPt W pq.2).subset fun t ⟨p, q, _, ht⟩ ↦ ⟨(p, q), ht.symm⟩
  have : Finite S := hSfin.to_subtype
  have hint : ∀ t ∈ S, IsIntegral ℚ t := fun t ht ↦
    ((Algebra.IsAlgebraic.isAlgebraic (⟨t, IntermediateField.subset_adjoin ℚ S ht⟩ : L)).isIntegral).map
      L.val
  have : FiniteDimensional ℚ L := IntermediateField.finiteDimensional_adjoin hint
  rw [hdeg]
  exact Nat.card_pos_iff.2 ⟨⟨IsAlgClosed.lift⟩, inferInstance⟩

theorem ZhangLowerX.proof (h : SuccessiveMinimaLowerBound) : ZhangLowerX.Statement := by
  intro K _ ι _ P P0 n A e II hII hP hP0 hs hnef hc hh
  refine h K ι P P0 n A e II hII hP hP0 hs hnef hc fun W hW hPW ↦ ?_
  have hd : (0 : ℝ) < degC W := Nat.cast_pos.2 (degC_pos_of_isArithVar_one hW)
  have h1 := hh W hW hPW
  rwa [IndefiniteRowSideFullHecke.HeightsSet.height, le_div_iff₀ hd] at h1

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.ProjLineLaplace
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology InnerProductSpace Laplacian MeasureTheory

namespace LineChart

theorem isOpen_nonzero : IsOpen {z : (Σ k : Unit, PBlk 2 k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have he : {z : (Σ k : Unit, PBlk 2 k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} =
      {y : (Σ _ : Unit, Fin 2) → ℂ | ∃ i, y ⟨(), i⟩ ≠ 0} := by
    ext z
    constructor
    · intro h
      exact h ()
    · intro h k
      cases k
      exact h
  rw [he]
  exact Line.isOpen_nonzeroL

theorem contDiff_log_h {A : HermLine (PBlk 2)} (hA : IsSmoothHerm A) {g : ℂ → (Σ k : Unit, PBlk 2 k) → ℂ}
    (hg : ContDiff ℝ 2 g) (hne : ∀ w, ∃ i, g w ⟨(), i⟩ ≠ 0) : ContDiff ℝ 2 fun w => Real.log (A.h (g w)) := by
  refine contDiff_iff_contDiffAt.2 fun w => ?_
  have hmem : g w ∈ {z : (Σ k : Unit, PBlk 2 k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := fun k => by
    cases k
    exact hne w
  have hh : ContDiffAt ℝ 2 A.h (g w) :=
    (hA.contDiffAt (isOpen_nonzero.mem_nhds hmem)).of_le (WithTop.coe_le_coe.2 le_top)
  exact (hh.comp w hg.contDiffAt).log (A.pos _ hmem).ne'

theorem contDiff_cons_one : ContDiff ℂ 2 fun w : ℂ => (Fin.cons 1 (fun _ => w) : Fin (1 + 1) → ℂ) := by
  refine contDiff_pi.2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero]
    exact contDiff_const
  · simp only [Fin.cons_succ]
    exact contDiff_id

theorem contDiff_cons_last : ContDiff ℂ 2 fun t : ℂ => (Fin.cons t (fun _ => 1) : Fin (1 + 1) → ℂ) := by
  refine contDiff_pi.2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero]
    exact contDiff_id
  · simp only [Fin.cons_succ]
    exact contDiff_const

theorem contDiff_lineLift_comp (L : (Fin (1 + 1) → ℂ) ≃ₗ[ℂ] (((k : Unit) → PBlk 2 k) → ℂ))
    {c : ℂ → Fin (1 + 1) → ℂ} (hc : ContDiff ℂ 2 c) : ContDiff ℝ 2 fun w => lineLift (L (c w)) := by
  have hL : ContDiff ℂ 2 fun w => L (c w) :=
    (LinearMap.toContinuousLinearMap L.toLinearMap).contDiff.comp hc
  have h : ContDiff ℂ 2 fun w => lineLift (L (c w)) :=
    contDiff_pi.2 fun p => (contDiff_apply ℂ ℂ (fun _ => p.2)).comp hL
  exact h.restrict_scalars ℝ

theorem lineLift_ne {L : (Fin (1 + 1) → ℂ) ≃ₗ[ℂ] (((k : Unit) → PBlk 2 k) → ℂ)} {v : Fin (1 + 1) → ℂ}
    (hv : v ≠ 0) : ∃ i, lineLift (L v) ⟨(), i⟩ ≠ 0 :=
  (mem_mcPts_bot _).1 (lineLift_mem ((L.map_ne_zero_iff).mpr hv))

def chartPot (A : HermLine (PBlk 2)) (L : (Fin (1 + 1) → ℂ) ≃ₗ[ℂ] (((k : Unit) → PBlk 2 k) → ℂ)) (w : ℂ) : ℝ :=
  Real.log (A.h (lineLift (L (Fin.cons 1 fun _ => w))))

def chartPotInf (A : HermLine (PBlk 2)) (L : (Fin (1 + 1) → ℂ) ≃ₗ[ℂ] (((k : Unit) → PBlk 2 k) → ℂ))
    (t : ℂ) : ℝ :=
  Real.log (A.h (lineLift (L (Fin.cons t fun _ => 1))))

theorem contDiff_chartPot {A : HermLine (PBlk 2)} (hA : IsSmoothHerm A)
    (L : (Fin (1 + 1) → ℂ) ≃ₗ[ℂ] (((k : Unit) → PBlk 2 k) → ℂ)) : ContDiff ℝ 2 (chartPot A L) :=
  contDiff_log_h hA (contDiff_lineLift_comp L contDiff_cons_one)
    fun _ => lineLift_ne fun h => one_ne_zero (congrFun h 0)

theorem contDiff_chartPotInf {A : HermLine (PBlk 2)} (hA : IsSmoothHerm A)
    (L : (Fin (1 + 1) → ℂ) ≃ₗ[ℂ] (((k : Unit) → PBlk 2 k) → ℂ)) : ContDiff ℝ 2 (chartPotInf A L) :=
  contDiff_log_h hA (contDiff_lineLift_comp L contDiff_cons_last)
    fun _ => lineLift_ne fun h => one_ne_zero (congrFun h 1)

theorem chartPot_eq (A : HermLine (PBlk 2)) (L : (Fin (1 + 1) → ℂ) ≃ₗ[ℂ] (((k : Unit) → PBlk 2 k) → ℂ))
    {w : ℂ} (hw : w ≠ 0) : chartPot A L w = (A.a () : ℝ) * Real.log ‖w‖ + chartPotInf A L w⁻¹ := by
  have hv : (Fin.cons 1 (fun _ => w) : Fin (1 + 1) → ℂ) = w • Fin.cons w⁻¹ (fun _ => 1) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [mul_inv_cancel₀ hw]
    · simp
  have hz : lineLift (L (Fin.cons 1 (fun _ => w))) =
      fun p => (fun _ : Unit => w) p.1 * lineLift (L (Fin.cons w⁻¹ fun _ => 1)) p := by
    rw [hv, map_smul]
    rfl
  have hmem : ∀ k, ∃ i, lineLift (L (Fin.cons w⁻¹ fun _ => 1)) ⟨k, i⟩ ≠ 0 := fun k => by
    cases k
    exact lineLift_ne fun h => one_ne_zero (congrFun h 1)
  unfold chartPot chartPotInf
  rw [hz, A.smul (fun _ => w) _ (fun _ => hw)]
  simp only [Finset.univ_unique, Finset.prod_singleton]
  rw [Real.log_mul (zpow_ne_zero _ (norm_ne_zero_iff.mpr hw)) (A.pos _ hmem).ne', Real.log_zpow]

theorem maDensity_eq_laplacian {u : ℂ → ℝ} (hu : ContDiff ℝ 2 u) (y : Fin 1 → ℂ) :
    maDensity (fun _ y' => u (y' 0)) y = Δ u (y 0) / (2 * Real.pi) := by
  set E : (Fin 1 → ℂ) →L[ℝ] ℂ := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℂ) 0 with hE
  have hf : (fun y' : Fin 1 → ℂ => u (y' 0)) = u ∘ E := rfl
  have key : ∀ v : Fin 1 → ℂ, fderiv ℝ (fderiv ℝ (fun y' : Fin 1 → ℂ => u (y' 0))) y v v =
      iteratedFDeriv ℝ 2 u (y 0) ![v 0, v 0] := by
    intro v
    have h2 := iteratedFDeriv_two_apply (𝕜 := ℝ) (u ∘ E) y ![v, v]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h2
    rw [hf, ← h2, E.iteratedFDeriv_comp_right hu y le_rfl]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
    funext i
    fin_cases i <;> rfl
  rw [maDensity_one (fun y' => u (y' 0)) y, key, key, laplacian_eq_iteratedFDeriv_complexPlane]
  simp

theorem geomDeg_eq_degree (hL : LaplacianLogGrowth.Statement) {A : HermLine (PBlk 2)} (hA : IsSmoothHerm A) :
    geomDeg (⊥ : Ideal (MRing (PBlk 2))) A 1 = (A.a () : ℝ) := by
  obtain ⟨L, hEq⟩ := geomDeg_eq_integral A
  rw [hEq]
  have hφ : (fun (_ : Fin 1) (y' : Fin 1 → ℂ) => Real.log (A.h (lineLift (L (Fin.cons 1 y'))))) =
      fun _ y' => chartPot A L (y' 0) := by
    funext j y'
    unfold chartPot
    have hy : (fun _ : Fin 1 => y' 0) = y' := funext fun i => by rw [Subsingleton.elim i 0]
    rw [hy]
  have hu := contDiff_chartPot hA L
  rw [hφ]
  simp_rw [maDensity_eq_laplacian hu]
  have hfu := (volume_preserving_funUnique (Fin 1) ℂ).integral_comp'
    (fun w : ℂ => Δ (chartPot A L) w / (2 * Real.pi))
  rw [show (∫ y : Fin 1 → ℂ, Δ (chartPot A L) (y 0) / (2 * Real.pi)) = _ from hfu, integral_div]
  obtain ⟨-, hint⟩ := hL (chartPot A L) (chartPotInf A L) (A.a () : ℝ) 1 hu one_pos
    (contDiff_chartPotInf hA L).contDiffOn fun w hw => by
      have hw0 : w ≠ 0 := norm_pos_iff.mp (lt_trans (by norm_num) hw)
      exact chartPot_eq A L hw0
  rw [hint]
  have := Real.pi_pos
  field_simp

end LineChart

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPushDown
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def PushDown.Statement : Prop :=
  ∀ (II : IntersectionSystem), IsFullIntersectionSystem II →
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
    (D : ComponentData II Ψ K ι Ω E) (Pl : PlueckerData D) (H : HodgeData D) (B : AdaptedBasis H),
    (∀ (G : GenFibre Pl.xV (Pl.flagPrime B))
        (J : IFamily G.Φ (fibreIdx Pl.ιY (Sum.inl : K → K ⊕ (Ψ × Fin (D.N - 1)))))
        (L : Fin (D.n + 1) → HermLine ι) (L' : Fin (D.n + 1) → HermLine Pl.ιY)
        (N : Fin D.flagDim0 → HermLine Pl.ιY),
        IsFieldIntersection J → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm Sum.inl Pl.xV (L j) (L' j)) →
        (∀ j, IsSmoothHerm (N j)) →
        II _ Pl.ιY (Pl.flagPrime B) (D.n + 1 + D.flagDim0) (Fin.append L' N) =
          (J (fibreIdeal Sum.inl G) D.flagDim0 (fun j => fibreDeg Sum.inl (N j).a) : ℝ) *
            II K ι (mCoordIdeal D.y) (D.n + 1) L) ∧
    (∀ (d r : ℕ) (L : Fin d → HermLine ι) (L' : Fin d → HermLine Pl.ιY) (N : Fin r → HermLine Pl.ιY),
        d + r = D.n + 1 + D.flagDim0 → D.n + 1 < d → (∀ j, IsSmoothHerm (L j)) →
        (∀ j, IsPullHerm Sum.inl Pl.xV (L j) (L' j)) → (∀ j, IsSmoothHerm (N j)) →
        II _ Pl.ιY (Pl.flagPrime B) (d + r) (Fin.append L' N) = 0)

section Bot

variable {K : Type} {ι : K → Type} {K' : Type} {ι' : K' → Type}

abbrev botAlgBase (v : (Σ k, ι k) → (Σ k', ι' k')) : Algebra (MRing ι) (FractionRing (MRing ι')) :=
  ((algebraMap (MRing ι') (FractionRing (MRing ι'))).comp (rename v : MRing ι →ₐ[ℤ] MRing ι').toRingHom).toAlgebra

theorem botAlgBase_injective {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : Function.Injective v) :
    Function.Injective (@algebraMap (MRing ι) (FractionRing (MRing ι')) _ _ (botAlgBase v)) :=
  (IsFractionRing.injective (MRing ι') (FractionRing (MRing ι'))).comp (rename_injective _ hv)

abbrev botAlg (v : (Σ k, ι k) → (Σ k', ι' k')) (hv : Function.Injective v) :
    Algebra (FractionRing (MRing ι)) (FractionRing (MRing ι')) :=
  letI := botAlgBase v
  haveI : FaithfulSMul (MRing ι) (FractionRing (MRing ι')) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (botAlgBase_injective hv)
  FractionRing.liftAlgebra _ _

theorem botAlg_algebraMap {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : Function.Injective v) (f : MRing ι) :
    @algebraMap _ _ _ _ (botAlg v hv) (algebraMap (MRing ι) (FractionRing (MRing ι)) f) =
      algebraMap (MRing ι') (FractionRing (MRing ι')) (rename v f) := by
  let := botAlgBase v
  have : FaithfulSMul (MRing ι) (FractionRing (MRing ι')) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (botAlgBase_injective hv)
  exact IsFractionRing.lift_algebraMap (botAlgBase_injective hv) f

def genFibreBot (v : (Σ k, ι k) → (Σ k', ι' k')) (hv : Function.Injective v) :
    GenFibre v (⊥ : Ideal (MRing ι')) where
  Φ := FractionRing (MRing ι)
  Φ' := FractionRing (MRing ι')
  alg := botAlg v hv
  x p := algebraMap (MRing ι) (FractionRing (MRing ι)) (X p)
  x' q := algebraMap (MRing ι') (FractionRing (MRing ι')) (X q)
  ker_x := by
    rw [show imageZ v (⊥ : Ideal (MRing ι')) = ⊥ from Ideal.comap_bot_of_injective _ (rename_injective _ hv)]
    ext f
    rw [RingHom.mem_ker, Ideal.mem_bot]
    convert map_eq_zero_iff (algebraMap (MRing ι) (FractionRing (MRing ι)))
      (IsFractionRing.injective _ _) using 2
    exact Inter.aeval_algebraMap_X_eq f
  gen c := by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := MRing ι) c
    refine ⟨a, b, ?_, ?_⟩
    · convert IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
        (K := FractionRing (MRing ι)) hb using 2
      exact Inter.aeval_algebraMap_X_eq b
    · exact (congrArg₂ (· / ·) (Inter.aeval_algebraMap_X_eq a) (Inter.aeval_algebraMap_X_eq b)).symm
  genericFibre_ker_target := by
    ext f
    rw [RingHom.mem_ker, Ideal.mem_bot]
    convert map_eq_zero_iff (algebraMap (MRing ι') (FractionRing (MRing ι')))
      (IsFractionRing.injective _ _) using 2
    exact Inter.aeval_algebraMap_X_eq f
  compat p := by
    rw [botAlg_algebraMap, rename_X]

end Bot

def Line.projLineFlagGenericFibre :
    GenFibre (Line.linePl Line.zeroSystem fun _ _ => le_rfl).xV
      ((Line.linePl Line.zeroSystem fun _ _ => le_rfl).flagPrime (Line.lineAdapted Line.zeroSystem fun _ _ => le_rfl)) :=
  Inter.PFHoriz.genFibreOf
    (genFibreBot (Line.linePl Line.zeroSystem fun _ _ => le_rfl).xV
      (Line.linePl Line.zeroSystem fun _ _ => le_rfl).isBlockMap_xV.2.1) _
    (by
      have h1 := (Line.linePl Line.zeroSystem fun _ _ => le_rfl).imageZ_xV_PY
      have h2 : (Line.linePl Line.zeroSystem fun _ _ => le_rfl).PY = ⊥ := Line.PY_line _ _
      rw [h2] at h1
      rw [PlueckerData.imageZ_forget_flagPrime, h1])

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

