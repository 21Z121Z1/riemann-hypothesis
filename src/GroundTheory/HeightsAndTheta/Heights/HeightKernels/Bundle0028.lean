import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0024
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0023
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0027
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.AssemblyLines
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem LinesLatticeBasis.full : LinesLatticeBasis.Statement :=
  LinesLatticeBasis.proof

theorem LinesGenIndexDet.full : LinesGenIndexDet.Statement :=
  LinesGenIndexDet.proof LinesLatticeBasis.full

theorem LinesIsLattice.full : LinesIsLattice.Statement :=
  LinesIsLattice.proof

theorem LinesGenIndexTrans.full : LinesGenIndexTrans.Statement :=
  LinesGenIndexTrans.proof LinesLatticeBasis.full LinesGenIndexDet.full

theorem LinesGenIndexMono.full : LinesGenIndexMono.Statement :=
  LinesGenIndexMono.proof LinesGenIndexTrans.full

theorem LinesGenIndexPi.full : LinesGenIndexPi.Statement :=
  LinesGenIndexPi.proof

theorem LinesStdPi.full : LinesStdPi.Statement :=
  LinesStdPi.proof

theorem LinesStdIndexDet.full : LinesStdIndexDet.Statement :=
  LinesStdIndexDet.proof LinesGenIndexDet.full

theorem LinesIdealIndexPos.full : LinesIdealIndexPos.Statement :=
  LinesIdealIndexPos.proof LinesIsLattice.full LinesGenIndexTrans.full

theorem LinesProductFormula.full : LinesProductFormula.Statement :=
  LinesProductFormula.proof

theorem LinesIdealLatticeFG.full : LinesIdealLatticeFG.Statement :=
  LinesIdealLatticeFG.proof

theorem LinesIdealStdIndex.full : LinesIdealStdIndex.Statement :=
  LinesIdealStdIndex.proof LinesGenIndexPi.full LinesStdPi.full

theorem LinesGramChange.full : LinesGramChange.Statement :=
  LinesGramChange.proof

theorem LinesGramPosDef.full : LinesGramPosDef.Statement :=
  LinesGramPosDef.proof

theorem LinesGramDetChange.full : LinesGramDetChange.Statement :=
  LinesGramDetChange.proof LinesGramChange.full

theorem LinesFischer.full : LinesFischer.Statement :=
  LinesFischer.proof

theorem LinesDiagGram.full : LinesDiagGram.Statement :=
  LinesDiagGram.proof

theorem LinesGramFischerBound.full : LinesGramFischerBound.Statement :=
  LinesGramFischerBound.proof LinesGramPosDef.full LinesFischer.full LinesDiagGram.full

theorem LinesExtendBasis.full : LinesExtendBasis.Statement :=
  LinesExtendBasis.proof

theorem LinesCoordDet.full : LinesCoordDet.Statement :=
  LinesCoordDet.proof

theorem LinesCoordImage.full : LinesCoordImage.Statement :=
  LinesCoordImage.proof

theorem LinesQuotIndex.full : LinesQuotIndex.Statement :=
  LinesQuotIndex.proof

theorem LinesProjLattice.full : LinesProjLattice.Statement :=
  LinesProjLattice.proof LinesIdealLatticeFG.full

theorem LinesQuotIndexSplit.full : LinesQuotIndexSplit.Statement :=
  LinesQuotIndexSplit.proof LinesQuotIndex.full LinesCoordImage.full LinesCoordDet.full LinesIsLattice.full LinesGenIndexTrans.full LinesStdIndexDet.full LinesProjLattice.full

theorem LinesProjIndexLower.full : LinesProjIndexLower.Statement :=
  LinesProjIndexLower.proof LinesProjLattice.full LinesIdealLatticeFG.full LinesIsLattice.full LinesGenIndexMono.full LinesIdealStdIndex.full

theorem LinesLineDegree.full : LinesLineDegree.Statement :=
  LinesLineDegree.proof

theorem LinesQuotIndexLog.full : LinesQuotIndexLog.Statement :=
  LinesQuotIndexLog.proof LinesQuotIndexSplit.full LinesProjIndexLower.full LinesIdealIndexPos.full LinesProductFormula.full LinesCoordDet.full

theorem LinesQuotGramLog.full : LinesQuotGramLog.Statement :=
  LinesQuotGramLog.proof LinesGramDetChange.full LinesCoordDet.full LinesGramFischerBound.full LinesGramPosDef.full

theorem LinesQuotDegreeBound.full : LinesQuotDegreeBound.Statement :=
  LinesQuotDegreeBound.proof LinesExtendBasis.full LinesQuotIndexLog.full LinesQuotGramLog.full

theorem OrthogonalLines.full : OrthogonalLines.Statement :=
  OrthogonalLines.proof LinesQuotDegreeBound.full LinesLineDegree.full

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PProjArithVar
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial NumberField

noncomputable section

namespace ProjectiveArithmeticVariety

variable (K : Type) [Field K] [NumberField K] (n : ℕ)

abbrev xc (j : Fin (n + 1)) : ProjField K (n + 1) :=
  algebraMap (MvPolynomial (Fin (n + 1)) K) (ProjField K (n + 1)) (X j)

def aff (l : Fin n) : ProjField K (n + 1) := xc K n l.succ / xc K n 0

omit [NumberField K] in
theorem xc_ne_zero (j : Fin (n + 1)) : xc K n j ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (X_ne_zero j)

theorem coord_eq (m : Module.Free.ChooseBasisIndex ℤ (𝓞 K)) (j : Fin (n + 1)) :
    projSpaceCoord K (n + 1) ⟨(), (m, j)⟩ =
      algebraMap K (ProjField K (n + 1)) (integralBasis K m) * xc K n j := by
  simp only [projSpaceCoord, map_mul, xc]
  rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]

def dehom : MvPolynomial (Fin (n + 1)) K →+* MvPolynomial (Fin n) K :=
  (aeval (Fin.cases 1 X : Fin (n + 1) → MvPolynomial (Fin n) K)).toRingHom

theorem aff_indep : AlgebraicIndependent ℚ (aff K n) := by
  let L := Localization.Away (X 0 : MvPolynomial (Fin (n + 1)) K)
  have hu : IsUnit (dehom K n (X 0)) := by simp [dehom]
  have hv : IsUnit (xc K n 0) := (xc_ne_zero K n 0).isUnit
  let ψ : L →+* MvPolynomial (Fin n) K := IsLocalization.Away.lift (X 0) hu
  let ι : L →+* ProjField K (n + 1) := IsLocalization.Away.lift (X 0) hv
  let s : Fin n → L := fun l =>
    IsLocalization.mk' L (X l.succ) (⟨X 0, Submonoid.mem_powers _⟩ : Submonoid.powers (X 0 : MvPolynomial (Fin (n + 1)) K))
  have hψ : ψ ∘ s = X := by
    funext l
    exact (IsLocalization.lift_mk'_spec _ _ _ _).mpr (by simp [dehom])
  have hι : ι ∘ s = aff K n := by
    funext l
    refine (IsLocalization.lift_mk'_spec _ _ _ _).mpr ?_
    have := xc_ne_zero K n 0
    simp only [aff]
    field_simp
  have hs : AlgebraicIndependent ℚ s := by
    refine AlgebraicIndependent.of_comp ψ.toRatAlgHom ?_
    change AlgebraicIndependent ℚ (ψ ∘ s)
    rw [hψ]
    exact (algebraicIndependent_X (Fin n) K).restrictScalars (algebraMap ℚ K).injective
  have hL : Function.Injective (algebraMap (MvPolynomial (Fin (n + 1)) K) L) :=
    IsLocalization.injective L (powers_le_nonZeroDivisors_of_noZeroDivisors (X_ne_zero 0))
  have hinj : Function.Injective ι :=
    (IsLocalization.lift_injective_iff _).mpr fun a b =>
      hL.eq_iff.trans (IsFractionRing.injective _ (ProjField K (n + 1))).eq_iff.symm
  rw [← hι]
  exact hs.map' (f := ι.toRatAlgHom) hinj

end ProjectiveArithmeticVariety

open ProjectiveArithmeticVariety in

theorem ProjArithVar.proof (h : CoordConeArithVar.Statement) : ProjArithVar.Statement := by
  intro K _ _ i hi
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  obtain ⟨m₀⟩ := (integralBasis K).index_nonempty
  have hω : ∀ m, algebraMap K (ProjField K (n + 1)) (integralBasis K m) / algebraMap K (ProjField K (n + 1)) (integralBasis K m₀) =
      algebraMap K (ProjField K (n + 1)) (integralBasis K m / integralBasis K m₀) := fun m => (map_div₀ _ _ _).symm
  have hω₀ : algebraMap K (ProjField K (n + 1)) (integralBasis K m₀) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap K (ProjField K (n + 1))).injective).mpr ((integralBasis K).ne_zero m₀)
  have hx₀ := xc_ne_zero K n 0
  have ratio : ∀ m j, projSpaceCoord K (n + 1) ⟨(), (m, j)⟩ / projSpaceCoord K (n + 1) ⟨(), (m₀, 0)⟩ =
      algebraMap K (ProjField K (n + 1)) (integralBasis K m / integralBasis K m₀) * (xc K n j / xc K n 0) := by
    intro m j
    rw [coord_eq, coord_eq, ← hω]
    field_simp
  show IsArithVar (mCoordIdeal (projSpaceCoord K (n + 1))) (n + 1)
  refine h Unit (projBlocks K (n + 1)) (ProjField K (n + 1)) (projSpaceCoord K (n + 1)) (fun _ => (m₀, 0)) n
    (aff K n) ⟨()⟩ (fun _ => ?_) (aff_indep K n) (fun l => ?_) ?_
  · rw [coord_eq]; exact mul_ne_zero hω₀ hx₀
  · apply IntermediateField.subset_adjoin
    refine ⟨⟨(), (m₀, l.succ)⟩, ?_⟩
    simp only [ratio, div_self ((integralBasis K).ne_zero m₀), map_one, one_mul, aff]
  · rintro r ⟨⟨u, m, j⟩, rfl⟩
    cases u
    show IsAlgebraic _ (projSpaceCoord K (n + 1) ⟨(), (m, j)⟩ / projSpaceCoord K (n + 1) ⟨(), (m₀, 0)⟩)
    rw [ratio]
    refine IsAlgebraic.mul ?_ ?_
    · exact (IsAlgebraic.algebraMap (A := ProjField K (n + 1))
        (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (integralBasis K m / integralBasis K m₀))).tower_top
        (L := IntermediateField.adjoin ℚ (Set.range (aff K n)))
    · have hmem : xc K n j / xc K n 0 ∈ IntermediateField.adjoin ℚ (Set.range (aff K n)) := by
        refine Fin.cases ?_ (fun l => ?_) j
        · rw [div_self hx₀]; exact one_mem _
        · exact IntermediateField.subset_adjoin _ _ ⟨l, rfl⟩
      exact isAlgebraic_algebraMap (R := IntermediateField.adjoin ℚ (Set.range (aff K n)))
        (A := ProjField K (n + 1)) ⟨_, hmem⟩

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PTelescope
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

namespace TelescopingSum

theorem comp_swap {α : Type*} (D k : ℕ) (hk : k < D + 1) (X Y : α) (m : ℕ) (hm : m = k ∨ m = k + 1) :
    (fun j : Fin (D + 1) => if (j : ℕ) < m then X else Y) ∘ Equiv.swap ⟨k, hk⟩ (Fin.last D) =
      Fin.snoc (fun j : Fin D => if (j : ℕ) < k then X else Y) (if k < m then X else Y) := by
  funext j
  refine Fin.lastCases ?_ (fun j' => ?_) j
  · simp [Equiv.swap_apply_right]
  · simp only [Function.comp_apply, Fin.snoc_castSucc]
    by_cases h : (j' : ℕ) = k
    · have hj : Fin.castSucc j' = ⟨k, hk⟩ := Fin.ext (by simp [h])
      rw [hj, Equiv.swap_apply_left]
      have := j'.isLt
      simp only [Fin.val_last]
      rw [if_neg (by omega), if_neg (by omega)]
    · have h1 : Fin.castSucc j' ≠ ⟨k, hk⟩ := fun e => h (by simpa using congrArg Fin.val e)
      have h2 : Fin.castSucc j' ≠ Fin.last D := Fin.castSucc_ne_last j'
      rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
      simp only [Fin.val_castSucc]
      rcases hm with rfl | rfl
      · rfl
      · by_cases h3 : (j' : ℕ) < k
        · rw [if_pos h3, if_pos (by omega)]
        · rw [if_neg h3, if_neg (by omega)]

end TelescopingSum

theorem Telescope.proof : TelescopeStatement := by
  intro K _ ι _ I hI P D A u hu hP hA hus
  set W := HermLine.ofWeight u hu with hWdef
  have hW : IsSmoothHerm W := by
    have : W.h = fun z => Real.exp (-u z) := rfl
    unfold IsSmoothHerm
    rw [this]
    exact Real.contDiff_exp.comp_contDiffOn hus.neg
  have hA' : IsSmoothHerm (A.tensor W) := by
    unfold IsSmoothHerm at hA hW ⊢
    exact hA.mul hW
  obtain ⟨T, hT⟩ : ∃ T : ℕ → ℝ, ∀ m, T m =
      I P (D + 1) (fun j : Fin (D + 1) => if (j : ℕ) < m then A.tensor W else A) := ⟨_, fun _ => rfl⟩
  have hsm : ∀ (m : ℕ) (j : Fin (D + 1)), IsSmoothHerm (if (j : ℕ) < m then A.tensor W else A) :=
    fun m j => by split_ifs <;> assumption
  have hstep : ∀ k ∈ Finset.range (D + 1), T (k + 1) - T k =
      -ptsIntegral P (pot fun j : Fin D => if (j : ℕ) < k then A.tensor W else A) u := by
    intro k hk
    have hk' : k < D + 1 := Finset.mem_range.mp hk
    have hL : ∀ j : Fin D, IsSmoothHerm (if (j : ℕ) < k then A.tensor W else A) :=
      fun j => by split_ifs <;> assumption
    have e1 : T (k + 1) = I P (D + 1)
        (Fin.snoc (fun j : Fin D => if (j : ℕ) < k then A.tensor W else A) (A.tensor W)) := by
      rw [hT, ← hI.1 P (D + 1) _ (Equiv.swap ⟨k, hk'⟩ (Fin.last D)) hP (hsm (k + 1)),
        TelescopingSum.comp_swap D k hk' _ _ (k + 1) (Or.inr rfl), if_pos (Nat.lt_succ_self k)]
    have e0 : T k = I P (D + 1)
        (Fin.snoc (fun j : Fin D => if (j : ℕ) < k then A.tensor W else A) A) := by
      rw [hT, ← hI.1 P (D + 1) _ (Equiv.swap ⟨k, hk'⟩ (Fin.last D)) hP (hsm k),
        TelescopingSum.comp_swap D k hk' _ _ k (Or.inl rfl), if_neg (lt_irrefl k)]
    have hmc := metricChange K ι I hI P D (fun j : Fin D => if (j : ℕ) < k then A.tensor W else A)
      A u hu hP hL hA hus
    rw [e1, e0, hmc]
    ring
  have h0 : T 0 = I P (D + 1) (fun _ => A) := by
    rw [hT]
    simp
  have hD : T (D + 1) = I P (D + 1) (fun _ => A.tensor W) := by
    rw [hT]
    congr 1
    funext j
    rw [if_pos j.isLt]
  rw [← h0, ← hD, ← Finset.sum_range_sub, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl hstep

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.ProjProjApply
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix NumberField

noncomputable section

variable {K : Type} [Field K] [NumberField K] {i : ℕ}

def projProj : (((k : Unit) → projBlocks K i k) → ℂ) →ₗ[ℂ] (Fin i → ℂ) where
  toFun s := ∑ σ : K →+* ℂ, embComp σ (fun q => s fun _ => q)
  map_add' s s' := by
    funext j
    simp only [Finset.sum_apply, Pi.add_apply, embComp, mul_add, Finset.sum_add_distrib]
  map_smul' c s := by
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, embComp, smul_eq_mul, RingHom.id_apply,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun m _ => by ring

theorem projProj_apply (s : ((k : Unit) → projBlocks K i k) → ℂ) :
    projProj s = ∑ σ : K →+* ℂ, embComp σ (fun q => s fun _ => q) := rfl

def projPlanePt (σ : K →+* ℂ) (v : Fin i → ℂ) : (Σ _ : Unit, ProjIdx K i) → ℂ :=
  fun p => σ (integralBasis K p.2.1) * v p.2.2

def ProjPtsOnPlane.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ), ∀ z ∈ mcPts (projSpaceIdeal K i),
    ∃ σ : K →+* ℂ, ∀ τ : K →+* ℂ, τ ≠ σ → embComp τ (fun q => z ⟨(), q⟩) = 0

def ProjPtsOfPlane.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (σ : K →+* ℂ) (v : Fin i → ℂ),
    v ≠ 0 → projPlanePt σ v ∈ mcPts (projSpaceIdeal K i)

def ProjStdMassAt.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (D : ℕ) (F : HermLattice K (D + 1)),
    (∀ σ, F.metric σ = 1) →
    ptsIntegralAt (e := D) (projSpaceIdeal K (D + 1)) projProj
      (fun _ z => Real.log ((latticeLine F).h z)) (fun _ => 1) = Fintype.card (K →+* ℂ)

example : (((k : Unit) → projBlocks ℚ 1 k) → ℂ) →ₗ[ℂ] (Fin 1 → ℂ) := projProj

example : (Σ _ : Unit, ProjIdx ℚ 1) → ℂ := projPlanePt (Rat.castHom ℂ) fun _ => 1

example : ∃ (_ : ℚ →+* ℂ) (v : Fin 1 → ℂ), v ≠ 0 :=
  ⟨Rat.castHom ℂ, fun _ => 1, fun h => one_ne_zero (congrFun h 0)⟩

example : ∀ σ, (HermLattice.standard ℚ (0 + 1)).metric σ = 1 := fun _ => rfl

end

end GroundTheory.Heights₂.Heights
end

