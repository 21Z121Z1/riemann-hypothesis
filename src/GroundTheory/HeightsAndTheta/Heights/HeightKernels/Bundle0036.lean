import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0032
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0034
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0012
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0021
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0031
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0030
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0029
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.LatticeBundleObjects

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualMetricEnergy
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField Matrix
open scoped ComplexOrder

namespace DualMetricEnergyAlt

theorem log_det_re_sub {m : Type} [Fintype m] [DecidableEq m] {H A : Matrix m m ℂ} (hH : H.PosDef)
    (hA : Function.Bijective A.mulVec) :
    Real.log (Aᴴ * H * A).det.re - Real.log (Aᴴ * A).det.re = Real.log H.det.re := by
  have hd : A.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det A).mp (Matrix.mulVec_injective_iff_isUnit.mp hA.1)).ne_zero
  obtain ⟨hre, him⟩ := Complex.lt_def.mp hH.det_pos
  simp only [Complex.zero_re, Complex.zero_im] at hre him
  have hHd : H.det = (H.det.re : ℂ) := Complex.ext (by simp) (by simp [← him])
  have hn : 0 < Complex.normSq A.det := Complex.normSq_pos.mpr hd
  have e1 : (Aᴴ * H * A).det.re = Complex.normSq A.det * H.det.re := by
    rw [det_mul, det_mul, det_conjTranspose, hHd, mul_right_comm, Complex.star_def,
      ← Complex.normSq_eq_conj_mul_self, ← Complex.ofReal_mul, Complex.ofReal_re, Complex.ofReal_re]
  have e2 : (Aᴴ * A).det.re = Complex.normSq A.det := by
    rw [det_mul, det_conjTranspose, Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
  rw [e1, e2, Real.log_mul hn.ne' hre.ne']
  ring

end DualMetricEnergyAlt

theorem DualMetricEnergy.proof (hD : DualEnergyCharts.Statement) (hC : ChartEnergy.Statement)
    (hG : GrassGeomDegChart.Statement) (hM : ChartMassInvariant.Statement) :
    DualMetricEnergy.Statement := by
  intro K _ _ i F T _ _ b hb hi
  obtain ⟨A, hA, hE⟩ := hD K i F T b hb hi
  obtain ⟨B, hB, hG'⟩ := hG (i - 1)
  have e1 : 1 * 1 * (i - 1) = i - 1 := by simp
  rw [e1, hG', hM _ _ (Matrix.PosDef.conjTranspose_mul_self B hB.1),
    Finset.sum_congr rfl fun k _ => hE k, Finset.sum_comm]
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  have hterm : ∀ σ : K →+* ℂ,
      ∑ k ∈ Finset.range (n + 1), chartMixedEnergy ((A σ)ᴴ * F.metric σ * A σ) ((A σ)ᴴ * A σ) k =
        1 / 2 * Real.log (F.metric σ).det.re *
          chartMass (1 : Matrix (Fin (n + 1 - 1 + 1)) (Fin (n + 1 - 1 + 1)) ℂ) := by
    intro σ
    have h := hC (n + 1 - 1) _ _ ((F.posDef σ).conjTranspose_mul_mul_same (hA σ).1)
      (Matrix.PosDef.conjTranspose_mul_self (A σ) (hA σ).1)
    have hl := DualMetricEnergyAlt.log_det_re_sub (m := Fin (n + 1)) (F.posDef σ) (hA σ)
    rw [hl] at h
    exact h
  rw [Finset.sum_congr rfl fun σ _ => hterm σ, ← Finset.sum_mul, ← Finset.mul_sum]

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualTopLatticeChange
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField Matrix
open scoped ComplexOrder

noncomputable section

namespace TopDualLatticeChange

variable {K : Type} [Field K] [NumberField K] {i : ℕ}

def supStandard (F : HermLattice K i) : HermLattice K i where
  lattice := F.lattice ⊔ (HermLattice.standard K i).lattice
  fg := F.fg.sup (HermLattice.standard K i).fg
  span_eq := eq_top_iff.mpr (F.span_eq ▸ Submodule.span_mono
    (SetLike.coe_subset_coe.mpr le_sup_left))
  metric := fun _ => 1
  posDef := fun _ => Matrix.PosDef.one
  conj := fun _ => by simp

omit [NumberField K] in

theorem gramAt_one_single (σ : K →+* ℂ) :
    gramAt (1 : Matrix (Fin i) (Fin i) ℂ) σ (fun j : Fin i => (Pi.single j 1 : Fin i → K)) = 1 := by
  ext a c
  simp only [gramAt, embVec, Matrix.one_mulVec, dotProduct, Pi.star_apply, Pi.single_apply,
    apply_ite σ, map_one, map_zero, Matrix.one_apply]
  by_cases h : a = c
  · subst h
    simp
  · simp [h, Ne.symm h]

theorem standard_degree : (HermLattice.standard K i).degree = 0 := by
  have hinf : (HermLattice.standard K i).lattice ⊓
      (Submodule.span K (Set.range fun j : Fin i => (Pi.single j 1 : Fin i → K))).restrictScalars (𝓞 K) =
      (HermLattice.standard K i).lattice :=
    inf_eq_left.mpr (Submodule.span_le_restrictScalars (𝓞 K) K _)
  simp only [HermLattice.degree, subDegree, hinf]
  have hstd : (HermLattice.standard K i).metric = fun _ => 1 := rfl
  simp only [hstd, gramAt_one_single, Matrix.det_one, Complex.one_re, Real.log_one,
    Finset.sum_const_zero, mul_zero, sub_zero, genIndex]
  show Real.log (((HermLattice.standard K i).lattice.toAddSubgroup.relIndex
    (HermLattice.standard K i).lattice.toAddSubgroup : ℝ) /
      ((HermLattice.standard K i).lattice.toAddSubgroup.relIndex
        (HermLattice.standard K i).lattice.toAddSubgroup : ℝ)) = 0
  simp [AddSubgroup.relIndex_self]

end TopDualLatticeChange

open TopDualLatticeChange in

theorem DualTopLatticeChange.proof (hSub : DualTopSubLattice.Statement) :
    DualTopLatticeChange.Statement := by
  intro K _ _ i F T T' _ _ _ _ b hb b' hb' II hi hII
  obtain ⟨TG, hTG, hdTG, ⟨bG⟩⟩ := DualLatticeBasisExists.proof K i (supStandard F)
  have hbG := DualEmbBijective.proof K i (supStandard F) TG bG
  have h1 := hSub K i (supStandard F) F TG T bG hbG b hb II hi hII le_sup_left
  have h2 := hSub K i (supStandard F) (HermLattice.standard K i) TG T' bG hbG b' hb' II hi hII
    le_sup_right
  have hstd : (HermLattice.standard K i).withStdMetric.degree = 0 := standard_degree
  have hline : dualLine (HermLattice.standard K i).withStdMetric b' hb' =
      dualLine (HermLattice.standard K i) b' hb' := rfl
  rw [hline, hstd] at h2
  rw [h1, h2]
  ring

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.ReMulOfPos
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels

open NumberField NumberField.ComplexEmbedding Matrix GroundTheory.Heights₂.Heights
open scoped nonZeroDivisors ComplexOrder

noncomputable section

theorem gramAt_single {K : Type*} [Field K] {k : ℕ} (h : Matrix (Fin k) (Fin k) ℂ) (σ : K →+* ℂ) :
    gramAt h σ (fun j : Fin k => (Pi.single j 1 : Fin k → K)) = h := by
  have he : ∀ j : Fin k, embVec σ (Pi.single j 1 : Fin k → K) = Pi.single j 1 := fun j => by
    funext i
    by_cases hij : i = j
    · subst hij; simp [embVec]
    · simp [embVec, hij]
  ext a b
  simp [gramAt, he, mulVec_single, single_dotProduct]

theorem re_mul_of_pos {x : ℂ} (y : ℂ) (hx : 0 < x) : (x * y).re = x.re * y.re := by
  have h := (Complex.pos_iff.mp hx).2
  rw [Complex.mul_re, show x.im = 0 by linarith]
  ring

theorem S6.QuotDegree.proof : S6.QuotDegree.Statement := by
  intro K _ _ n a d ha hd m k b c hli hmk
  set B := sumBasis b c hli hmk
  have hb : (fun i => B (Sum.inl i)) = b := funext fun i => by simp [B, sumBasis_apply]
  have hc : coordProj B ∘ c = fun j : Fin k => (Pi.single j 1 : Fin k → K) := funext fun j => by
    have : c j = B (Sum.inr j) := by simp [B, sumBasis_apply]
    rw [Function.comp_apply, this, KLinesProjLattice.coordProj_basis_inr]
  refine ⟨?_, ?_⟩
  · rw [quotLattice, Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image,
      (LinesIdealLatticeFG.full K n a ha).2, Submodule.map_top, LinearMap.range_eq_top]
    exact KLinesQuotIndex.coordProj_surjective B
  · have hspan : Submodule.span K (Set.range fun j : Fin k => (Pi.single j 1 : Fin k → K)) = ⊤ := by
      have h : (Set.range fun j : Fin k => (Pi.single j 1 : Fin k → K)) =
          Set.range (Pi.basisFun K (Fin k)) := by
        congr 1; funext j; exact (Pi.basisFun_apply _ _ _).symm
      rw [h]; exact (Pi.basisFun K (Fin k)).span_eq
    have hidx := LinesQuotIndex.full K n m k B (idealLattice a) c
    rw [hb, hc] at hidx
    unfold subDegree quotDegree
    rw [hspan, Submodule.restrictScalars_top, inf_top_eq, hidx]
    congr 2
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [gramAt_single]
    set G := gramAt (diagMetric d σ) σ (Sum.elim b c)
    have hG : G.PosDef := LinesGramPosDef.full K n _ σ _ _ (diagMetric_posDef hd σ) hli
    have hA : G.toBlocks₁₁.PosDef := hG.submatrix Sum.inl_injective
    have hS : (schurMetric d b c σ).PosDef := schurMetric_posDef hd hli σ
    have hbb : gramAt (diagMetric d σ) σ b = G.toBlocks₁₁ := rfl
    have : Invertible G.toBlocks₁₁ := hA.isUnit.invertible
    have hdet : G.det = G.toBlocks₁₁.det * (schurMetric d b c σ).det := by
      conv_lhs => rw [← fromBlocks_toBlocks G]
      rw [det_fromBlocks₁₁, invOf_eq_nonsing_inv]
      rfl
    have hApos := hA.det_pos
    have hSpos := hS.det_pos
    rw [hbb, hdet, re_mul_of_pos _ hApos,
      Real.log_mul (Complex.pos_iff.mp hApos).1.ne' (Complex.pos_iff.mp hSpos).1.ne']
    ring

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.SingleMemDualLatticeStandard
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.ChartRestriction.G.AI.I1 NumberField Matrix

noncomputable section

theorem single_mem_dualLattice_standard (K : Type) [Field K] [NumberField K] {i : ℕ} (j : Fin i) :
    (Pi.single j 1 : Fin i → K) ∈ dualLattice (HermLattice.standard K i) := by
  intro x hx
  rw [single_one_dotProduct]
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨k, rfl⟩ := hy
    by_cases h : j = k
    · subst h
      exact ⟨1, by simp⟩
    · exact ⟨0, by simp [h]⟩
  | zero => exact ⟨0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha⟩ := hy
    obtain ⟨c, hc⟩ := hz
    exact ⟨a + c, by simp [ha, hc]⟩
  | smul a y _ hy =>
    obtain ⟨c, hc⟩ := hy
    exact ⟨a * c, by simp [hc, Algebra.smul_def]⟩

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T] [DecidableEq T]

def dualStdCoordMat (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) :
    ∀ _ : Unit, Fin i → T → ℤ :=
  fun _ j t => b.repr ⟨Pi.single j 1, single_mem_dualLattice_standard K j⟩ t

omit [DecidableEq T] in

theorem dualStdCoordMat_sum (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) (j : Fin i) :
    ∑ t, dualStdCoordMat b () j t • (b t : Fin i → K) = Pi.single j 1 := by
  have h := congrArg (fun v : dualLattice (HermLattice.standard K i) => (v : Fin i → K))
    (b.sum_repr ⟨Pi.single j 1, single_mem_dualLattice_standard K j⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at h
  exact h

def DualStdBasePtFree.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (T : Type) [Fintype T] [DecidableEq T]
    (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))),
    IsBasePtFree (K₂ := Unit) (ι₂ := PBlk i) (dualIdeal b) (linForm (ι₂ := PBlk i) (dualStdCoordMat b))

def DualStdImageBot.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (T : Type) [Fintype T] [DecidableEq T]
    (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))),
    imageZ (inrV (ι := dualBlocks T) (ι₂ := PBlk i))
      (graphIdeal (dualIdeal b) (linForm (ι₂ := PBlk i) (dualStdCoordMat b))) = ⊥

def DualStdGenDeg.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (T : Type) [Fintype T] [DecidableEq T]
    (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i)))
    (G : GenFibre (inrV (ι := dualBlocks T) (ι₂ := PBlk i))
      (graphIdeal (dualIdeal b) (linForm (ι₂ := PBlk i) (dualStdCoordMat b))))
    (J : IFamily G.Φ (fibreIdx (Sum.elim (dualBlocks T) (PBlk i)) (Sum.inr : Unit → Unit ⊕ Unit))),
    1 ≤ i → IsFieldIntersection J →
    J (fibreIdeal Sum.inr G) 0 Fin.elim0 = (Module.finrank ℚ K : ℤ)

def DualStdMetricPull.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (T : Type) [Fintype T] [DecidableEq T]
    (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i)))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))),
    ∀ z ∈ mcPts (dualIdeal b),
      (dualLine (HermLattice.standard K i) b hb).h z =
        (fsMulti (PBlk i)).h (linApply (ι₂ := PBlk i) (dualStdCoordMat b) z)

example : ∀ _ : Unit, Fin 1 → Unit → ℤ := dualStdCoordMat dualBasisStandard

example (hP : DualPtsOfPlane.Statement) :
    ∃ (b : Module.Basis Unit ℤ (dualLattice (HermLattice.standard ℚ 1)))
      (_ : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (z : (Σ _ : Unit, Unit) → ℂ),
      z ∈ mcPts (dualIdeal b) :=
  ⟨dualBasisStandard, dualEmbMatrix_standard_bijective, _,
    hP ℚ 1 _ Unit dualBasisStandard dualEmbMatrix_standard_bijective (Rat.castHom ℂ) (fun _ => 1)
      fun h => one_ne_zero (congrFun h 0)⟩

example : ∃ _ : Module.Basis Unit ℤ (dualLattice (HermLattice.standard ℚ 1)), 1 ≤ 1 :=
  ⟨dualBasisStandard, le_rfl⟩

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.SingleMemIdealLattice
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels

open NumberField NumberField.ComplexEmbedding Matrix GroundTheory.Heights₂.Heights TensorProduct
open scoped nonZeroDivisors

noncomputable section

variable {K : Type} [Field K] [NumberField K]

omit [NumberField K] in

theorem mem_coordLine {n : ℕ} {a : Fin n → FractionalIdeal (𝓞 K)⁰ K} {x : Fin n}
    {w : idealLattice a} : w ∈ coordLine a x ↔ ∀ y, y ≠ x → (w : Fin n → K) y = 0 := by
  simp only [coordLine, satSub, Submodule.mem_comap, Submodule.subtype_apply,
    Submodule.restrictScalars_mem, Set.range_const, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨t, ht⟩ y hy
    rw [← ht]
    simp [hy]
  · intro h
    refine ⟨(w : Fin n → K) x, funext fun y => ?_⟩
    by_cases hy : y = x
    · subst hy; simp
    · simp [hy, h y hy]

omit [NumberField K] in

theorem single_mem_idealLattice {n : ℕ} {a : Fin n → FractionalIdeal (𝓞 K)⁰ K} (v : idealLattice a)
    (x : Fin n) : (Pi.single x ((v : Fin n → K) x) : Fin n → K) ∈ idealLattice a := by
  have hv := v.2
  unfold idealLattice at hv ⊢
  rw [Submodule.mem_pi] at hv ⊢
  intro y _
  by_cases hy : y = x
  · subst hy; simpa using hv y (Set.mem_univ _)
  · simp [Pi.single_apply, hy]

theorem coordLine_isInternal {n : ℕ} (a : Fin n → FractionalIdeal (𝓞 K)⁰ K) :
    DirectSum.IsInternal (coordLine a) := by
  classical
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · rw [iSupIndep_def]
    intro x
    rw [Submodule.disjoint_def]
    intro w hw hw'
    have hle : (⨆ j, ⨆ (_ : j ≠ x), coordLine a j) ≤
        LinearMap.ker ((LinearMap.proj (R := 𝓞 K) (φ := fun _ : Fin n => K) x) ∘ₗ
          (idealLattice a).subtype) :=
      iSup₂_le fun j hj v hv => by
        simp [mem_coordLine.mp hv x (Ne.symm hj)]
    have h0 : (w : Fin n → K) x = 0 := by simpa using hle hw'
    ext y
    by_cases hy : y = x
    · subst hy; simpa using h0
    · simpa using mem_coordLine.mp hw y hy
  · refine eq_top_iff.mpr fun w _ => ?_
    have hw : w = ∑ x, (⟨_, single_mem_idealLattice w x⟩ : idealLattice a) := by
      ext y
      simp [Submodule.coe_sum, Finset.sum_apply, Pi.single_apply]
    rw [hw]
    refine Submodule.sum_mem _ fun x _ => Submodule.mem_iSup_of_mem x (mem_coordLine.mpr ?_)
    intro y hy
    simp [Pi.single_apply, hy]

theorem coordLine_orthogonal {n : ℕ} (a : Fin n → FractionalIdeal (𝓞 K)⁰ K)
    (d : (K →+* ℂ) → Fin n → ℝ) (hd : ∀ σ x, 0 < d σ x) (hc : ∀ σ x, d (conjugate σ) x = d σ x) :
    IsOrthogonalFamily (latticeBundle a d hd hc) (coordLine a) := by
  intro σ x y hxy l hl l' hl'
  refine (matrixMetric_inner_one_tmul (idealLattice a) (diagMetric d) (diagMetric_posDef hd)
    (diagMetric_conj hc) σ l l').trans ?_
  simp only [diagMetric, mulVec_diagonal, dotProduct, embVec, Pi.star_apply]
  refine Finset.sum_eq_zero fun z _ => ?_
  by_cases hz : z = x
  · subst hz
    simp [mem_coordLine.mp hl' z hxy]
  · simp [mem_coordLine.mp hl z hz]

theorem S6.LatticeAsBundle.proof (hS : S6.MatrixSubDegree.Statement)
    (hE : S6.QuotExtension.Statement) (hQ : S6.QuotDegree.Statement) :
    S6.LatticeAsBundle.Statement := by
  intro K _ _ n a d ha hd hc
  have hspan := (LinesIdealLatticeFG.full K n a ha).2
  have hline : ∀ x : Fin n, LinearIndependent K (fun _ : Fin 1 => (Pi.single x 1 : Fin n → K)) :=
    fun x => linearIndependent_unique_iff.mpr (by simp)
  refine ⟨latticeBundle a d hd hc, coordLine a, coordLine_isInternal a, fun x => ?_,
    coordLine_orthogonal a d hd hc, fun x => ?_, ?_⟩
  · exact (hS K n (idealLattice a) (diagMetric d) (diagMetric_posDef hd) (diagMetric_conj hc)
      hspan 1 _ (hline x)).1
  · have h := (hS K n (idealLattice a) (diagMetric d) (diagMetric_posDef hd) (diagMetric_conj hc)
      hspan 1 _ (hline x)).2
    unfold HermitianBundle.normDegree normalise
    exact congrArg (· / (Module.finrank ℚ K : ℝ)) h
  · intro m k b c hli hmk
    obtain ⟨X, -, -⟩ := hE K n a d hd hc ha m k b c hli hmk
    obtain ⟨hspan'', hdeg⟩ := hQ K n a d ha hd m k b c hli hmk
    have hstd : (fun j : Fin k => (Pi.single j 1 : Fin k → K)) = ⇑(Pi.basisFun K (Fin k)) :=
      funext fun j => (Pi.basisFun_apply K (Fin k) j).symm
    have htop : satSub (quotLattice a b c hli hmk) (fun j : Fin k => (Pi.single j 1 : Fin k → K)) =
        ⊤ := by
      refine eq_top_iff.mpr fun w _ => ?_
      simp only [satSub, Submodule.mem_comap, Submodule.restrictScalars_mem, hstd,
        (Pi.basisFun K (Fin k)).span_eq, Submodule.mem_top]
    obtain ⟨hr, hdg⟩ := hS K k (quotLattice a b c hli hmk) (schurMetric d b c)
      (schurMetric_posDef hd hli) (schurMetric_conj hc b c) hspan'' k _
      (hstd ▸ (Pi.basisFun K (Fin k)).linearIndependent)
    rw [htop] at hr hdg
    refine ⟨subBundle a d hd hc b, quotBundle a d hd hc b c hli hmk, ⟨X⟩, hr, ?_⟩
    unfold HermitianBundle.normDegree normalise
    exact congrArg (· / (Module.finrank ℚ K : ℝ)) (hdg.trans hdeg)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualLatticeIndex
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

noncomputable section

def DualLatticeIndex.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i), F'.lattice ≤ F.lattice →
    (dualLattice F).toAddSubgroup.relIndex (dualLattice F').toAddSubgroup =
      F'.lattice.toAddSubgroup.relIndex F.lattice.toAddSubgroup

example : HermLattice.twiceStandardExample.lattice ≤ (HermLattice.standard ℚ 1).lattice :=
  twiceStandardExample_le

end

end GroundTheory.Heights₂.Heights
end

