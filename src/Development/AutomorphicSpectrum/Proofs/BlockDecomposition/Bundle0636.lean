import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0596
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import GroundTheory.AutomorphicForms.GL2.GJMatrixLocal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0613
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0611
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenOf

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductMeasureStatement
section
noncomputable section

open MeasureTheory Measure Set
open scoped Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.CompanionTheory.ThTot

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThTot.ProdMeasPf

section Abstract

variable {X Y Z : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

theorem isAddFundamentalDomain_join (J : X × Y ≃ᵐ Z) (hJ : ∀ a b, J (a + b) = J a + J b)
    (Γ : AddSubgroup X) (Δ : AddSubgroup Y) (Λ : AddSubgroup Z)
    (hΛ : ∀ z, z ∈ Λ ↔ (J.symm z).1 ∈ Γ ∧ (J.symm z).2 ∈ Δ)
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν] (F : Set X) (G : Set Y)
    (hF : IsAddFundamentalDomain Γ F μ) (hG : IsAddFundamentalDomain Δ G ν) :
    IsAddFundamentalDomain Λ (J '' (F ×ˢ G)) ((μ.prod ν).map J) := by
  have hm : ∀ R : Set (X × Y), (μ.prod ν).map J (J '' R) = μ.prod ν R := fun R => by
    rw [J.map_apply, Set.preimage_image_eq _ J.injective]
  have htr : ∀ (l : Z) (w : X × Y), l + J w = J (J.symm l + w) := fun l w => by
    rw [hJ, J.apply_symm_apply]
  have himg : ∀ l : Λ, (l +ᵥ (J '' (F ×ˢ G)) : Set Z) =
      J '' ((((⟨(J.symm l.1).1, ((hΛ _).1 l.2).1⟩ : Γ) +ᵥ F : Set X)) ×ˢ
        (((⟨(J.symm l.1).2, ((hΛ _).1 l.2).2⟩ : Δ) +ᵥ G : Set Y))) := by
    intro l
    ext z
    constructor
    · rintro ⟨_, ⟨w, ⟨h1, h2⟩, rfl⟩, rfl⟩
      refine ⟨J.symm l.1 + w, ⟨⟨w.1, h1, rfl⟩, ⟨w.2, h2, rfl⟩⟩, ?_⟩
      exact (htr l.1 w).symm
    · rintro ⟨w, ⟨⟨a, ha, h1⟩, ⟨b, hb, h2⟩⟩, rfl⟩
      refine ⟨J (a, b), ⟨(a, b), ⟨ha, hb⟩, rfl⟩, ?_⟩
      have : J.symm l.1 + (a, b) = w := Prod.ext h1 h2
      change l.1 + J (a, b) = J w
      rw [htr, this]
  refine ⟨?_, ?_, ?_⟩
  · have hq : QuasiMeasurePreserving J.symm ((μ.prod ν).map J) (μ.prod ν) := by
      refine ⟨J.symm.measurable, ?_⟩
      rw [Measure.map_map J.symm.measurable J.measurable]
      simp only [MeasurableEquiv.symm_comp_self, Measure.map_id]
      exact Measure.AbsolutelyContinuous.rfl
    rw [J.image_eq_preimage_symm]
    exact (hF.nullMeasurableSet.prod hG.nullMeasurableSet).preimage hq
  · rw [J.measurableEmbedding.ae_map_iff]
    have h1 := (quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae hF.ae_covers
    have h2 := (quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae hG.ae_covers
    filter_upwards [h1, h2] with w hw1 hw2
    obtain ⟨g, hg⟩ := hw1
    obtain ⟨d, hd⟩ := hw2
    refine ⟨⟨J (g.1, d.1), (hΛ _).2 (by simp)⟩, (g.1 + w.1, d.1 + w.2), ⟨hg, hd⟩, ?_⟩
    change J (g.1 + w.1, d.1 + w.2) = J (g.1, d.1) + J w
    rw [← hJ]
    rfl
  · intro l l' hll
    change (μ.prod ν).map J ((l +ᵥ (J '' (F ×ˢ G)) : Set Z) ∩ (l' +ᵥ (J '' (F ×ˢ G)) : Set Z)) = 0
    rw [himg, himg, ← Set.image_inter J.injective, hm, Set.prod_inter_prod, Measure.prod_prod]
    have hne : (⟨(J.symm l.1).1, ((hΛ _).1 l.2).1⟩ : Γ) ≠ ⟨(J.symm l'.1).1, ((hΛ _).1 l'.2).1⟩ ∨
        (⟨(J.symm l.1).2, ((hΛ _).1 l.2).2⟩ : Δ) ≠ ⟨(J.symm l'.1).2, ((hΛ _).1 l'.2).2⟩ := by
      by_contra hcon
      push_neg at hcon
      apply hll
      apply Subtype.ext
      apply J.symm.injective
      exact Prod.ext (congrArg Subtype.val hcon.1) (congrArg Subtype.val hcon.2)
    rcases hne with h | h
    · have := hF.aedisjoint h
      rw [show μ _ = 0 from this, zero_mul]
    · have := hG.aedisjoint h
      rw [show ν _ = 0 from this, mul_zero]

end Abstract

variable {D : D7} {r s p : ℕ}

theorem rowT_rowJ (x : Mx D r p) (z : Mx D s p) : rowT (rowJ x z) = x := by
  funext i j; simp [rowT, rowJ]

theorem rowB_rowJ (x : Mx D r p) (z : Mx D s p) : rowB (rowJ x z) = z := by
  funext i j; simp [rowB, rowJ]

theorem rowJ_rowT_rowB (y : Mx D (r + s) p) : rowJ (rowT y) (rowB y) = y := by
  funext i j
  induction i using Fin.addCases with
  | left a => simp [rowT, rowJ]
  | right b => simp [rowB, rowJ]

theorem rowJ_add (x x' : Mx D r p) (z z' : Mx D s p) : rowJ (x + x') (z + z') = rowJ x z + rowJ x' z' := by
  funext i j
  induction i using Fin.addCases with
  | left a => simp [rowJ]
  | right b => simp [rowJ]

theorem continuous_rowT : Continuous (rowT : Mx D (r + s) p → Mx D r p) :=
  continuous_matrix fun i j => continuous_id.matrix_elem _ _

theorem continuous_rowB : Continuous (rowB : Mx D (r + s) p → Mx D s p) :=
  continuous_matrix fun i j => continuous_id.matrix_elem _ _

theorem continuous_rowJ : Continuous (fun z : Mx D r p × Mx D s p => rowJ z.1 z.2) := by
  refine continuous_matrix fun i j => ?_
  induction i using Fin.addCases with
  | left a =>
    simpa [rowJ] using (continuous_fst.matrix_elem a j)
  | right b =>
    simpa [rowJ] using (continuous_snd.matrix_elem b j)

def rowH : Mx D r p × Mx D s p ≃ₜ Mx D (r + s) p where
  toFun z := rowJ z.1 z.2
  invFun y := (rowT y, rowB y)
  left_inv z := Prod.ext (rowT_rowJ _ _) (rowB_rowJ _ _)
  right_inv := rowJ_rowT_rowB
  continuous_toFun := continuous_rowJ
  continuous_invFun := continuous_rowT.prodMk continuous_rowB

theorem mem_ratMx_iff (y : Mx D (r + s) p) :
    y ∈ ratMx D (r + s) p ↔ rowT y ∈ ratMx D r p ∧ rowB y ∈ ratMx D s p := by
  constructor
  · rintro ⟨γ, rfl⟩
    exact ⟨⟨fun i j => γ (Fin.castAdd s i) j, rfl⟩, ⟨fun i j => γ (Fin.natAdd r i) j, rfl⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    replace ha : rat a = rowT y := ha
    replace hb : rat b = rowB y := hb
    refine ⟨fun i j => Fin.addCases (motive := fun _ => D.host.E) (fun u => a u j) (fun v => b v j) i, ?_⟩
    change rat _ = y
    funext i j
    induction i using Fin.addCases with
    | left u =>
      refine Eq.trans ?_ (congrFun (congrFun ha u) j)
      change incA D (Fin.addCases (motive := fun _ => D.host.E) (fun u => a u j) (fun v => b v j) (Fin.castAdd s u)) =
        incA D (a u j)
      rw [Fin.addCases_left]
    | right v =>
      refine Eq.trans ?_ (congrFun (congrFun hb v) j)
      change incA D (Fin.addCases (motive := fun _ => D.host.E) (fun u => a u j) (fun v => b v j) (Fin.natAdd r v)) =
        incA D (b v j)
      rw [Fin.addCases_right]

theorem prodMeas : ProdMeas := by
  intro D r s p μr 𝓕r μs 𝓕s μ 𝓕 hr hs h
  obtain ⟨a1, a2, a3, a4, -⟩ := lattice_Mx D r p
  obtain ⟨b1, b2, b3, b4, -⟩ := lattice_Mx D s p
  obtain ⟨c1, c2, c3, c4, -⟩ := lattice_Mx D (r + s) p
  haveI : BorelSpace (Mx D r p) := ⟨rfl⟩
  haveI : BorelSpace (Mx D s p) := ⟨rfl⟩
  haveI : BorelSpace (Mx D (r + s) p) := ⟨rfl⟩
  haveI := hr.1
  haveI := hs.1
  let J : Mx D r p × Mx D s p ≃ᵐ Mx D (r + s) p := (rowH (D := D) (r := r) (s := s) (p := p)).toMeasurableEquiv
  have hJ : ∀ a b, J (a + b) = J a + J b := fun a b => rowJ_add a.1 b.1 a.2 b.2
  have hJf : (J : Mx D r p × Mx D s p → Mx D (r + s) p) = fun z => rowJ z.1 z.2 := rfl
  let e : Mx D r p × Mx D s p ≃+ Mx D (r + s) p :=
    { (rowH (D := D) (r := r) (s := s) (p := p)).toEquiv with map_add' := hJ }
  have hH : ((μr.prod μs).map e).IsAddHaarMeasure :=
    AddEquiv.isAddHaarMeasure_map (μr.prod μs) e continuous_rowJ (continuous_rowT.prodMk continuous_rowB)
  have hF : IsAddFundamentalDomain (ratMx D (r + s) p) (J '' (𝓕r ×ˢ 𝓕s)) ((μr.prod μs).map J) :=
    isAddFundamentalDomain_join J hJ (ratMx D r p) (ratMx D s p) (ratMx D (r + s) p)
      (fun z => mem_ratMx_iff z) μr μs 𝓕r 𝓕s hr.2.1 hs.2.1
  have h1 : (μr.prod μs).map J (J '' (𝓕r ×ˢ 𝓕s)) = 1 := by
    rw [J.map_apply, Set.preimage_image_eq _ J.injective, Measure.prod_prod, hr.2.2, hs.2.2, one_mul]
  have hcov : IsCovolOne (ratMx D (r + s) p) ((μr.prod μs).map J) (J '' (𝓕r ×ˢ 𝓕s)) := ⟨hH, hF, h1⟩
  exact covolOne_measure_eq hcov h

end GlobalTheory.CompanionTheory.ThTot.ProdMeasPf
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductThetaOfSchwartzTensor
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ThTot
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThTot.ProductTheta

variable {D : D7} {r s p : ℕ}

theorem continuous_rowT : Continuous (rowT : Mx D (r + s) p → Mx D r p) :=
  continuous_pi fun i => continuous_pi fun j =>
    (continuous_apply j).comp (continuous_apply (Fin.castAdd s i))

theorem continuous_rowB : Continuous (rowB : Mx D (r + s) p → Mx D s p) :=
  continuous_pi fun i => continuous_pi fun j =>
    (continuous_apply j).comp (continuous_apply (Fin.natAdd r i))

theorem rowT_rowJ (x : Mx D r p) (z : Mx D s p) : rowT (rowJ x z) = x := by
  funext i j
  simp [rowT, rowJ]

theorem rowB_rowJ (x : Mx D r p) (z : Mx D s p) : rowB (rowJ x z) = z := by
  funext i j
  simp [rowB, rowJ]

theorem rowJ_rowT_rowB (y : Mx D (r + s) p) : rowJ (rowT y) (rowB y) = y := by
  funext i j
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i <;> simp [rowT, rowB, rowJ]

theorem continuous_rowJ :
    Continuous fun z : Mx D r p × Mx D s p => rowJ z.1 z.2 := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · simpa [rowJ, Function.comp_def] using (continuous_apply j).comp ((continuous_apply a).comp continuous_fst)
  · simpa [rowJ, Function.comp_def] using (continuous_apply j).comp ((continuous_apply b).comp continuous_snd)

def rowHomeo : Mx D r p × Mx D s p ≃ₜ Mx D (r + s) p where
  toFun z := rowJ z.1 z.2
  invFun y := (rowT y, rowB y)
  left_inv z := by simp [rowT_rowJ, rowB_rowJ]
  right_inv y := rowJ_rowT_rowB y
  continuous_toFun := continuous_rowJ
  continuous_invFun := continuous_rowT.prodMk continuous_rowB

theorem rowT_mul (y : Mx D (r + s) p) (a : Mx D p p) :
    rowT (HMul.hMul y a : Mx D (r + s) p) = (HMul.hMul (rowT y) a : Mx D r p) := rfl

theorem rowB_mul (y : Mx D (r + s) p) (a : Mx D p p) :
    rowB (HMul.hMul y a : Mx D (r + s) p) = (HMul.hMul (rowB y) a : Mx D s p) := rfl

theorem pr_split {b : HermE D (r + s)} {br : HermE D r} {bs : HermE D s} (h : IsBlockSL2Embedding b br bs)
    (x y : Mx D (r + s) p) :
    pr b x y = pr br (rowT x) (rowT y) + pr bs (rowB x) (rowB y) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  funext i j
  simp only [pr, Matrix.mul_apply, Matrix.add_apply, Matrix.map_apply, Fin.sum_univ_add, h1, h2, h3, h4,
    map_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add]
  rfl

theorem halfTr_add (u v : AE D) : halfTr (u + v) = halfTr u + halfTr v := by
  simp only [halfTr, trA, map_add, mul_add]

theorem npow_half_mul (x : ℝ≥0) (hx : x ≠ 0) :
    npow x ((r : ℂ) / 2) * npow x ((s : ℂ) / 2) = npow x (((r + s : ℕ) : ℂ) / 2) := by
  have hx' : ((x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx
  simp only [npow]
  rw [← Complex.cpow_add _ _ hx']
  congr 1
  push_cast
  ring

theorem absA_ne_zero (u : (AE D)ˣ) : absA D u ≠ 0 := by
  intro h
  have := map_mul (absA D) u u⁻¹
  rw [mul_inv_cancel, map_one, h, zero_mul] at this
  exact one_ne_zero this

theorem prodTh_of_schwTensor : SchwTensor → ProdTh := by
  intro hT D r s p μr 𝓕r μs 𝓕s hμr hμs ψ hψ χr χs θ hθ br bs b hb Ωr Ωs hr hs
  haveI : BorelSpace (Mx D r p) := ⟨rfl⟩
  haveI : BorelSpace (Mx D s p) := ⟨rfl⟩
  haveI : BorelSpace (Mx D (r + s) p) := ⟨rfl⟩
  haveI : SecondCountableTopology (Mx D r p) := (GlobalTheory.MixModel.lattice_Mx D r p).2.2.1
  haveI : SecondCountableTopology (Mx D s p) := (GlobalTheory.MixModel.lattice_Mx D s p).2.2.1
  refine ⟨fun h => hT D θ hθ r s p _ (hr.mem h) _ (hs.mem h), ?_, ?_, ?_, ?_, ?_⟩
  · have c1 : Continuous fun u : G D p × Mx D (r + s) p => ((u.1, rowT u.2) : G D p × Mx D r p) :=
      continuous_fst.prodMk (continuous_rowT.comp continuous_snd)
    have c2 : Continuous fun u : G D p × Mx D (r + s) p => ((u.1, rowB u.2) : G D p × Mx D s p) :=
      continuous_fst.prodMk (continuous_rowB.comp continuous_snd)
    exact (hr.cont.comp c1).mul (hs.cont.comp c2)
  · intro C hC
    obtain ⟨Mr, hMr, h1⟩ := hr.maj C hC
    obtain ⟨Ms, hMs, h2⟩ := hs.maj C hC
    refine ⟨_, hT D θ hθ r s p _ hMr _ hMs, fun h hh y => ?_⟩
    rw [norm_mul, norm_mul]
    exact mul_le_mul (h1 h hh _) (h2 h hh _) (norm_nonneg _) (norm_nonneg _)
  · intro g a hg h y
    have e := npow_half_mul (r := r) (s := s) (absA D (Matrix.GeneralLinearGroup.det a)) (absA_ne_zero _)
    rw [hr.levi g a hg h, hs.levi g a hg h, rowT_mul, rowB_mul, ← e]
    simp only [MonoidHom.mul_apply, Circle.coe_mul]
    ring
  · intro g c hg h y
    rw [hr.unip g c hg h, hs.unip g c hg h, pr_split hb, mul_add, Matrix.trace_add, halfTr_add,
      AddChar.map_add_eq_mul]
    ring
  · intro g hg h x
    haveI := hμr.1
    haveI := hμs.1
    haveI : LocallyCompactSpace (Mx D r p) := (GlobalTheory.MixModel.lattice_Mx D r p).2.1
    haveI : LocallyCompactSpace (Mx D s p) := (GlobalTheory.MixModel.lattice_Mx D s p).2.1
    have hemb : MeasurableEmbedding (fun z : Mx D r p × Mx D s p => rowJ z.1 z.2) :=
      (rowHomeo (D := D) (r := r) (s := s) (p := p)).measurableEmbedding
    rw [hemb.integral_map, hr.weyl g hg h, hs.weyl g hg h, ← integral_prod_mul]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [rowT_rowJ, rowB_rowJ, pr_split hb, Matrix.trace_add, map_add, AddChar.map_add_eq_mul]
    ring

end GlobalTheory.CompanionTheory.ThTot.ProductTheta

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergArchimedeanFactor
section
open Filter Topology

namespace GlobalTheory.CompanionTheory.RankinSelberg

theorem eq_of_punctured {f g : ℂ → ℂ} {a : ℂ} (hf : ContinuousAt f a) (hg : ContinuousAt g a)
    (h : f =ᶠ[𝓝[≠] a] g) : f a = g a :=
  tendsto_nhds_unique_of_eventuallyEq (hf.tendsto.mono_left nhdsWithin_le_nhds)
    (hg.tendsto.mono_left nhdsWithin_le_nhds) h

theorem differentiable_euler_two : Differentiable ℂ (fun s : ℂ => 1 - (2 : ℂ) ^ (1 - s)) := by
  intro s
  have h : DifferentiableAt ℂ (fun s : ℂ => (2 : ℂ) ^ (1 - s)) s :=
    DifferentiableAt.const_cpow (by fun_prop) (Or.inl two_ne_zero)
  exact (differentiableAt_const _).sub h

theorem dslope_euler_two_ne_zero : dslope (fun s : ℂ => 1 - (2 : ℂ) ^ (1 - s)) 1 1 ≠ 0 := by
  have hd : HasDerivAt (fun s : ℂ => 1 - (2 : ℂ) ^ (1 - s))
      (-((2 : ℂ) ^ ((1 : ℂ) - 1) * Complex.log 2 * (-1))) 1 := by
    have h1 : HasDerivAt (fun s : ℂ => 1 - s) (-1) 1 := by
      simpa using (hasDerivAt_id (1 : ℂ)).const_sub 1
    exact (h1.const_cpow (Or.inl two_ne_zero)).const_sub 1
  have hlog : Complex.log 2 ≠ 0 := by
    have h2 : Complex.log 2 = ((Real.log 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_log (by norm_num)]; simp
    rw [h2]
    exact_mod_cast (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  rw [dslope_same, hd.deriv]
  simpa using hlog

theorem x1a : Ad3.R.HalfPlaneAnalyticIdentities := by
  intro E Λ L Z P Q hE hΛ hL hZ hid
  have hUo : IsOpen {s : ℂ | 1 / 4 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hUc : IsPreconnected {s : ℂ | 1 / 4 < s.re} :=
    (convex_halfSpace_re_gt (1 / 4)).isPreconnected
  have hsub : {s : ℂ | 1 / 4 < s.re} ⊆ {s : ℂ | 0 < s.re} := by
    intro s hs
    have h : (1 / 4 : ℝ) < s.re := hs
    show 0 < s.re
    linarith
  have hH := differentiable_euler_two
  have hf : DifferentiableOn ℂ (fun s : ℂ => (s - 1) ^ 2 * E s) {s : ℂ | 1 / 4 < s.re} :=
    (by fun_prop : Differentiable ℂ fun s : ℂ => (s - 1) ^ 2).differentiableOn.mul (hE.mono hsub)
  have hg : DifferentiableOn ℂ (fun s : ℂ => (1 - (2 : ℂ) ^ (1 - s)) * Z s * Λ s * L s)
      {s : ℂ | 1 / 4 < s.re} :=
    ((hH.differentiableOn.mul (hZ.mono hsub)).mul hΛ).mul hL.differentiableOn
  have hev : (fun s : ℂ => (s - 1) ^ 2 * E s) =ᶠ[𝓝 (2 : ℂ)]
      fun s : ℂ => (1 - (2 : ℂ) ^ (1 - s)) * Z s * Λ s * L s := by
    have hmem : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)
    filter_upwards [hmem] with s hs
    obtain ⟨h1, h2, h3⟩ := hid s hs
    rw [h1, h2, h3]
    ring
  have h2U : (2 : ℂ) ∈ {s : ℂ | 1 / 4 < s.re} := by
    show (1 / 4 : ℝ) < (2 : ℂ).re
    norm_num
  have heq := (hf.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq
    (hg.analyticOnNhd hUo) hUc h2U hev
  refine ⟨fun s hs => heq hs, ?_⟩
  intro hZ1
  have h1U : (1 : ℂ) ∈ {s : ℂ | 1 / 4 < s.re} := by
    show (1 / 4 : ℝ) < (1 : ℂ).re
    norm_num
  have hUn : {s : ℂ | 1 / 4 < s.re} ∈ 𝓝 (1 : ℂ) := hUo.mem_nhds h1U
  have hEc : ContinuousAt E 1 :=
    (hE.differentiableAt (mem_of_superset hUn hsub)).continuousAt
  have hZc : ContinuousAt Z 1 :=
    (hZ.differentiableAt (mem_of_superset hUn hsub)).continuousAt
  have hΛc : ContinuousAt Λ 1 := (hΛ.differentiableAt hUn).continuousAt
  have hLc : ContinuousAt L 1 := (hL 1).continuousAt
  have hgc : ContinuousAt (dslope (fun s : ℂ => 1 - (2 : ℂ) ^ (1 - s)) 1) 1 :=
    continuousAt_dslope_same.2 (hH 1)
  have hg1 := dslope_euler_two_ne_zero
  have hfac : ∀ s : ℂ, 1 - (2 : ℂ) ^ (1 - s) =
      (s - 1) * dslope (fun s : ℂ => 1 - (2 : ℂ) ^ (1 - s)) 1 s := by
    intro s
    have h := sub_smul_dslope (fun s : ℂ => 1 - (2 : ℂ) ^ (1 - s)) 1 s
    simp only [smul_eq_mul, sub_self, Complex.cpow_zero] at h
    rw [h]
    ring

  have hpunct : ∀ᶠ s in 𝓝[≠] (1 : ℂ), s ≠ 1 ∧ (s - 1) * E s =
      dslope (fun s : ℂ => 1 - (2 : ℂ) ^ (1 - s)) 1 s * Z s * Λ s * L s := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hUn] with s hs hsU
    refine ⟨hs, ?_⟩
    have hne : s - 1 ≠ 0 := sub_ne_zero.2 hs
    have h := heq hsU
    simp only at h
    rw [hfac s] at h
    apply mul_left_cancel₀ hne
    linear_combination h
  constructor
  · intro hL1
    have h := eq_of_punctured (f := fun s : ℂ => (s - 1) * E s)
      (g := fun s : ℂ => dslope (fun s : ℂ => 1 - (2 : ℂ) ^ (1 - s)) 1 s * Z s * Λ s * L s)
      ((by fun_prop : ContinuousAt (fun s : ℂ => s - 1) 1).mul hEc)
      (((hgc.mul hZc).mul hΛc).mul hLc) (hpunct.mono fun s hs => hs.2)
    have h' : dslope (fun s : ℂ => 1 - (2 : ℂ) ^ (1 - s)) 1 1 * Z 1 * Λ 1 * L 1 = 0 :=
      h.symm.trans (by simp)
    exact (mul_eq_zero.1 ((mul_eq_zero.1 h').resolve_right hL1)).resolve_left
      (mul_ne_zero hg1 hZ1)
  · intro hL1 hdL hE1
    have hLfac : ∀ s : ℂ, L s = (s - 1) * dslope L 1 s := by
      intro s
      have h := sub_smul_dslope L 1 s
      simp only [smul_eq_mul, hL1, sub_zero] at h
      exact h.symm
    have hlc : ContinuousAt (dslope L 1) 1 := continuousAt_dslope_same.2 (hL 1)
    have hl1 : dslope L 1 1 ≠ 0 := by rwa [dslope_same]
    have h := eq_of_punctured (f := E)
      (g := fun s : ℂ => dslope (fun s : ℂ => 1 - (2 : ℂ) ^ (1 - s)) 1 s * Z s * Λ s * dslope L 1 s)
      hEc (((hgc.mul hZc).mul hΛc).mul hlc) (hpunct.mono fun s hs => by
        have hne : s - 1 ≠ 0 := sub_ne_zero.2 hs.1
        have h2 := hs.2
        rw [hLfac s] at h2
        apply mul_left_cancel₀ hne
        linear_combination h2)
    have h' : dslope (fun s : ℂ => 1 - (2 : ℂ) ^ (1 - s)) 1 1 * Z 1 * Λ 1 * dslope L 1 1 = 0 :=
      h.symm.trans hE1
    exact (mul_eq_zero.1 ((mul_eq_zero.1 h').resolve_right hl1)).resolve_left
      (mul_ne_zero hg1 hZ1)

end GlobalTheory.CompanionTheory.RankinSelberg
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergLocalFirst
section
noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.R
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.RankinSelbergRotation

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

def rotHomeo : (Fin 2 → F) ≃ₜ (Fin 2 → F) where
  toFun r := ![r 1, -r 0]
  invFun r := ![-r 1, r 0]
  left_inv r := by
    funext i
    fin_cases i <;> simp
  right_inv r := by
    funext i
    fin_cases i <;> simp
  continuous_toFun := by
    refine continuous_pi fun i => ?_
    fin_cases i <;> simp <;> fun_prop
  continuous_invFun := by
    refine continuous_pi fun i => ?_
    fin_cases i <;> simp <;> fun_prop

variable [MeasurableSpace F] [BorelSpace F]

theorem sF_eq (ψ : AddChar F Circle) (φ : (Fin 2 → F) → ℂ) :
    sF ψ φ = fun r => GJMatrix.localFourierPi ψ φ (rotHomeo r) := by
  funext r
  have h : ∀ r' : Fin 2 → F, dt r' r = ∑ i, r' i * (rotHomeo r) i := by
    intro r'
    simp [dt, rotHomeo, Fin.sum_univ_two, sub_eq_add_neg]
  simp only [sF, GJMatrix.localFourierPi, h]
  rfl

theorem sF_mem {ψ : AddChar F Circle} (hψ : IsStd ψ) {φ : (Fin 2 → F) → ℂ} (hφ : SB φ) :
    SB (sF ψ φ) := by
  have h : GJMatrix.localFourierPi ψ φ ∈ GJMatrix.localSchwartzBruhatPi F :=
    GJMatrix.localFourierPi_mem hψ.1 hψ.2.1 hφ
  rw [sF_eq]
  exact ⟨h.1.comp_continuous rotHomeo.continuous, h.2.comp_homeomorph rotHomeo⟩

theorem whittakerGL2_smul_eq (ψ : AddChar F Circle) (μ₁ μ₂ : Fˣ →* ℂˣ) (φ : (Fin 2 → F) → ℂ) (z : ℂ) :
    W2 ψ μ₁ μ₂ (z • φ) = z • W2 ψ μ₁ μ₂ φ := by
  funext g
  simp only [W2, Pi.smul_apply, smul_eq_mul, mul_assoc z, integral_const_mul]
  have e : ∀ (a b c : ℂ), a * b * (z * c) = z * (a * b * c) := fun a b c => by ring
  simp only [e, integral_const_mul]

theorem a1 : Ad3.R.A1 := by
  intro F _ _ _ _ _ _ ψ hψ μ₁ μ₂ φ h hφ
  exact ⟨GlobalTheory.CompanionTheory.WhittakerTrans.rt_mem hφ h, sF_mem hψ hφ, whittakerGL2_smul_eq ψ μ₁ μ₂ φ,
    fun g => GlobalTheory.CompanionTheory.WhittakerTrans.whittaker_right_translation_formula ψ μ₁ μ₂ φ g h⟩

end GlobalTheory.CompanionTheory.RankinSelbergRotation

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedFormulaPolynomialGenStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_formula_polynomial_gen : PositivityTheory.PfSWUS.Loc.UnrFormula → PositivityTheory.SiegelWeilFormula.Gen.UnrPoly := by
  first | exact @GlobalTheory.CompanionTheory.SiegLoc.UnimodSeries.unrPoly | exact GlobalTheory.CompanionTheory.SiegLoc.UnimodSeries.unrPoly | (intros; apply GlobalTheory.CompanionTheory.SiegLoc.UnimodSeries.unrPoly <;> assumption)
end

