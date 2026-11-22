import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittDecompositionMixedCoordsRankZero
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf

theorem mixS_rankZero {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (d : HypDec S S₀ 0)
    (μ : Measure (Mx D T.rank 0)) (𝓕 : Set (Mx D T.rank 0)) (hμ : IsCovolOne (ratMx D T.rank 0) μ 𝓕)
    (f : WO S T → ℂ) (x : Mx D T.rank 0) : d.mixS T ψ μ 𝓕 f x = fun w => f (d.ext0 T w) := by
  funext w
  have h1 : ∀ a : Mx D T.rank 0,
      heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w) f)) 0 = f (d.ext0 T w) := by
    intro a
    rw [d.integrandS_eq, Subsingleton.elim a 0, Subsingleton.elim x 0, map_zero, map_zero, symplOH_zero_left,
      AddChar.map_zero_eq_one, one_mul, zero_add, zero_add]
  simp only [HypDec.mixS, h1]
  rw [MeasureTheory.setIntegral_const]
  simp [Measure.real, hμ.2.2]

theorem mixT_rankZero {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T T₀ : HSp D) (d : HypDec T T₀ 0)
    (μ : Measure (Mx D 0 S.rank)) (𝓕 : Set (Mx D 0 S.rank)) (hμ : IsCovolOne (ratMx D 0 S.rank) μ 𝓕)
    (f : WO S T → ℂ) (y : Mx D S.rank 0) : d.mixT S ψ μ 𝓕 f y = fun w => f (d.inc0 S w) := by
  funext w
  have h1 : ∀ ξ : Mx D 0 S.rank,
      heisO ψ S T (d.incX S ξ) (heisO ψ S T (d.incAdj S y) (heisO ψ S T (d.inc0 S w) f)) 0 = f (d.inc0 S w) := by
    intro ξ
    rw [d.integrandT_eq, Subsingleton.elim ξ 0, Subsingleton.elim y 0, map_zero, map_zero, symplOH_zero_left,
      AddChar.map_zero_eq_one, one_mul, zero_add, zero_add]
  simp only [HypDec.mixT, h1]
  rw [MeasureTheory.setIntegral_const]
  simp [Measure.real, hμ.2.2]

theorem rankZero_trivial {D : D7} (S S₀ : HSp D) (d : HypDec S S₀ 0) :
    (∀ a, d.levi a = 1) ∧ (∀ b, d.nB b = 1) ∧ ∀ c, d.nC c = 1 := by
  refine ⟨fun a => ?_, fun b => ?_, fun c => ?_⟩
  · rw [Subsingleton.elim a 1, map_one]
  · rw [Subsingleton.elim b 0, d.nB_zero]
  · rw [Subsingleton.elim c 0, d.nC_zero]

theorem mixRankZero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), (∀ (S S₀ T : HSp D) (d : HypDec S S₀ 0) (μ : Measure (Mx D T.rank 0)) (𝓕 : Set (Mx D T.rank 0)), IsCovolOne (ratMx D T.rank 0) μ 𝓕 → ∀ f x, d.mixS T ψ μ 𝓕 f x = fun w => f (d.ext0 T w)) ∧ (∀ (S T T₀ : HSp D) (d : HypDec T T₀ 0) (μ : Measure (Mx D 0 S.rank)) (𝓕 : Set (Mx D 0 S.rank)), IsCovolOne (ratMx D 0 S.rank) μ 𝓕 → ∀ f y, d.mixT S ψ μ 𝓕 f y = fun w => f (d.inc0 S w)) ∧ ∀ (S S₀ : HSp D) (d : HypDec S S₀ 0), (∀ a, d.levi a = 1) ∧ (∀ b, d.nB b = 1) ∧ ∀ c, d.nC c = 1 := by
  intro D ψ
  exact ⟨fun S S₀ T d μ 𝓕 hμ f x => mixS_rankZero ψ S S₀ T d μ 𝓕 hμ f x,
    fun S T T₀ d μ 𝓕 hμ f y => mixT_rankZero ψ S T T₀ d μ 𝓕 hμ f y,
    fun S S₀ d => rankZero_trivial S S₀ d⟩

end GlobalTheory.Unf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittMixedCoordsConjHermitianAdjoint
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.MixSwap

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger (dagger dagger_dagger cj)

variable {D : D7}

theorem dagger_add (S T : HSp D) (x y : WO S T) : dagger S T (x + y) = dagger S T x + dagger S T y := by
  simp only [dagger, adj_add, Matrix.add_mul, Matrix.mul_add]

theorem hO_dagger (S T : HSp D) (x y : WO S T) : hO T S (dagger S T x) (dagger S T y) = hO S T y x := by
  simp only [hO_eq_trace, dagger, adj_mul, adj_adj, adj_gA, adj_giA, Matrix.mul_assoc, giA_gA_cancel]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem symplOH_dagger (S T : HSp D) (x y : WO S T) :
    symplOH T S (dagger S T x) (dagger S T y) = -symplOH S T x y := by
  rw [symplOH_eq, hO_dagger, ← symplOH_eq, symplOH_skew]

theorem conj_psi_of_std {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (a : AF D.host.F) :
    starRingEnd ℂ (ψ a) = ψ (-a) := by
  have h1 : ‖ψ a‖ = 1 := hψ.1.2.1 a
  have h2 : ψ a * ψ (-a) = 1 := by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have h3 : ψ a * starRingEnd ℂ (ψ a) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]; simp
  have hne : ψ a ≠ 0 := by intro h; rw [h, norm_zero] at h1; exact zero_ne_one h1
  exact mul_left_cancel₀ hne (h3.trans h2.symm)

theorem adelicConj_incl_neg_inv_hermitianScalar : cA D (incA D (-D.host.xi0⁻¹)) = incA D D.host.xi0⁻¹ := by
  rw [GlobalTheory.DualPairCheck.cA_incA, star_neg, star_inv₀, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, inv_neg, neg_neg]

section Target

variable {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D)

theorem dagger_incAdj (y : Mx D S.rank ρ) :
    dagger S T (d.incAdj S y) = d.extX S (incA D D.host.xi0⁻¹ • y) := by
  rw [dagger, HypDec.incAdj_apply, HypDec.incY_apply, HypDec.extX_apply, d.pX_eq, adj_mul, adj_smul, adj_mul, adj_adj,
    adj_gA, adelicConj_incl_neg_inv_hermitianScalar]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc, giA_gA_cancel]

theorem dagger_incX (ξ : Mx D ρ S.rank) : dagger S T (d.incX S ξ) = d.extY S (giA S ⬝ adj ξ) := by
  simp only [dagger, HypDec.incX_apply, HypDec.extY_apply, d.pY_eq, adj_mul, Matrix.mul_assoc]

theorem hermitianAdjointHomSpace_wittCoreInclusion (w : WO S T₀) : dagger S T (d.inc0 S w) = d.ext0 S (dagger S T₀ w) := by
  simp only [dagger, HypDec.wittDecomp_inclAnisotropicHom_apply, HypDec.matrixExtendByZero_apply, d.p0_eq, adj_mul, Matrix.mul_assoc, gA_giA_cancel]

end Target

end GlobalTheory.MixSwap

end

noncomputable section

namespace GlobalTheory.MixSwap

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger (dagger dagger_dagger cj)
open scoped Pointwise

variable {D : D7}

theorem borelMx (m n : ℕ) : BorelSpace (Mx D m n) := ⟨rfl⟩

attribute [local instance] borelMx

def adjE (S : HSp D) (ρ : ℕ) : Mx D ρ S.rank ≃+ Mx D S.rank ρ where
  toFun ξ := giA S ⬝ adj ξ
  invFun a := adj (gA S ⬝ a)
  left_inv ξ := by simp only [gA_giA_cancel, adj_adj]
  right_inv a := by simp only [adj_adj, giA_gA_cancel]
  map_add' ξ ξ' := by simp only [adj_add, Matrix.mul_add]

theorem adjE_apply (S : HSp D) (ρ : ℕ) (ξ : Mx D ρ S.rank) : adjE S ρ ξ = giA S ⬝ adj ξ := rfl

theorem adjE_symm_apply (S : HSp D) (ρ : ℕ) (a : Mx D S.rank ρ) : (adjE S ρ).symm a = adj (gA S ⬝ a) := rfl

theorem continuous_adjE (S : HSp D) (ρ : ℕ) : Continuous (adjE S ρ) :=
  continuous_const.matrix_mul continuous_adj

theorem continuous_adjE_symm (S : HSp D) (ρ : ℕ) : Continuous (adjE S ρ).symm :=
  continuous_adj.comp (continuous_const.matrix_mul continuous_id)

def adjM (S : HSp D) (ρ : ℕ) : Mx D ρ S.rank ≃ᵐ Mx D S.rank ρ :=
  (Homeomorph.mk (adjE S ρ).toEquiv (continuous_adjE S ρ) (continuous_adjE_symm S ρ)).toMeasurableEquiv

theorem coe_adjM (S : HSp D) (ρ : ℕ) : ⇑(adjM S ρ) = ⇑(adjE S ρ) := rfl

theorem coe_adjM_symm (S : HSp D) (ρ : ℕ) : ⇑(adjM S ρ).symm = ⇑(adjE S ρ).symm := rfl

theorem adjE_mem {S : HSp D} {ρ : ℕ} {ξ : Mx D ρ S.rank} (h : ξ ∈ ratMx D ρ S.rank) : adjE S ρ ξ ∈ ratMx D S.rank ρ :=
  ratMx_mul (rat_mem _) (ratMx_adj h)

theorem adjE_symm_mem {S : HSp D} {ρ : ℕ} {a : Mx D S.rank ρ} (h : a ∈ ratMx D S.rank ρ) :
    (adjE S ρ).symm a ∈ ratMx D ρ S.rank :=
  ratMx_adj (ratMx_mul (rat_mem _) h)

theorem isCovolOne_map {S : HSp D} {ρ : ℕ} {μ : Measure (Mx D ρ S.rank)} {𝓕 : Set (Mx D ρ S.rank)}
    (hμ : IsCovolOne (ratMx D ρ S.rank) μ 𝓕) :
    IsCovolOne (ratMx D S.rank ρ) (μ.map (adjM S ρ)) (adjM S ρ '' 𝓕) := by
  obtain ⟨hH, hF, h1⟩ := hμ
  have P : MeasurePreserving (adjM S ρ) μ (μ.map (adjM S ρ)) := (adjM S ρ).measurable.measurePreserving μ
  have Q : MeasurePreserving (adjM S ρ).symm (μ.map (adjM S ρ)) μ := P.symm (adjM S ρ)
  refine ⟨?_, ?_, ?_⟩
  · rw [coe_adjM]
    exact (adjE S ρ).isAddHaarMeasure_map μ (continuous_adjE S ρ) (continuous_adjE_symm S ρ)
  · rw [MeasurableEquiv.image_eq_preimage_symm]
    refine ⟨hF.nullMeasurableSet.preimage Q.quasiMeasurePreserving, ?_, ?_⟩
    · filter_upwards [Q.quasiMeasurePreserving.ae hF.ae_covers] with a ha
      obtain ⟨g, hg⟩ := ha
      refine ⟨⟨adjE S ρ g, adjE_mem g.2⟩, ?_⟩
      rw [Set.mem_preimage, AddSubgroup.vadd_def, vadd_eq_add, coe_adjM_symm, map_add,
        AddEquiv.symm_apply_apply]
      rw [AddSubgroup.vadd_def, vadd_eq_add, coe_adjM_symm] at hg
      exact hg
    · have key : ∀ g : ratMx D S.rank ρ, g +ᵥ ((adjM S ρ).symm ⁻¹' 𝓕) =
          (adjM S ρ).symm ⁻¹' ((⟨(adjE S ρ).symm g, adjE_symm_mem g.2⟩ : ratMx D ρ S.rank) +ᵥ 𝓕) := by
        intro g
        ext x
        simp only [Set.mem_preimage, Set.mem_vadd_set_iff_neg_vadd_mem, AddSubgroup.vadd_def, vadd_eq_add,
          coe_adjM_symm, map_add, map_neg]
      intro g g' hne
      have hne' : (⟨(adjE S ρ).symm g, adjE_symm_mem g.2⟩ : ratMx D ρ S.rank) ≠ ⟨(adjE S ρ).symm g', adjE_symm_mem g'.2⟩ := by
        intro h
        apply hne
        exact Subtype.ext ((adjE S ρ).symm.injective (congrArg Subtype.val h))
      show AEDisjoint _ (g +ᵥ _) (g' +ᵥ _)
      rw [key g, key g']
      exact (hF.aedisjoint hne').preimage Q.quasiMeasurePreserving
  · rw [MeasurableEquiv.map_apply, MeasurableEquiv.preimage_image, h1]

end GlobalTheory.MixSwap

end

noncomputable section

namespace GlobalTheory.MixSwap

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger (dagger dagger_dagger cj)

attribute [local instance] borelMx

theorem mixS_cj_dagger : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T T₀ : HSp D) (ρ : ℕ) (d : HypDec T T₀ ρ) (μ : Measure (Mx D ρ S.rank)) (𝓕 : Set (Mx D ρ S.rank)), IsCovolOne (ratMx D ρ S.rank) μ 𝓕 → ∃ (μ' : Measure (Mx D S.rank ρ)) (𝓕' : Set (Mx D S.rank ρ)), IsCovolOne (ratMx D S.rank ρ) μ' 𝓕' ∧ (∀ y, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S T (d.incAdj S y) = d.extX S (incA D D.host.xi0⁻¹ • y)) ∧ (∀ ξ, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S T (d.incX S ξ) = d.extY S (giA S ⬝ adj ξ)) ∧ (∀ w, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S T (d.inc0 S w) = d.ext0 S (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S T₀ w)) ∧ ∀ (f : WO S T → ℂ) y, d.mixS S ψ μ' 𝓕' (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger T S) f) (incA D D.host.xi0⁻¹ • y) = GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger T₀ S) (d.mixT S ψ μ 𝓕 f y) := by
  intro D ψ hψ S T T₀ ρ d μ 𝓕 hμ
  refine ⟨μ.map (adjM S ρ), adjM S ρ '' 𝓕, isCovolOne_map hμ, dagger_incAdj d S, dagger_incX d S, hermitianAdjointHomSpace_wittCoreInclusion d S, ?_⟩
  intro f y
  funext w
  have P : MeasurePreserving (adjM S ρ) μ (μ.map (adjM S ρ)) := (adjM S ρ).measurable.measurePreserving μ
  have hint : ∀ G : Mx D S.rank ρ → ℂ,
      ∫ a in adjM S ρ '' 𝓕, G a ∂(μ.map (adjM S ρ)) = ∫ ξ in 𝓕, G (adjM S ρ ξ) ∂μ :=
    fun G => P.setIntegral_image_emb (adjM S ρ).measurableEmbedding G 𝓕
  simp only [HypDec.mixS, HypDec.mixT, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]
  rw [hint, ← integral_conj]
  congr 1
  funext ξ
  rw [HypDec.integrandS_eq, HypDec.integrandT_eq]
  have e1 : d.extY S (adjM S ρ ξ) = dagger S T (d.incX S ξ) := (dagger_incX d S ξ).symm
  have e2 : d.extX S (incA D D.host.xi0⁻¹ • y) = dagger S T (d.incAdj S y) := (dagger_incAdj d S y).symm
  have e3 : d.ext0 S w = dagger S T (d.inc0 S (dagger T₀ S w)) := by rw [hermitianAdjointHomSpace_wittCoreInclusion, dagger_dagger]
  rw [e1, e2, e3, symplOH_dagger, ← dagger_add, ← dagger_add]
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, dagger_dagger, map_mul, conj_psi_of_std hψ]

end GlobalTheory.MixSwap

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittSourceMixedCoordHeisenbergRestriction
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Bridge

open GlobalTheory.MixModel

variable {D : D7}

theorem isIsoSplit_hyp {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (hρ : 0 < ρ) :
    GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit S S₀ d.e d.i₀ := by
  have hq : d.qX * d.e = 1 := d.e'e
  refine ⟨⟨hρ, ?_, ?_⟩, ?_, ?_, d.rank_add.symm⟩
  · exact Matrix.mulVec_injective_iff.1 fun x y h => by
      have := congrArg (d.qX *ᵥ ·) h
      simpa only [Matrix.mulVec_mulVec, hq, Matrix.one_mulVec] using this
  · rw [cT_sig]; exact d.ee
  · simp only [GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj, cT_sig]; exact d.iso
  · simp only [GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj, cT_sig]
    apply rat_injective
    rw [rat_mul, rat_mul, rat_conjTranspose, rat_zero, Matrix.mul_assoc]
    exact d.wittDecomp_gram_X_anisotropic

set_option maxHeartbeats 1000000 in
theorem mem_NI_hyp {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (g : GA D S) (h1 : mt S g ⬝ d.jX = d.jX)
    (h2 : d.pY ⬝ mt S g = d.pY) (B : Mx D ρ S₀.rank) (h3 : mt S g ⬝ d.j0 = d.j0 + d.jX ⬝ B) : g ∈ NI S d.e := by
  apply Subgroup.subset_closure
  have hm1 : (mt S g - 1) ⬝ d.jX = 0 := by rw [Matrix.sub_mul, h1, Matrix.one_mul, sub_self]
  have hm0 : (mt S g - 1) ⬝ d.j0 = d.jX ⬝ B := by rw [Matrix.sub_mul, h3, Matrix.one_mul, add_sub_cancel_left]
  refine ⟨hm1, ?_, ?_⟩
  · rw [cT_sig]
    change d.pY ⬝ (mt S g - 1) = 0
    rw [Matrix.mul_sub, h2, Matrix.mul_one, sub_self]
  · intro x hx
    rw [cT_sig] at hx
    refine ⟨B *ᵥ (d.p0 *ᵥ fun i => incA D (x i)), ?_⟩
    have hv : d.pY *ᵥ (fun i => incA D (x i)) = 0 := by
      funext i
      have := RingHom.map_mulVec (incA D) d.qY x i
      change incA D (((d.eᴴ * HSpace.gram S) *ᵥ x) i) = _ at this
      rw [hx, Pi.zero_apply, map_zero] at this
      exact this.symm
    have hsum : (fun i => incA D (x i)) = d.jX *ᵥ (d.pX *ᵥ fun i => incA D (x i)) +
        d.j0 *ᵥ (d.p0 *ᵥ fun i => incA D (x i)) := by
      have h := congrArg (· *ᵥ fun i => incA D (x i)) d.sum_eq_one
      simp only [Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero, add_zero] at h
      exact h.symm
    have hX : ∀ a, mt S g *ᵥ (d.jX *ᵥ a) = d.jX *ᵥ a := fun a => by rw [Matrix.mulVec_mulVec, h1]
    have h0 : ∀ a, mt S g *ᵥ (d.j0 *ᵥ a) = d.j0 *ᵥ a + d.jX *ᵥ (B *ᵥ a) := fun a => by
      rw [Matrix.mulVec_mulVec, h3, Matrix.add_mulVec, Matrix.mulVec_mulVec]
    have final : (mt S g - 1) *ᵥ (fun i => incA D (x i)) = d.jX *ᵥ (B *ᵥ (d.p0 *ᵥ fun i => incA D (x i))) := by
      have hs := Matrix.sub_mulVec (mt S g) (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) (fun i => incA D (x i))
      rw [Matrix.one_mulVec] at hs
      rw [hs]
      conv_lhs => rw [hsum]
      rw [Matrix.mulVec_add, hX, h0]
      abel
    exact final

end GlobalTheory.Bridge

namespace GlobalTheory.Bridge
open GlobalTheory.MixModel
variable {D : D7}

theorem orthProjPartHomToHermitian_eq_wittDecompositionCore {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D) (w : WO S₀ T) :
    GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart S S₀ T d.i₀ w = d.ext0 T w := by
  rw [HypDec.matrixExtendByZero_apply]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj, cT_sig, Matrix.mul_assoc]
  rfl

theorem integrand_eq {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (ψ : AddChar (AF D.host.F) ℂ) (f : WO S T → ℂ)
    (x a : Mx D T.rank ρ) (w : WO S₀ T) :
    heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w) f)) 0 =
      heisO ψ S T (d.extX T x) f (d.extY T a + d.ext0 T w) := by
  rw [d.integrandS_eq]
  simp only [heisO]
  rw [GlobalTheory.OrientedHeis.symplOH_add_left, symplOH_skew S T (d.extX T x) (d.ext0 T w), d.wittDecomp_sympl_extIsotropic_extAnisotropic T x w,
    neg_zero, add_zero, add_right_comm]

theorem mixS_eq_res {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (ψ : AddChar (AF D.host.F) ℂ)
    (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) :
    d.mixS T ψ μ 𝓕 f x = GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res S S₀ T d.e d.i₀ μ 𝓕 (heisO ψ S T (d.extX T x) f) := by
  funext w
  simp only [HypDec.mixS, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res, orthProjPartHomToHermitian_eq_wittDecompositionCore]
  congr 1
  funext a
  exact integrand_eq d ψ f x a w

theorem mixS_heis {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (ψ : AddChar (AF D.host.F) ℂ)
    (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) :
    d.mixS T ψ μ 𝓕 f x = d.mixS T ψ μ 𝓕 (heisO ψ S T (d.extX T x) f) 0 := by
  funext w
  simp only [HypDec.mixS]
  congr 1
  funext a
  rw [integrand_eq d ψ f x a w, integrand_eq d ψ _ 0 a w, map_zero]
  simp only [heisO, add_zero, GlobalTheory.OrientedHeis.symplOH_add_left]
  rw [symplOH_skew S T 0 (d.extY T a), symplOH_skew S T 0 (d.ext0 T w)]
  simp only [symplOH_zero_left, neg_zero, zero_add, AddChar.map_zero_eq_one, one_mul]

end GlobalTheory.Bridge

namespace GlobalTheory.Bridge

open GlobalTheory.MixModel

theorem heis_bridge : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), (0 < ρ → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit S S₀ d.e d.i₀) ∧ GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D T.rank ρ = ratMx D T.rank ρ ∧ (∀ y, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart S T d.e y = d.extY T y) ∧ (∀ y, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart S T d.e' y = d.extX T y) ∧ (∀ w, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart S S₀ T d.i₀ w = d.ext0 T w) ∧ (∀ μ 𝓕 f x, d.mixS T ψ μ 𝓕 f x = GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res S S₀ T d.e d.i₀ μ 𝓕 (heisO ψ S T (d.extX T x) f)) ∧ (∀ μ 𝓕 f x, d.mixS T ψ μ 𝓕 f x = d.mixS T ψ μ 𝓕 (heisO ψ S T (d.extX T x) f) 0) ∧ (∀ b, d.nB b ∈ NI S d.e) ∧ ∀ c, d.nC c ∈ NI S d.e := by
  intro D ψ S S₀ T ρ d
  exact ⟨isIsoSplit_hyp d, rfl, fun _ => rfl, fun _ => rfl, orthProjPartHomToHermitian_eq_wittDecompositionCore d T,
    fun μ 𝓕 f x => mixS_eq_res d ψ μ 𝓕 f x, fun μ 𝓕 f x => mixS_heis d ψ μ 𝓕 f x,
    fun b => mem_NI_hyp d _ (d.nB_jX b) (d.pY_nB b) b (d.nB_j0 b),
    fun c => mem_NI_hyp d _ (d.nC_jX c) (d.pY_nC c) 0 (by rw [d.nC_j0, Matrix.mul_zero, add_zero])⟩

end GlobalTheory.Bridge

end
end

