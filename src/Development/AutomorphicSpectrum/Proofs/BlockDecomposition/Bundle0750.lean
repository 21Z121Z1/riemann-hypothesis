import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0742
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0635
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0402
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0578
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0400
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0417
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0741
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0613
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0727
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0407
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0687
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.Bundle0001
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.WeilBound.CoreStatements.PublishedTheorems.SiegelWeilSchrodinger.SiegelWeilUnitarySchrodingerLit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0370
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0375
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0003
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspLinesIrr
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle0006
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0467
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0495
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousPairProjection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1204
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0723
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0732

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.L2InnerProductHermitianForm
section
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.ModelS.L2InnerProduct

theorem isCompact_unitary_set (n : ℕ) :
    IsCompact ((Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ))) := by
  have hK : IsCompact (Set.pi Set.univ
      (fun _ : Fin n => Set.pi Set.univ (fun _ : Fin n => Metric.closedBall (0 : ℂ) 1)) :
        Set (Matrix (Fin n) (Fin n) ℂ)) :=
    isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_closedBall _ _))
  have hC : IsClosed ((Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ))) :=
    isClosed_unitary (R := Matrix (Fin n) (Fin n) ℂ)
  refine hK.of_isClosed_subset hC ?_
  intro x hx
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
  intro i j
  exact entry_norm_bound_of_unitary hx i j

theorem compactSpace_unitary (n : ℕ) : CompactSpace (Matrix.unitaryGroup (Fin n) ℂ) :=
  isCompact_iff_compactSpace.mp (isCompact_unitary_set n)

theorem continuous_restrict {n : ℕ} (x : SmF n) :
    Continuous fun k : Matrix.unitaryGroup (Fin n) ℂ => x.1 k.1 :=
  x.2.1.continuousOn.comp_continuous continuous_subtype_val unit_mem

section

variable {n : ℕ} [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)]
  [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)]
  (κ : Measure (Matrix.unitaryGroup (Fin n) ℂ)) [IsFiniteMeasure κ]

theorem integrable_integrand (x y : SmF n) :
    Integrable (fun k : Matrix.unitaryGroup (Fin n) ℂ => conj (x.1 k.1) * y.1 k.1) κ := by
  haveI := compactSpace_unitary n
  exact ((Complex.continuous_conj.comp (continuous_restrict x)).mul
    (continuous_restrict y)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem integrable_normSq (x : SmF n) :
    Integrable (fun k : Matrix.unitaryGroup (Fin n) ℂ => ‖x.1 k.1‖ ^ 2) κ := by
  haveI := compactSpace_unitary n
  exact ((continuous_restrict x).norm.pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem ipK_self (x : SmF n) :
    ipK κ x x = ((∫ k, ‖x.1 k.1‖ ^ 2 ∂κ : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  unfold ipK
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp [Complex.conj_mul']

theorem ipK_conj (x y : SmF n) : conj (ipK κ y x) = ipK κ x y := by
  unfold ipK
  rw [← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp [mul_comm]

theorem ipK_add_left (x y z : SmF n) : ipK κ (x + y) z = ipK κ x z + ipK κ y z := by
  unfold ipK
  rw [← integral_add (integrable_integrand κ x z) (integrable_integrand κ y z)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp [add_mul]

theorem ipK_smul_left (c : ℂ) (x y : SmF n) : ipK κ (c • x) y = conj c * ipK κ x y := by
  unfold ipK
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp [mul_assoc]

theorem eq_zero_of_ipK_self [κ.IsOpenPosMeasure] (x : SmF n) (h : ipK κ x x = 0)
    (k : Matrix.unitaryGroup (Fin n) ℂ) : x.1 k.1 = 0 := by
  rw [ipK_self, Complex.ofReal_eq_zero] at h
  have hae := (integral_eq_zero_iff_of_nonneg (fun k => by positivity) (integrable_normSq κ x)).1 h
  have hc : Continuous fun k : Matrix.unitaryGroup (Fin n) ℂ => ‖x.1 k.1‖ ^ 2 :=
    (continuous_restrict x).norm.pow 2
  have := (hc.ae_eq_iff_eq κ continuous_zero).1 hae
  simpa using congrFun this k

end

theorem ipK_form : ∀ (n : ℕ) [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)] [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)] (κ : Measure (Matrix.unitaryGroup (Fin n) ℂ)) [IsFiniteMeasure κ] [κ.IsOpenPosMeasure], (∀ x y : GlobalTheory.CompanionTheory.ModelS.SmF n, conj (GlobalTheory.CompanionTheory.ModelS.ipK κ y x) = GlobalTheory.CompanionTheory.ModelS.ipK κ x y) ∧ (∀ x : GlobalTheory.CompanionTheory.ModelS.SmF n, 0 ≤ (GlobalTheory.CompanionTheory.ModelS.ipK κ x x).re) ∧ (∀ x y z : GlobalTheory.CompanionTheory.ModelS.SmF n, GlobalTheory.CompanionTheory.ModelS.ipK κ (x + y) z = GlobalTheory.CompanionTheory.ModelS.ipK κ x z + GlobalTheory.CompanionTheory.ModelS.ipK κ y z) ∧ (∀ (c : ℂ) (x y : GlobalTheory.CompanionTheory.ModelS.SmF n), GlobalTheory.CompanionTheory.ModelS.ipK κ (c • x) y = conj c * GlobalTheory.CompanionTheory.ModelS.ipK κ x y) ∧ ∀ x : GlobalTheory.CompanionTheory.ModelS.SmF n, GlobalTheory.CompanionTheory.ModelS.ipK κ x x = 0 → ∀ k : Matrix.unitaryGroup (Fin n) ℂ, x.1 k.1 = 0 := by
  intro n _ _ κ _ _
  refine ⟨ipK_conj κ, fun x => ?_, ipK_add_left κ, ipK_smul_left κ, eq_zero_of_ipK_self κ⟩
  rw [ipK_self, Complex.ofReal_re]
  exact integral_nonneg fun k => by positivity

end GlobalTheory.CompanionTheory.ModelS.L2InnerProduct
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSumSubquotientProduct
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace GlobalTheory.CompanionTheory.LangSumSub

theorem isL_of_exhaust {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hEx : ∀ x : IrrGL k, ∃ 𝔪 : Multiset (Segment k), IsL 𝔪 x.rep) {N : ℕ} (τ : IrrRep (GL (Fin N) k)) :
    ∃ 𝔭 : Multiset (Segment k), IsL 𝔭 τ.ρ := by
  obtain ⟨𝔭, h𝔭⟩ := hEx (IrrGL.of τ.ρ τ.smooth τ.irr)
  exact ⟨𝔭, h𝔭.of_equiv (IrrGL.equivOf τ.ρ τ.smooth τ.irr).symm⟩

set_option maxHeartbeats 1000000 in

theorem isSubquotient_prodIrr {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hSoc : LSocleGL k)
    (hSeg : LSegJacquet k) (hFree : LOrderFree k) (hEx : ∀ x : IrrGL k, ∃ 𝔪 : Multiset (Segment k), IsL 𝔪 x.rep)
    (𝔪 𝔫 : Multiset (Segment k)) (x : Fin 2 → IrrGL k) (y : IrrGL k) (hd : ∑ a, (x a).1 = y.1)
    (h0 : IsL 𝔪 (x 0).rep) (h1 : IsL 𝔫 (x 1).rep) (hy : IsL (𝔪 + 𝔫) y.rep) : IsSubquotient y.rep (prodIrr x hd) := by
  obtain ⟨n, c⟩ := y
  obtain rfl : (x 0).1 + (x 1).1 = n := (Fin.sum_univ_two _).symm.trans hd
  obtain ⟨φ⟩ := nonempty_prod₂_equiv_prodIrr_rep x hd
  have hPs : IsSmooth (prodIrr x hd) := isSmooth_prodIrr x hd
  have hPf := GlobalTheory.CompanionTheory.ProdFL.hasFiniteLength_prodIrr hA x hd
  obtain ⟨h₁, h₂, h, Δ₁, Δ₂, Δ, hΔ₁, hΔ₂, hΔ, hI⟩ := GlobalTheory.T.ordered_forms_interleave_sum hA 𝔪 𝔫
  have w0 : Wd (x 0).rep (wtW Δ₁) := GlobalTheory.T.langlands_rep_ordered_word_occurs hA hSoc hSeg 𝔪 (x 0).rep h0 h₁ Δ₁ hΔ₁
  have w1 : Wd (x 1).rep (wtW Δ₂) := GlobalTheory.T.langlands_rep_ordered_word_occurs hA hSoc hSeg 𝔫 (x 1).rep h1 h₂ Δ₂ hΔ₂
  have wp : Wd (prod₂ (x 0).rep (x 1).rep) (wtW Δ) :=
    GlobalTheory.T.word_occurs_product_interleave hA (x 0) (x 1) _ _ _ (GlobalTheory.T.ordered_word_letters_cuspidal Δ₁) (GlobalTheory.T.ordered_word_letters_cuspidal Δ₂) w0 w1 hI
  have wP : Wd (prodIrr x hd) (wtW Δ) := GlobalTheory.T.word_occurs_of_subquotient (prodIrr x hd) (prod₂ (x 0).rep (x 1).rep) hPs
    (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective) _ wp
  have hτ := GlobalTheory.T.word_occurs_irreducible_subquotient hA (prodIrr x hd) hPs hPf (wtW Δ) wP
  obtain ⟨τ, hτP, hτW⟩ := hτ
  obtain ⟨𝔭, hτL⟩ := isL_of_exhaust hEx τ
  obtain ⟨h', z, hz, ⟨Γ, hΓ, hzL⟩, hcos⟩ := id hτL
  have s1 : InShW 𝔭 (wtW Δ) := by
    have := GlobalTheory.T.segment_product_word_in_shuffle hA hSeg z hz Γ hzL (wtW Δ) (GlobalTheory.T.ordered_word_letters_cuspidal Δ)
      (GlobalTheory.T.word_occurs_of_subquotient _ _ (isSmooth_prodIrr z hz) hcos.isSubquotient _ hτW)
    rwa [hΓ.1] at this
  have wΓ : Wd τ.ρ (wtW Γ) := GlobalTheory.T.langlands_rep_ordered_word_occurs hA hSoc hSeg 𝔭 τ.ρ hτL h' Γ hΓ
  have wΓP : Wd (prodIrr x hd) (wtW Γ) := GlobalTheory.T.word_occurs_of_subquotient _ _ hPs hτP _ wΓ
  have wΓ2 : Wd (prod₂ (x 0).rep (x 1).rep) (wtW Γ) := GlobalTheory.T.word_occurs_of_subquotient _ _ (isSmooth_prod₂ _ _)
    (.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective) _ wΓP
  obtain ⟨h'', z', Δ', hz', hz'L, hmap, hsub⟩ := GlobalTheory.T.product_langlands_subquotient_segments hA 𝔪 𝔫 (x 0) (x 1) h0 h1
  have s2 : InShW (𝔪 + 𝔫) (wtW Γ) := by
    have := GlobalTheory.T.segment_product_word_in_shuffle hA hSeg z' hz' Δ' hz'L (wtW Γ) (GlobalTheory.T.ordered_word_letters_cuspidal Γ)
      (GlobalTheory.T.word_occurs_of_subquotient _ _ (isSmooth_prodIrr z' hz') hsub _ wΓ2)
    rwa [hmap] at this
  have he : 𝔪 + 𝔫 = 𝔭 := GlobalTheory.T.ordered_forms_mutual_shuffle_eq hA (𝔪 + 𝔫) 𝔭 h h' Δ Γ hΔ hΓ s1 s2
  obtain ⟨ψ⟩ := GlobalTheory.T.langlands_classification_order_free_equiv hFree (𝔪 + 𝔫) τ.ρ (IrrGL.rep ⟨_, c⟩) (he ▸ hτL) hy
  exact (IsSubquotient.of_surjective ψ.toIntertwiningMap ψ.toLinearEquiv.surjective).trans hτP

theorem main : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), LSocleGL k → LSegJacquet k → LOrderFree k →
    (∀ x : IrrGL k, ∃ 𝔪 : Multiset (Segment k), IsL 𝔪 x.rep) →
    ∀ (𝔪 𝔫 : Multiset (Segment k)) (x : Fin 2 → IrrGL k) (y : IrrGL k) (hd : ∑ a, (x a).1 = y.1),
      IsL 𝔪 (x 0).rep → IsL 𝔫 (x 1).rep → IsL (𝔪 + 𝔫) y.rep → IsSubquotient y.rep (prodIrr x hd) :=
  fun hA hSoc hSeg hFree hEx 𝔪 𝔫 x y hd h0 h1 hy =>
    isSubquotient_prodIrr hA hSoc hSeg hFree hEx 𝔪 𝔫 x y hd h0 h1 hy

end GlobalTheory.CompanionTheory.LangSumSub

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateOfWhittaker
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SWGlue

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

variable {D : D7} {n : ℕ}

theorem weil_cell_zero {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D} {V : HSp D}
    {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)}
    (hω : IsWeilSch ψ χ θ V μ ω) {w u : G D n} (hw : mat w = blk4 0 1 (-1) 0) (b : hermA D n)
    (hu : mat u = blk4 1 b.1 0 1) (Φ : schwartzA θ V.rank n) (g : G D n) :
    (ω (w * u * g) Φ).1 0 = Jt ψ V μ (ω g Φ).1 b := by
  have e : ω (w * u * g) Φ = ω w (ω u (ω g Φ)) := by
    simp only [map_mul, Module.End.mul_apply]
  rw [e, hω.weyl w hw _ 0]
  unfold Jt
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have h0 : GlobalTheory.StdUnn.inner V (0 : Mx D V.rank n) y = 0 := by
    simp [GlobalTheory.StdUnn.inner, GlobalTheory.MixModel.adj]
  simp only [h0, Matrix.trace_zero, map_zero, AddChar.map_zero_eq_one, mul_one]
  rw [hω.unip u b.1 hu (ω g Φ) y, mul_comm]

theorem ndOfWhit : PositivityTheory.PfSWUS.NDOfWhit := by
  intro hU hT hW D n V ψ χ θ μ ω H l s ν Φ hS hR nb lam 𝓖 hC β hβ g
  obtain ⟨w, hw⟩ := GlobalTheory.StdUnn.Model.exists_weyl (D := D) (n := n)
  have h1 := hW D n V ψ χ θ μ ω H l s ν Φ hS hR lam 𝓖 nb hC w hw β hβ g
  rw [hT D n V ψ χ θ μ ω H l s ν Φ hS hR nb lam 𝓖 hC β hβ g]
  refine h1.congr ⟨(n : ℝ) / 2, fun z hz => ?_⟩
  show _ = fc ψ lam 𝓖 nb (fun x => eis ω H Φ x z) β g
  rw [(hU D n V ψ χ θ μ ω H l s ν Φ hS hR nb lam 𝓖 hC w hw β hβ z hz g).2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
  show _ * _ = sect ω H Φ z (w * nb b * g) * _
  rw [sect, weil_cell_zero hS.hω hw b (hC.1 b) Φ g]

end GlobalTheory.CompanionTheory.SWGlue

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicUnipotentLeviFactor
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SiegelNM
open GlobalTheory.StdUnn.Model

theorem unip_mul_levi : ∀ (D : D7) (p : ℕ) (q : G D p), q ∈ P D p → ∀ a : GL (Fin p) (AE D), blkA (mat q) = a.1 →
    ∃ (g₁ g₂ : G D p) (b : Mx D p p), q = g₁ * g₂ ∧ mat g₁ = blk4 1 b 0 1 ∧ mat g₂ = blk4 a.1 0 0 (adj (a⁻¹).1) := by
  intro D p q hq a ha
  obtain ⟨m, u, b, e, hm, hu⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_levi_unip hq a ha
  obtain ⟨m', hm'⟩ := GlobalTheory.StdUnn.Model.exists_levi (D := D) (n := p) a⁻¹
  rw [inv_inv] at hm'
  have hmm : m * m' = 1 := GlobalTheory.StdUnn.LeftInvSect.mat_inj (by
    rw [GlobalTheory.StdUnn.LeftInvSect.mat_mul, GlobalTheory.StdUnn.LeftInvSect.mat_one, hm, hm',
      GlobalTheory.StdUnn.LeftInvSect.levi_mul_inv])
  have hmm' : m' * m = 1 := by
    rw [eq_inv_of_mul_eq_one_right hmm, inv_mul_cancel]
  have h2 : (adj (a⁻¹).1 : Mx D p p) * adj a.1 = 1 := by
    rw [← adj_mul]; simp [adj_one]
  refine ⟨m * u * m', m, a.1 * b * adj a.1, ?_, ?_, hm⟩
  · rw [mul_assoc (m * u), hmm', mul_one, e]
  · rw [GlobalTheory.StdUnn.LeftInvSect.mat_mul, GlobalTheory.StdUnn.LeftInvSect.mat_mul, hm, hu, hm']
    simp [GlobalTheory.StdUnn.Model.submatrix_fromBlocks_mul, h2, -Matrix.coe_units_inv]

end GlobalTheory.CompanionTheory.SiegelNM
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReducibleCuspidalPairNongenericSubquotientStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir Zc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reducible_cuspidal_pair_nongeneric_subquotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    WhitRankIrr k → ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 →
    ∀ (x y : IrrGL k) (N : ℕ) (hd : ∑ a, (![x, y] a).1 = N), x.IsCusp → y.IsCusp →
      ¬ (prodIrr ![x, y] hd).IsIrreducible →
      ∃ τ : IrrRep (GL (Fin N) k), IsSubquotient τ.ρ (prodIrr ![x, y] hd) ∧ ¬ IsGenericFor ψ τ.ρ := by
  first | exact @GlobalTheory.CompanionTheory.CuspPair.exists_nongeneric_subquotient | exact GlobalTheory.CompanionTheory.CuspPair.exists_nongeneric_subquotient | (intros; apply GlobalTheory.CompanionTheory.CuspPair.exists_nongeneric_subquotient <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictedProductIntegral
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.FA
open scoped Classical
open GlobalTheory.CompanionTheory.FinActS

noncomputable section

namespace GlobalTheory.CompanionTheory.FinActCore

theorem relIndex_ne_of_out {G : Type} [Group G] (L K : Subgroup G) (hLK : L ≤ K)
    (h : {q : G ⧸ L | q.out ∈ K}.Finite) : L.relIndex K ≠ 0 := by
  have hmem : ∀ c : K ⧸ L.subgroupOf K, (((c.out : K) : G) : G ⧸ L).out ∈ K := by
    intro c
    obtain ⟨t, ht⟩ := QuotientGroup.mk_out_eq_mul L ((c.out : K) : G)
    rw [ht]
    exact mul_mem (c.out).2 (hLK t.2)
  have hinj : Function.Injective (fun c : K ⧸ L.subgroupOf K =>
      (⟨(((c.out : K) : G) : G ⧸ L), hmem c⟩ : {q : G ⧸ L | q.out ∈ K})) := by
    intro a b hab
    have h1 : (((a.out : K) : G) : G ⧸ L) = (((b.out : K) : G) : G ⧸ L) :=
      congrArg Subtype.val hab
    have h2 : ((a.out : K) : G)⁻¹ * ((b.out : K) : G) ∈ L := QuotientGroup.eq.1 h1
    rw [← QuotientGroup.out_eq' a, ← QuotientGroup.out_eq' b]
    refine QuotientGroup.eq.2 ?_
    rw [Subgroup.mem_subgroupOf]
    simpa using h2
  haveI := h.to_subtype
  haveI : Finite (K ⧸ L.subgroupOf K) := Finite.of_injective _ hinj
  exact Subgroup.index_ne_zero_of_finite

theorem out_finite_of_relIndex {H : Type} [Group H] (V K : Subgroup H) (hi : V.relIndex K ≠ 0) :
    {q : H ⧸ V | q.out ∈ K}.Finite := by
  have hm : Nat.card (K ⧸ V.subgroupOf K) ≠ 0 := hi
  haveI : Finite (K ⧸ V.subgroupOf K) := Nat.finite_of_card_ne_zero hm
  have hinj : Function.Injective (fun q : {q : H ⧸ V | q.out ∈ K} =>
      (((⟨q.1.out, q.2⟩ : K)) : K ⧸ V.subgroupOf K)) := by
    intro a b hab
    have h1 := QuotientGroup.eq.1 hab
    rw [Subgroup.mem_subgroupOf] at h1
    have h2 : (a.1.out)⁻¹ * b.1.out ∈ V := by simpa using h1
    apply Subtype.ext
    rw [← QuotientGroup.out_eq' a.1, ← QuotientGroup.out_eq' b.1]
    exact QuotientGroup.eq.2 h2
  haveI : Finite {q : H ⧸ V | q.out ∈ K} := Finite.of_injective _ hinj
  exact Set.toFinite _

theorem hint_prod_eq_foldr : ∀ {ι Γ : Type} [Group Γ] {Hl : ι → Type} [∀ i, Group (Hl i)] (p : ∀ i, Γ →* Hl i) (e : ∀ i, Hl i →* Γ) (K : Subgroup Γ) (KH V : ∀ i, Subgroup (Hl i))
    (f : ∀ i, Hl i → ℂ)
    (hpe : ∀ i m, p i (e i m) = m) (hpe' : ∀ i j m, i ≠ j → p j (e i m) = 1)
    (hsep : ∀ x y : Γ, (∀ i, p i x = p i y) → x = y)
    (hev : ∀ x, ∀ᶠ i in cofinite, p i x ∈ KH i)
    (hK : ∀ x, x ∈ K ↔ ∀ i, p i x ∈ KH i)
    (hVK : ∀ i, V i ≤ KH i) (hVi : ∀ i, (V i).relIndex (KH i) ≠ 0)
    (hVe : ∀ᶠ i in cofinite, V i = KH i ∧ f i = (KH i : Set (Hl i)).indicator 1)
    (hfV : ∀ i, ∀ u ∈ V i, ∀ x, f i (x * u) = f i x)
    (hfs : ∀ i, {q : Hl i ⧸ V i | f i q.out ≠ 0}.Finite)
    (g : Γ → ℂ) (hg : ∀ u, (∀ i, p i u ∈ V i) → ∀ x, g (x * u) = g x)
    (l : List ι) (hl : l.Nodup)
    (hfix : ∀ i, i ∉ l → (fun x => hint (KH i) fun m => f i m * g (x * e i m)) = g),
    hint K (fun x => (∏ᶠ i, f i (p i x)) * g x) =
      l.foldr (fun i g' x => hint (KH i) fun m => f i m * g' (x * e i m)) g 1 := by
  intro ι Γ _ Hl _ p e K KH V f hpe hpe' hsep hev hK hVK hVi hVe hfV hfs g hg l hl hfix
  have hmemL : ∀ u, u ∈ (⨅ i, (V i).comap (p i)) ↔ ∀ i, p i u ∈ V i := by
    intro u
    simp [Subgroup.mem_iInf]
  generalize hLdef : (⨅ i, (V i).comap (p i)) = L at hmemL
  have hLK : L ≤ K := fun u hu => (hK u).2 fun i => hVK i ((hmemL u).1 hu i)
  have hfinKH : ∀ i, {q : Hl i ⧸ V i | q.out ∈ KH i}.Finite :=
    fun i => out_finite_of_relIndex (V i) (KH i) (hVi i)
  have hVe1 : ∀ᶠ i in cofinite, V i = KH i := hVe.mono fun i h => h.1
  have hidx : L.relIndex K ≠ 0 := by
    refine relIndex_ne_of_out L K hLK ?_
    have h0 := GlobalTheory.T.finite_restricted_product_quotient p V (fun i => (KH i : Set (Hl i)))
      (fun i x hx u hu => mul_mem hx (hVK i hu)) hfinKH
      (hVe1.mono fun i h x hx => by
        rw [SetLike.mem_coe, h]
        exact hx)
    rw [hLdef] at h0
    exact h0.subset fun q hq => (hK _).1 hq
  have hB := Filter.eventually_cofinite.1 hVe
  obtain ⟨extra, hextra, hend, hcov⟩ : ∃ extra : List ι, (∀ i ∈ extra, i ∉ l) ∧ extra.Nodup ∧
      ∀ j, j ∉ l ++ extra → V j = KH j ∧ f j = (KH j : Set (Hl j)).indicator 1 := by
    refine ⟨(hB.toFinset.filter (· ∉ l)).toList, ?_, Finset.nodup_toList _, ?_⟩
    · intro i hi
      rw [Finset.mem_toList, Finset.mem_filter] at hi
      exact hi.2
    · intro j hj
      by_contra hc
      apply hj
      rw [List.mem_append]
      by_cases hjl : j ∈ l
      · exact Or.inl hjl
      · refine Or.inr ?_
        rw [Finset.mem_toList, Finset.mem_filter]
        exact ⟨hB.mem_toFinset.2 hc, hjl⟩
  have hnd : (l ++ extra).Nodup :=
    List.Nodup.append hl hend fun a ha hb => hextra a hb ha
  generalize hT : l ++ extra = T at hnd hcov
  have hfoldE : ∀ m : List ι, (∀ i ∈ m, i ∉ l) →
      m.foldr (fun i g' x => hint (KH i) fun m => f i m * g' (x * e i m)) g = g := by
    intro m
    induction m with
    | nil => intro _; rfl
    | cons a t ih =>
      intro hm
      rw [List.foldr_cons, ih fun i hi => hm i (List.mem_cons_of_mem _ hi)]
      exact hfix a (hm a List.mem_cons_self)
  have hfold : T.foldr (fun i g' x => hint (KH i) fun m => f i m * g' (x * e i m)) g =
      l.foldr (fun i g' x => hint (KH i) fun m => f i m * g' (x * e i m)) g := by
    rw [← hT, List.foldr_append, hfoldE extra hextra]
  have hsum := GlobalTheory.T.restricted_product_hecke_sum p e KH V f hpe hpe' hsep hev hVK hVi hVe1 hfV hfs T hnd g hg 1
  rw [hLdef] at hsum
  simp only [one_mul] at hsum
  have hF : ∀ x, (∏ᶠ j, if j ∈ T then f j (p j x)
      else (V j : Set (Hl j)).indicator (1 : Hl j → ℂ) (p j x)) = ∏ᶠ i, f i (p i x) := by
    intro x
    refine finprod_congr fun j => ?_
    split_ifs with hj
    · rfl
    · obtain ⟨h1, h2⟩ := hcov j hj
      rw [h2, h1]
  simp only [hF] at hsum
  have hlev : L ≤ rStab (fun x => (∏ᶠ i, f i (p i x)) * g x) := by
    intro r hr
    refine GlobalTheory.CompanionTheory.FamClP.mem_rStab'.2 fun x => ?_
    have h1 : (∏ᶠ i, f i (p i (x * r))) = ∏ᶠ i, f i (p i x) := by
      refine finprod_congr fun i => ?_
      rw [map_mul]
      exact hfV i _ ((hmemL r).1 hr i) _
    show (∏ᶠ i, f i (p i (x * r))) * g (x * r) = (∏ᶠ i, f i (p i x)) * g x
    rw [h1, hg r ((hmemL r).1 hr) x]
  have h1 := GlobalTheory.CompanionTheory.HintLevel.hint_eq_level Γ K L (fun x => (∏ᶠ i, f i (p i x)) * g x) hLK hlev hidx

  have hfVI : ∀ i, ∀ u ∈ V i, ∀ x, (KH i : Set (Hl i)).indicator (1 : Hl i → ℂ) (x * u) =
      (KH i : Set (Hl i)).indicator (1 : Hl i → ℂ) x := by
    intro i u hu x
    have h0 : u ∈ rStab ((KH i : Set (Hl i)).indicator (1 : Hl i → ℂ)) := by
      rw [GlobalTheory.CompanionTheory.FamClP.rStab_ind]
      exact hVK i hu
    exact GlobalTheory.CompanionTheory.FamClP.mem_rStab'.1 h0 x
  have hfsI : ∀ i, {q : Hl i ⧸ V i | (KH i : Set (Hl i)).indicator (1 : Hl i → ℂ) q.out ≠ 0}.Finite := by
    intro i
    refine (hfinKH i).subset fun q hq => ?_
    by_contra hn
    exact hq (Set.indicator_of_notMem (s := (KH i : Set (Hl i))) (show q.out ∉ (KH i : Set (Hl i)) from hn) _)
  have hsum2 := GlobalTheory.T.restricted_product_hecke_sum p e KH V (fun i => (KH i : Set (Hl i)).indicator (1 : Hl i → ℂ))
    hpe hpe' hsep hev hVK hVi hVe1 hfVI hfsI T hnd (fun _ => 1) (fun _ _ _ => rfl) 1
  rw [hLdef] at hsum2
  have hfold2 : ∀ m : List ι, m.foldr (fun i g' x => hint (KH i) fun m =>
      (KH i : Set (Hl i)).indicator (1 : Hl i → ℂ) m * g' (x * e i m)) (fun _ => (1 : ℂ)) =
      fun _ => 1 := by
    intro m
    induction m with
    | nil => rfl
    | cons a t ih =>
      rw [List.foldr_cons, ih]
      funext x
      simp only [mul_one]
      exact GlobalTheory.CompanionTheory.FamClP.hint_ind _
  rw [hfold2 T] at hsum2
  have hF2 : ∀ x, (∏ᶠ j, if j ∈ T then (KH j : Set (Hl j)).indicator (1 : Hl j → ℂ) (p j x)
      else (V j : Set (Hl j)).indicator (1 : Hl j → ℂ) (p j x)) =
      (K : Set Γ).indicator (1 : Γ → ℂ) x := by
    intro x
    have h0 : (∏ᶠ j, if j ∈ T then (KH j : Set (Hl j)).indicator (1 : Hl j → ℂ) (p j x)
        else (V j : Set (Hl j)).indicator (1 : Hl j → ℂ) (p j x)) =
        ∏ᶠ j, (KH j : Set (Hl j)).indicator (1 : Hl j → ℂ) (p j x) := by
      refine finprod_congr fun j => ?_
      split_ifs with hj
      · rfl
      · rw [(hcov j hj).1]
    rw [h0]
    by_cases hx : x ∈ K
    · have h2 : (K : Set Γ).indicator (1 : Γ → ℂ) x = 1 := Set.indicator_of_mem hx _
      rw [h2]
      have h3 : ∀ j, (KH j : Set (Hl j)).indicator (1 : Hl j → ℂ) (p j x) = 1 :=
        fun j => Set.indicator_of_mem ((hK x).1 hx j) _
      simp only [h3, finprod_one]
    · have h2 : (K : Set Γ).indicator (1 : Γ → ℂ) x = 0 := Set.indicator_of_notMem hx _
      rw [h2]
      have h3 : ∃ j, p j x ∉ KH j := by
        by_contra hc
        push_neg at hc
        exact hx ((hK x).2 hc)
      obtain ⟨j, hj⟩ := h3
      refine finprod_eq_zero _ j (Set.indicator_of_notMem hj _) ?_
      refine (Filter.eventually_cofinite.1 (hev x)).subset fun i hi hin => hi ?_
      exact Set.indicator_of_mem hin _
  simp only [hF2, mul_one] at hsum2
  have h2 := GlobalTheory.CompanionTheory.HintLevel.hint_eq_level Γ K L ((K : Set Γ).indicator (1 : Γ → ℂ)) hLK
    (by rw [GlobalTheory.CompanionTheory.FamClP.rStab_ind]; exact hLK) hidx
  rw [GlobalTheory.CompanionTheory.FamClP.hint_ind, hsum2] at h2
  have hC : ((L.relIndex K : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hidx
  have hCeq : (T.map fun i => (((V i).relIndex (KH i) : ℕ) : ℂ)).prod = ((L.relIndex K : ℕ) : ℂ) := by
    have h3 : ((L.relIndex K : ℕ) : ℂ) * (((L.relIndex K : ℕ) : ℂ)⁻¹ *
        (T.map fun i => (((V i).relIndex (KH i) : ℕ) : ℂ)).prod) = ((L.relIndex K : ℕ) : ℂ) * 1 := by
      rw [← h2]
    rwa [← mul_assoc, mul_inv_cancel₀ hC, one_mul, mul_one] at h3
  rw [h1, hsum, hCeq, ← mul_assoc, inv_mul_cancel₀ hC, one_mul, hfold]

end GlobalTheory.CompanionTheory.FinActCore

end
end

