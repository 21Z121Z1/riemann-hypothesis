import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRadNMulLevM
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0146
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0632
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspStdSubGeneric
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdjacentQuotientOfTwoSegment
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0643
import CompanionTheory.AutomorphicTheory.HeckeStandardModules.EqZeroOfCompAt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FintypeResidue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0601
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0645
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0644
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0485
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0226
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0508
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0530
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivPiExteriorTensorBlockLevi
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0044
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZetaIntegralAbsoluteConvergence
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentRadicalHaarFromProduct
section
noncomputable section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.QKAvg.RadHaar

theorem isMulLeftInvariant_map_of {X G : Type*} [MeasurableSpace X] [MeasurableSpace G] [Mul G] (P : Measure X)
    (e : X ≃ᵐ G) (h : ∀ q, ∃ T : X → X, MeasurePreserving T P P ∧ ∀ p, e (T p) = e q * e p) :
    (P.map e).IsMulLeftInvariant := by
  refine ⟨fun g => ?_⟩
  obtain ⟨T, hT, hTe⟩ := h (e.symm g)
  have h1 : (fun x => g * x) = e ∘ T ∘ e.symm := by
    funext x
    simp [hTe]
  have hm : Measurable (fun x => g * x) := by
    rw [h1]
    exact e.measurable.comp (hT.measurable.comp e.symm.measurable)
  rw [Measure.map_map hm e.measurable]
  have h2 : (fun x => g * x) ∘ e = e ∘ T := by
    funext p
    simp [hTe]
  rw [h2, ← Measure.map_map e.measurable hT.measurable, hT.map_eq]

theorem measurePreserving_shear {A C : Type*} [AddCommGroup A] [MeasurableSpace A] [MeasurableAdd₂ A]
    [AddCommGroup C] [MeasurableSpace C] [MeasurableAdd₂ C] (κ : Measure A) (β : Measure C) [SFinite κ] [SFinite β]
    [κ.IsAddLeftInvariant] [β.IsAddLeftInvariant] {f : C → A} (hf : Measurable f) (b₀ : C) :
    MeasurePreserving (fun p : A × C => (p.1 + f p.2, p.2 + b₀)) (κ.prod β) (κ.prod β) := by
  have h1 : MeasurePreserving (fun p : C × A => (b₀ + p.1, f p.1 + p.2)) (β.prod κ) (β.prod κ) :=
    (measurePreserving_add_left β b₀).skew_product (g := fun c a => f c + a)
      (by exact (hf.comp measurable_fst).add measurable_snd)
      (Filter.Eventually.of_forall fun c => map_add_left_eq_self κ (f c))
  have h2 := (Measure.measurePreserving_swap (μ := β) (ν := κ)).comp
    (h1.comp (Measure.measurePreserving_swap (μ := κ) (ν := β)))
  have hfun : (fun p : A × C => (p.1 + f p.2, p.2 + b₀)) =
      Prod.swap ∘ (fun p : C × A => (b₀ + p.1, f p.1 + p.2)) ∘ Prod.swap := by
    funext p
    exact Prod.ext (add_comm _ _) (add_comm _ _)
  rw [hfun]
  exact h2

private theorem isMulRightInvariant_map_of_exists_measurePreserving {X G : Type*} [MeasurableSpace X] [MeasurableSpace G] [Mul G] (P : Measure X)
    (e : X ≃ᵐ G) (h : ∀ q, ∃ T : X → X, MeasurePreserving T P P ∧ ∀ p, e (T p) = e p * e q) :
    (P.map e).IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  obtain ⟨T, hT, hTe⟩ := h (e.symm g)
  have h1 : (fun x => x * g) = e ∘ T ∘ e.symm := by
    funext x
    simp [hTe]
  have hm : Measurable (fun x => x * g) := by
    rw [h1]
    exact e.measurable.comp (hT.measurable.comp e.symm.measurable)
  rw [Measure.map_map hm e.measurable]
  have h2 : (fun x => x * g) ∘ e = e ∘ T := by
    funext p
    simp [hTe]
  rw [h2, ← Measure.map_map e.measurable hT.measurable, hT.map_eq]

theorem haar_of_shear {A C G : Type*} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A] [LocallyCompactSpace A]
    [AddCommGroup C] [TopologicalSpace C] [IsTopologicalAddGroup C]
    [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C] [LocallyCompactSpace C]
    [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    (e : A × C ≃ₜ G) (f : C → C → A) (hf : Continuous fun x : C × C => f x.1 x.2)
    (hmul : ∀ c b c' b', e (c, b) * e (c', b') = e (c + (c' + f b b'), b + b'))
    (κ : Measure A) (β : Measure C) [κ.IsAddHaarMeasure] [β.IsAddHaarMeasure] :
    ((κ.prod β).map e).IsHaarMeasure ∧ ((κ.prod β).map e).IsMulRightInvariant := by
  have hfc : IsFiniteMeasureOnCompacts ((κ.prod β).map e) := by
    refine ⟨fun K hK => ?_⟩
    change (κ.prod β).map e.toMeasurableEquiv K < ⊤
    rw [MeasurableEquiv.map_apply]
    exact (e.isCompact_preimage.2 hK).measure_lt_top
  have hop : Measure.IsOpenPosMeasure ((κ.prod β).map e) := by
    refine ⟨fun U hU hne => ?_⟩
    change (κ.prod β).map e.toMeasurableEquiv U ≠ 0
    rw [MeasurableEquiv.map_apply]
    exact (hU.preimage e.continuous).measure_ne_zero _ (hne.preimage e.surjective)
  have hl : ((κ.prod β).map e).IsMulLeftInvariant := by
    refine isMulLeftInvariant_map_of (κ.prod β) e.toMeasurableEquiv ?_
    rintro ⟨c, b⟩
    refine ⟨fun p => (p.1 + (c + f b p.2), p.2 + b),
      measurePreserving_shear κ β ((hf.comp (continuous_const.prodMk continuous_id)).measurable.const_add c) b, ?_⟩
    rintro ⟨c', b'⟩
    change e _ = e (c, b) * e (c', b')
    rw [hmul]
    congr 1
    exact Prod.ext (add_left_comm _ _ _) (add_comm _ _)
  have hr : ((κ.prod β).map e).IsMulRightInvariant := by
    refine isMulRightInvariant_map_of_exists_measurePreserving (κ.prod β) e.toMeasurableEquiv ?_
    rintro ⟨c, b⟩
    refine ⟨fun p => (p.1 + (c + f p.2 b), p.2 + b),
      measurePreserving_shear κ β ((hf.comp (continuous_id.prodMk continuous_const)).measurable.const_add c) b, ?_⟩
    rintro ⟨c', b'⟩
    change e _ = e (c', b') * e (c, b)
    rw [hmul]
  exact ⟨{ toIsFiniteMeasureOnCompacts := hfc, toIsMulLeftInvariant := hl, toIsOpenPosMeasure := hop }, hr⟩

variable {D : D7} {B W : HSp D} {t : ℕ} (d : HypDec B W t)

def coordB (q : GA D B) : Mx D t W.rank := d.pX ⬝ mt B q ⬝ d.j0

def coordC (q : GA D B) : Mx D t t :=
  d.pX ⬝ mt B q ⬝ d.jY + half D • (coordB d q ⬝ plus W (coordB d q))

theorem pX_nn (c : skewA D t) (b : Mx D t W.rank) : d.pX ⬝ mt B (d.nC c * d.nB b) =
    d.pX + b ⬝ d.p0 - (half D • (b ⬝ plus W b)) ⬝ d.pY + c.1 ⬝ d.pY := by
  rw [GlobalTheory.MixModel.mt_mul, ← Matrix.mul_assoc, GlobalTheory.MixModel.HypDec.pX_nC, Matrix.add_mul, Matrix.mul_assoc, GlobalTheory.MixModel.HypDec.pY_nB, GlobalTheory.MixModel.HypDec.pX_nB]

theorem coordB_nn (c : skewA D t) (b : Mx D t W.rank) : coordB d (d.nC c * d.nB b) = b := by
  rw [coordB, pX_nn]
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, GlobalTheory.MixModel.HypDec.pX_j0, GlobalTheory.MixModel.HypDec.p0_j0, GlobalTheory.MixModel.HypDec.pY_j0, Matrix.mul_one,
    Matrix.mul_zero, zero_add, sub_zero, add_zero]

theorem coordC_nn (c : skewA D t) (b : Mx D t W.rank) : coordC d (d.nC c * d.nB b) = c.1 := by
  rw [coordC, coordB_nn, pX_nn]
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, GlobalTheory.MixModel.HypDec.pX_jY, GlobalTheory.MixModel.HypDec.p0_jY, GlobalTheory.MixModel.HypDec.pY_jY, Matrix.mul_one,
    Matrix.mul_zero]
  abel

section Top

local instance topRingAE : IsTopologicalRing (AE D) := (Formalism.IndefR.Eqv.ae_facts D).1

local instance topGrpGA (S : HSp D) : IsTopologicalGroup (GA D S) := (Formalism.IndefR.Eqv.ga_facts D S).1

theorem continuous_coordB : Continuous (coordB d) := by
  show Continuous fun q : GA D B => d.pX * mt B q * d.j0
  exact (continuous_const.matrix_mul (GlobalTheory.MixModel.continuous_mt B)).matrix_mul continuous_const

theorem continuous_coordC : Continuous (coordC d) := by
  have hB := continuous_coordB d
  have hP : Continuous fun q : GA D B => GlobalTheory.MixModel.giA W * GlobalTheory.MixModel.adj (coordB d q) :=
    continuous_const.matrix_mul (GlobalTheory.MixModel.continuous_adj.comp hB)
  have hS : Continuous fun q : GA D B =>
      GlobalTheory.MixModel.half D • (coordB d q * (GlobalTheory.MixModel.giA W * GlobalTheory.MixModel.adj (coordB d q))) :=
    (hB.matrix_mul hP).const_smul (GlobalTheory.MixModel.half D)
  have hA : Continuous fun q : GA D B => d.pX * mt B q * d.jY :=
    (continuous_const.matrix_mul (GlobalTheory.MixModel.continuous_mt B)).matrix_mul continuous_const
  exact hA.add hS

theorem coordC_mem (n : radN d) : coordC d n.1.1 ∈ skewA D t := by
  obtain ⟨c, b, h⟩ := n.2
  rw [h, coordC_nn]
  exact c.2

def coordHomeo : (skewA D t × Mx D t W.rank) ≃ₜ radN d where
  toFun p := ⟨⟨d.nC p.1 * d.nB p.2, mul_mem (GlobalTheory.GodementSectionReduction.nC_mem d _) (GlobalTheory.GodementSectionReduction.nB_mem d _)⟩, p.1, p.2, rfl⟩
  invFun n := (⟨coordC d n.1.1, coordC_mem d n⟩, coordB d n.1.1)
  left_inv p := by
    apply Prod.ext
    · exact Subtype.ext (coordC_nn d p.1 p.2)
    · exact coordB_nn d p.1 p.2
  right_inv n := by
    obtain ⟨c, b, h⟩ := n.2
    apply Subtype.ext
    apply Subtype.ext
    change d.nC ⟨coordC d n.1.1, coordC_mem d n⟩ * d.nB (coordB d n.1.1) = n.1.1
    have e1 : (⟨coordC d n.1.1, coordC_mem d n⟩ : skewA D t) = c :=
      Subtype.ext (by change coordC d n.1.1 = c.1; rw [h, coordC_nn])
    rw [e1, h, coordB_nn]
  continuous_toFun :=
    Continuous.subtype_mk (Continuous.subtype_mk
      ((d.continuous_nC.comp continuous_fst).mul (d.continuous_nB.comp continuous_snd)) _) _
  continuous_invFun :=
    (Continuous.subtype_mk ((continuous_coordC d).comp (continuous_subtype_val.comp continuous_subtype_val)) _).prodMk
      ((continuous_coordB d).comp (continuous_subtype_val.comp continuous_subtype_val))

theorem coordHomeo_coe (p : skewA D t × Mx D t W.rank) :
    (((coordHomeo d p : radN d) : GlobalTheory.RegSW.stab d) : GA D B) = d.nC p.1 * d.nB p.2 := rfl

end Top

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in

theorem exists_coord : ∀ (D : D7) (B W : HSp D) (t : ℕ) (d : HypDec B W t) [LocallyCompactSpace (radN d)] (κ : Measure (skewA D t)) (β : Measure (Mx D t W.rank)), κ.IsAddHaarMeasure → β.IsAddHaarMeasure → ∃ Ψ : (skewA D t × Mx D t W.rank) ≃ₜ radN d, (∀ p, (((Ψ p : GlobalTheory.RegSW.stab d) : GA D B)) = d.nC p.1 * d.nB p.2) ∧ ((κ.prod β).map Ψ).IsHaarMeasure ∧ ((κ.prod β).map Ψ).IsMulRightInvariant := by
  intro D B W t d _ κ β hκ hβ
  have hc := coordHomeo_coe d
  obtain ⟨i1, i2, i3, i4, i5⟩ := Formalism.IndefR.Eqv.ae_facts D
  obtain ⟨j1, j2, j3, j4, j5⟩ := Formalism.IndefR.Eqv.ga_facts D B
  have : T2Space (Mx D t t) := inferInstanceAs (T2Space (Fin t → Fin t → AE D))
  have : BorelSpace (Mx D t t) := ⟨rfl⟩
  have : SecondCountableTopology (Mx D t t) := inferInstanceAs (SecondCountableTopology (Fin t → Fin t → AE D))
  have : LocallyCompactSpace (Mx D t t) := inferInstanceAs (LocallyCompactSpace (Fin t → Fin t → AE D))
  have : T2Space (Mx D t W.rank) := inferInstanceAs (T2Space (Fin t → Fin W.rank → AE D))
  have : BorelSpace (Mx D t W.rank) := ⟨rfl⟩
  have : SecondCountableTopology (Mx D t W.rank) := inferInstanceAs (SecondCountableTopology (Fin t → Fin W.rank → AE D))
  have : LocallyCompactSpace (Mx D t W.rank) := inferInstanceAs (LocallyCompactSpace (Fin t → Fin W.rank → AE D))
  have q3 : SecondCountableTopology (skewA D t) :=
    inferInstanceAs (SecondCountableTopology ((skewA D t : Set (Mx D t t))))
  have hcl : IsClosed ((skewA D t : Set (Mx D t t))) := by
    show IsClosed {c : Mx D t t | GlobalTheory.MixModel.adj c = -c}
    exact isClosed_eq GlobalTheory.MixModel.continuous_adj continuous_neg
  have : LocallyCompactSpace (skewA D t) := hcl.locallyCompactSpace
  refine ⟨coordHomeo d, hc, ?_⟩
  refine haar_of_shear (coordHomeo d) (fun b b' => cComm W b b') (GlobalTheory.Unf.HaarCoord.continuous_cComm W t) ?_ κ β
  intro c b c' b'
  apply Subtype.ext
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hc, hc, hc]
  dsimp only
  rw [GlobalTheory.MixModel.HypDec.nC_add, GlobalTheory.MixModel.HypDec.nC_add]
  simp only [mul_assoc]
  rw [← mul_assoc (d.nB b) (d.nC c'), ← GlobalTheory.MixModel.HypDec.nC_mul_nB d b c', mul_assoc (d.nC c'), GlobalTheory.MixModel.HypDec.nB_mul_nB,
    ← GlobalTheory.MixModel.HypDec.nC_mul_nB d (b + b') (cComm W b b')]

end GlobalTheory.CompanionTheory.QKAvg.RadHaar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitConditionsOfEquiv
section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

namespace GlobalTheory.CompanionTheory.UnitTransport

theorem unitConds_of_homeo : ∀ {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G'] (e : G ≃ₜ* G') (θ : G →* G) (θ' : G' →* G')
  (K : Subgroup G) (K' : Subgroup G') (d : G) (f : G → ℂ) (f' : G' → ℂ), (∀ x, e (θ x) = θ' (e x)) → (∀ x, x ∈ K ↔ e x ∈ K') →
  (∀ x, f x = f' (e x)) → UnitConds θ' K' (e d) f' → UnitConds θ K d f := by
  intro G G' _ _ _ _ e θ θ' K K' d f f' hθ hK hf h
  unfold GlobalTheory.CompanionTheory.LocalHypotheses.UnitConds at h ⊢
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, (hK d).2 h2, ?_, ?_⟩
  · funext x
    rw [hf x, h1]
    simp only [Set.indicator_apply, SetLike.mem_coe, hK x, Pi.one_apply]
  · unfold GlobalTheory.BCT.cptPart
    rw [Subgroup.closure_le]
    rintro t ⟨ht, hc⟩
    rw [SetLike.mem_coe, hK t]
    have hte : e t ∈ GlobalTheory.BCT.twCent θ' (e d) := by
      have htd : t * d = d * θ t := ht
      show e t * e d = e d * θ' (e t)
      rw [← hθ, ← map_mul e, ← map_mul e, htd]
    have hcl : closure (Subgroup.zpowers (e t) : Set G') =
        e '' closure (Subgroup.zpowers t : Set G) := by
      apply Set.Subset.antisymm
      · intro y hy
        refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
        refine map_mem_closure e.symm.continuous hy ?_
        intro z hz
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
        exact Subgroup.mem_zpowers_iff.2 ⟨k, by rw [map_zpow, e.symm_apply_apply]⟩
      · rintro y ⟨x, hx, rfl⟩
        refine map_mem_closure e.continuous hx ?_
        intro z hz
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
        exact Subgroup.mem_zpowers_iff.2 ⟨k, (map_zpow e t k).symm⟩
    have hce : IsCompact (closure (Subgroup.zpowers (e t) : Set G')) := by
      rw [hcl]
      exact hc.image e.continuous
    unfold GlobalTheory.BCT.cptPart at h3
    exact h3 (Subgroup.subset_closure (And.intro hte hce))
  · intro y hy
    have hy' : (e y)⁻¹ * e d * θ' (e y) ∈ K' := by
      rw [← hθ, ← map_inv e, ← map_mul e, ← map_mul e]
      exact (hK _).1 hy
    obtain ⟨t', ht', k', hk', hyt⟩ := h4 (e y) hy'
    refine ⟨e.symm t', ?_, e.symm k', ?_, ?_⟩
    · show e.symm t' * d = d * θ (e.symm t')
      apply e.injective
      rw [map_mul, map_mul, hθ, e.apply_symm_apply]
      exact ht'
    · rw [hK, e.apply_symm_apply]
      exact hk'
    · apply e.injective
      rw [map_mul, e.apply_symm_apply, e.apply_symm_apply]
      exact hyt

end GlobalTheory.CompanionTheory.UnitTransport
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnlinkedProductIrreducible
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.CompanionTheory.BZSeg.Unlinked

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def subIncl (π : Representation ℂ (GL (Fin N) k) V) (S : Subrepresentation π) :
    S.toRepresentation.IntertwiningMap π where
  toLinearMap := S.toSubmodule.subtype
  isIntertwining' := fun _ => rfl

def quotProj {W : Type} [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin N) k) V)
    (σ : Representation ℂ (GL (Fin N) k) W) (f : σ.IntertwiningMap π) :
    π.IntertwiningMap (GlobalTheory.CompanionTheory.BZSeg.TwoSeg.quotRep π σ f) where
  toLinearMap := (LinearMap.range f.toLinearMap).mkQ
  isIntertwining' := fun _ => rfl

theorem isIrreducible_of_generic {ψ : AddChar k Circle} (hψ : Continuous ψ) (h1 : ψ ≠ 1)
    (π : Representation ℂ (GL (Fin N) k) V) [Nontrivial V] (hπ : IsSmooth π)
    (hr : Module.rank ℂ (TwJacquet π (unipB k (Fin N)) (whitChar ψ N)) ≤ 1)
    (hsub : ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin N) k) W)
      (f : σ.IntertwiningMap π), Function.Injective f → Nontrivial W → IsGeneric σ)
    (hquo : ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (GL (Fin N) k) W)
      (f : π.IntertwiningMap τ), Function.Surjective f → Nontrivial W → IsGeneric τ) :
    π.IsIrreducible := by
  have hbt : (⊥ : Subrepresentation π) ≠ ⊤ := by
    intro e
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have h2 : v ∈ (⊤ : Subrepresentation π).toSubmodule := trivial
    rw [← e] at h2
    exact hv h2
  haveI : Nontrivial (Subrepresentation π) := ⟨⟨⊥, ⊤, hbt⟩⟩
  refine ⟨fun S => ?_⟩
  by_contra hc
  push Not at hc
  obtain ⟨hb, ht⟩ := hc
  have hinj : Function.Injective (subIncl π S) := Subtype.val_injective
  have hSn : Nontrivial S.toSubmodule := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    refine hb (Subrepresentation.toSubmodule_injective ?_)
    refine (Submodule.eq_bot_iff _).2 fun v hv => ?_
    exact congrArg Subtype.val (Subsingleton.elim (⟨v, hv⟩ : S.toSubmodule) 0)
  have hrange : LinearMap.range (subIncl π S).toLinearMap = S.toSubmodule := Submodule.range_subtype _
  have hQn : Nontrivial (V ⧸ LinearMap.range (subIncl π S).toLinearMap) := by
    refine Submodule.Quotient.nontrivial_iff.2 ?_
    rw [hrange]
    intro e
    exact ht (Subrepresentation.toSubmodule_injective e)
  have hσ := hsub _ S.toRepresentation (subIncl π S) hinj hSn
  exact GlobalTheory.CompanionTheory.BZSeg.TwoSeg.not_isGeneric_quotRep hψ h1 π _ (subIncl π S) hinj hπ hr hσ
    (hquo _ _ (quotProj π _ (subIncl π S)) (Submodule.mkQ_surjective _) hQn)

theorem lUnlinkedIrr : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.BZSeg.StdSubGeneric k → GlobalTheory.BZSeg.StdQuotGeneric k → GlobalTheory.BZSeg.WhitRankStd k →
    GlobalTheory.BZSeg.ProdIrrFiniteLength k → GlobalTheory.BZSeg.LUnlinkedIrr k := by
  intro k _ _ _ _ hS hQ hR _ h N Δ x hd hun hL
  obtain ⟨ψ, hψ, h1⟩ := exists_continuous_addChar_ne_one k
  haveI := GlobalTheory.CompanionTheory.AdjQuot.nontrivial_prodIrr x hd
  exact isIrreducible_of_generic hψ h1 (prodIrr x hd) (isSmooth_prodIrr x hd) (hR ψ hψ h1 h N x hd)
    (fun W _ _ σ f hf hW => hS h N Δ x hd hL (fun i j _ hp => hun i j hp.1) W σ f hf hW)
    (fun W _ _ τ f hf hW => hQ h N Δ x hd hL (fun i j _ hp => hun j i hp.1) W τ f hf hW)

end GlobalTheory.CompanionTheory.BZSeg.Unlinked

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedCharacterUniformizerPower
section
noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom

namespace GlobalTheory.CompanionTheory.LFUDom

theorem mp_uniformizerUnit_zpow_half (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (m t : ℤ) :
    Ad3.mp (uniformizerUnit F ^ m) ((t : ℂ) / 2) = sqrtQ F ^ (-(t * m)) := by
  set r : ℝ := (NNReal.sqrt (qF F : NNReal) : ℝ) with hr
  have hq0 : (0 : ℝ) < residueCard F := by
    exact_mod_cast zero_lt_one.trans one_lt_residueCard
  have hrq : r ^ 2 = (residueCard F : ℝ) := by
    rw [hr, ← NNReal.coe_pow, NNReal.sq_sqrt]
    simp [qF, residueCard]
  have hr0 : 0 < r := by
    rcases (NNReal.coe_nonneg (NNReal.sqrt (qF F : NNReal))).lt_or_eq with h | h
    · exact h
    · exfalso
      have : r = 0 := h.symm
      rw [this] at hrq
      simp at hrq
      exact hq0.ne' (by exact_mod_cast hrq.symm)
  have hord : ord (((uniformizerUnit F ^ m : Fˣ)) : F) = m := by
    rw [ord_units_zpow, coe_uniformizerUnit, ord_uniformizer (irreducible_uniformizer F), mul_one]
  have hmod : ((modulus (((uniformizerUnit F ^ m : Fˣ)) : F) : NNReal) : ℝ) = r ^ (-(2 * m)) := by
    rw [modulus_of_ne_zero (Units.ne_zero _), hord, NNReal.coe_zpow, NNReal.coe_natCast, ← hrq,
      ← zpow_natCast, ← _root_.zpow_mul]
    norm_num
  have hpow : (r ^ (-(2 * m))) ^ ((t : ℝ) / 2) = r ^ (-(t * m)) := by
    rw [← Real.rpow_intCast, ← Real.rpow_mul hr0.le, ← Real.rpow_intCast]
    congr 1
    push_cast
    ring
  have hcast : ((t : ℂ) / 2) = (((t : ℝ) / 2 : ℝ) : ℂ) := by push_cast; rfl
  have hnn : 0 ≤ r ^ (-(2 * m)) := (zpow_pos hr0 _).le
  unfold Ad3.mp
  rw [hmod, hcast, ← Complex.ofReal_cpow hnn, hpow, Complex.ofReal_zpow]
  rfl

end GlobalTheory.CompanionTheory.LFUDom
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilRepresentationFourierCoefficientStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_representation_fourier_coefficient : ∀ {D : D7} {n r t : ℕ} (hP : PartFT) {hn : r + t = n} (M : Maps D hn) (V : HSp D) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (hη : ResEta D χ V.rank) {θ : InfFam D} (hθ : IsInfFam θ) {μ : Measure (Mx D V.rank n)} (hμ : ∃ 𝓕, IsCovolOne (ratMx D V.rank n) μ 𝓕) {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} (hω : IsWeilSch ψ χ θ V μ ω) {μr : Measure (Mx D V.rank r)} (hμr : ∃ 𝓕, IsCovolOne (ratMx D V.rank r) μr 𝓕) {μt : Measure (Mx D V.rank t)} (hμt : ∃ 𝓕, IsCovolOne (ratMx D V.rank t) μt 𝓕) (Φ : schwartzA θ V.rank n) {nb : hermA D t → G D t} (hnb : IsNMap nb) {w : G D t} (hw : IsW w) (b : hermA D t) (y : Mx D r t) (x : Mx D V.rank r), (ω (M.sh y * M.emb (w * nb b) * 1) Φ).1 (jn hn x 0) = ∫ v, pch ψ b.1 (ip V v v) * Φ.1 (jn hn x v) * ψ (trA (Matrix.trace (ip V (mm x y) v))) ∂μt := by
  first | exact @GlobalTheory.CompanionTheory.CellVal.weil_translate_frame | exact GlobalTheory.CompanionTheory.CellVal.weil_translate_frame | (intros; apply GlobalTheory.CompanionTheory.CellVal.weil_translate_frame <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilRepresentationThetaIntegralStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_representation_theta_integral : ∀ {D : D7} {n r t : ℕ} (hP : PartFT) {hn : r + t = n} (M : Maps D hn) (m : Meas D r t) (V : HSp D) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (hη : ResEta D χ V.rank) {θ : InfFam D} (hθ : IsInfFam θ) {μ : Measure (Mx D V.rank n)} (hμ : ∃ 𝓕, IsCovolOne (ratMx D V.rank n) μ 𝓕) {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} (hω : IsWeilSch ψ χ θ V μ ω) {μr : Measure (Mx D V.rank r)} (hμr : ∃ 𝓕, IsCovolOne (ratMx D V.rank r) μr 𝓕) {μt : Measure (Mx D V.rank t)} (hμt : ∃ 𝓕, IsCovolOne (ratMx D V.rank t) μt 𝓕) (b₀ : HermE D r) {fib : Measure (Mx D V.rank r)} (hfib : IsFib ψ θ V b₀ μr m.lz fib) (Φ : schwartzA θ V.rank n) (g : G D n), Wz M m ψ b₀ (fun g => (ω g Φ).1 0) g = ∫ x, (ω g Φ).1 (jn hn x 0) ∂fib := by
  first | exact @GlobalTheory.CompanionTheory.WzFib.wz_eq_fib | exact GlobalTheory.CompanionTheory.WzFib.wz_eq_fib | (intros; apply GlobalTheory.CompanionTheory.WzFib.wz_eq_fib <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerTorusValueFormulaHolds
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom

namespace GlobalTheory.CompanionTheory.LFUDom

theorem whittaker_torus_value_formula (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F]
    (ψ : AddChar F Circle) (hψ : Ad3.IsStd ψ) (ν : Fˣ →* ℂˣ) (a b : ℤ) :
    (b ≤ a → Ad3.LFS.s2 ψ ν (torusPow F 2 ![a, b]) =
      sqrtQ F ^ (-(a - b)) * evalAt ![ν (unifUnit F), (ν (unifUnit F))⁻¹] (schur ![a, b])) ∧
    (a < b → Ad3.LFS.s2 ψ ν (torusPow F 2 ![a, b]) = 0) := by
  have hψ₀ : ∀ x ∈ 𝒪[F], (Circle.coeHom.compAddChar ψ) x = 1 := by
    intro x hx
    obtain ⟨hc, h1, h0⟩ := hψ
    have ht := isTrivialOn_addCharConductor hc h1
    rw [h0] at ht
    have := ht x (mem_valBall_zero_iff.2 hx)
    show ((ψ x : Circle) : ℂ) = 1
    rw [this, Circle.coe_one]
  have hanti : Antitone (![a, b] : Fin 2 → ℤ) ↔ b ≤ a := by
    constructor
    · intro h
      simpa using h (show (0 : Fin 2) ≤ 1 by decide)
    · intro h i j hij
      fin_cases i <;> fin_cases j <;> simp_all
  have hrho : rhoPair (![a, b] : Fin 2 → ℤ) = a - b := by
    simp [rhoPair, Fin.sum_univ_two]
    ring
  have key := sphericalWhittaker_torusPow hψ₀ ![ν (unifUnit F), ν⁻¹ (unifUnit F)] ![a, b]
  rw [MonoidHom.inv_apply] at key
  unfold Ad3.LFS.s2
  rw [MonoidHom.inv_apply, key]
  constructor
  · intro h
    rw [if_pos (hanti.2 h), halfModulus_eq, hrho]
  · intro h
    rw [if_neg (fun h' => absurd (hanti.1 h') (not_le.2 h))]

end GlobalTheory.CompanionTheory.LFUDom
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerTwoBlockInjectiveIrreducibleStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.CompanionTheory.BZNuPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_two_block_injective_irreducible : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (d : Fin 2 → ℕ) (X : Type) [AddCommGroup X] [Module ℂ X]
    (J : Representation ℂ (Levi k fun a => Fin (d a)) X), IsSmooth J → HasFiniteLength J → Nontrivial (X ⧸ whitKer ψ d J) →
    ∃ (S : IrrRep (GL (Fin (d 0)) k)) (f : S.ρ.IntertwiningMap (whit2 ψ d J)), Function.Injective f := by
  first | exact @GlobalTheory.CompanionTheory.BZNuPair.WhitSub.exists_irr_sub | exact GlobalTheory.CompanionTheory.BZNuPair.WhitSub.exists_irr_sub | (intros; apply GlobalTheory.CompanionTheory.BZNuPair.WhitSub.exists_irr_sub <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZetaIntegralAbsoluteConvergenceStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zeta_integral_absolute_convergence : Ad3.R.AdelicThetaPoissonSummation := by
  first | exact @GlobalTheory.CompanionTheory.RankinSelberg.theta_functional_equation | exact GlobalTheory.CompanionTheory.RankinSelberg.theta_functional_equation | (intros; apply GlobalTheory.CompanionTheory.RankinSelberg.theta_functional_equation <;> assumption)
end

