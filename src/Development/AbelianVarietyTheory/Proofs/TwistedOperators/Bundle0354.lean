import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0336
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0012
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryPart
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralMulRightOfCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0339
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0145
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0191
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0192
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0199
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0193
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodAtReductionConjugatedUnitaryElement
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDimensionalCoeffSpan
section
namespace GlobalTheory.CoefficientSpanFiniteDimensional

theorem dual_apply_eq_sum {W ι : Type} [AddCommGroup W] [Module ℂ W] [Fintype ι] (b : Module.Basis ι ℂ W)
    (ℓ : Module.Dual ℂ W) (w : W) (A : W →ₗ[ℂ] W) :
    ℓ (A w) = ∑ j, ∑ i, (b.repr w j * ℓ (b i)) * b.repr (A (b j)) i := by
  conv_lhs => rw [← b.sum_repr w]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, map_smul]
  conv_lhs => rw [← b.sum_repr (A (b j))]
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul, smul_eq_mul]
  ring

theorem finiteDimensional_coeffSpan {K W : Type} [Group K] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ K W) : FiniteDimensional ℂ ↥(GlobalTheory.Published.AutFin.coeffSpan ρ) := by
  classical
  let b := Module.finBasis ℂ W
  let e : Fin (Module.finrank ℂ W) × Fin (Module.finrank ℂ W) → (K → ℂ) :=
    fun p k => b.repr (ρ k (b p.2)) p.1
  haveI : FiniteDimensional ℂ ↥(Submodule.span ℂ (Set.range e)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range e)
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range e)) (Submodule.span_le.mpr ?_)
  rintro f ⟨ℓ, w, rfl⟩
  have h : (fun k => ℓ (ρ k w)) = ∑ j, ∑ i, (b.repr w j * ℓ (b i)) • e (i, j) := by
    funext k
    rw [dual_apply_eq_sum b ℓ w (ρ k)]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, e]
  rw [h]
  exact Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, j), rfl⟩)

end GlobalTheory.CoefficientSpanFiniteDimensional
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePartLocalToFiniteAdelicComponentNeStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finitePart_localToFiniteAdelic_component_ne : ∀ {D : D7} (V : HSp D) {v u : HeightOneSpectrum (𝓞 D.host.F)}, u ≠ v → ∀ (g : Gv V v), (Formalism.IndefR.Lev.finE V (locFin V v g : GA D V)).val.map (Formalism.UG.prV (E := D.host.E) u) = 1 := by
  first | exact @GlobalTheory.LocFinComp.finE_locFin_map_prV_ne | exact GlobalTheory.LocFinComp.finE_locFin_map_prV_ne | (intros; apply GlobalTheory.LocFinComp.finE_locFin_map_prV_ne <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePartLocalToFiniteAdelicComponentSelfStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finitePart_localToFiniteAdelic_component_self : ∀ {D : D7} (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (g : Gv V v), (Formalism.IndefR.Lev.finE V (locFin V v g : GA D V)).val.map (Formalism.UG.prV (E := D.host.E) v) = (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram g).val.map (Algebra.TensorProduct.comm D.host.F (Fv D.host.F v) D.host.E) := by
  first | exact @GlobalTheory.FinLocSelf.finE_locFin_map_prV | exact GlobalTheory.FinLocSelf.finE_locFin_map_prV | (intros; apply GlobalTheory.FinLocSelf.finE_locFin_map_prV <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinprodFiniteHeightTransposeGramUnitaryLe
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.SquareAgree.FinHeightBound

open GlobalTheory.AdelicU

variable {D : D7}

def cst (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : NNReal :=
  max 1 (Finset.univ.sup fun k : Fin (Module.finrank D.host.F D.host.E) =>
    absFin D.host.F v ((1 : Fv D.host.F v) ⊗ₜ[D.host.F] (Module.finBasis D.host.F D.host.E k)))

theorem one_le_cst (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : 1 ≤ cst D v := le_max_left _ _

theorem compFin_eq (v : HeightOneSpectrum (𝓞 D.host.F)) (y : AF D.host.F ⊗[D.host.F] D.host.E) :
    compFin D.host.F D.host.E v y =
      Algebra.TensorProduct.map (evalV D.host.F v) (AlgHom.id D.host.F D.host.E)
        (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x =>
    simp only [compFin, evFin, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
      AlgHom.comp_apply, AlgHom.id_apply]

theorem sum_finCoord (y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :
    ∑ k, GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D y k ⊗ₜ[D.host.F] (Module.finBasis D.host.F D.host.E k) = y := by
  conv_rhs => rw [← (Algebra.TensorProduct.basis (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)
    (Module.finBasis D.host.F D.host.E)).sum_repr y]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rfl

theorem absFin_map_le (v : HeightOneSpectrum (𝓞 D.host.F)) (y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :
    absFin D.host.F v (Algebra.TensorProduct.map (evalV D.host.F v) (AlgHom.id D.host.F D.host.E) y) ≤
      cst D v * Finset.univ.sup fun k => ‖evalV D.host.F v (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D y k)‖₊ := by
  conv_lhs => rw [← sum_finCoord y]
  rw [map_sum]
  refine absFin_sum_le _ v _ _ fun k _ => ?_
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  have e1 : evalV D.host.F v (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D y k) ⊗ₜ[D.host.F] (Module.finBasis D.host.F D.host.E k) =
      (evalV D.host.F v (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D y k) ⊗ₜ[D.host.F] (1 : D.host.E)) *
        ((1 : Fv D.host.F v) ⊗ₜ[D.host.F] (Module.finBasis D.host.F D.host.E k)) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [e1]
  refine (absFin_mul_le _ v _ _).trans ?_
  rw [absFin_tmul_one, mul_comm]
  refine mul_le_mul' ?_ ?_
  · exact le_max_of_le_right (Finset.le_sup (f := fun k : Fin (Module.finrank D.host.F D.host.E) =>
      absFin D.host.F v ((1 : Fv D.host.F v) ⊗ₜ[D.host.F] (Module.finBasis D.host.F D.host.E k))) (Finset.mem_univ k))
  · exact Finset.le_sup (f := fun k => ‖evalV D.host.F v (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D y k)‖₊) (Finset.mem_univ k)

theorem absFin_le (v : HeightOneSpectrum (𝓞 D.host.F)) (y : AF D.host.F ⊗[D.host.F] D.host.E) :
    absFin D.host.F v (compFin D.host.F D.host.E v y) ≤ cst D v * Finset.univ.sup fun k =>
      ‖evalV D.host.F v (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D
        (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) y) k)‖₊ := by
  rw [compFin_eq]
  exact absFin_map_le v _

end GlobalTheory.SquareAgree.FinHeightBound

namespace GlobalTheory.SquareAgree.FinHeightBound

open GlobalTheory.AdelicU

variable {D : D7}

theorem coordNorm_le_finNorm (X : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : GA D X) (a b : Fin X.rank)
    (k : Fin (Module.finrank D.host.F D.host.E)) :
    ‖evalV D.host.F v (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D (finMat D.sp.cm.sig X.gram h a b) k)‖₊ ≤
      GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finNorm X v h := by
  have := Finset.le_sup (f := fun p : Fin X.rank × Fin X.rank × Fin (Module.finrank D.host.F D.host.E) =>
    ‖evalV D.host.F v (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D (finMat D.sp.cm.sig X.gram h p.1 p.2.1) p.2.2)‖₊)
    (Finset.mem_univ (a, b, k))
  dsimp only at this
  unfold GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finNorm
  exact this

theorem normFin_reindex_le (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) (v : HeightOneSpectrum (𝓞 D.host.F))
    (h : GA D X) :
    normFin D.host.F v ((reindex e e (Formalism.L2.Theta.mt X h)).map (compFin D.host.F D.host.E v)) ≤
      cst D v * GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finNorm X v h := by
  refine (normFin_le_iff D.host.F v).2 fun i j => ?_
  rw [Matrix.map_apply, reindex_apply, Matrix.submatrix_apply]
  have hfm : Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)
      (Formalism.L2.Theta.mt X h (e.symm i) (e.symm j)) = finMat D.sp.cm.sig X.gram h (e.symm i) (e.symm j) := rfl
  have h1 := absFin_le v (Formalism.L2.Theta.mt X h (e.symm i) (e.symm j))
  rw [hfm] at h1
  have h2 := Finset.sup_le (s := Finset.univ) fun k _ => coordNorm_le_finNorm X v h (e.symm i) (e.symm j) k
  exact h1.trans (mul_le_mul' le_rfl h2)

theorem kapX_inv (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ) (h : GA D X) : (kapX X e hJ h).1⁻¹ = (kapX X e hJ h⁻¹).1 := by
  show (Units.map _ (Formalism.L2.Theta.matHom X h))⁻¹ = Units.map _ (Formalism.L2.Theta.matHom X h⁻¹)
  rw [map_inv, map_inv]

theorem coe_bc_kapX (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ) (h : GA D X) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    ((Formalism.UG.bc (compFin D.host.F D.host.E v) (kapX X e hJ h).1 : GL (Fin d) _) : Matrix (Fin d) (Fin d) _) =
      (reindex e e (Formalism.L2.Theta.mt X h)).map (compFin D.host.F D.host.E v) := by
  rw [← mat_kapX X e hJ h]
  rfl

theorem htFin_kapX_le (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ) (h : GA D X) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    htFin D.host.F v (Formalism.UG.bc (compFin D.host.F D.host.E v) (kapX X e hJ h).1) ≤
      cst D v * GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finHt X v h := by
  have h1 := normFin_reindex_le X e v h
  have h2 := normFin_reindex_le X e v h⁻¹
  unfold htFin htOf GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finHt
  rw [← map_inv, kapX_inv, coe_bc_kapX, coe_bc_kapX]
  refine max_le ?_ (max_le ?_ ?_)
  · exact (one_le_cst D v).trans (le_mul_of_one_le_right' (le_max_left _ _))
  · exact h1.trans (mul_le_mul' le_rfl (le_max_of_le_right (le_max_left _ _)))
  · exact h2.trans (mul_le_mul' le_rfl (le_max_of_le_right (le_max_right _ _)))

theorem cst_mulSupport_finite (D : D7) : Function.HasFiniteMulSupport (cst D) := by
  have h : ∀ k : Fin (Module.finrank D.host.F D.host.E), ∀ᶠ v in Filter.cofinite,
      absFin D.host.F v ((1 : Fv D.host.F v) ⊗ₜ[D.host.F] (Module.finBasis D.host.F D.host.E k)) ≤ 1 := by
    intro k
    refine (eventually_absFin_le_one D.host.F
      ((1 : AF D.host.F) ⊗ₜ[D.host.F] (Module.finBasis D.host.F D.host.E k))).mono fun v hv => ?_
    have e1 : compFin D.host.F D.host.E v ((1 : AF D.host.F) ⊗ₜ[D.host.F] (Module.finBasis D.host.F D.host.E k)) =
        (1 : Fv D.host.F v) ⊗ₜ[D.host.F] (Module.finBasis D.host.F D.host.E k) := by
      simp only [compFin, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, map_one,
        AlgHom.id_apply]
    rwa [e1] at hv
  refine (Filter.eventually_cofinite.1 (Filter.eventually_all.2 h)).subset fun v hv hv' => hv ?_
  exact max_eq_left (Finset.sup_le fun k _ => hv' k)

end GlobalTheory.SquareAgree.FinHeightBound

namespace GlobalTheory.SquareAgree

open GlobalTheory.AdelicU GlobalTheory.SquareAgree.FinHeightBound

theorem finprod_htFin_kapX_le : ∀ (D : D7) (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d)
    {J : Matrix (Fin d) (Fin d) D.host.E} (hJ : J = D.host.xi0 • reindex e e X.gramᵀ), ∃ C : NNReal,
    ∀ h : GA D X, ∏ᶠ v, GlobalTheory.AdelicU.htFin D.host.F v
      (Formalism.UG.bc (GlobalTheory.AdelicU.compFin D.host.F D.host.E v) (kapX X e hJ h).1) ≤
      C * ∏ᶠ v, GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finHt X v h := by
  intro D X d e J hJ
  refine ⟨∏ᶠ v, cst D v, fun h => ?_⟩
  have hc := cst_mulSupport_finite D
  have hf : Function.HasFiniteMulSupport fun v => GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finHt X v h :=
    GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finHt_mulSupport_finite X h
  rw [← finprod_mul_distrib hc hf]
  refine finprod_le_finprod (finite_mulSupport_htFin D.host.F (kapX X e hJ h).1) (fun _ => bot_le) ?_
    (fun v => htFin_kapX_le X e hJ h v)
  exact (hc.union hf).subset (Function.mulSupport_mul _ _)

end GlobalTheory.SquareAgree
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstRowTowerMultiplicitySpacesOfArrow
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SepRows

theorem rowTower_of_step : RowModels → RowStep → RowTower := by
  intro hmod hstep D q hs T L μ0 hL sc hc G W M hM M₀ h₀ n
  induction n with
  | zero =>
    intro h
    refine ⟨parB (Ptw D) 0, M₀, (parRow_zero D sc.cGap).symm, h₀, fun _ w => w, fun t ht Φ => ⟨t, ht, fun ρ w => ⟨trivial, rfl⟩⟩⟩
  | succ n ih =>
    intro h
    obtain ⟨S, MA, hS, hA, vec, hvec⟩ := ih (Nat.le_of_succ_le h)
    obtain ⟨MB, hB⟩ := hmod D q hs T L μ0 hL sc hc G W M hM (n + 1) h
    obtain ⟨It, hIt⟩ := hstep D q hs T L μ0 hL sc hc G W M hM n h S _ MA MB hS rfl hA hB
    refine ⟨_, MB, rfl, hB, fun ρ w => It (ρ ⟨n, h⟩) (vec ρ w), fun t ht Φ => ?_⟩
    obtain ⟨F, hF, hF'⟩ := hvec t ht Φ
    obtain ⟨F', hF1, hF2⟩ := hIt F hF (Φ ⟨n, h⟩)
    refine ⟨F', hF1, fun ρ w => ?_⟩
    obtain ⟨h1, h2⟩ := hF' ρ w
    obtain ⟨h3, h4⟩ := hF2 (ρ ⟨n, h⟩) (vec ρ w)
    rw [← h2] at h3 h4
    exact ⟨⟨h1, h3⟩, h4⟩

end GlobalTheory.SepRows
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FixedOfForallLocalSubgroupFixedFiniteAdelic
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.TrIdem

noncomputable section

namespace GlobalTheory.TrIdem

theorem fixed_of_forall_finLoc_mem : ∀ (D : D7) (V : HSp D) (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), GlobalTheory.PRep.IsSmooth σ → ∀ (K' : ∀ v, Subgroup (GLoc D.sp.cm.sig V.gram v)), (∀ v, K' v ≤ Kv V v) → ∀ x : W, (∀ v, ∀ k ∈ K' v, σ (locFin V v k) x = x) → ∀ g : GfC V, (∀ v, finLoc V v g ∈ K' v) → σ g x = x := by
  intro D V W _ _ σ hσ K' hK' x hx g hg
  have fl_self : ∀ a (y : GLoc D.sp.cm.sig V.gram a), finLoc V a (locFin V a y) = y :=
    fun a y => proj_emb_self _ _ a y
  have fl_ne : ∀ v a, v ≠ a → ∀ (y : GLoc D.sp.cm.sig V.gram a), finLoc V v (locFin V a y) = 1 :=
    fun v a h y => proj_emb_ne _ _ h y
  let St : Subgroup (GfC V) :=
    { carrier := {k | σ k x = x}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, Module.End.mul_apply, hb, ha]
      one_mem' := by simp
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        have e : σ a⁻¹ (σ a x) = x := by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
        rwa [ha] at e }
  have hSt : IsOpen (St : Set (GfC V)) := hσ x
  let U : Subgroup (GA D V) := St.comap (toFin V)
  have hU : IsOpen (U : Set (GA D V)) := hSt.preimage (continuous_toFin V)
  obtain ⟨S, hS⟩ := GlobalTheory.PlaceGen.exists_levelOff_le D.sp.cm.sig V.gram (frameLat V) U hU
  have key : ∀ k : GfC V, (∀ v ∈ S, finLoc V v k = 1) → (∀ v, v ∉ S → finLoc V v k ∈ Kv V v) → σ k x = x := by
    intro k h1 h2
    have hk : (k : GA D V) ∈ levelOff D.sp.cm.sig V.gram (frameLat V) S := mem_levelOff.2 ⟨k.2, h1, h2⟩
    have h := hS hk
    have e : toFin V (k : GA D V) = k := toFin_coe k
    change σ (toFin V (k : GA D V)) x = x at h
    rwa [e] at h
  have step : ∀ T : Finset (HeightOneSpectrum (𝓞 D.host.F)), ∀ k : GfC V, (∀ v, finLoc V v k ∈ K' v) →
      (∀ v ∈ S, v ∉ T → finLoc V v k = 1) → σ k x = x := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro k hk h1
      exact key k (fun v hv => h1 v hv (Finset.notMem_empty v)) (fun v _ => hK' v (hk v))
    | insert a T ha ih =>
      intro k hk h1
      set k' := locFin V a (finLoc V a k)⁻¹ * k with hk'
      have hfix : σ k' x = x := by
        refine ih k' (fun v => ?_) (fun v hv hvT => ?_)
        · by_cases h : v = a
          · subst h
            simp [k', map_mul, fl_self]
          · simp only [k', map_mul, fl_ne v a h, one_mul]
            exact hk v
        · by_cases h : v = a
          · subst h
            simp [k', map_mul, fl_self]
          · simp only [k', map_mul, fl_ne v a h, one_mul]
            exact h1 v hv (by simp [h, hvT])
      have hkk : k = locFin V a (finLoc V a k) * k' := by
        simp [k', ← mul_assoc, ← map_mul]
      rw [hkk, map_mul, Module.End.mul_apply, hfix]
      exact hx a _ (hk a)
  exact step S g hg (fun v hv hvS => absurd hv hvS)

end GlobalTheory.TrIdem
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiBesselGroupsClosedHaarProduct
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MixPer

theorem jacGrp_besGrp_haar : ∀ (D : D7) (S S₀ A L : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) (ν : Measure (flagN d)) (𝓝 : Set (flagN d)), GlobalTheory.Per.IsUnitN S d.e ν 𝓝 → (IsClosed (jacGrp d : Set (GA D S)) ∧ ∀ μ : Measure (GA D S₀), μ.IsHaarMeasure → (semiMeas (flagN d) d.emb0 μ ν).IsHaarMeasure) ∧ IsClosed (besGrp d o : Set (GA D S)) ∧ ∀ μ : Measure (GA D A), μ.IsHaarMeasure → (semiMeas (flagN d) (embA d o) μ ν).IsHaarMeasure := by
  intro D S S₀ A L ρ d o ν 𝓝 hν
  have hNc : IsClosed (flagN d : Set (GA D S)) := GlobalTheory.Mem.TrueRecord.isClosed_NFlag S (isIsoSub_e d)
  have hνH : ν.IsHaarMeasure := hν.1
  have hcA : Continuous (embA d o) := by
    have h1 : Continuous (fun h : GA D A => o.emb (h, 1)) := by
      have := o.continuous_emb
      fun_prop
    exact d.continuous_embed.comp h1
  have hnA : ∀ n ∈ flagN d, ∀ h, embA d o h * n * (embA d o h)⁻¹ ∈ flagN d := fun n hn h =>
    GlobalTheory.MixPer.witt_anisotropic_group_normalizes_flag_unipotent D S S₀ ρ d n hn (o.emb (h, 1))
  have hmA : ∀ h, ν.map (fun n : flagN d => embA d o h * n.1 * (embA d o h)⁻¹) = ν.map Subtype.val := fun h =>
    GlobalTheory.FlagModulus.map_conj_smallerUnitary_flagUnipotent_haar D S S₀ ρ d ν hνH (o.emb (h, 1))
  refine ⟨⟨GlobalTheory.jacGrp_isClosed D S S₀ ρ d, fun μ hμ => ?_⟩, GlobalTheory.BesClosed.besGrp_isClosed D S S₀ A L ρ d o, fun μ hμ => ?_⟩
  · have a := GlobalTheory.MixPer.semiMeas_isMulLeftInvariant (flagN d) d.emb0 hNc d.continuous_embed (GlobalTheory.MixPer.witt_anisotropic_group_normalizes_flag_unipotent D S S₀ ρ d) (GlobalTheory.JacProj.exists_continuous_proj D S S₀ ρ d) μ ν hμ hνH
      (GlobalTheory.FlagModulus.map_conj_smallerUnitary_flagUnipotent_haar D S S₀ ρ d ν hνH)
    obtain ⟨b, c⟩ := GlobalTheory.MixPer.semiMeas_finite_on_compacts_and_open_pos (flagN d) d.emb0 hNc d.continuous_embed (GlobalTheory.MixPer.witt_anisotropic_group_normalizes_flag_unipotent D S S₀ ρ d) (GlobalTheory.JacProj.exists_continuous_proj D S S₀ ρ d) μ ν hμ hνH
      (GlobalTheory.FlagModulus.map_conj_smallerUnitary_flagUnipotent_haar D S S₀ ρ d ν hνH)
    exact { toIsFiniteMeasureOnCompacts := b, toIsMulLeftInvariant := a, toIsOpenPosMeasure := c }
  · have a := GlobalTheory.MixPer.semiMeas_isMulLeftInvariant (flagN d) (embA d o) hNc hcA hnA (GlobalTheory.BesProj.exists_continuous_proj D S S₀ A L ρ d o) μ ν hμ hνH hmA
    obtain ⟨b, c⟩ := GlobalTheory.MixPer.semiMeas_finite_on_compacts_and_open_pos (flagN d) (embA d o) hNc hcA hnA (GlobalTheory.BesProj.exists_continuous_proj D S S₀ A L ρ d o) μ ν hμ hνH hmA
    exact { toIsFiniteMeasureOnCompacts := b, toIsMulLeftInvariant := a, toIsOpenPosMeasure := c }

end GlobalTheory.MixPer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodAtReductionConjugatedUnitaryElementStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodAt_reduction_conjugated_unitary_element : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (t : GA D (Yc D 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∃ (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1), (∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧ (∀ g, D.what₂.embLL ((idemOf A.X).coeff g) = D.ntypes.e0.coeff ((R.eG.trans cG) g)) ∧ (∀ kv, R.C.P.Div kv.1 (plg kv).1) ∧ ∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) ((R.eG.trans cG) g kv)) → IdempotentRealFixed D → t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → IsFrame (finE (Yc D 0) t * R.βY 0) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∀ k ∈ X.B.I.Kset, GoodAt X k (cG (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (kap X h t k)))) := by
  first | exact @GlobalTheory.RedFrame.goodAt_kap_red | exact GlobalTheory.RedFrame.goodAt_kap_red | (intros; apply GlobalTheory.RedFrame.goodAt_kap_red <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GroupConvolutionNormalizedIndicatorSelf
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.TrIdem

noncomputable section
namespace GlobalTheory.TrIdem

theorem conv_normInd_self (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (H : Subgroup G)
    (hHo : IsOpen (H : Set G)) (hHc : IsCompact (H : Set G)) :
    conv μ (normInd μ (H : Set G)) (normInd μ (H : Set G)) = normInd μ (H : Set G) := by
  have hm : MeasurableSet (H : Set G) := hHo.measurableSet
  have hpos : μ (H : Set G) ≠ 0 := (hHo.measure_pos μ ⟨1, H.one_mem⟩).ne'
  have hfin : μ (H : Set G) ≠ ⊤ := hHc.measure_lt_top.ne
  have hr : (μ.real (H : Set G) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero, measureReal_def]
    exact (ENNReal.toReal_pos hpos hfin).ne'
  funext y
  simp only [conv, normInd]
  set c : ℂ := (μ.real (H : Set G) : ℂ)⁻¹ with hc
  by_cases hy : y ∈ H
  · have key : (fun x => (c • (H : Set G).indicator (1 : G → ℂ)) x * (c • (H : Set G).indicator (1 : G → ℂ)) (x⁻¹ * y))
        = (H : Set G).indicator (fun _ => c * c) := by
      funext x
      by_cases hx : x ∈ H
      · have : x⁻¹ * y ∈ H := H.mul_mem (H.inv_mem hx) hy
        simp [Set.indicator_of_mem (show x ∈ (H : Set G) from hx),
          Set.indicator_of_mem (show x⁻¹ * y ∈ (H : Set G) from this)]
      · simp [Set.indicator_of_notMem (show x ∉ (H : Set G) from hx)]
    rw [key, integral_indicator_const _ hm]
    simp only [Pi.smul_apply, Set.indicator_of_mem (show y ∈ (H : Set G) from hy), Pi.one_apply, smul_eq_mul, mul_one]
    rw [Complex.real_smul, hc]
    field_simp
  · have key : (fun x => (c • (H : Set G).indicator (1 : G → ℂ)) x * (c • (H : Set G).indicator (1 : G → ℂ)) (x⁻¹ * y))
        = fun _ => 0 := by
      funext x
      by_cases hx : x ∈ H
      · have : x⁻¹ * y ∉ H := fun h => hy (by simpa using H.mul_mem hx h)
        simp [Set.indicator_of_notMem (show x⁻¹ * y ∉ (H : Set G) from this)]
      · simp [Set.indicator_of_notMem (show x ∉ (H : Set G) from hx)]
    rw [key, integral_zero]
    simp [Set.indicator_of_notMem (show y ∉ (H : Set G) from hy)]

end GlobalTheory.TrIdem
end
end

