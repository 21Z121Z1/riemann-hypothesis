import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsMatrixCoefficientsEqFockRepresentatio
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsRealPlaceActAsFockPolynomials
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0231
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0218
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Formalism.PeriodIntegrals.Bundle0022
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.Bundle0003
import Formalism.RealPlaceAnalysis.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0232
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0196
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0234
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0171
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCentralIdempotentOfGoodSeriesIdempotent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0106
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HighestWeightFunctionalCharacter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0233
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HyperbolicPairSplitTorus

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsMatrixCoefficientsEqFockRepresentatioStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVectors_matrixCoefficients_eq_fockRepresentation : ∀ (p q r s n : ℕ) (T₀ : GrpData (p * r + q * s) (p * s + q * r)) (T₁ : GrpData p q) (T₂ : GrpData r s) (F : FockData T₀ T₁ T₂) (ι Z : Type) (G fr : Mn n) (ε : Fin n → Bool) (br : Bool) (e : Ix p q ≃ Fin n) (A : Mn n → (Z → ℂ) → (Z → ℂ)) (pt : MvPolynomial ι ℂ → (Z → ℂ)) (ip : (Z → ℂ) → (Z → ℂ) → ℂ) (Θ : Submodule ℂ (Z → ℂ)) (κ : MvPolynomial ι ℂ ≃ₗ[ℂ] Pol p q r s) (c : ℚ) (m : ℤ) (N : ℝ), 1 ≤ p + q → IsUnit fr → frᴴ * Formalism.REAL.Jm ε * fr = G → SignCompat ε e → (m : ℚ) = 2 * c → Side A pt κ (phiFr fr br e) c (fockAct1 p q r s) → L2UnitaryRepresentationData G A pt ip Θ → Fischer pt ip κ N → Coef F A pt ip κ (phiFr fr br e) m N := by
  first | exact @GlobalTheory.ArchRec.FockCoef.coef_of_side | exact GlobalTheory.ArchRec.FockCoef.coef_of_side | (intros; apply GlobalTheory.ArchRec.FockCoef.coef_of_side <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsRealPlaceActAsFockPolynomialsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVectors_realPlace_act_as_fockPolynomials : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (τ : D.what₂.Tau), IsInfFam θ → ∀ (sS frS : Mn S.rank) (εS : Fin S.rank → Bool) (sT frT : Mn T.rank) (εT : Fin T.rank → Bool), IsFrameOf (gramAt D S τ) sS εS frS → IsFrameOf (gramAt D T τ) sT εT frT → ∀ (aS aT : ℚ) (pt : LPol T.rank S.rank →ₗ[ℂ] (WO S T → ℂ)), Function.Injective pt → LieAt ψ θ τ ω εS frS εT frT aS aT pt → ∀ (p q r s : ℕ) (e : Ix p q ≃ Fin S.rank) (e' : Ix r s ≃ Fin T.rank), SignCompat εS e → SignCompat εT e' → ∀ κ : LPol T.rank S.rank ≃ₗ[ℂ] Pol p q r s, IsPolyIso εS εT e e' κ → Side (actSrc θ ω τ) pt κ (phiFr frS true e) aT (fockAct1 p q r s) ∧ Side (actTgt θ ω τ) pt κ (phiFr frT false e') aS (fockAct2 p q r s) := by
  first | exact @GlobalTheory.ArchRec.SideAt.side_at | exact GlobalTheory.ArchRec.SideAt.side_at | (intros; apply GlobalTheory.ArchRec.SideAt.side_at <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameAdjointPartAtMovedRationalPointRowStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameAdjoint_partAt_movedRationalPoint_row : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ (a : AE D) (k₀ : GA D S), (∃ b : AE D, a * b = e) → GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ → GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a → GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊤ → GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊥ → IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (conjI (GlobalTheory.LiftLevel.liftI Pg Q)) → IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (Ideal.span {2}) → ∀ y : Matrix (Fin S.rank) (Fin T.rank) D.host.E, frMapAdj S T βS βT (GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T y))) = Matrix.of fun i j => GlobalTheory.LiftDat.rowAdj T βT a e (y i) 0 j := by
  first | exact @GlobalTheory.LiftDat.frMapAdj_partAt_actO_finW | exact GlobalTheory.LiftDat.frMapAdj_partAt_actO_finW | (intros; apply GlobalTheory.LiftDat.frMapAdj_partAt_actO_finW <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameCongruentSubOneMulVecMemIdealLatticeComplet
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel ValuativeRel Matrix NumberField
open scoped Pointwise TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.FinPl.FrameCong

variable {D : D7}

theorem intAt_mul_mem {S : HSp D} {L : Lat S} {v : Pl D} {a : AE D} (ha : a ∈ intAt D (· = v))
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L (· = v)) : (fun i => a * y i) ∈ latV S L (· = v) := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, -, c, hc, x, hx, rfl⟩ := hy
    rw [Set.mem_singleton_iff] at hc
    subst hc
    have hint : a * (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) ∈ intAt D (· = v) := by
      refine ⟨Ideal.mul_mem_right _ _ ha.1, ?_⟩
      rw [RingHom.map_mul]
      exact FrameLat.mul_mem_intAE ha.2 (AddSubgroup.subset_closure ⟨α, hα, 1, rfl⟩)
    have h := FrameLat.int_mul_mem hint hx
    have h1 : ∀ i, (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) * incA D (x i) =
        pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x i) := fun i => by
      change _ * ((1 : AF D.host.F) ⊗ₜ[D.host.F] x i) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    simpa only [mul_assoc, h1] using h
  | zero => simp only [Pi.zero_apply, mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => simp only [Pi.add_apply, mul_add]; exact add_mem hx hy
  | neg x _ hx => simp only [Pi.neg_apply, mul_neg]; exact neg_mem hx

theorem inc_mul_mem {S : HSp D} {L : Lat S} {P : Pl D → Prop} {𝔪 : Ideal (𝓞 D.host.E)} {m : 𝓞 D.host.E} (hm : m ∈ 𝔪)
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L P) :
    (fun i => incA D (m : D.host.E) * y i) ∈ latV S (𝔪 • L) P := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, hα0, c, hc, x, hx, rfl⟩ := hy
    rw [Set.mem_singleton_iff] at hc
    subst hc
    refine AddSubgroup.subset_closure ⟨α, hα, hα0, 1, rfl, m • x, Submodule.smul_mem_smul hm hx, ?_⟩
    funext i
    change ((1 : AF D.host.F) ⊗ₜ[D.host.F] (m : D.host.E)) * _ = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul, one_mul]
    rfl
  | zero => simp only [Pi.zero_apply, mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => simp only [Pi.add_apply, mul_add]; exact add_mem hx hy
  | neg x _ hx => simp only [Pi.neg_apply, mul_neg]; exact neg_mem hx

theorem sub_one_mulVec_mem : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (p : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (n : Type) [Fintype n]
    [DecidableEq n] (β : GlobalTheory.FinPl.Frame p S n),
    β.IsLat L (Submodule.pi Set.univ fun _ : n => (1 : Submodule 𝒪[k] k)) → ∀ (𝔪 : Ideal (𝓞 D.host.E)) (d : ℕ),
    (∃ m ∈ 𝔪, ∀ z ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ d, ∃ c ∈ 𝒪[k],
      (z : k) = c * p.pr (incA D ((m : 𝓞 D.host.E) : D.host.E))) →
    ∀ k₀ : GL n 𝒪[k], (∀ i j, (k₀.1 - 1) i j ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ d) →
    ∀ y : Fin S.rank → AE D, y ∈ latV S L (· = p.v) →
    (fun i => p.e * ((mt S (β.gl (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) k₀)) - 1) *ᵥ y) i) ∈
      latV S (𝔪 • L) (· = p.v) := by
  intro D k _ _ _ _ p S L n _ _ β hβ 𝔪 d ⟨m, hm, hmd⟩ k₀ hk y hy
  have hpi : ∀ x : n → k, x ∈ (Submodule.pi Set.univ fun _ : n => (1 : Submodule 𝒪[k] k)) ↔ ∀ j, x j ∈ 𝒪[k] := by
    intro x
    simp only [Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]
    refine forall_congr' fun j => ⟨?_, fun h => ⟨⟨x j, h⟩, rfl⟩⟩
    rintro ⟨z, hz⟩
    rw [← hz]; exact z.2
  set g : GL n k := Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) k₀ with hg
  set Y : Fin S.rank → k := fun i => p.pr (y i) with hY
  set x : n → k := β.b' *ᵥ Y with hx
  have hbx : β.b *ᵥ x = Y := by rw [hx, Matrix.mulVec_mulVec, β.bb', Matrix.one_mulVec]
  have hxint : ∀ j, x j ∈ 𝒪[k] := by
    rw [← hpi, hβ x, hbx]
    simp only [hY, p.sec_pr]
    exact intAt_mul_mem (FrameLat.e_mem_intAt p) hy
  let x₀ : n → 𝒪[k] := fun j => ⟨x j, hxint j⟩
  have hz : ∀ i, ((k₀.1 - 1) *ᵥ x₀) i ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ d := fun i =>
    Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (hk i j)
  choose c hc hcz using fun i => hmd _ (hz i)
  have hgx : (g.val - 1) *ᵥ x = p.pr (incA D (m : D.host.E)) • c := by
    funext i
    rw [Pi.smul_apply, smul_eq_mul, mul_comm, ← hcz i]
    have h1 : g.val - 1 = (k₀.1 - 1).map (algebraMap 𝒪[k] k) := by
      rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
      rfl
    rw [h1]
    exact (RingHom.map_mulVec (algebraMap 𝒪[k] k) (k₀.1 - 1) x₀ i).symm
  have hpr : ∀ i, p.pr (((mt S (β.gl g) - 1) *ᵥ y) i) = p.pr (incA D (m : D.host.E)) * (β.b *ᵥ c) i := by
    intro i
    rw [RingHom.map_mulVec, Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), β.gl_mat g]
    have h2 : β.b * g.val * β.b' - 1 = β.b * (g.val - 1) * β.b' := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, β.bb']
    rw [h2, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    change (β.b *ᵥ ((g.val - 1) *ᵥ x)) i = _
    rw [hgx, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
  have hc' := (hβ c).1 ((hpi c).2 hc)
  have h := inc_mul_mem hm hc'
  have heq : (fun i => p.e * ((mt S (β.gl g) - 1) *ᵥ y) i) =
      fun i => incA D (m : D.host.E) * p.sec ((β.b *ᵥ c) i) := by
    funext i
    rw [← p.sec_pr, hpr, mul_comm (incA D _), FrameLat.sec_mul_right, mul_comm]
  rw [heq]
  exact h

end GlobalTheory.FinPl.FrameCong
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FreeAlgebraLiftMonoidSumStatement
section
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.freeAlgebra_lift_monoid_sum : ∀ {B : Type} [Ring B] [Algebra ℂ B] {X : Type} (f : X → B) (p : FreeAlgebra ℂ X), FreeAlgebra.lift ℂ f p = Finsupp.sum (FreeAlgebra.equivMonoidAlgebraFreeMonoid p).coeff fun (w : FreeMonoid X) (c : ℂ) => c • (w.toList.map f).prod := by
  first | exact @GlobalTheory.freeAlgebra_lift_eq_sum_monomials | exact GlobalTheory.freeAlgebra_lift_eq_sum_monomials | (intros; apply GlobalTheory.freeAlgebra_lift_eq_sum_monomials <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GelfandTraceConjInvertibleScalarMatrixStatement
section
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gelfandTrace_conj_invertible_scalarMatrix : ∀ {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (P : Matrix (Fin n) (Fin n) ℂ), IsUnit P → ∀ k : ℕ, Formalism.REAL.etr (fun a b => ∑ c, ∑ d, (P c a * P⁻¹ b d) • E c d) k = Formalism.REAL.etr E k := by
  first | exact @GlobalTheory.etr_conj_scalar_matrix | exact GlobalTheory.etr_conj_scalar_matrix | (intros; apply GlobalTheory.etr_conj_scalar_matrix <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GluingLawHoldsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gluing_law_holds : ∀ (D : D7) (a b : ℕ), GlueLaw D a b := by
  first | exact @GlobalTheory.Chain.RealIt.GlueProof.glueLaw | exact GlobalTheory.Chain.RealIt.GlueProof.glueLaw | (intros; apply GlobalTheory.Chain.RealIt.GlueProof.glueLaw <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodProjectorLevelMultiplicitySpaceMemGoodRows
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField IsDedekindDomain
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev
open scoped TensorProduct Pointwise

namespace GlobalTheory.ProjLift

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ActPreservesMult : Prop :=
  ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : Datum.InfFam D) (M : DSModel V S) (β : GL (Fin V.rank) (Lev.EAf D))
    (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (g0 : Formalism.L2.DIV.G0 L.Pg L.r),
    ∀ T ∈ Mult θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L)),
      ∃ T' ∈ Mult θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L)), ∀ v, T' v = actG0 V β L g0 (T v)

def FiniteGroupLifts : Prop :=
  ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank)
    (Λ : Submodule (NumberField.RingOfIntegers D.host.E) (Fin V.rank → D.host.E)) (N : ℕ),
    IsBaseFrame V β Λ N → L.Q = ∅ → (∀ PP ∈ L.Pg, ∀ PP' ∈ L.Pg, ¬ IsConjPl PP PP') → LiftsExist V β L

theorem not_isConjPl_of_div {D : D7} (P : Formalism.L2.Host.PiBar D.host) {k k' : Fin 2} {w w' : Pl D.host.E}
    (hw : P.Div k w) (hw' : P.Div k' w') : ¬ IsConjPl w w' := by
  intro hc
  have hov : ∀ {j : Fin 2} {u : Pl D.host.E}, P.Div j u → ((D.host.g j : ℕ) : 𝓞 D.host.E) ∈ u.asIdeal := by
    intro j u hu
    have h1 := P.pb_over j
    rw [← hu] at h1
    have : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g j : ℕ) : 𝓞 D.host.K) ∈ u.asIdeal := h1
    rwa [map_natCast] at this
  have hle : D.host.conj • w.asIdeal ≤ w'.asIdeal := by
    intro y hy
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hy
    obtain ⟨z, hz, hzv⟩ := hc _ hy
    have e : z = y := RingOfIntegers.ext (hzv.trans ((bridge_star_holds D.R D.host _).trans
      (D.host.conj.apply_symm_apply (y : D.host.E))))
    exact e ▸ hz
  have hmax : (D.host.conj • w.asIdeal).IsMaximal := by
    have := w.isPrime
    refine Ideal.IsPrime.isMaximal inferInstance fun h0 => w.ne_bot ?_
    have := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h0
    simpa using this
  have heq : D.host.conj • w.asIdeal = w'.asIdeal := hmax.eq_of_le w'.isPrime.ne_top hle
  have hm := (GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) (D.host.g_prime k) (D.nd.g_split k) w (hov hw)).2.2.2
    (P.pb k) (P.pb_over k) w' ((GlobalTheory.Mem.Chr.conjPl_iff_smul D.host.conj w w').2 heq)
  have hg : D.host.g k = D.host.g k' :=
    (GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) (D.host.g_prime k) (D.nd.g_split k) w' hm.1).1.symm.trans
      (GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k') (D.host.g_prime k') (D.nd.g_split k') w' (hov hw')).1
  obtain rfl : k = k' := by
    have := D.host.g_ne
    fin_cases k <;> fin_cases k' <;> first | rfl | exact absurd hg this | exact absurd hg.symm this
  exact hm.2.1 hw hw'

theorem mult_congr {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : Datum.InfFam D) (M : DSModel V S) {J J' : Set (GA D V)}
    {χ χ' : GA D V → ℂ} (hJ : J = J') (hχ : ∀ k ∈ J, χ k = χ' k) : Mult θ M J χ ≤ Mult θ M J' χ' := by
  subst hJ
  exact Submodule.span_mono fun T h => ⟨h.aut, h.cusp, fun v k hk g => hχ k hk ▸ h.lev v k hk g, h.equiv, h.cont⟩

theorem conv_coeff_of_idem {H : Type} [Group H] [Fintype H] {e : MonoidAlgebra ℂ H} (he : e * e = e) (g : H) :
    ∑ a, e.coeff a * e.coeff (a⁻¹ * g) = e.coeff g := by
  conv_rhs => rw [← he]
  rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype _ _ (by simp)]

theorem sum_act_idem {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (hL : LiftsExist V β L)
    {G : Type} [Group G] [Fintype G] (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ) (hc : ∀ g, ∑ a, c a * c (a⁻¹ * g) = c g)
    {F : GA D V → ℂ} (hF : HasType V β (flag1L L) F) :
    ∑ g, c g • actG0 V β L (eG g) (∑ g', c g' • actG0 V β L (eG g') F) = ∑ g, c g • actG0 V β L (eG g) F := by
  letI I : Fintype (G0 L.Pg L.r) := Fintype.ofEquiv G eG.toEquiv
  have e : ∀ F', ∑ g, c g • actG0 V β L (eG g) F' = ∑ g ∈ @Finset.univ _ I, c (eG.symm g) • actG0 V β L g F' := fun F' =>
    @Fintype.sum_equiv _ _ _ _ I _ eG.toEquiv _ _ fun g => by simp
  rw [e, e]
  refine @GlobalTheory.FlagAction.convIdempotent_act D V β L I hL (fun g => c (eG.symm g)) (fun g => ?_) F hF
  rw [← hc (eG.symm g)]
  exact @Fintype.sum_equiv _ _ _ I _ _ eG.symm.toEquiv _ _ fun a => by simp

section

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem eC_conv (h : R.grp_record) (g : G) :
    ∑ a, RealDat.eC (A := A) D.what₂.embLL a * RealDat.eC (A := A) D.what₂.embLL (a⁻¹ * g) = RealDat.eC (A := A) D.what₂.embLL g := by
  obtain ⟨eR, -, -, h, -⟩ := h
  letI : Fintype (G0g D.nd) := Fintype.ofEquiv G eR.toEquiv
  unfold RealDat.eC
  simp only [h, map_mul, map_inv]
  rw [← conv_coeff_of_idem (GlobalTheory.GoodLatCompare.goodSeriesIdempotent_central_idempotent D).2 (eR g)]
  exact Fintype.sum_equiv eR.toEquiv _ _ fun _ => rfl

theorem thDn_mem_CC (t : T) (x : (R.HX t).H) : R.thDn t x ∈ R.CC t 0 := by
  unfold RealDat.thDn
  rw [LinearMap.comp_apply]
  exact Submodule.coe_mem _

theorem mult_datYt_le (t : T) :
    Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.datYt t 0 R.triv)) (levChi _ (R.βY 0) (R.datYt t 0 R.triv)) ≤
      Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) := by
  have hr : (Yc D 0).rank = D.R.r := by
    rw [D.sp.Y_rank _ (min_le_right _ _)]; simp [Ranks.rankY]
  obtain ⟨h2, h3⟩ := GlobalTheory.levG_twist_trivial_of_rank_eq (Yc D 0) (R.βY 0) D.R.r D.R.t (r_le_Y 0) hr R.Pg (R.Q t) R.triv R.chi (R.xiR t)
  exact mult_congr R.θ (R.MY 0) (congrArg SetLike.coe h2) h3

theorem thDn_mem (t : T) (x : (R.HX t).H) :
    (PiTensorProduct.lift.symm : (SmT (R.MY 0) →ₗ[ℂ] (GA D (Yc D 0) → ℂ)) ≃ₗ[ℂ] MMap (R.MY 0)) (R.thDn t x) ∈
      Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) :=
  mult_datYt_le R t ((mem_multT R.θ (R.MY 0) _ _ _).1 (thDn_mem_CC R t x))

theorem goodRowsProjector_apply_eq_sum (F : GA D (Yc D 0) → ℂ) :
    R.e0 F = ∑ g, RealDat.eC (A := A) D.what₂.embLL g • actG0 (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g) F := by
  unfold RealDat.e0 gaL
  rw [LinearMap.sum_apply]
  rfl

theorem goodProjector_levelMultiplicitySpace_mem_goodRows (hA : ActPreservesMult) {U : MMap (R.MY 0)}
    (hU : U ∈ Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv))) :
    postOn (R.MY 0) R.e0 U ∈ Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) := by
  choose U' hU' hv using fun g => hA R.θ (R.MY 0) (R.βY 0) (R.dat0 R.triv) (R.eG g) U hU
  have e : postOn (R.MY 0) R.e0 U = ∑ g, RealDat.eC (A := A) D.what₂.embLL g • U' g := by
    refine MultilinearMap.ext fun v => ?_
    rw [MultilinearMap.sum_apply]
    refine (goodRowsProjector_apply_eq_sum R (U v)).trans (Finset.sum_congr rfl fun g _ => ?_)
    rw [MultilinearMap.smul_apply, hv]
  rw [e]
  exact Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (hU' g)

theorem lifts_exist_at_base_level (hL : FiniteGroupLifts) (h : R.toLevCh.Is A.μ0) :
    LiftsExist (Yc D 0) (R.βY 0) (R.dat0 R.triv) := by
  obtain ⟨c, hc⟩ := h.βY 0 (lt_of_lt_of_le two_pos D.R.two_le_m)
  refine hL _ _ _ _ _ hc rfl fun w hw w' hw' => ?_
  obtain ⟨k, hk⟩ := (h.Pg w).1 hw
  obtain ⟨k', hk'⟩ := (h.Pg w').1 hw'
  exact not_isConjPl_of_div _ hk hk'

theorem heckeProjector_idempotent_compositeLift (hL : FiniteGroupLifts) (h : R.toLevCh.Is A.μ0) (hr : R.grp_record) {F : GA D (Yc D 0) → ℂ}
    (hF : HasType (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv)) F) : R.e0 (R.e0 F) = R.e0 F := by
  rw [goodRowsProjector_apply_eq_sum, goodRowsProjector_apply_eq_sum]
  exact sum_act_idem _ _ _ (lifts_exist_at_base_level R hL h) R.eG _ (eC_conv R hr) hF

end

theorem projLiftExists_of (hA : ActPreservesMult) (hL : FiniteGroupLifts) : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveLiftExistence.ProjLiftExists := by
  intro D G _ _ Pl0 T A Ks _ _ _ R h hr hE t
  refine (GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveLiftExistence.exists_represents_iff hE t).2 fun x => ?_
  have h1 := thDn_mem R t x
  rw [GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveLiftExistence.projLift_apply]
  refine (mem_goodPart _ _ _ _ _ _).2 ⟨goodProjector_levelMultiplicitySpace_mem_goodRows R hA h1, fun v => ?_⟩
  exact heckeProjector_idempotent_compositeLift R hL h hr (GlobalTheory.hasType_of_mem_mult R.θ (R.MY 0) (R.βY 0) _ _ h1 v)

theorem projLiftExists : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveLiftExistence.ProjLiftExists :=
  projLiftExists_of GlobalTheory.T.levelMultiplicity_stable_under_action GlobalTheory.T.finite_group_lifts_to_parahoric_level

end GlobalTheory.ProjLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HighestWeightFunctionalCharacterStatement
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.highest_weight_functional_character : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V) (χ : Fin n → ℂ), GlRel E → (∀ (Y : ℂ) (v : V), qdet E (Y + ((n : ℂ) - 1) / 2) v = (∏ s, (Y + χ s)) • v) → ∀ (p q : Fin n), p ≠ q → ∀ (ℓ : V →ₗ[ℂ] ℂ) (α β : ℂ), ℓ ≠ 0 → (∀ b, b ≠ p → ∀ v, ℓ (E p b v) = 0) → (∀ a, a ≠ q → ∀ v, ℓ (E a q v) = 0) → (∀ v, ℓ (E p p v) = α * ℓ v) → (∀ v, ℓ (E q q v) = β * ℓ v) → ∃ i j, i ≠ j ∧ χ i = α - ((n : ℂ) - 1) / 2 ∧ χ j = β + ((n : ℂ) - 1) / 2 := by
  first | exact @GlobalTheory.CapelliRoots.two_roots_of_parabolic_functional | exact GlobalTheory.CapelliRoots.two_roots_of_parabolic_functional | (intros; apply GlobalTheory.CapelliRoots.two_roots_of_parabolic_functional <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HyperbolicPairChangeOfBasisStatement
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperbolic_pair_change_of_basis : ∀ (n : ℕ) (ε : Fin n → Bool) (e : Fin n → ℂ), e ≠ 0 → star e ⬝ᵥ (Jm ε *ᵥ e) = 0 → ∃ (P : Matrix (Fin n) (Fin n) ℂ) (p q : Fin n) (c : ℂ), IsUnit P ∧ p ≠ q ∧ P *ᵥ Pi.single p 1 = e ∧ P *ᵥ Pi.single q 1 = c • (Jm ε *ᵥ e) ∧ ∀ a b, (a = p ∨ a = q ∨ b = p ∨ b = q) → (Pᴴ * Jm ε * P) a b = if (a = p ∧ b = q) ∨ (a = q ∧ b = p) then 1 else 0 := by
  first | exact @GlobalTheory.IsotropicPartner.exists_adapted_basis | exact GlobalTheory.IsotropicPartner.exists_adapted_basis | (intros; apply GlobalTheory.IsotropicPartner.exists_adapted_basis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HyperbolicPairInFirstFlagSpaceStatement
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperbolic_pair_in_first_flag_space : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Flag n a) (h : 0 < a), IsIsoFlag ε j W → j ⟨0, h⟩ = 1 → ∀ (P : Matrix (Fin n) (Fin n) ℂ) (p q : Fin n) (c : ℂ), IsUnit P → p ≠ q → P *ᵥ Pi.single p 1 ∈ W ⟨1, Nat.succ_lt_succ h⟩ → P *ᵥ Pi.single q 1 = c • (Jm ε *ᵥ (P *ᵥ Pi.single p 1)) → (∀ a b, (a = p ∨ a = q ∨ b = p ∨ b = q) → (Pᴴ * Jm ε * P) a b = if (a = p ∧ b = q) ∨ (a = q ∧ b = p) then 1 else 0) → (∀ b, b ≠ p → ∃ X X' : Matrix (Fin n) (Fin n) ℂ, X ∈ lieSet ε ∧ X' ∈ lieSet ε ∧ (∀ t, expG ε X t ∈ flagN ε W) ∧ (∀ t, expG ε X' t ∈ flagN ε W) ∧ P * Matrix.single p b 1 * P⁻¹ = X + Complex.I • X') ∧ ∀ b, b ≠ q → ∃ X X' : Matrix (Fin n) (Fin n) ℂ, X ∈ lieSet ε ∧ X' ∈ lieSet ε ∧ (∀ t, expG ε X t ∈ flagN ε W) ∧ (∀ t, expG ε X' t ∈ flagN ε W) ∧ P * Matrix.single b q 1 * P⁻¹ = X + Complex.I • X' := by
  first | exact @GlobalTheory.UnipRadUnit.matrixUnits_mem_radical | exact GlobalTheory.UnipRadUnit.matrixUnits_mem_radical | (intros; apply GlobalTheory.UnipRadUnit.matrixUnits_mem_radical <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HyperbolicPairSplitTorusStatement
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperbolic_pair_split_torus : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Flag n a) (h : 0 < a), IsIsoFlag ε j W → j ⟨0, h⟩ = 1 → ∀ (P : Matrix (Fin n) (Fin n) ℂ) (p q : Fin n) (c : ℂ), IsUnit P → p ≠ q → P *ᵥ Pi.single p 1 ∈ W ⟨1, Nat.succ_lt_succ h⟩ → P *ᵥ Pi.single q 1 = c • (Jm ε *ᵥ (P *ᵥ Pi.single p 1)) → (∀ a b, (a = p ∨ a = q ∨ b = p ∨ b = q) → (Pᴴ * Jm ε * P) a b = if (a = p ∧ b = q) ∨ (a = q ∧ b = p) then 1 else 0) → P * diagonal (Pi.single p 1 - Pi.single q 1) * P⁻¹ ∈ lieSet ε ∧ (∀ x : ℝ, IsSplit ε W (Pi.single ⟨0, h⟩ x) (expG ε (P * diagonal (Pi.single p 1 - Pi.single q 1) * P⁻¹) x)) ∧ P * diagonal (Pi.single p Complex.I + Pi.single q Complex.I) * P⁻¹ ∈ lieSet ε ∧ ∀ θ : ℝ, expG ε (P * diagonal (Pi.single p Complex.I + Pi.single q Complex.I) * P⁻¹) θ ∈ KG ε ⊓ leviOne ε W ∧ ∀ m ∈ leviOne ε W, expG ε (P * diagonal (Pi.single p Complex.I + Pi.single q Complex.I) * P⁻¹) θ * m = m * expG ε (P * diagonal (Pi.single p Complex.I + Pi.single q Complex.I) * P⁻¹) θ := by
  first | exact @GlobalTheory.SplitTorus.split_torus_circle | exact GlobalTheory.SplitTorus.split_torus_circle | (intros; apply GlobalTheory.SplitTorus.split_torus_circle <;> assumption)
end

