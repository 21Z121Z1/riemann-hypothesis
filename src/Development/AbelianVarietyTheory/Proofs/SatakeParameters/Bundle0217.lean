import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0070
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0001
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0197
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0125
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolyWeilDelignePotSemistableEnlargeCoefficie
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0606
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0206
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0205
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0180
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0200
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0141
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0169
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0133
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EOpEqAsAlgebraHom
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0207
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0170
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0053
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParIndJacPlacing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0194
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AutomorphicArithmetic.BlochKatoExtensions.PhtCmp
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.RkMultVOfNotJump
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0222
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0193
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocA
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0213
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0204
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0211
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0149
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0208
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleSubspaceTrivialOutsideSplitPlac
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsBalancedBilinearTensorProductMap
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
open scoped TensorProduct
open GlobalTheory.Pst.TwistLetters

noncomputable section

namespace GlobalTheory.LetterDescent

open TensorProduct

variable {LL U D₁ D₂ D₃ : Type} [Field LL] [Field U] [AddCommGroup D₁] [Module LL D₁] [AddCommGroup D₂]
  [Module LL D₂] [AddCommGroup D₃] [Module LL D₃] (F : Type) [Field F] [Algebra LL F]

def baseBil (β : D₁ →ₗ[LL] D₂ →ₗ[LL] D₃) : F ⊗[LL] D₁ →ₗ[F] F ⊗[LL] D₂ →ₗ[F] F ⊗[LL] D₃ :=
  ((LinearMap.baseChangeHom LL F D₂ D₃) ∘ₗ β).liftBaseChange F

theorem baseBil_tmul (β : D₁ →ₗ[LL] D₂ →ₗ[LL] D₃) (a b : F) (x : D₁) (y : D₂) :
    baseBil F β (a ⊗ₜ x) (b ⊗ₜ y) = (a * b) ⊗ₜ β x y := by
  simp [baseBil, LinearMap.liftBaseChange_tmul, TensorProduct.smul_tmul']

theorem baseBil_left (β : D₁ →ₗ[LL] D₂ →ₗ[LL] D₃) (f₁ : Module.End LL D₁) (f₃ : Module.End LL D₃)
    (h : ∀ x y, β (f₁ x) y = f₃ (β x y)) (w : F ⊗[LL] D₁) (z : F ⊗[LL] D₂) :
    baseBil F β (f₁.baseChange F w) z = f₃.baseChange F (baseBil F β w z) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add w w' hw hw' => simp [map_add, LinearMap.add_apply, hw, hw']
  | tmul a x =>
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z z' hz hz' => simp only [map_add, hz, hz']
    | tmul b y => simp [LinearMap.baseChange_tmul, baseBil_tmul, h]

theorem baseBil_right (β : D₁ →ₗ[LL] D₂ →ₗ[LL] D₃) (f₂ : Module.End LL D₂) (f₃ : Module.End LL D₃)
    (h : ∀ x y, β x (f₂ y) = f₃ (β x y)) (w : F ⊗[LL] D₁) (z : F ⊗[LL] D₂) :
    baseBil F β w (f₂.baseChange F z) = f₃.baseChange F (baseBil F β w z) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add w w' hw hw' => simp [map_add, LinearMap.add_apply, hw, hw']
  | tmul a x =>
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z z' hz hz' => simp only [map_add, hz, hz']
    | tmul b y => simp [LinearMap.baseChange_tmul, baseBil_tmul, h]

end GlobalTheory.LetterDescent

namespace GlobalTheory.LetterDescent

open TensorProduct

theorem exists_letter_tensor_map {LL U D₁ D₂ D₃ : Type} [Field LL] [Field U] [AddCommGroup D₁] [Module LL D₁]
    [AddCommGroup D₂] [Module LL D₂] [AddCommGroup D₃] [Module LL D₃] (m₁ : U →+* Module.End LL D₁)
    (m₂ : U →+* Module.End LL D₂) (m₃ : U →+* Module.End LL D₃) (F : Type) [Field F] [Algebra LL F]
    (τ : U →+* F) (β : D₁ →ₗ[LL] D₂ →ₗ[LL] D₃) (h₁ : ∀ c x y, β (m₁ c x) y = m₃ c (β x y))
    (h₂ : ∀ c x y, β x (m₂ c y) = m₃ c (β x y)) :
    ∃ Φ : GlobalTheory.Pst.Letter m₁ F τ ⊗[F] GlobalTheory.Pst.Letter m₂ F τ →ₗ[F] GlobalTheory.Pst.Letter m₃ F τ,
      ∀ x y, Φ (GlobalTheory.Pst.letterMk m₁ F τ x ⊗ₜ GlobalTheory.Pst.letterMk m₂ F τ y) =
        GlobalTheory.Pst.letterMk m₃ F τ (β x y) := by
  let C : F ⊗[LL] D₁ →ₗ[F] F ⊗[LL] D₂ →ₗ[F] GlobalTheory.Pst.Letter m₃ F τ :=
    (baseBil F β).compr₂ (GlobalTheory.Pst.letterQ m₃ F τ)
  have hmem : ∀ (c : U) (v : F ⊗[LL] D₃),
      GlobalTheory.Pst.letterQ m₃ F τ ((m₃ c).baseChange F v - τ c • v) = 0 := by
    intro c v
    rw [← LinearMap.mem_ker, GlobalTheory.Pst.ker_letterQ]
    exact Submodule.mem_iSup_of_mem c ⟨v, rfl⟩
  have k₂ : GlobalTheory.Pst.letterKer m₂ F τ ≤ LinearMap.ker C.flip := by
    refine iSup_le fun c => ?_
    rintro _ ⟨z, rfl⟩
    rw [LinearMap.mem_ker]
    ext w
    simp only [C, LinearMap.flip_apply, LinearMap.compr₂_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, map_sub, map_smul, baseBil_right F β (m₂ c) (m₃ c) (h₂ c), LinearMap.zero_apply]
    rw [← map_smul, ← map_sub]
    exact hmem c _
  let C₂ := (GlobalTheory.Pst.letterKer m₂ F τ).liftQ C.flip k₂
  have k₁ : GlobalTheory.Pst.letterKer m₁ F τ ≤ LinearMap.ker C₂.flip := by
    refine iSup_le fun c => ?_
    rintro _ ⟨w, rfl⟩
    rw [LinearMap.mem_ker]
    refine LinearMap.ext fun q => ?_
    obtain ⟨z, rfl⟩ := GlobalTheory.Pst.letterQ_surjective m₂ F τ q
    change GlobalTheory.Pst.letterQ m₃ F τ (baseBil F β (((m₁ c).baseChange F - τ c • LinearMap.id : F ⊗[LL] D₁ →ₗ[F] F ⊗[LL] D₁) w) z) = 0
    rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sub, map_smul, LinearMap.sub_apply,
      LinearMap.smul_apply, baseBil_left F β (m₁ c) (m₃ c) (h₁ c)]
    exact hmem c _
  refine ⟨TensorProduct.lift ((GlobalTheory.Pst.letterKer m₁ F τ).liftQ C₂.flip k₁), fun x y => ?_⟩
  change GlobalTheory.Pst.letterQ m₃ F τ (baseBil F β (1 ⊗ₜ x) (1 ⊗ₜ y)) = _
  rw [baseBil_tmul, mul_one]
  rfl

end GlobalTheory.LetterDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsBaseLevelVectorInGoodAlgebraicFormsSpanStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_baseLevel_vector_in_goodAlgebraicForms_span : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → ∀ s, A3.fam3.Ok3 s → GoodGeneric A3.A.X F.P0 F.ψ0⁻¹ → R.toRealDat.LUnif → ∀ j c, R.Wc' j c ≠ ⊥ → ∃ w ∈ R.Wc' j c, w ≠ 0 ∧ w ∈ R.toRealDat.WS F.lv2 false j (sg0 D A3.A) := by
  first | exact @GlobalTheory.Hk3.exists_part_level_vector | exact GlobalTheory.Hk3.exists_part_level_vector | (intros; apply GlobalTheory.Hk3.exists_part_level_vector <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCentralScalarDistinctGeometricLemmaCellsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_central_scalar_distinct_geometricLemma_cells : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (d : Fin 2 → ℕ) (σ : ∀ i, Irr k (d i)), (∀ i, 0 < d i ∧ IsCuspidal (σ i).π) → d 1 = 1 →
    (∀ (h : d 0 = d 1) (α : ℂˣ), ¬ Nonempty ((h ▸ σ 0 : Irr k (d 1)).π.Equiv
      (twist (σ 1).π (detChar (Fin (d 1)) (unrChar k α))))) →
    ∃ (z : Levi k fun j : Fin 2 => Fin (d (Equiv.swap 0 1 j))) (c c' : ℂ), (∀ g, g * z = z * g) ∧ c ≠ c' ∧
      (∀ x, (piTensor fun j => (σ (Equiv.swap 0 1 j)).π) z x = c • x) ∧
      ∀ (b : SizeMatrix (fun i : Fin 2 => Fin (d i)) (fun j : Fin 2 => Fin (d (Equiv.swap 0 1 j)))),
        b.1 1 0 = 0 → ∀ (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin (d i))
          (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (d (Equiv.swap 0 1 j))) y,
          cellFunctor f g (piTensor fun i => (σ i).π) z y = c' • y := by
  first | exact @GlobalTheory.CellCentral.exists_central_scalar_ne_cell | exact GlobalTheory.CellCentral.exists_central_scalar_ne_cell | (intros; apply GlobalTheory.CellCentral.exists_central_scalar_ne_cell <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCount
section
noncomputable section

namespace GlobalTheory.HtCardProof

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.L2 Module

section Local

variable {l m : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) {K LL : FinExt l}
  (r : ↥(GK K) →* GL (Fin m) ↥LL.1)

set_option maxHeartbeats 1000000 in
include T in

theorem exists_count (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) [FiniteDimensional ↥LL.1 ↥(DdRE (P.PD K) (vrep r) τ)] :
    ∃ M : Multiset ℤ, Multiset.card M = finrank ↥LL.1 ↥(DdRE (P.PD K) (vrep r) τ) ∧
      ∀ a, (M.count a : ℤ) = multV (P.PD K) (vrep r) τ a := by
  obtain ⟨lo, hlo⟩ := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_fildR_lo (P.PD K) (vrep r) τ
  obtain ⟨hi, hhi⟩ := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_fildR_hi (P.PD K) (vrep r) τ
  have anti := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_fildR_anti (P.PD K) (vrep r) τ
  haveI : ∀ a, FiniteDimensional ↥LL.1 ↥(FildR (P.PD K) (vrep r) τ a) := fun a =>
    Submodule.finiteDimensional_of_le (inf_le_left : FildR (P.PD K) (vrep r) τ a ≤ DdRE (P.PD K) (vrep r) τ)
  have nn : ∀ a, 0 ≤ multV (P.PD K) (vrep r) τ a := fun a => by
    have := Submodule.finrank_mono (anti (show a ≤ a + 1 by omega))
    unfold multV
    omega
  obtain ⟨lo₁, hl1, hl2⟩ : ∃ lo₁, lo₁ ≤ lo ∧ lo₁ ≤ hi := ⟨min lo hi, min_le_left _ _, min_le_right _ _⟩
  have zero : ∀ a, a ∉ Finset.Ico lo₁ hi → multV (P.PD K) (vrep r) τ a = 0 := fun a ha => by
    rw [Finset.mem_Ico, not_and_or, not_le, not_lt] at ha
    have e : FildR (P.PD K) (vrep r) τ a = FildR (P.PD K) (vrep r) τ (a + 1) := by
      rcases ha with ha | ha
      · exact (hlo a (by omega)).trans (hlo (a + 1) (by omega)).symm
      · exact (hhi a ha).trans (hhi (a + 1) (by omega)).symm
    unfold multV
    rw [e, sub_self]
  refine ⟨∑ a ∈ Finset.Ico lo₁ hi, Multiset.replicate (multV (P.PD K) (vrep r) τ a).toNat a, ?_, fun b => ?_⟩
  · rw [Multiset.card_sum]
    simp only [Multiset.card_replicate]
    have hs : ∑ a ∈ Finset.Ico lo₁ hi, multV (P.PD K) (vrep r) τ a =
        (finrank ↥LL.1 ↥(FildR (P.PD K) (vrep r) τ lo₁) : ℤ) - finrank ↥LL.1 ↥(FildR (P.PD K) (vrep r) τ hi) :=
      Formalism.MainNotions.N.Pv.LocalLengthBound.rk_sum_multV _ _ _ _ _ hl2
    have e1 : finrank ↥LL.1 ↥(FildR (P.PD K) (vrep r) τ lo₁) = finrank ↥LL.1 ↥(DdRE (P.PD K) (vrep r) τ) := by
      rw [hlo lo₁ hl1]
    have e2 : finrank ↥LL.1 ↥(FildR (P.PD K) (vrep r) τ hi) = 0 := Submodule.finrank_eq_zero.2 (hhi hi le_rfl)
    rw [e1, e2] at hs
    have : ((∑ a ∈ Finset.Ico lo₁ hi, (multV (P.PD K) (vrep r) τ a).toNat : ℕ) : ℤ) =
        (finrank ↥LL.1 ↥(DdRE (P.PD K) (vrep r) τ) : ℤ) := by
      push_cast
      rw [Finset.sum_congr rfl fun a _ => Int.toNat_of_nonneg (nn a), hs]
      simp
    exact_mod_cast this
  · rw [Multiset.count_sum']
    simp only [Multiset.count_replicate]
    rw [Finset.sum_ite_eq']
    by_cases hb : b ∈ Finset.Ico lo₁ hi
    · rw [if_pos hb, Int.toNat_of_nonneg (nn b)]
    · rw [if_neg hb, zero b hb]
      rfl

end Local

theorem htCard : GlobalTheory.HeightCounting.HtCard := GlobalTheory.PhtCompare.phtCmp

end GlobalTheory.HtCardProof

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCuspidalSupportIrreducibleSmoothGL
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory.CuspSupportExist

theorem L_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (π : Irr k 0), ∃ (s : ℕ) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)), IsCuspSupport π.π d (fun a => (σ a).π) := GlobalTheory.T.exists_cuspidal_support

theorem L_jacq : GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (π : Irr k n) (s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), ¬ Subsingleton (Jacquet π.π (unipRad k e)) → ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (τ : Representation ℂ (Levi k fun a => Fin (d a)) Y), τ.IsIrreducible ∧ IsSmooth τ ∧ IsSubquotient τ (jac e π.π) ∧ ∃ φ : π.π.IntertwiningMap (parInd e τ), Function.Injective φ := GlobalTheory.T.exists_injective_parInd_of_jacquet_nontrivial

theorem L_tens : GlobalTheory.Published.GeometricLemma → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (π : Irr k n) (s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n) (Y : Type) [AddCommGroup Y] [Module ℂ Y] (τ : Representation ℂ (Levi k fun a => Fin (d a)) Y), τ.IsIrreducible → IsSubquotient τ (jac e π.π) → ∃ σ : ∀ a, Irr k (d a), IsSubquotient τ (piTensor fun a => (σ a).π) := GlobalTheory.T.exists_irreducible_tensor_of_jacquet_subquotient

theorem L_ind : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α n : Type) (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) (W W' : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (ρ : Representation ℂ (Levi k m) W) (ρ' : Representation ℂ (Levi k m) W'), IsSmooth ρ' → IsSubquotient ρ ρ' → IsSubquotient (parInd e ρ) (parInd e ρ') := GlobalTheory.T.parabolicInduction_preserves_subquotient

theorem L_lt : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), unipRad k e ≠ ⊥ → ∀ a, d a < n := GlobalTheory.T.blocks_lt_of_parabolicUnipotentRadical_ne_bot

theorem L_pit : ∀ (α : Type) [Fintype α] [DecidableEq α] (Γ : α → Type) [∀ a, Group (Γ a)] (X Y : α → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (ρ' : ∀ a, Representation ℂ (Γ a) (Y a)), (∀ a, IsSubquotient (ρ a) (ρ' a)) → IsSubquotient (piTensor ρ) (piTensor ρ') := GlobalTheory.T.piExteriorTensor_isSubquotient_of_forall

theorem L_stage : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s n : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n) (t : Fin s → ℕ) (d' : ∀ a, Fin (t a) → ℕ) (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) (X : ∀ a, Fin (t a) → Type) [∀ a b, AddCommGroup (X a b)] [∀ a b, Module ℂ (X a b)] (ρ : ∀ a b, Representation ℂ (GL (Fin (d' a b)) k) (X a b)), (∀ a b, IsSmooth (ρ a b)) → ∃ E : (Σ c : Fin (∑ a, t a), Fin (d' (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2)) ≃ Fin n, IsSubquotient (multiProd e fun a => multiProd (e' a) (ρ a)) (multiProd E fun c => ρ (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2) := GlobalTheory.T.isSubquotient_parInd_products_flattened

theorem cusp_case (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (hn : 0 < n) (π : Irr k n) (hc : IsCuspidal π.π) :
    ∃ (s : ℕ) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)), IsCuspSupport π.π d (fun a => (σ a).π) := by
  let e : (Σ _ : Fin 1, Fin n) ≃ Fin n :=
    { toFun := fun p => p.2, invFun := fun i => ⟨0, i⟩,
      left_inv := fun p => by
        obtain ⟨a, i⟩ := p
        obtain rfl : a = 0 := Subsingleton.elim _ _
        rfl
      right_inv := fun _ => rfl }
  obtain ⟨φ⟩ := GlobalTheory.LocGL.nonempty_equiv_multiProd_one π.smooth e (fun _ _ => rfl)
  exact ⟨1, fun _ => n, fun _ => π, π.irr, fun _ => ⟨hn, π.irr, hc⟩, e,
    .of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective⟩

theorem reduce (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) (hGL : GlobalTheory.Published.GeometricLemma) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (π : Irr k n) (hc : ¬ IsCuspidal π.π) :
    ∃ (s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n) (σ : ∀ a, Irr k (d a)),
      (∀ a, d a < n) ∧ IsSubquotient π.π (multiProd e fun a => (σ a).π) := by
  obtain ⟨s, d, e, hne, hns⟩ : ∃ (s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n),
      unipRad k e ≠ ⊥ ∧ ¬ Subsingleton (Jacquet π.π (unipRad k e)) := by
    by_contra h
    push_neg at h
    exact hc ⟨π.smooth, fun s d e hne => h s d e hne⟩
  obtain ⟨Y, _, _, τ, hτi, hτs, hτq, φ, hφ⟩ := L_jacq hBZ k n π s d e hns
  obtain ⟨σ, hσ⟩ := L_tens hGL k n π s d e Y τ hτi hτq
  exact ⟨s, d, e, σ, L_lt k n s d e hne, (IsSubquotient.of_injective φ hφ).trans
    (L_ind k _ _ _ e _ _ τ _ (isSmooth_piTensor fun a => (σ a).smooth) hσ)⟩

theorem glue (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (π : Irr k n) (s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n)
    (σ : ∀ a, Irr k (d a)) (hsub : IsSubquotient π.π (multiProd e fun a => (σ a).π))
    (t : Fin s → ℕ) (d' : ∀ a, Fin (t a) → ℕ) (τ : ∀ a b, Irr k (d' a b))
    (hτ : ∀ a, IsCuspSupport (σ a).π (d' a) (fun b => (τ a b).π)) :
    ∃ (s : ℕ) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)), IsCuspSupport π.π d (fun a => (σ a).π) := by
  have h3 := fun a => (hτ a).2.2
  choose e' he' using h3
  have step1 : IsSubquotient (multiProd e fun a => (σ a).π)
      (multiProd e fun a => multiProd (e' a) fun b => (τ a b).π) :=
    L_ind k _ _ _ e _ _ _ _ (isSmooth_piTensor fun a => isSmooth_parInd _ _)
      (L_pit _ _ _ _ _ _ he')
  obtain ⟨E, hE⟩ := L_stage k s n d e t d' e' _ (fun a b => (τ a b).π) fun a b => (τ a b).smooth
  exact ⟨∑ a, t a, _, fun c => τ (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2, π.irr,
    fun c => (hτ _).2.1 _, E, hsub.trans (step1.trans hE)⟩

theorem main : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (π : Irr k n), ∃ (s : ℕ) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)), GlobalTheory.SmGL.IsCuspSupport π.π d (fun a => (σ a).π) := by
  intro hBZ hGL k _ _ _ _ n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro π
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact L_zero k π
  by_cases hc : IsCuspidal π.π
  · exact cusp_case k n hn π hc
  · obtain ⟨s, d, e, σ, hlt, hsub⟩ := reduce hBZ hGL k n π hc
    have h := fun a => ih (d a) (hlt a) (σ a)
    choose t d' τ hτ using h
    exact glue k n π s d e σ hsub t d' τ hτ

end GlobalTheory.CuspSupportExist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntUnitaryOfGramClassStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_intUnitary_of_gramClass_alt : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n n' : ℕ)
    (JS : GL (Fin n) L) (JT : GL (Fin n') L), Formalism.UG.IsUnramInv ϖ σ q → Odd q →
    JS ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ x y : Matrix (Fin n') (Fin n) L,
    (∀ i j, (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) i j ∈ Formalism.UG.intL L) →
    GlobalTheory.Hk3.HoweG.HomA σ JS JT x y → GlobalTheory.Hk3.HoweG.GramEq σ JT x y → GlobalTheory.Hk3.HoweDuality.latIdx y = GlobalTheory.Hk3.HoweDuality.latIdx x →
    ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
      ∀ i j, (y - ((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) i j ∈ Formalism.UG.intL L := by
  first | exact @GlobalTheory.Hk3.HoweG.exists_intUnitary_of_gramClass | exact GlobalTheory.Hk3.HoweG.exists_intUnitary_of_gramClass | (intros; apply GlobalTheory.Hk3.HoweG.exists_intUnitary_of_gramClass <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntertwiningOfCentralFiltrationStepStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_intertwining_of_central_filtration_step : ∀ {G V Y : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ G V) (τ : Representation ℂ G Y) (N : ℕ) (S : Fin (N + 1) → Subrepresentation ρ),
    Monotone S → S 0 = ⊥ → S (Fin.last N) = ⊤ → ∀ (z : G), (∀ g, g * z = z * g) →
    ∀ (t₀ : Fin N) (c : ℂ) (c' : Fin N → ℂ), (∀ t, t ≠ t₀ → c' t ≠ c) →
    (∀ t, t ≠ t₀ → ∀ y, subQuot (S t.succ) (S t.castSucc) z y = c' t • y) →
    Nonempty ((subQuot (S t₀.succ) (S t₀.castSucc)).Equiv τ) → (∀ y, τ z y = c • y) → Nontrivial Y →
    ∃ (φ : ρ.IntertwiningMap τ) (v : V), φ v ≠ 0 := by
  first | exact @GlobalTheory.exists_intertwining_of_central_step | exact GlobalTheory.exists_intertwining_of_central_step | (intros; apply GlobalTheory.exists_intertwining_of_central_step <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleSubspaceTrivialOutsideSplitPlacStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_irreducible_subspace_trivialOutside_splitPlace : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.FinTyp L n) (B : π.S → π.S → ℂ), (∀ x y z (c : ℂ), B x (y + c • z) = B x y + c * B x z) → (∀ x y, B x y = starRingEnd ℂ (B y x)) → (∀ x, x ≠ 0 → 0 < (B x x).re) → (∀ h (x y x' y' : π.S), (x' : GAf L n → ℂ) = NG.rt L n h x → (y' : GAf L n → ℂ) = NG.rt L n h y → B x' y' = B x y) → (∀ N : ℕ, 0 < N → FiniteDimensional ℂ ↥(Submodule.span ℂ {f | f ∈ π.S ∧ ∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f})) → ∀ s : SplitPlace L, ∃ W : Submodule ℂ (GAf L n → ℂ), W ≤ π.S ∧ W ≠ ⊥ ∧ (∀ x : GAf L n, TrivOutside {s.v} x → ∀ f ∈ W, NG.rt L n x f ∈ W) ∧ ∀ W' : Submodule ℂ (GAf L n → ℂ), W' ≤ W → (∀ x : GAf L n, TrivOutside {s.v} x → ∀ f ∈ W', NG.rt L n x f ∈ W') → W' = ⊥ ∨ W' = W := by
  first | exact @GlobalTheory.exists_irreducible_sub_trivOutside_split | exact GlobalTheory.exists_irreducible_sub_trivOutside_split | (intros; apply GlobalTheory.exists_irreducible_sub_trivOutside_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLevelCharacterAtConjugateSplitPlaceStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_character_at_conjugateSplitPlace : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L) (K : Subgroup (GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)))) (θ : K →* ℂˣ), (∀ g ∈ K, g ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring) → IsOpen (θ.ker : Set K) → ∃ (K' : Subgroup (GL (Fin n) ((GlobalTheory.TypeTame.conjSP s).v.adicCompletion (maximalRealSubfield L)))) (θ' : K' →* ℂˣ), (∀ g ∈ K', g ∈ Formalism.UG.GLint (Fin n) ((GlobalTheory.TypeTame.conjSP s).v.adicCompletionIntegers (maximalRealSubfield L)).toSubring) ∧ IsOpen (θ'.ker : Set K') ∧ (∀ κ : GAf L n, (GlobalTheory.TypeTame.conjSP s).loc n κ ∈ K' ↔ s.loc n κ ∈ K) ∧ (∀ (κ : GAf L n) (h : s.loc n κ ∈ K) (h' : (GlobalTheory.TypeTame.conjSP s).loc n κ ∈ K'), θ' ⟨(GlobalTheory.TypeTame.conjSP s).loc n κ, h'⟩ = θ ⟨s.loc n κ, h⟩) ∧ ∀ g (hg : g ∈ K) (g' : GL (Fin n) ((GlobalTheory.TypeTame.conjSP s).v.adicCompletion (maximalRealSubfield L))), g'.val = (g⁻¹).val.transpose → ∃ h' : g' ∈ K', θ' ⟨g', h'⟩ = θ ⟨g, hg⟩ := by
  first | exact @GlobalTheory.TypeTame.exists_conj_level | exact GlobalTheory.TypeTame.exists_conj_level | (intros; apply GlobalTheory.TypeTame.exists_conj_level <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNonsplitPlaceWithInertDatumStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonsplit_place_with_inertDatum : ∀ (D : D7) (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))), (∀ s : SplitPlace D.host.E, s.v ≠ v) → ∃ w : HeightOneSpectrum (𝓞 D.host.E), NG.OverPl w v ∧ ¬ IsSplitPl D.host w ∧ Nonempty (InertDatum D.host.E n v w) := by
  first | exact @GlobalTheory.InertDatumExist.exists_inertDatum | exact GlobalTheory.InertDatumExist.exists_inertDatum | (intros; apply GlobalTheory.InertDatumExist.exists_inertDatum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTameInflationCharacterOfPadicIsoStatement
section
open GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tameInflationCharacter_of_padic_iso : ∀ (g : ℕ) [Fact g.Prime] (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (e : ℚ_[g] ≃+* F), Continuous e → ∀ ξ : Fˣ →* ℂˣ, GlobalTheory.SplitWeil.IsTame ξ → ∃ χ : (ZMod g)ˣ →* ℂˣ, TamePart (ξ.comp (Units.map e.toMonoidHom)) χ := by
  first | exact @GlobalTheory.TameRead.exists_tamePart | exact GlobalTheory.TameRead.exists_tamePart | (intros; apply GlobalTheory.TameRead.exists_tamePart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineParameterIndependentOfLocalEmbeddingStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fontaineParameter_independent_of_localEmbedding : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (ι : Loc.Om l ≃+* ℂ) (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver (F := E) A w) (O O' : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] [CommRing O'] [Algebra ℤ_[l] O'] [TopologicalSpace O'] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (Bw' : LocBridge l E Ω (Dec (F := E) A) O') (hj : GlobalTheory.Pst.Induces Bw) (hj' : GlobalTheory.Pst.Induces Bw') (a : ℕ) (r : ↥(Dec (F := E) A) →* GL (Fin a) (Loc.Om l)), Continuous (fun g => ((r g : GL (Fin a) (Loc.Om l)) : Matrix (Fin a) (Fin a) (Loc.Om l))) → GlobalTheory.Pst.IsPstAt P Bw r → GlobalTheory.Pst.IsPstAt P Bw' r → GlobalTheory.Pst.wdAt P ι Bw h hj r = GlobalTheory.Pst.wdAt P ι Bw' h hj' r := by
  first | exact @GlobalTheory.Pst.BridgeWD.wdAt_bridge_indep | exact GlobalTheory.Pst.BridgeWD.wdAt_bridge_indep | (intros; apply GlobalTheory.Pst.BridgeWD.wdAt_bridge_indep <;> assumption)
end

