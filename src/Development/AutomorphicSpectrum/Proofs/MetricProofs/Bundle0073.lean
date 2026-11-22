import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0068
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0005
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0057
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0064
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0024
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0059
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0041
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0023
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0089
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionOrderAtPoint
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0024
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0022
import GroundTheory.HeightsAndTheta.Heights.FactorialBounds.Assembly
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0018
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsUnitOfLagrangian
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0003
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaHolomorphic
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.Imports
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0013
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsotropicSublatticeGramDeterminant
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagVarietyArithmeticStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_variety_arithmetic : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N : ℕ), 2 ≤ N → IsArithVar (PFl Ψ N) (antisymDegree Ψ N + 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.pFl_isArithVar | exact GlobalTheory.CompanionTheory.Ar.PB.pFl_isArithVar | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.pFl_isArithVar <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagVarietyBoundaryDimensionDropStatement
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_variety_boundary_dimension_drop : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N : ℕ), 2 ≤ N → IsArithVar (PFl Ψ N) (antisymDegree Ψ N + 1) ∧ ∀ q₀ : FlBlock Ψ N, Nonempty {q : FlBlock Ψ N // q ≠ q₀} → ∃ d₀ < antisymDegree Ψ N + 1, IsArithVar (imageZ (fun p : Σ q : {q : FlBlock Ψ N // q ≠ q₀}, FlIdx Ψ N q.1 => (⟨p.1.1, p.2⟩ : Σ q, FlIdx Ψ N q)) (PFl Ψ N)) d₀ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.flag_isArithVar_and_image | exact GlobalTheory.CompanionTheory.Ar.PB.flag_isArithVar_and_image | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.flag_isArithVar_and_image <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameDataLocalDegreeEstimateStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameData_local_degree_estimate : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ PIdx j keep ≃ Fin e), IsPCtx M Rb keep κ v F kb V bl r h → ∀ w ∈ pD ε V, ∃ z ∈ mcPts (mCoordIdeal y), z ∘ v = pPhi M F keep v bl h ε w ∧ basePart M.blk z = bl (pB ε w) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.PFl.Ext.main | exact GlobalTheory.CompanionTheory.Ar.PB.PFl.Ext.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.PFl.Ext.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.GMatIsGenericFlag
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.GenMat

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

section GenU

variable (Ω : Type) [Field Ω] {S : Type} (r : S → ℕ) (s : S)

theorem genU_self (a : Fin (r s)) : genU Ω r s a a = 1 := by
  simp [genU]

theorem genU_of_lt {a b : Fin (r s)} (h : a < b) : genU Ω r s a b = 0 := by
  simp [genU, not_lt.2 h.le, h.ne]

theorem genU_of_gt {l k : Fin (r s)} (h : k < l) :
    genU Ω r s l k = algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X ⟨s, ⟨(l, k), h⟩⟩) :=
  dif_pos h

end GenU

variable {Ψ : Type} {p q : ℕ} (Ω : Type) [Field Ω]

theorem symm_omEmb (a : Fin q) : (blockEquiv p q).symm (omEmb p q a) = .inl a := by
  rw [← blockEquiv_inl, Equiv.symm_apply_apply]

theorem symm_wEmb (a : Fin p) : (blockEquiv p q).symm (wEmb p q a) = .inr a := by
  rw [← blockEquiv_inr, Equiv.symm_apply_apply]

theorem gMat_apply (τ : Ψ) (i j : Fin (p + q)) :
    gMat p q Ω τ i j = (Matrix.fromBlocks (genU Ω (rk Ψ p q) (.inr τ) : Matrix (Fin q) (Fin q) _) 0 0
      (genU Ω (rk Ψ p q) (.inl τ) : Matrix (Fin p) (Fin p) _)) ((blockEquiv p q).symm i) ((blockEquiv p q).symm j) :=
  rfl

theorem gMat_om (τ : Ψ) (a b : Fin q) :
    gMat p q Ω τ (omEmb p q a) (omEmb p q b) = genU Ω (rk Ψ p q) (.inr τ) a b := by
  rw [gMat_apply, symm_omEmb, symm_omEmb]
  rfl

theorem gMat_w (τ : Ψ) (a b : Fin p) :
    gMat p q Ω τ (wEmb p q a) (wEmb p q b) = genU Ω (rk Ψ p q) (.inl τ) a b := by
  rw [gMat_apply, symm_wEmb, symm_wEmb]
  rfl

theorem gMat_om_w (τ : Ψ) (a : Fin q) (b : Fin p) : gMat p q Ω τ (omEmb p q a) (wEmb p q b) = 0 := by
  rw [gMat_apply, symm_omEmb, symm_wEmb]
  rfl

theorem gMat_lowerUni (τ : Ψ) : IsLowerUni (gMat p q Ω τ) := by
  constructor
  · intro a
    obtain ⟨x, rfl⟩ := (blockEquiv p q).surjective a
    rcases x with x | x
    · rw [blockEquiv_inl, gMat_om]
      exact genU_self Ω (rk Ψ p q) (.inr τ) x
    · rw [blockEquiv_inr, gMat_w]
      exact genU_self Ω (rk Ψ p q) (.inl τ) x
  · intro a b hab
    obtain ⟨x, rfl⟩ := (blockEquiv p q).surjective a
    obtain ⟨y, rfl⟩ := (blockEquiv p q).surjective b
    rcases x with x | x <;> rcases y with y | y
    · rw [blockEquiv_inl, blockEquiv_inl] at hab ⊢
      rw [gMat_om]
      exact genU_of_lt Ω (rk Ψ p q) (.inr τ) ((omEmb_strictMono p q).lt_iff_lt.1 hab)
    · rw [blockEquiv_inl, blockEquiv_inr, gMat_om_w]
    · rw [blockEquiv_inr, blockEquiv_inl] at hab
      have h : q + (x : ℕ) < (y : ℕ) := hab
      have := y.2
      omega
    · rw [blockEquiv_inr, blockEquiv_inr] at hab ⊢
      rw [gMat_w]
      exact genU_of_lt Ω (rk Ψ p q) (.inl τ) ((wEmb_strictMono p q).lt_iff_lt.1 hab)

def loc (t : GenIx (rk Ψ p q)) : Ψ × Fin (p + q) × Fin (p + q) :=
  match t with
  | ⟨.inl τ, lk⟩ => (τ, wEmb p q lk.1.1, wEmb p q lk.1.2)
  | ⟨.inr τ, lk⟩ => (τ, omEmb p q lk.1.1, omEmb p q lk.1.2)

theorem exists_var (x : LowIdx Ψ (p + q) p) :
    ∃ t : GenIx (rk Ψ p q), loc t = x.1 ∧ gMat p q Ω x.1.1 x.1.2.1 x.1.2.2 =
      algebraMap (MvPolynomial (GenIx (rk Ψ p q)) Ω) (GenField Ω (rk Ψ p q)) (MvPolynomial.X t) := by
  obtain ⟨⟨τ, a, b⟩, hlt, hiff⟩ := x
  obtain ⟨a, rfl⟩ := (blockEquiv p q).surjective a
  obtain ⟨b, rfl⟩ := (blockEquiv p q).surjective b
  rcases a with a | a <;> rcases b with b | b
  · simp only [blockEquiv_inl] at hlt hiff ⊢
    have h : b < a := (omEmb_strictMono p q).lt_iff_lt.1 hlt
    exact ⟨⟨.inr τ, ⟨(a, b), h⟩⟩, rfl, by
      rw [gMat_om]; exact genU_of_gt Ω (rk Ψ p q) (.inr τ) h⟩
  · exfalso
    simp only [blockEquiv_inl, blockEquiv_inr] at hlt
    have h : q + (b : ℕ) < (a : ℕ) := hlt
    have := a.2
    omega
  · exfalso
    simp only [blockEquiv_inl, blockEquiv_inr] at hiff
    have h : (q + (a : ℕ) < p + q - p ↔ (b : ℕ) < p + q - p) := hiff
    have := b.2
    omega
  · simp only [blockEquiv_inr] at hlt hiff ⊢
    have h : b < a := (wEmb_strictMono p q).lt_iff_lt.1 hlt
    exact ⟨⟨.inl τ, ⟨(a, b), h⟩⟩, rfl, by
      rw [gMat_w]; exact genU_of_gt Ω (rk Ψ p q) (.inl τ) h⟩

theorem gMat_indep :
    AlgebraicIndependent Ω fun x : LowIdx Ψ (p + q) p => gMat p q Ω x.1.1 x.1.2.1 x.1.2.2 := by
  choose e he₁ he₂ using exists_var (Ψ := Ψ) (p := p) (q := q) Ω
  have hinj : Function.Injective e := fun x y h => Subtype.ext (by rw [← he₁ x, ← he₁ y, h])
  have hX : AlgebraicIndependent Ω fun t : GenIx (rk Ψ p q) =>
      algebraMap (MvPolynomial (GenIx (rk Ψ p q)) Ω) (GenField Ω (rk Ψ p q)) (MvPolynomial.X t) :=
    (MvPolynomial.algebraicIndependent_X (GenIx (rk Ψ p q)) Ω).map'
      (f := IsScalarTower.toAlgHom Ω (MvPolynomial (GenIx (rk Ψ p q)) Ω) (GenField Ω (rk Ψ p q)))
      (IsFractionRing.injective _ _)
  have e' : (fun x : LowIdx Ψ (p + q) p => gMat p q Ω x.1.1 x.1.2.1 x.1.2.2) =
      (fun t : GenIx (rk Ψ p q) =>
        algebraMap (MvPolynomial (GenIx (rk Ψ p q)) Ω) (GenField Ω (rk Ψ p q)) (MvPolynomial.X t)) ∘ e :=
    funext he₂
  rw [e']
  exact hX.comp e hinj

theorem gMat_isGenericFlag : ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω],
    GlobalTheory.CompanionTheory.Ar.PB.IsGenericFlag Ω p (gMat (Ψ := Ψ) p q Ω) := fun _ _ _ _ Ω _ =>
  IsGenericFlag.of_lowerUni (fun τ => gMat_lowerUni Ω τ) (gMat_indep Ω)

end GlobalTheory.CompanionTheory.Ar.PB.FMX.GenMat
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.GenericDegreeEqGeometricDegreeStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_degree_eq_geometric_degree : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → GroundTheory.Heights₂.Heights.HilbertSamuel.GenDegGeomDeg.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.genDegGeomDeg_of_system | exact GlobalTheory.CompanionTheory.Ar.Giv.genDegGeomDeg_of_system | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.genDegGeomDeg_of_system <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HeightsNonnegOfIntersectionSystem
section
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.Giv

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I2 Filter Topology NumberField
open GroundTheory.Heights₂.Heights.Targets.BoundedSectionTransfer

noncomputable section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

def VanishesOnChart (W : Ideal (MRing ι)) (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (t : Ω) : Prop :=
  ∃ (δ : K → ℕ) (G : MRing ι), IsMultiHomog G δ ∧ G ∈ W ∧ aeval y G = t * ∏ k, y ⟨k, c k⟩ ^ δ k

theorem prod_pow_add' (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (δ₁ δ₂ : K → ℕ) :
    ∏ k, y ⟨k, c k⟩ ^ (δ₁ + δ₂) k = (∏ k, y ⟨k, c k⟩ ^ δ₁ k) * ∏ k, y ⟨k, c k⟩ ^ δ₂ k := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ ↦ by rw [Pi.add_apply, pow_add]

theorem xpow_notMem {W : Ideal (MRing ι)} (hW : W.IsPrime) {c : ∀ k, ι k}
    (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ W) (e : K → ℕ) : xpow c e ∉ W := by
  intro h
  obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hW)).1 h
  exact hc k (hW.mem_of_pow_mem _ hk)

theorem vanishesOnChart_zero (W : Ideal (MRing ι)) (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) :
    VanishesOnChart W y c 0 :=
  ⟨0, 0, fun m hm ↦ by simp at hm, W.zero_mem, by simp⟩

theorem VanishesOnChart.add {W : Ideal (MRing ι)} {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} {a b : Ω}
    (ha : VanishesOnChart W y c a) (hb : VanishesOnChart W y c b) : VanishesOnChart W y c (a + b) := by
  classical
  obtain ⟨δ₁, e₁, h₁, m₁, v₁⟩ := ha
  obtain ⟨δ₂, e₂, h₂, m₂, v₂⟩ := hb
  refine ⟨δ₁ + δ₂, e₁ * xpow c δ₂ + e₂ * xpow c δ₁,
    isMultiHomog_add (isMultiHomog_mul h₁ (isMultiHomog_xpow c δ₂)) ?_,
    W.add_mem (W.mul_mem_right _ m₁) (W.mul_mem_right _ m₂), ?_⟩
  · rw [add_comm δ₁]
    exact isMultiHomog_mul h₂ (isMultiHomog_xpow c δ₁)
  · rw [map_add, map_mul, map_mul, v₁, v₂, aeval_xpow, aeval_xpow, prod_pow_add']
    ring

theorem VanishesOnChart.mul_left {W : Ideal (MRing ι)} {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k}
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {u t : Ω} (hu : u ∈ chartRingZ y c) (ht : VanishesOnChart W y c t) :
    VanishesOnChart W y c (u * t) := by
  obtain ⟨δ, e, h, m, v⟩ := ht
  obtain ⟨δ', e', h', v'⟩ := exists_form y c hc hu
  refine ⟨δ' + δ, e' * e, isMultiHomog_mul h' h, W.mul_mem_left _ m, ?_⟩
  rw [map_mul, v, v', prod_pow_add']
  ring

theorem not_vanishesOnChart_one {W : Ideal (MRing ι)} {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k}
    (hle : mCoordIdeal y ≤ W) (hW : W.IsPrime) (hcW : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ W) :
    ¬ VanishesOnChart W y c 1 := by
  classical
  rintro ⟨δ, G, hG, hm, hv⟩
  have h0 : G - xpow c δ ∈ mCoordIdeal y :=
    (mem_mCoordIdeal_iff y (isMultiHomog_sub hG (isMultiHomog_xpow c δ))).2
      (by rw [map_sub, hv, aeval_xpow, one_mul, sub_self])
  refine xpow_notMem hW hcW δ ?_
  have := W.sub_mem hm (hle h0)
  simpa using this

theorem exists_form_notMem {W : Ideal (MRing ι)} {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k}
    (hle : mCoordIdeal y ≤ W) (hW : W.IsPrime) (hcW : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ W)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {q : ℕ} {u v : Fin q → Ω} (hu : ∀ j, u j ∈ chartRingZ y c)
    (hv : ∀ j, v j ∈ chartRingZ y c) (h1 : ∑ j, u j * v j = 1) :
    ∃ (j : Fin q) (δ : K → ℕ) (g : MRing ι), IsMultiHomog g δ ∧ g ∉ W ∧
      aeval y g = v j * ∏ k, y ⟨k, c k⟩ ^ δ k := by
  by_contra hno
  have hall : ∀ j, VanishesOnChart W y c (v j) := fun j ↦ by
    obtain ⟨δ, g, hg, hgv⟩ := exists_form y c hc (hv j)
    refine ⟨δ, g, hg, ?_, hgv⟩
    by_contra hn
    exact hno ⟨j, δ, g, hg, hn, hgv⟩
  have hs : VanishesOnChart W y c (∑ j, u j * v j) :=
    Finset.sum_induction _ (VanishesOnChart W y c) (fun _ _ ↦ VanishesOnChart.add)
      (vanishesOnChart_zero W y c) fun j _ ↦ VanishesOnChart.mul_left hc (hu j) (hall j)
  rw [h1] at hs
  exact not_vanishesOnChart_one hle hW hcW hs

theorem height_nonneg_of_forms {II : IntersectionSystem} (hII : IsIntersectionSystem II)
    {y : (Σ k, ι k) → Ω} {A : HermLine ι} {τ : ℕ} {s : Ω} {W : Ideal (MRing ι)}
    (hW : IsArithVar W 1) (hPW : mCoordIdeal y ≤ W) (hA : IsSmoothHerm A) (hτ : 1 ≤ τ)
    (hs : s ∈ chartLatNm y A.a τ) (hsmall : IsSmallH (mCoordIdeal y) y A τ s)
    {G H : MRing ι} {dg dh : K → ℕ} (hG : IsMultiHomog G dg) (hH : IsMultiHomog H dh)
    (hdeg : ∀ k, (dg k : ℤ) = dh k + τ * A.a k) (hGH : aeval y G = s * aeval y H)
    (hGW : G ∉ W) (hHW : H ∉ W) : 0 ≤ II K ι W 1 ![A] := by
  classical
  have hI : IsIntersectionFamily (II K ι) := hII K ι
  set E := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.powLine A τ with hEdef
  have hE : IsSmoothHerm E := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.isSmoothHerm_powLine hA τ
  set B := HermLine.sqMetric (ι := ι) dh with hBdef
  have hB : IsSmoothHerm B := isSmoothHerm_sqMetric _
  have hEB : IsSmoothHerm (E.tensor B) := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.isSmoothHerm_tensor hE hB
  have hEBa : ∀ k, (E.tensor B).a k = (dg k : ℕ) := fun k ↦ by
    show E.a k + B.a k = _
    rw [hEdef, GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.powLine_a, hdeg k]
    show _ + (dh k : ℤ) = _
    ring
  have hsecG : IsSectionOn W (E.tensor B) G := ⟨_, hEBa, hG, hGW⟩
  have hsecH : IsSectionOn W B H := ⟨_, fun k ↦ rfl, hH, hHW⟩
  have hRG := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.inter_eq_recR (II K ι) hI hW hEB hEBa hG hGW
  have hRH := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.inter_eq_recR (II K ι) hI hW hB (fun k ↦ rfl) hH hHW
  have hadd := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.inter_tensor (II K ι) hI hW hE hB
  have hpow := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.inter_powLine (II K ι) hI hW hA τ
  rw [recR_eq, GroundTheory.Heights₂.Heights.Inter.cycR_eq_vertR_of_dimOne GroundTheory.Heights₂.Heights.Inter.arithVarZero _ hW hsecG] at hRG
  rw [recR_eq, GroundTheory.Heights₂.Heights.Inter.cycR_eq_vertR_of_dimOne GroundTheory.Heights₂.Heights.Inter.arithVarZero _ hW hsecH] at hRH
  have hvert := GroundTheory.Heights₂.Heights.HilbertSamuel.SmallSectionPointHeight.vertR_le
    (GroundTheory.Heights₂.Heights.HilbertSamuel.SectionOrderAtPoint.proof K ι Ω y A.a τ s W G H dg dh hW hPW hs hG hH hdeg hGH hGW hHW)
  have harch : arInt W G (E.tensor B) (Fin.elim0 : Fin 0 → HermLine ι) ≤
      arInt W H B (Fin.elim0 : Fin 0 → HermLine ι) := by
    unfold arInt
    rw [GroundTheory.Heights₂.Heights.Inter.ptsIntegral_add_of_dimOne fibreFinite hW _ (g₁ := logNorm B H)
      (g₂ := fun z ↦ logNorm (E.tensor B) G z - logNorm B H z) fun z _ ↦ by ring]
    refine add_le_of_nonpos_right (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.ptsIntegral_nonpos W _ fun z hz ↦ ?_)
    show logNorm (E.tensor B) G z - logNorm B H z ≤ 0
    have hGz := norm_pos_iff.mpr (GroundTheory.Heights₂.Heights.Inter.eval_ne_zero_of_dimOne GroundTheory.Heights₂.Heights.Inter.arithVarZero hW hsecG hz)
    have hHz := norm_pos_iff.mpr (GroundTheory.Heights₂.Heights.Inter.eval_ne_zero_of_dimOne GroundTheory.Heights₂.Heights.Inter.arithVarZero hW hsecH hz)
    have hAz := A.pos z hz.1
    have hBz := B.pos z hz.1
    have hEz : E.h z = A.h z ^ τ := GroundTheory.Heights₂.Heights.HilbertSamuel.SmallSectionPointHeight.powLine_h A τ z
    have hEz0 : 0 < E.h z := hEz ▸ pow_pos hAz τ
    have hzP : z ∈ mcPts (mCoordIdeal y) := ⟨hz.1, fun f hf ↦ hz.2 f (hPW hf)⟩
    have hsm := hsmall dg dh G H z hG hH hdeg hGH hzP
    rw [← hEz] at hsm
    refine sub_nonpos.mpr (Real.log_le_log (div_pos hGz (mul_pos hEz0 hBz)) ?_)
    show _ / (E.h z * B.h z) ≤ _ / B.h z
    rw [div_le_div_iff₀ (mul_pos hEz0 hBz) hBz]
    nlinarith [mul_le_mul_of_nonneg_right hsm hBz.le]
  have hτI : 0 ≤ (τ : ℝ) * II K ι W 1 ![A] := by
    rw [← hpow]
    linarith
  have hτ0 : (0 : ℝ) < τ := by exact_mod_cast hτ
  exact le_of_mul_le_mul_left (by rw [mul_zero]; exact hτI) hτ0

theorem heightsNonneg_of_smallGenerators :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
      (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι) (II : IntersectionSystem) (q : ℕ) (w : Fin q → Ω),
      IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y → IsSmoothHerm A →
      (∀ j, w j ∈ chartLat y A.a 1) → KH.GeneratesOn y A.a w →
      (∀ j, IsSmallH (mCoordIdeal y) y A 1 (w j)) → HeightsNonneg II (mCoordIdeal y) A := by
  intro K _ ι _ Ω _ y D A II q w hII _ _ hA hw hgen hsmall W hW hPW
  classical
  obtain ⟨hWp, -, hWr⟩ := hW.2.1
  choose c hcW using hWr
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k ↦ GroundTheory.Heights₂.Heights.HilbertSamuel.SmallSectionPointHeight.coord_ne_zero fun h ↦ hcW k (hPW h)
  obtain ⟨u, hu, hsum⟩ := hgen c hyc
  have hv : ∀ j, w j * ∏ k, y ⟨k, c k⟩ ^ (-A.a k) ∈ chartRingZ y c := fun j ↦ by
    simpa using hw j c hyc
  obtain ⟨j, δ, g, hg, hgW, hgv⟩ := exists_form_notMem hPW hWp hcW hyc hu hv hsum
  have hGH := (chart_iff y c hyc A.a (w j) g δ).1 hgv
  have hmem : w j ∈ chartLatNm y A.a 1 := GroundTheory.Heights₂.Heights.HilbertSamuel.SmallSectionPointHeight.chartLat_le_chartLatNm y A.a 1 (hw j)
  refine height_nonneg_of_forms hII hW hPW hA le_rfl hmem (hsmall j)
    (isMultiHomog_mul hg (isMultiHomog_xpow c _)) (isMultiHomog_xpow c _) (fun k ↦ ?_) hGH ?_
    (xpow_notMem hWp hcW _)
  · have := Int.toNat_sub_toNat_neg (A.a k)
    simp only [Pi.add_apply, Nat.cast_add, Nat.cast_one, one_mul]
    linarith
  · intro h
    rcases hWp.mem_or_mem h with h | h
    · exact hgW h
    · exact xpow_notMem hWp hcW _ h

end

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HermitianFormPeriodMatrixNormalFormStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_form_period_matrix_normal_form : ∀ (g : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (v : Fin g ⊕ Fin g → Fin g → ℂ),
    Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) →
    (∀ α β, (hermForm Hm (v α) (v β)).im = Matrix.J (Fin g) ℝ α β) →
    ∃ (h : Matrix (Fin g) (Fin g) ℂ) (X Y : Matrix (Fin g) (Fin g) ℝ),
      IsUnit h.det ∧ X.IsSymm ∧ Y.PosDef ∧
      (∀ z w, hermForm Hm z w = hermForm (GlobalTheory.CanTh.imInv (periodMatrix X Y)) (h.mulVec z) (h.mulVec w)) ∧
      (∀ i, h.mulVec (v (Sum.inl i)) = Pi.single i 1) ∧
      (∀ i, h.mulVec (v (Sum.inr i)) = (periodMatrix X Y).mulVec (Pi.single i 1)) ∧
      (Matrix.of fun α β => (hermForm Hm (v α) (v β)).re) = siegelGram X Y := by
  first | exact @GlobalTheory.CompanionTheory.NForm.normal_form_gram | exact GlobalTheory.CompanionTheory.NForm.normal_form_gram | (intros; apply GlobalTheory.CompanionTheory.NForm.normal_form_gram <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptBasesLinearIndependentSpan
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.GenBases

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

theorem basis_image {Ω M N ι : Type} [Field Ω] [AddCommGroup M] [Module Ω M] [AddCommGroup N] [Module Ω N]
    (b : Module.Basis ι Ω M) (f : M →ₗ[Ω] N) (hf : Function.Injective f) :
    LinearIndependent Ω (fun a => f (b a)) ∧
      Submodule.span Ω (Set.range fun a => f (b a)) = (⊤ : Submodule Ω M).map f := by
  refine ⟨b.linearIndependent.map' f (LinearMap.ker_eq_bot.2 hf), ?_⟩
  have h : (Set.range fun a => f (b a)) = f '' Set.range b := by
    rw [← Set.range_comp]; rfl
  rw [h, Submodule.span_image, b.span_eq]

theorem inW_injective {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
    {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {x : (Σ k, J k) → Ω} (A : HodgeCpt Y S x) :
    Function.Injective (inW A) :=
  LinearMap.inl_injective

theorem inO_injective {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
    {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {x : (Σ k, J k) → Ω} (A : HodgeCpt Y S x)
    (τ : CMType H) : Function.Injective (inO A τ) := by
  classical
  unfold inO
  rw [LinearMap.coe_comp]
  refine LinearMap.inr_injective.comp ?_
  rw [LinearMap.coe_single]
  exact Pi.single_injective τ

theorem cc_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐), ∀ s, LinearIndependent Ω (cc 𝔐 bW bO s) ∧ Submodule.span Ω (Set.range (cc 𝔐 bW bO s)) = VV 𝔐 s := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K₀ _ J₀ _ x₀ 𝔐 bW bO s
  rcases s with τ | τ
  · have h := basis_image (bW τ) ((inW 𝔐).comp (𝔐.Vgen (.inl τ)).subtype)
      ((inW_injective 𝔐).comp Subtype.val_injective)
    rw [Submodule.map_comp, Submodule.map_subtype_top] at h
    exact h
  · exact basis_image (bO τ) (inO 𝔐 τ) (inO_injective 𝔐 τ)

end GlobalTheory.CompanionTheory.Ar.PB.FMX.GenBases
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameDegreeFormula
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX

theorem flag_total_normal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)), FormsOK 𝔐 bW bO m φ → ∀ (Z : Scheme.{0}) (ξ' : Spec (CommRingCat.of (GenField Ω (rk (CMType H) D.p D.q))) ⟶ Z) (f : Z ⟶ 𝔐.X), @CoordTie Z _ _ ℤ _ (Ring.toIntAlgebra _) ξ' _ (seg (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) → (∀ q : Z, genPt ξ' ⤳ q) → GlobalTheory.CompanionTheory.Ar.Dominates ξ' 𝔐.ξ f (algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q))) → Smooth f → IsNormalScheme Z := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K₀ _ J₀ _ x₀ 𝔐 bW bO n m φ _ Z ξ' f _ _ _ hf
  exact GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth f 𝔐.normal

end GlobalTheory.CompanionTheory.Ar.PB.FMX
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HsLinksOfMoriwaki
section
namespace GlobalTheory.CompanionTheory.Ar.Giv

open ReciprocityTheory.ChartRestriction.G.Geo

theorem hsLinks_of_moriwaki :
    ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiHSStatement → ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement →
      ArithmeticIntersectionNonneg ∧ SuccessiveMinimaLowerBound ∧ SuccessiveMinimaUpperBound ∧ ArithmeticVolumeLowerBound ∧
        GroundTheory.Heights₂.Heights.LowerBoundFree.ZhangLowerX.Statement ∧ GroundTheory.Heights₂.Heights.DimX.Statement := by
  intro hHS hBig
  have a0 : SuccessiveMinimaLowerBound := GroundTheory.Heights₂.Heights.ForSecondHalf.Z1.of_moriwakiHS hHS
  exact ⟨GroundTheory.Heights₂.Heights.ForSecondHalf.G1.full, a0,
    GroundTheory.Heights₂.Heights.ForSecondHalf.Z2.proof hBig,
    GroundTheory.Heights₂.Heights.ForSecondHalf.BigLineBundleMoriwaki.of_moriwakiBig hBig,
    GroundTheory.Heights₂.Heights.LowerBoundFree.ZhangLowerX.proof a0,
    GroundTheory.Heights₂.Heights.DimX.proof⟩

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsotropicSublatticeGramDeterminantStatement
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropic_sublattice_gram_determinant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (I : Submodule (𝓞 E) Λ), IsCMFam σ → IsIsoSub R.form I → I ≠ ⊥ → ∀ (m : ℕ) (b : Module.Basis (Fin m) ℤ I), m = 2 * Fintype.card Ψ * Module.finrank (𝓞 E) I ∧ (Matrix.of fun i j => (R.ip (R.P (b i : Λ)) (R.P (b j : Λ))).re).det = (R.nz σ I * (|(discr E : ℝ)| ^ (1 / (Module.finrank ℚ E : ℝ))) ^ (Fintype.card Ψ * Module.finrank (𝓞 E) I)) ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.IsoCovol.det_re_gram_eq | exact GlobalTheory.CompanionTheory.Ar.Cusp.IsoCovol.det_re_gram_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.IsoCovol.det_re_gram_eq <;> assumption)
end

