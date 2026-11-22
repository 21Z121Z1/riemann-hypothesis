import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1749
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1842
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1785
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1746
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1833
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTestVectorExpansion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixTwoByTwoFinTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1461
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1860
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1726
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1849
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1776
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1766
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchroedingerEigenvectorCompactCocycle
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1702
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfDualOrientedModelConjugateHermitian
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1777
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1815
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1851
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSkewCayleyInertPlaceStabilizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1406
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ParabolicLeviDecomposition
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1847
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1862
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPeriodicMeasurableSchwartzBoundStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_periodic_measurable_schwartz_bound : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F),
    ∃ (r : (κ → AF F) → ℂ) (K : Set (κ → Fv F v)), @Measurable _ _ (borel _) _ r ∧
      (∀ x z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z → r (x + z) = r x) ∧
      (∀ φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ r ∈ GlobalTheory.WeilM.schA F κ) ∧
      IsCompact K ∧ (interior K).Nonempty ∧
      ∀ μA : @MeasureTheory.Measure (κ → AF F) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μA →
        ∫⁻ x, K.indicator 1 (fun i => evFin F v (x i)) * ‖r x‖ₑ ^ 2 ∂μA ≠ 0 ∧
        ∫⁻ x, K.indicator 1 (fun i => evFin F v (x i)) * ‖r x‖ₑ ^ 2 ∂μA ≠ ⊤ := by
  first | exact @GlobalTheory.Cofactor.exists_cofactor | exact GlobalTheory.Cofactor.exists_cofactor | (intros; apply GlobalTheory.Cofactor.exists_cofactor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosNatMulInvIdealLatticeMemIntegral
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormSum.IdealDenom

open Formalism.MainNotions.StandardLatticesGL3 (IhE OhE inc)

theorem exists_nat_mul_mem {D : D7} (cc : Ideal (𝓞 D.host.K)) : ∃ n : ℕ, 0 < n ∧
    ∀ t ∈ IhE D cc, (n : Formalism.MainNotions.StandardLatticesGL3.AE D) * t ∈ OhE D := by
  obtain ⟨a₀, ha₀, hint⟩ := D.host.AA0.isFractional
  have ha₀' : (algebraMap (𝓞 D.host.E) D.host.E a₀) ≠ 0 := by
    intro h
    exact nonZeroDivisors.ne_zero ha₀ (IsFractionRing.injective (𝓞 D.host.E) D.host.E (by simpa using h))
  obtain ⟨n, hn, hmem⟩ := GlobalTheory.NormSum.Expand.denom (inc D (algebraMap (𝓞 D.host.E) D.host.E a₀)⁻¹)
  refine ⟨n, hn, fun t ht => ?_⟩
  induction ht using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨c, hc, a, ha, s, hs, rfl⟩ := hy
    obtain ⟨b, hb⟩ := hint a ha
    have hci : IsIntegral ℤ (((c : D.host.K) : D.host.E)) :=
      (RingOfIntegers.isIntegral_coe c).map (IsScalarTower.toAlgHom ℤ D.host.K D.host.E)
    have hcm : inc D (((c : D.host.K) : D.host.E)) ∈ OhE D :=
      GlobalTheory.NormSum.Expand.inc_int (⟨_, hci⟩ : 𝓞 D.host.E)
    have hbm := GlobalTheory.NormSum.Expand.inc_int b
    have hab : a = (algebraMap (𝓞 D.host.E) D.host.E a₀)⁻¹ * algebraMap (𝓞 D.host.E) D.host.E b := by
      rw [hb, Algebra.smul_def, ← mul_assoc, inv_mul_cancel₀ ha₀', one_mul]
    have key : (n : Formalism.MainNotions.StandardLatticesGL3.AE D) * (inc D ((((c : D.host.K) : D.host.E)) * a) * s) =
        ((n : Formalism.MainNotions.StandardLatticesGL3.AE D) * inc D (algebraMap (𝓞 D.host.E) D.host.E a₀)⁻¹) *
          (inc D (((c : D.host.K) : D.host.E)) *
            inc D (algebraMap (𝓞 D.host.E) D.host.E b) * s) := by
      rw [hab, map_mul, map_mul]; ring
    rw [key]
    exact (OhE D).mul_mem hmem ((OhE D).mul_mem ((OhE D).mul_mem hcm hbm) hs)
  | zero => rw [mul_zero]; exact (OhE D).zero_mem
  | add x y _ _ hx hy => rw [mul_add]; exact (OhE D).add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact (OhE D).neg_mem hx

theorem exists_nat_mul_inv_mul_mem : ∀ {D : D7} (cc : Ideal (𝓞 D.host.K)) (r : D.host.E), ∃ M : ℕ, 0 < M ∧
    ∀ t ∈ Formalism.MainNotions.StandardLatticesGL3.IhE D cc, (M : Formalism.MainNotions.StandardLatticesGL3.AE D) * (Formalism.MainNotions.StandardLatticesGL3.inc D r⁻¹ * t) ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D := by
  intro D cc r
  obtain ⟨n₁, h₁, m₁⟩ := GlobalTheory.NormSum.Expand.denom (inc D r⁻¹)
  obtain ⟨n₂, h₂, m₂⟩ := exists_nat_mul_mem cc
  refine ⟨n₁ * n₂, Nat.mul_pos h₁ h₂, fun t ht => ?_⟩
  have key : ((n₁ * n₂ : ℕ) : Formalism.MainNotions.StandardLatticesGL3.AE D) * (inc D r⁻¹ * t) =
      ((n₁ : Formalism.MainNotions.StandardLatticesGL3.AE D) * inc D r⁻¹) * ((n₂ : Formalism.MainNotions.StandardLatticesGL3.AE D) * t) := by
    push_cast; ring
  rw [key]
  exact (OhE D).mul_mem m₁ (m₂ t ht)

end GlobalTheory.NormSum.IdealDenom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPtAnti
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.SWLit
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (UA incM ratU)
open GlobalTheory.WeilM (Darboux symp schA thetaSum UG)
open GlobalTheory.SiegelFormula (coord)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SWLink

variable {D : D7} {n : ℕ} {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D}
  {μ : Measure (Mx D V.rank n)} {ω : StdUnn.G D n →* Module.End ℂ (schwartzA θ V.rank n)}
  {J : Matrix (Fin n) (Fin n) D.host.E} {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E}
  {T : GL (Fin (n + n)) D.host.E} {κ : UD D J₂ ≃* StdUnn.G D n} {ι : UD D (-V.gram) ≃ₜ* GA D V} {d : ℕ}
  {ε : Module.Basis (Fin d) D.host.F D.host.E} {co : Dbx V J₂ d}
  {om : UD D (-V.gram) × UD D J₂ →* Module.End ℂ ((Fin V.rank × Fin n × Fin d → AF D.host.F) → ℂ)}

theorem exists_pt_anti (hT : IsWittBasis D.sp.cm.sig J 1 T) {m : ℕ} {u : Mx D m (n + n)}
    (hu : ∀ i, u i ∈ antiSub (AE D) finSumFinEquiv) : ∃ x, u = pt T 0 x := by
  obtain ⟨q, x, rfl⟩ := exists_pt T u
  rw [(pt_anti_iff hT q x).1 hu]
  exact ⟨x, rfl⟩

theorem IsTrans.right (hom : IsTrans ε ι κ ω om) (g : UD D J₂) {φ : (Fin V.rank × Fin n × Fin d → AF D.host.F) → ℂ}
    (hφ : φ ∈ schA D.host.F (Fin V.rank × Fin n × Fin d)) (Φ : schwartzA θ V.rank n) (h : φ ∘ coord ε = Φ.1)
    (x : Mx D V.rank n) : om (1, g) φ (coord ε x) = (ω (κ g) Φ).1 x := by
  rw [hom.2 1 g φ hφ Φ h, map_one, inv_one, mt_one, Matrix.one_mul]

theorem invOf_two_mul (z : AE D) : ⅟(2 : AF D.host.F) * StdUnn.trA z = StdUnn.halfTr z := by
  rw [StdUnn.halfTr]
  congr 1
  refine invOf_eq_right_inv ?_
  rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul, mul_one_div_cancel two_ne_zero, map_one]

theorem mat_inv_weyl {w : StdUnn.G D n} (hw : StdUnn.mat w = StdUnn.blk4 0 1 (-1) 0) :
    StdUnn.mat w⁻¹ = StdUnn.blk4 0 (-1) 1 0 := by
  have h1 : StdUnn.mat w⁻¹ * StdUnn.mat w = 1 := by
    rw [← StdUnn.LeftInvSect.mat_mul, inv_mul_cancel, StdUnn.LeftInvSect.mat_one]
  have h2 : (StdUnn.blk4 0 1 (-1) 0 : Mx D (n + n) (n + n)) * StdUnn.blk4 0 (-1) 1 0 = 1 := by
    rw [StdUnn.Model.submatrix_fromBlocks_mul, ← StdUnn.Model.block_matrix_one]
    simp only [mul_zero, zero_mul, mul_one, add_zero, zero_add, mul_neg, neg_zero, neg_neg]
  rw [← Matrix.mul_one (StdUnn.mat w⁻¹), ← h2, ← hw, ← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem zmul {a b c : ℕ} (y : Mx D b c) : ((0 : Mx D a b) ⬝ y : Mx D a c) = 0 := Matrix.zero_mul y

theorem mulz {a b c : ℕ} (y : Mx D a b) : (y ⬝ (0 : Mx D b c) : Mx D a c) = 0 := Matrix.mul_zero y

theorem mulo {a b : ℕ} (y : Mx D a b) : (y ⬝ (1 : Mx D b b) : Mx D a b) = y := Matrix.mul_one y

theorem formula_lin (hθ : IsInfFam θ) (hι : IsConjV V ι) (hco : IsCoord V T ε co) (hom : IsTrans ε ι κ ω om)
    (h : UD D (-V.gram)) {φ : (Fin V.rank × Fin n × Fin d → AF D.host.F) → ℂ}
    (hφ : φ ∈ schA D.host.F (Fin V.rank × Fin n × Fin d)) (x : Mx D V.rank n) :
    om (h, 1) φ (co.e (pt T 0 x)).1 = φ (co.e (umat h⁻¹ ⬝ pt T 0 x)).1 := by
  have hS := GlobalTheory.SchwartzCoord.mem_schwartzA_comp_coord D θ hθ V.rank n d ε ⟨φ, hφ⟩
  rw [mul_pt, (hco _ _).1, (hco _ _).1, hom.2 h 1 φ hφ ⟨_, hS⟩ rfl, map_one, map_one, ← map_inv, hι]
  rfl

theorem formula_levi (hθ : IsInfFam θ) (hω : StdUnn.IsWeilSch ψ χ θ V μ ω) (hκ : IsChartW T κ) (hco : IsCoord V T ε co)
    (hom : IsTrans ε ι κ ω om) {p : UD D J₂} {a : GL (Fin n) (AE D)}
    (h1 : StdUnn.mat (κ p) = StdUnn.blk4 a.1 0 0 (adj (a⁻¹).1))
    (h2 : StdUnn.mat (κ p⁻¹) = StdUnn.blk4 (a⁻¹).1 0 0 (adj a.1)) {φ : (Fin V.rank × Fin n × Fin d → AF D.host.F) → ℂ}
    (hφ : φ ∈ schA D.host.F (Fin V.rank × Fin n × Fin d)) (x : Mx D V.rank n) :
    om (1, p) φ (co.e (pt T 0 x)).1 = (χ (Matrix.GeneralLinearGroup.det a) : ℂ) *
      npow (absA D (Matrix.GeneralLinearGroup.det a)) ((V.rank : ℂ) / 2) * φ (co.e (pt T 0 x ⬝ (umat p⁻¹)ᵀ)).1 := by
  have hS := GlobalTheory.SchwartzCoord.mem_schwartzA_comp_coord D θ hθ V.rank n d ε ⟨φ, hφ⟩
  rw [hκ.pt_mul h2, (hco _ _).1, (hco _ _).1, hom.right _ hφ ⟨_, hS⟩ rfl, hω.levi _ _ h1, zmul, zero_add, adj_adj]
  rfl

theorem formula_unip (hθ : IsInfFam θ) (hω : StdUnn.IsWeilSch ψ χ θ V μ ω)
    (hG : T.1ᵀ * J₂ * T.1.map D.sp.cm.sig = StdUnn.Jst D n) (hκ : IsChartW T κ) (hco : IsCoord V T ε co)
    (hom : IsTrans ε ι κ ω om) {b : UD D J₂} {β : Mx D n n} (hβ : StdUnn.mat (κ b) = StdUnn.blk4 1 β 0 1)
    {φ : (Fin V.rank × Fin n × Fin d → AF D.host.F) → ℂ}
    (hφ : φ ∈ schA D.host.F (Fin V.rank × Fin n × Fin d)) (x : Mx D V.rank n) :
    om (1, b) φ (co.e (pt T 0 x)).1 =
      ψ (⅟(2 : AF D.host.F) * symp (R := AF D.host.F) (cAl D) (-1) (incM D.host.F (-V.gram)) (incM D.host.F J₂)
        (pt T 0 x ⬝ (umat b)ᵀ) (pt T 0 x)) * φ (co.e (pt T 0 x)).1 := by
  have hS := GlobalTheory.SchwartzCoord.mem_schwartzA_comp_coord D θ hθ V.rank n d ε ⟨φ, hφ⟩
  have e1 : StdUnn.inner V (x ⬝ adj β : Mx D V.rank n) x = β ⬝ StdUnn.inner V x x := by
    rw [StdUnn.inner, StdUnn.inner, adj_mul, adj_adj, Matrix.mul_assoc]
  have e2 : ∀ y, StdUnn.inner V y (0 : Mx D V.rank n) = 0 := fun y => by rw [StdUnn.inner, mulz, mulz]
  rw [hκ.pt_mul hβ, (hco _ _).1, hom.right _ hφ ⟨_, hS⟩ rfl, hω.unip _ _ hβ, symp_pt V hG, e2, zmul, zero_add, e1,
    Matrix.trace_zero]
  have e3 : StdUnn.trA (0 : AE D) = 0 := map_zero _
  rw [e3, sub_zero, invOf_two_mul]
  rfl

theorem formula_weyl (hθ : IsInfFam θ) (hω : StdUnn.IsWeilSch ψ χ θ V μ ω) (hκ : IsChartW T κ) (hco : IsCoord V T ε co)
    [MeasurableSpace (Fin V.rank × Fin n × Fin d → AF D.host.F)] {μ' : Measure (Fin V.rank × Fin n × Fin d → AF D.host.F)}
    (hμ : ∀ f : (Fin V.rank × Fin n × Fin d → AF D.host.F) → ℂ, ∫ y, f y ∂μ' = ∫ x, f (coord ε x) ∂μ)
    (hom : IsTrans ε ι κ ω om) {w : UD D J₂} (hw : StdUnn.mat (κ w) = StdUnn.blk4 0 1 (-1) 0)
    {φ : (Fin V.rank × Fin n × Fin d → AF D.host.F) → ℂ}
    (hφ : φ ∈ schA D.host.F (Fin V.rank × Fin n × Fin d)) (x : Mx D V.rank n) :
    om (1, w) φ (co.e (pt T 0 x)).1 = 1 * ∫ y, φ y * ψ (y ⬝ᵥ (co.e (pt T 0 x ⬝ (umat w⁻¹)ᵀ)).2) ∂μ' := by
  have hS := GlobalTheory.SchwartzCoord.mem_schwartzA_comp_coord D θ hθ V.rank n d ε ⟨φ, hφ⟩
  have h2 : StdUnn.mat (κ w⁻¹) = StdUnn.blk4 0 (-1) 1 0 := by rw [map_inv]; exact mat_inv_weyl hw
  have e0 : ((0 : Mx D V.rank n) ⬝ adj (0 : Mx D n n) + x ⬝ adj (-1 : Mx D n n) : Mx D V.rank n) = -x := by
    rw [zmul, zero_add, adj_neg, adj_one, Matrix.mul_neg, mulo]
  rw [hκ.pt_mul h2, e0, (hco _ _).1, hom.right _ hφ ⟨_, hS⟩ rfl, hω.weyl _ hw, one_mul, hμ]
  refine integral_congr_ae (.of_forall fun y => ?_)
  have e1 : StdUnn.inner V y (-x) = -StdUnn.inner V y x := by
    rw [StdUnn.inner, StdUnn.inner, Matrix.mul_neg, Matrix.mul_neg]
  have e3 : ∀ z : AE D, StdUnn.trA (-z) = -StdUnn.trA z := fun z => map_neg _ z
  beta_reduce
  rw [(hco _ _).2, e1, Matrix.trace_neg, e3, neg_neg, trA_inner_comm]
  rfl

theorem levi_pair (hT : IsWittBasis D.sp.cm.sig J 1 T) (hκ : IsChartW T κ) {p : UD D J₂}
    (hs : p ∈ siegelOf finSumFinEquiv (uinc D J₂)) (hp : p ∈ leviSubOf finSumFinEquiv (uinc D J₂)) :
    ∃ a : GL (Fin n) (AE D), aOf finSumFinEquiv (uinc D J₂) ⟨p, hs⟩ = Matrix.GeneralLinearGroup.det a ∧
      StdUnn.mat (κ p) = StdUnn.blk4 a.1 0 0 (adj (a⁻¹).1) ∧ StdUnn.mat (κ p⁻¹) = StdUnn.blk4 (a⁻¹).1 0 0 (adj a.1) := by
  have h1 := (GlobalTheory.T.levi_chart_block_diagonal_adjoint D n J₂ T κ hκ J hT).1 ⟨p, hs⟩ hp
  refine ⟨leviOf finSumFinEquiv (uinc D J₂) ⟨p, hs⟩, rfl, h1, ?_⟩
  generalize leviOf finSumFinEquiv (uinc D J₂) ⟨p, hs⟩ = a at h1 ⊢
  have h2 : StdUnn.mat (κ p⁻¹) * StdUnn.mat (κ p) = 1 := by
    rw [← StdUnn.LeftInvSect.mat_mul, ← map_mul, inv_mul_cancel, map_one, StdUnn.LeftInvSect.mat_one]
  rw [← Matrix.mul_one (StdUnn.mat (κ p⁻¹)), ← StdUnn.LeftInvSect.levi_mul_inv a, ← h1, ← Matrix.mul_assoc, h2, Matrix.one_mul]

set_option maxHeartbeats 4000000 in

theorem formulas (hθ : IsInfFam θ) (hω : StdUnn.IsWeilSch ψ χ θ V μ ω) (hT : IsWittBasis D.sp.cm.sig J 1 T)
    (hG : T.1ᵀ * J₂ * T.1.map D.sp.cm.sig = StdUnn.Jst D n) (hκ : IsChartW T κ) (hι : IsConjV V ι) (hco : IsCoord V T ε co)
    [MeasurableSpace (Fin V.rank × Fin n × Fin d → AF D.host.F)] {μ' : Measure (Fin V.rank × Fin n × Fin d → AF D.host.F)}
    (hμ : ∀ f : (Fin V.rank × Fin n × Fin d → AF D.host.F) → ℂ, ∫ y, f y ∂μ' = ∫ x, f (coord ε x) ∂μ)
    (hom : IsTrans ε ι κ ω om) : IsWeilFormulas D.sp.cm.sig ψ χ T co μ' om := by
  refine ⟨hom.1, ?_, ?_, ?_, ?_⟩
  · intro h φ hφ u hu
    obtain ⟨x, rfl⟩ := exists_pt_anti hT hu
    exact formula_lin hθ hι hco hom h hφ x
  · rintro ⟨p, hs⟩ hp φ hφ u hu
    obtain ⟨x, rfl⟩ := exists_pt_anti hT hu
    obtain ⟨a, ha, h1, h2⟩ := levi_pair hT hκ hs hp
    rw [ha]
    exact formula_levi hθ hω hκ hco hom h1 h2 hφ x
  · intro b hb φ hφ u hu
    obtain ⟨x, rfl⟩ := exists_pt_anti hT hu
    obtain ⟨β, hβ⟩ := (GlobalTheory.T.levi_chart_block_diagonal_adjoint D n J₂ T κ hκ J hT).2 b hb
    exact formula_unip hθ hω hG hκ hco hom hβ hφ x
  · intro w hw
    refine ⟨1, 1, one_pos, one_pow _, fun φ hφ u hu => ?_⟩
    obtain ⟨x, rfl⟩ := exists_pt_anti hT hu
    exact formula_weyl hθ hω hκ hco hμ hom ((hκ w).trans hw) hφ x

end GlobalTheory.SWLink

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRosatiCoordinatesDivisibleOfPow
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

noncomputable section
namespace GlobalTheory.FlatCM.RosatiCoord

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]
  {σ₁ : K →+* ℂ} {A B : PAT H (Sp (𝓞 K))}

theorem weilEq_prod_snd {I₀ : Type} (f : A.t.G ⟶ B.t.G) (hf : IsMonHom f)
    (G : I₀ → (A.t.G ⟶ B.t.G)) (hG : ∀ i, GlobalTheory.Serre.IsLinearHom A.t.act B.t.act (G i)) (r : I₀ → 𝓞 E)
    (h : ∀ i, WeilEq B.t.PP.L f (G i) A.t.PP.L (A.t.act.act (r i)) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))))
    {T : Finset I₀} (hT : T.Nonempty) :
    WeilEq B.t.PP.L f (∏ i ∈ T, G i) A.t.PP.L (A.t.act.act (∑ i ∈ T, r i)) (𝟙 _)
      (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  induction hT using Finset.Nonempty.cons_induction with
  | singleton a => simpa using h a
  | cons a s has hs ih =>
    rw [Finset.prod_cons, Finset.sum_cons]
    have hs' : GlobalTheory.Serre.IsLinearHom A.t.act B.t.act (∏ i ∈ s, G i) :=
      Finset.prod_induction _ (GlobalTheory.Serre.IsLinearHom A.t.act B.t.act) (fun f g hf hg => hf.mul hg)
        (GlobalTheory.Serre.IsLinearHom.one _ _) fun i _ => hG i
    exact GlobalTheory.T.weilPairingCompatible_add_second_position_complex E H K σ₁ A B f (G a) _ hf (hG a).isMonHom hs'.isMonHom _ _ (h a) ih

theorem exists_mul_eq_gram_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p q) (gP : Matrix (Fin p) (Fin p) (𝓞 E)) (gQ : Matrix (Fin q) (Fin q) (𝓞 E)),
    GlobalTheory.FlatCM.IsGram X gP gQ → ∀ (n : ℕ) (x : Fin p → 𝓞 E) (f : (X.A true).t.G ⟶ X.B.t.G), 0 < n →
    GlobalTheory.Serre.IsLinearHom (X.A true).t.act X.B.t.act f →
    f ^ n = ∏ a, ((X.A true).t.act.act (x a) ≫ GlobalTheory.FlatCM.phiP X a) →
    ∀ a, ∃ y : 𝓞 E, (n : 𝓞 E) * y = ∑ b, gP a b * H.bar (x b) := by
  intro E _ _ _ H _ K _ _ ρ σ₁ p q X gP gQ hG n x f hn hf hfx a
  have hφ : ∀ b, GlobalTheory.Serre.IsLinearHom (X.A true).t.act X.B.t.act (phiP X b) := fun b => X.lin (Sum.inl b)
  obtain ⟨r, hr⟩ := GlobalTheory.FlatCM.GramExists.exists_weilEq_entry E H K ρ σ₁ (X.A true) X.B 1 0 X.ρ_sq rfl X.typeP
    (phiP X a) f (hφ a) hf
  have h1 := weilEq_prod_snd (phiP X a) (hφ a).isMonHom (fun _ : ℕ => f) (fun _ => hf) (fun _ => r) (fun _ => hr)
    (Finset.nonempty_range_iff.2 hn.ne')
  rw [Finset.prod_const, Finset.sum_const, Finset.card_range, nsmul_eq_mul, hfx] at h1
  have h2 := weilEq_prod_snd (phiP X a) (hφ a).isMonHom (fun b => (X.A true).t.act.act (x b) ≫ phiP X b)
    (fun b => (GlobalTheory.Serre.IsLinearHom.act _ _).comp (hφ b)) (fun b => gP a b * H.bar (x b))
    (fun b => GlobalTheory.T.weilPairingCompatible_scalar_second_position_conj E H K σ₁ (X.A true) X.B _ _ (hφ a).isMonHom (hφ b).isMonHom _ (x b) (hG.1 a b))
    (T := Finset.univ) ⟨a, Finset.mem_univ a⟩
  exact ⟨r, GlobalTheory.T.scalar_eq_of_weilPairing_eq_principalCMTriple E H K ρ σ₁ (X.A true) X.ρ_sq X.typeP _ _ fun k u v e hk hu hv =>
    (h1 k u v e hk hu hv).symm.trans (h2 k u v e hk hu hv)⟩

end GlobalTheory.FlatCM.RosatiCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchroedingerEigenvectorCompactCocycleStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped GlobalTheory.VacAny

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_schroedinger_eigenvector_compact_cocycle : ∀ {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (ψ : AddChar (Fv F v) ℂ), Continuous ψ → ψ ≠ 1 →
    ∀ {κ M : Type} [Fintype κ] [Fintype M] (u : M → (κ → Fv F v) × (κ → Fv F v))
      (χ : (M → v.adicCompletionIntegers F) → ℂ), Continuous χ →
      (∀ a : M → v.adicCompletionIntegers F, ∑ m, (a m : Fv F v) • u m = 0 → χ a = 1) →
      (∀ a b : M → v.adicCompletionIntegers F, χ (a + b) = χ a * χ b *
        ψ (-(⅟(2 : Fv F v) * ((∑ m, (a m : Fv F v) • u m).1 ⬝ᵥ (∑ m, (b m : Fv F v) • u m).2 -
          (∑ m, (b m : Fv F v) • u m).1 ⬝ᵥ (∑ m, (a m : Fv F v) • u m).2)))) →
      ∃ φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v), φ ≠ 0 ∧
        ∀ a : M → v.adicCompletionIntegers F, GlobalTheory.WeilM.schr ψ (∑ m, (a m : Fv F v) • u m) φ = χ a • φ := by
  first | exact @GlobalTheory.VacLoc.exists_schr_eigen | exact GlobalTheory.VacLoc.exists_schr_eigen | (intros; apply GlobalTheory.VacLoc.exists_schr_eigen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfDualOrientedModelConjugateHermitianStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_selfDual_orientedModel_conjugate_hermitian : ∀ (D : D7) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → GlobalTheory.SqStepBig.EmbCM Bs →
    ∀ (n r p : ℕ) (V : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E n), V.IsHerm D.sp.cm.sig Bs r p →
      ∃ (B : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin B.rank → D.host.E)),
        IsSelfDualC B Λ ∧ NegIdx B p ∧ GlobalTheory.SqStepBig.OverH 1 B Λ V := by
  first | exact @GlobalTheory.ConjSpace.main | exact GlobalTheory.ConjSpace.main | (intros; apply GlobalTheory.ConjSpace.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfDualOrthogonalComplementHyperbolicPlanStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_selfDual_orthogonalComplement_hyperbolicPlane : ∀ (D : D7) (S : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (x y : S.V)
    (s : (D.host.E →+* ℂ) → ℕ × ℕ), IsSelfDualC S Λ → S.hT x x = 0 → S.hT y y = 0 → S.hT x y = 1 →
    (∀ z, GlobalTheory.SqStepK.InLat S Λ z → GlobalTheory.SqStepK.InLat S Λ (S.hT y z • x) ∧ GlobalTheory.SqStepK.InLat S Λ (S.hT x z • y)) →
    ∃ (S₁ : HSp D) (Λ₁ : Submodule (𝓞 D.host.E) (Fin S₁.rank → D.host.E)) (ι : S₁.V →ₗ[D.host.E] S.V),
      GlobalTheory.SqStepK.PlaneSplit S S₁ Λ Λ₁ ι x y ∧ IsSelfDualC S₁ Λ₁ ∧ S₁.sig = s := by
  first | exact @GlobalTheory.PlaneCompl.exists_compl | exact GlobalTheory.PlaneCompl.exists_compl | (intros; apply GlobalTheory.PlaneCompl.exists_compl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSkewCayleyInertPlaceStabilizerStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_skew_cayley_inertPlace_stabilizer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v, ∃ Y : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E),
    At (evFin F v) Y ∧ (∀ z ∈ GlobalTheory.InertSph.latAt G.W v, Y *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) ∧
    Yᵀ * incM F G.W.J + incM F G.W.J * Y.map (cA σ) = 0 ∧
    (∃ M : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E), (1 + Y) * M = 1 ∧ M * (1 + Y) = 1 ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) ∧
    (∃ M : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E), (1 - Y) * M = 1 ∧ M * (1 - Y) = 1 ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) ∧
    (∃ M : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E), (1 + Y + mat k * (1 - Y)) * M = 1 ∧
      M * (1 + Y + mat k * (1 - Y)) = 1 ∧ ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) := by
  first | exact @GlobalTheory.TwoFacCore.exists_skew_cayley | exact GlobalTheory.TwoFacCore.exists_skew_cayley | (intros; apply GlobalTheory.TwoFacCore.exists_skew_cayley <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitFactorRegularSemisimpleReducible
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TruncKer GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp
open scoped TensorProduct

namespace GlobalTheory.SplitFactor

theorem exists_split_factor : ∀ {F E : Type} [Field F] [Field E] [Algebra F E] {n : ℕ} (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (γ : GL (Fin n) E), 0 < n → IsRegSS (γ : Matrix (Fin n) (Fin n) E) → GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.ClauseAlg σ J γ → GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.ClauseRank σ J γ → ¬ Irreducible (γ : Matrix (Fin n) (Fin n) E).charpoly → ¬ IsNonFieldAniso σ J (γ : Matrix (Fin n) (Fin n) E) → ∃ (k : ℕ) (K : Fin k → Type) (_ : ∀ i, Field (K i)) (_ : ∀ i, Algebra F (K i)), Nonempty (GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.plusAlg σ J (γ : Matrix (Fin n) (Fin n) E) ≃ₐ[F] ∀ i, K i) ∧ ∃ i, ¬ IsField (K i ⊗[F] E) := by
  intro F E _ _ _ n σ J γ hn hreg hAlg hRank hirr hnf
  obtain ⟨k, K, hK, hKA, ⟨e⟩⟩ := hRank.1
  refine ⟨k, K, hK, hKA, ⟨e⟩, ?_⟩
  by_contra hall
  push_neg at hall
  have h2 := hRank.2 k K ⟨e⟩
  have hk1 : 1 ≤ k := h2.2.1 ⟨⟨0, hn⟩⟩
  rcases Nat.lt_or_ge k 2 with hk | hk
  · have hk' : k = 1 := by omega
    have hfield : IsField (GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.genAlg (γ : Matrix (Fin n) (Fin n) E)) := h2.2.2.2 ⟨hk', hall⟩
    obtain ⟨φ, -⟩ := hAlg.1
    have hfA : IsField (AdjoinRoot (γ : Matrix (Fin n) (Fin n) E).charpoly) :=
      φ.toMulEquiv.isField hfield
    have hmax : (Ideal.span {(γ : Matrix (Fin n) (Fin n) E).charpoly}).IsMaximal :=
      Ideal.Quotient.maximal_of_isField _ hfA
    have hne : (γ : Matrix (Fin n) (Fin n) E).charpoly ≠ 0 := (Matrix.charpoly_monic _).ne_zero
    have hprime : Prime (γ : Matrix (Fin n) (Fin n) E).charpoly :=
      (Ideal.span_singleton_prime hne).1 hmax.isPrime
    exact hirr hprime.irreducible
  · exact hnf ⟨hreg, k, K, hK, hKA, ⟨e⟩, hk, hall⟩

end GlobalTheory.SplitFactor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStandardPositiveDefiniteHermitianSpaceRankStatement
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_standardPositiveDefinite_hermitianSpace_rank : ∀ (D : D7) (n : ℕ), ∃ V : HSp D, V.rank = n ∧ V.gram = 1 ∧ IsDefiniteSpace V := by
  first | exact @GlobalTheory.StdDefSpace.exists_std_definite | exact GlobalTheory.StdDefSpace.exists_std_definite | (intros; apply GlobalTheory.StdDefSpace.exists_std_definite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalPseudoCoefficientExistenceUnitaryGroupStatement
section
open GlobalTheory.PsCo.Pc1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localPseudoCoefficientExistence_unitaryGroup : GlobalTheory.PsCo.Pc.LocalPC := by
  first | exact @GlobalTheory.PsCo.Pc.localPC_holds | exact GlobalTheory.PsCo.Pc.localPC_holds | (intros; apply GlobalTheory.PsCo.Pc.localPC_holds <;> assumption)
end

