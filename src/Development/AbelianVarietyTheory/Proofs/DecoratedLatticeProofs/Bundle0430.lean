import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianChartComplexRationalIntegralForms
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0347
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousFinGL
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0326
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0247
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0298
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0309
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0413
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0078
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0411
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AdelicConjTransposeBlockMatrixTwoByTwoFin
import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.GramMatrixAdjoint
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0244
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0322
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0222
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0391
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0370
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0416
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0375
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SemicharacterSqEqOneOnHalfA
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0368
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0071
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0084
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1151
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0399
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0294
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalarFormsOnChartsOfTrueColumnTuple
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

namespace GlobalTheory.AdForm.ChartVal

theorem infM_fin' {D : D7} (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n) (k : GA D V) (hk : k ∈ GfC V)
    (τ : D.what₂.Tau) : infM θ V hn k τ = 1 := by
  subst hn
  exact GlobalTheory.AdForm.RdLaw.infM_fin θ V k hk τ

end GlobalTheory.AdForm.ChartVal

open GlobalTheory.AdForm.ChartVal in

theorem GlobalTheory.AdForm.rd_charts : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ (i : ℕ) (hi : i ≤ B.R.m), ∀ φ ∈ (I.fm l u a).Fi i, (∀ c, (fun z : FrN (I.rec7 l Z) (B.R.N i) => φ c ⟨z.1, z.2⟩) ∈ ValC _ (Formalism.L2.Forms.lamT (D := (I.rec7 l Z)) u i)) ∧ ∀ β y, ∀ γ ∈ GQ ((I.rec7 l Z).sp.X i), ∀ c, ∀ k ∈ GinfC ((I.rec7 l Z).sp.X i), ∀ (κ : A.U i β) (y' : (I.chain l u a).Y i), IsTr (G := fun _ => 1) (infM θ _ (rankN (I.rec7 l Z) i hi) k) ⟨y.1, y.2⟩ ⟨y'.1, y'.2⟩ → A.rd θ i hi β φ y (γ * (A.h i β c * k) * κ.1) = (A.chi i β κ : ℂ) * φ c.1 y' := by
  intro B X I hok hpins l Z u a Ch A hA θ hθ i hi φ hφ
  let eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi :=
    { toFun := fun y => ⟨y.1, y.2⟩, invFun := fun z => ⟨z.1, z.2⟩, left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  have hV := GlobalTheory.Mem.Col2.TC.val_tied I hok hpins l Z u a i hi (A.bad i) (Ch i) (A.chOf i) (A.K i hi) eY
    ⟨A.kb i, hA.reads i hi⟩ (fun _ => rfl)
  have hF := (hV.Fi φ).1 hφ
  refine ⟨?_, ?_⟩
  · intro c
    obtain ⟨Ψ, hΨ, he⟩ := Submodule.mem_map.1 (hF (A.chOf i c))
    have hval := (Submodule.mem_pi.1 (Submodule.mem_inf.1 hΨ).2) ((A.K i hi (A.chOf i c)).y ⟨c, rfl⟩) (Set.mem_univ _)
    have e2 : Ψ ((A.K i hi (A.chOf i c)).y ⟨c, rfl⟩) = fun z => φ c (eY.symm z) := congrFun he ⟨c, rfl⟩
    rw [e2] at hval
    exact hval

  · intro β y γ hγ c k hk κ y' hy
    obtain ⟨Ψ, hΨ, he⟩ := Submodule.mem_map.1 (hF β)
    have hAd : Ψ ∈ AdFun (A.K i hi β).lev (embT (I.rec7 l Z)) := (Submodule.mem_inf.1 hΨ).1
    have hfun : (fun (c : {c // A.chOf i c = β}) (z : Frames (gramC (gramN (I.rec7 l Z) i hi) (embT (I.rec7 l Z)))) =>
        φ c.1 ⟨z.1, z.2⟩) = fun c => Ψ ((A.K i hi β).y c) := he.symm
    have laws := GlobalTheory.AdForm.RdLaw.rdS_laws (I.rec7 l Z) θ hθ ((I.rec7 l Z).sp.X i) (B.R.N i) (rankN (I.rec7 l Z) i hi)
      (gramN (I.rec7 l Z) i hi) rfl (B.T u) (I.rec7 l Z).R.f (A.bad i) (A.K i hi β).lev {c // A.chOf i c = β}
      (A.K i hi β).y (A.K i hi β).y_bij _ (fun c z => φ c.1 ⟨z.1, z.2⟩) (hF β) ⟨y.1, y.2⟩
    obtain ⟨hL, hK, hR, -⟩ := laws
    have hκ := (hA.U i hi β κ.1).1 κ.2
    obtain ⟨hκf, κ', hκ'⟩ := hκ
    have hchi := hA.chi i hi β κ κ' hκ'
    have hval := (GlobalTheory.AdForm.rdS_val (I.rec7 l Z) θ hθ ((I.rec7 l Z).sp.X i) (B.R.N i) (rankN (I.rec7 l Z) i hi)
      (gramN (I.rec7 l Z) i hi) rfl (B.T u) (I.rec7 l Z).R.f (A.bad i) (A.K i hi β).lev {c // A.chOf i c = β}
      (A.K i hi β).y (A.K i hi β).y_bij Ψ hAd ⟨y'.1, y'.2⟩ (A.h i β c)).2.2 ((A.K i hi β).y c) ⟨y'.1, y'.2⟩
      ((hA.h i hi β c).2.symm) (fun τ => by
        have h1 := infM_fin' θ ((I.rec7 l Z).sp.X i) (rankN (I.rec7 l Z) i hi) (A.h i β c) (hA.h i hi β c).1 τ
        show y'.1 τ = infM θ _ _ (A.h i β c) τ * y'.1 τ
        erw [h1, Matrix.one_mul])
    show rdS θ _ (rankN (I.rec7 l Z) i hi) (A.K i hi β).lev (A.K i hi β).y (fun c z => φ c.1 ⟨z.1, z.2⟩) ⟨y.1, y.2⟩
      (γ * (A.h i β c * k) * κ.1) = _
    have e1 := hL γ hγ (A.h i β c * k * κ.1)
    have e2 := hK κ.1 hκf κ' hκ' (A.h i β c * k)
    have e3 := hR k hk ⟨y'.1, y'.2⟩ hy (A.h i β c)
    have e5 := congrArg (fun F => rdS θ ((I.rec7 l Z).sp.X i) (rankN (I.rec7 l Z) i hi) (A.K i hi β).lev (A.K i hi β).y F
      ⟨y'.1, y'.2⟩ (A.h i β c)) hfun
    have e6 : Ψ ((A.K i hi β).y c) ⟨y'.1, y'.2⟩ = φ c.1 y' := (congrFun (congrFun hfun c) ⟨y'.1, y'.2⟩).symm
    have e4 := e3.trans (e5.trans (hval.trans e6))
    rw [mul_assoc]
    exact e1.trans (e2.trans (congrArg₂ (· * ·) (congrArg (fun x : ℂˣ => (x : ℂ)) hchi.symm) e4))
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchroedingerFunctionFockVectorPolynomialGaussian
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

theorem isThetaFunO_annih_of_std {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {θ : InfFam D}
    (hθ : IsInfFam θ) {A B : HSp D} {ν : Measure (WO A B)} {𝓨 : Set (WO A B)} (hν : IsCovolOne (ratL B A) ν 𝓨)
    (τ : D.what₂.Tau)
    (J : Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ → Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ)
    (z : Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ) {f : WO (dblSp A) B → ℂ}
    (hf : IsThetaFunO ψ (dblSp A) B f) :
    IsThetaFunO ψ (dblSp A) B (annih (heisO ψ (dblSp A) B) θ τ J z f) := by
  have h1 := GlobalTheory.OrientedHeis.theta_dRho hθ hψ τ z hf
  have h2 := GlobalTheory.OrientedHeis.theta_dRho hθ hψ τ (J z) hf
  have h3 := (GlobalTheory.T.schrodingerFunction_linear_thetaFunctions D ψ hψ A B ν 𝓨 hν _ _ h2 h2 Complex.I).2.1
  exact (GlobalTheory.T.schrodingerFunction_linear_thetaFunctions D ψ hψ A B ν 𝓨 hν _ _ h1 h3 Complex.I).1

theorem sch_mem_fockA : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ μ : D.host.E, IsSkew μ → ∀ (s' : RealMat (dblSp A)) (sB : RealMat B), IsStdInv A μ s' → (∀ τ, IsCartanInv (gramAt D B τ) (sB τ)) → ∀ l : D.what₂.Tau → ℝ, (∀ τ, |l τ| = ‖tauE D τ D.host.xi0‖ / ‖tauE D τ μ‖) → ∀ f, IsFockVec ψ θ (dblSp A) B s' sB f → sch ψ A B ν 𝓨 f ∈ fockA θ B A.rank l sB := by
  intro D ψ hψ θ hθ A B ν 𝓨 hν μ hμ s' sB hs' hsB l hl f hf
  obtain ⟨hth, N, hN⟩ := hf
  have hS : sch ψ A B ν 𝓨 f ∈ schwartzA θ B.rank A.rank :=
    (GlobalTheory.T.schrodingerTheta_eq_schwartzBruhat D ψ hψ θ hθ A B ν 𝓨 hν).1 f hth
  have key : ∀ L : List (D.what₂.Tau × Matrix (Fin B.rank) (Fin A.rank) ℂ),
      IsThetaFunO ψ (dblSp A) B
        (List.foldr (fun (p : D.what₂.Tau × Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ) g =>
          annih (heisO ψ (dblSp A) B) θ p.1 (cplxO (s' p.1) (sB p.1)) p.2 g) f
          (L.map (fun q => (q.1, q.2 * (dblDec A).qX.map (tauE D q.1))))) ∧
      sch ψ A B ν 𝓨
        (List.foldr (fun (p : D.what₂.Tau × Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ) g =>
          annih (heisO ψ (dblSp A) B) θ p.1 (cplxO (s' p.1) (sB p.1)) p.2 g) f
          (L.map (fun q => (q.1, q.2 * (dblDec A).qX.map (tauE D q.1))))) =
        L.foldr (fun q g => annS B l sB θ q.1 q.2 g) (sch ψ A B ν 𝓨 f) := by
    intro L
    induction L with
    | nil => exact ⟨hth, rfl⟩
    | cons q L ih =>
      obtain ⟨ih1, ih2⟩ := ih
      refine ⟨isThetaFunO_annih_of_std hψ hθ hν _ _ _ ih1, ?_⟩
      rw [List.foldr_cons, ← ih2]
      exact GlobalTheory.T.annihilationOperator_schroedingerFunctions_doubledPair D ψ hψ θ hθ A B ν 𝓨 hν μ hμ s' sB hs' hsB l hl _ ih1 q.1 q.2
  have hz : sch ψ A B ν 𝓨 0 = 0 := by
    have h := (GlobalTheory.T.schrodingerFunction_linear_thetaFunctions D ψ hψ A B ν 𝓨 hν f f hth hth 0).2.2.2
    rwa [zero_smul, zero_smul] at h
  refine GlobalTheory.T.mem_fockSpace_of_polynomial_gaussian_slices D θ hθ B A.rank l sB _ hS
    (GlobalTheory.T.adelicSchwartz_slice_polynomial_gaussian_of_annihilated D θ hθ B A.rank l sB hsB N _ hS ?_)
  intro L hL
  rw [← (key L).2, hN _ (by rw [List.length_map, hL]), hz]

end GlobalTheory.StdUnn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatHalfTensorOrthogonalIdempotents
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.PutIn

theorem isHalf_nsmul {D : D7} {m n : ℕ} {e : AE D} {x : Mx D m n} (hx : IsHalf e x) (k : ℕ) : IsHalf e (k • x) := by
  intro i j
  rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, hx i j]

theorem isHalf_smul_idem {D : D7} {m n : ℕ} {b : AE D} (hbb : b * b = b) (x : Mx D m n) : IsHalf b (b • x) := by
  intro i j
  rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hbb]

theorem isHalf_sub_smul {D : D7} {m n : ℕ} {a b : AE D} (hab : a * b = 0) {u : Mx D m n} (hu : IsHalf (a + b) u) :
    IsHalf a (u - b • u) := by
  intro i j
  have h := hu i j
  rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, mul_sub, ← mul_assoc, hab, zero_mul, sub_zero]
  rw [add_mul] at h
  linear_combination h

theorem isSBHalf_tens : ∀ (D : D7) (S T : HSp D) (a b : AE D) (Λ : AddSubgroup (WO S T)) (Φ Ψ : WO S T → ℂ),
    a * b = 0 → b * b = b → (∀ u ∈ Λ, b • u ∈ Λ) → IsSBHalf a Λ Φ → IsSBHalf b Λ Ψ →
    IsSBHalf (a + b) Λ (GlobalTheory.FinPl.PutIn.tens b Φ Ψ) := by
  intro D S T a b Λ Φ Ψ hab hbb hΛ ⟨hΦs, kΦ, hkΦ, hΦi, hΦb⟩ ⟨hΨs, kΨ, hkΨ, hΨi, hΨb⟩
  refine ⟨?_, kΦ * kΨ, Nat.mul_pos hkΦ hkΨ, ?_, ?_⟩
  · intro t ht
    rw [tens_apply] at ht
    have h1 := hΦs _ (left_ne_zero_of_mul ht)
    have h2 := hΨs _ (right_ne_zero_of_mul ht)
    intro i j
    have e1 := h1 i j
    have e2 := h2 i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at e1 e2
    rw [mul_sub, ← mul_assoc, hab, zero_mul, sub_zero] at e1
    rw [add_mul, e1]
    ring
  · intro u hu hhu t
    have hu1 : u - b • u ∈ Λ := Λ.sub_mem hu (hΛ u hu)
    have hu2 : b • u ∈ Λ := hΛ u hu
    have e1 : (t + (kΦ * kΨ) • u) - b • (t + (kΦ * kΨ) • u) = (t - b • t) + kΦ • (kΨ • (u - b • u)) := by
      ext i j
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul]
      push_cast; ring
    have e2 : b • (t + (kΦ * kΨ) • u) = b • t + kΨ • (kΦ • (b • u)) := by
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul]
      push_cast; ring
    rw [tens_apply, tens_apply, e1, e2,
      hΦi _ (Λ.nsmul_mem hu1 kΨ) (isHalf_nsmul (isHalf_sub_smul hab hhu) kΨ),
      hΨi _ (Λ.nsmul_mem hu2 kΦ) (isHalf_nsmul (isHalf_smul_idem hbb u) kΦ)]
  · intro t ht
    rw [tens_apply] at ht
    have h1 := hΦb _ (left_ne_zero_of_mul ht)
    have h2 := hΨb _ (right_ne_zero_of_mul ht)
    have e : (kΦ * kΨ) • t = kΨ • (kΦ • (t - b • t)) + kΦ • (kΨ • (b • t)) := by
      ext i j
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul]
      push_cast; ring
    rw [e]
    exact Λ.add_mem (Λ.nsmul_mem h1 kΨ) (Λ.nsmul_mem h2 kΦ)

end GlobalTheory.FinPl.PutIn

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondOnCommonRangeOfSecond
section
noncomputable section
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SiegelWeilLitCompare

open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model
open GlobalTheory.IndefiniteRowSideFullHecke
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

variable {D : D7} {n : ℕ}

theorem summable_rat {θ : InfFam D} (hθ : IsInfFam θ) {m : ℕ} (φ : schwartzA θ m n) :
    Summable fun ξ : Matrix (Fin m) (Fin n) D.host.E => ‖φ.1 (ξ.map (incA D))‖ := by
  obtain ⟨N, hN⟩ := GlobalTheory.T.exists_summable_bound_schwartz_majorant_rational_translates D θ hθ m n
  obtain ⟨-, K, hK, hC⟩ := GlobalTheory.T.schwartzBruhatAdelicMatrix_continuous_le_majorant D θ hθ m n φ.1
    (GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA D θ hθ m n φ.1 φ.2)
  obtain ⟨C, hC⟩ := hC N
  obtain ⟨b, hb, hb'⟩ := hN K {0} hK isCompact_singleton
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ξ => (hC _).trans ?_) (hb.mul_left |C|)
  have := hb' 0 rfl ξ
  rw [zero_add] at this
  exact mul_le_mul (le_abs_self C) this (GlobalTheory.Unf.maj_nonneg _ _ _ _) (abs_nonneg C)

theorem gramQ_adj {m : ℕ} {T : Matrix (Fin m) (Fin m) D.host.E} (hT : IsHermND D.sp.cm.sig T) (x y : Mx D m n) :
    adj (GramMatrixBlocks.gramQ T x y) = GramMatrixBlocks.gramQ T y x := by
  have h : adj (rat T : Mx D m m) = rat T := by
    ext i j
    exact (GlobalTheory.DualPairCheck.cA_incA _).trans (congrArg (incA D) (hT.1 i j))
  change adj ((adj x ⬝ (rat T : Mx D m m)) ⬝ y) = (adj y ⬝ (rat T : Mx D m m)) ⬝ x
  rw [adj_mul, adj_mul, adj_adj, h, Matrix.mul_assoc]

theorem selfDual_of_covolOne {m : ℕ} {T : Matrix (Fin m) (Fin m) D.host.E} (hT : IsHermND D.sp.cm.sig T)
    {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {μ : Measure (Mx D m n)} {𝓕 : Set (Mx D m n)}
    (hμ : IsCovolOne (ratMx D m n) μ 𝓕) : SelfDual μ (GramMatrixBlocks.pairing (n := n) T ψ) := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  obtain ⟨h1, h2⟩ := GlobalTheory.T.rationalAdelicMatrices_self_annihilator D m n T hT ψ hψ
  have hs : ∀ x y : Mx D m n, GramMatrixBlocks.pairing T ψ x y = GramMatrixBlocks.pairing T ψ y x := fun x y => by
    unfold GramMatrixBlocks.pairing GramMatrixBlocks.trA
    rw [← gramQ_adj hT x y, ← GlobalTheory.DualPairCheck.trace_cA (Matrix.trace (GramMatrixBlocks.gramQ T x y))]
    congr 2
    simp only [Matrix.trace, map_sum]
    rfl
  refine GlobalTheory.T.selfDual_of_fundamentalDomain_volume_eq_one _ (ratMx D m n) K hK hKc _ (fun y => ?_) hs (fun x x' y => ?_) (fun x y => hψ.2.1 _) h1 h2 μ 𝓕
    hμ.1 hμ.2.1 hμ.2.2
  · simp only [hs _ y]
    haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
    haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
    have ht : Continuous (GramMatrixBlocks.trA (D := D)) :=
      IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D))
    exact hψ.1.comp (ht.comp (continuous_const.matrix_mul continuous_id).matrix_trace)
  · simp only [hs _ y]
    unfold GramMatrixBlocks.pairing GramMatrixBlocks.trA GramMatrixBlocks.gramQ GramMatrixBlocks.mmul
    rw [Matrix.mul_add, Matrix.trace_add, map_add, AddChar.map_add_eq_mul]

theorem mem_siegelParabolic_of_lowerLeft_entries_eq_zero {g : G D n}
    (h : ∀ i j, mat g (finSumFinEquiv (.inr i)) (finSumFinEquiv (.inl j)) = 0)
    (h' : ∀ i j, mat g⁻¹ (finSumFinEquiv (.inr i)) (finSumFinEquiv (.inl j)) = 0) : g ∈ P D n := by
  have key : ∀ g : G D n, (∀ i j, mat g (finSumFinEquiv (.inr i)) (finSumFinEquiv (.inl j)) = 0) →
      ∀ x ∈ upperHalf D n, (mat g).mulVec x ∈ upperHalf D n := by
    intro g h x hx
    ext i
    have hx' : ∀ j, x (finSumFinEquiv (Sum.inr j : Fin n ⊕ Fin n)) = 0 := fun j => congrFun hx j
    simp only [LinearMap.funLeft_apply, Matrix.mulVec, dotProduct, Pi.zero_apply]
    rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
    simp only [h, hx', zero_mul, mul_zero, Finset.sum_const_zero, add_zero]
  refine fun x => ⟨key g h x, fun hx => ?_⟩
  have := key _ h' _ hx
  change (mat g⁻¹).mulVec ((mat g).mulVec x) ∈ _ at this
  rwa [Matrix.mulVec_mulVec, show mat g⁻¹ * mat g = mat (g⁻¹ * g) from rfl, inv_mul_cancel,
    show mat (1 : G D n) = 1 from rfl, Matrix.one_mulVec] at this

theorem siegel_eq : GramMatrixBlocks.siegel D n = P D n := by
  have lower : ∀ g : G D n, g ∈ GramMatrixBlocks.siegel D n →
      ∀ i j, mat g (finSumFinEquiv (.inr i)) (finSumFinEquiv (.inl j)) = 0 := fun g hg i j =>
    hg (by simp [GramMatrixBlocks.blockIdx])
  ext g
  refine ⟨fun hg => mem_siegelParabolic_of_lowerLeft_entries_eq_zero (lower g hg) (lower _ ((GramMatrixBlocks.siegel D n).inv_mem hg)), fun hg i j hij => ?_⟩
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases i with i | i <;> rcases j with j | j
  · simp [GramMatrixBlocks.blockIdx] at hij
  · simp [GramMatrixBlocks.blockIdx] at hij
  · exact lower_eq_zero hg i j
  · simp [GramMatrixBlocks.blockIdx] at hij

theorem hE_equivFun (V : HSp D) (x y : V.V) :
    hE D.sp.cm.sig V.gram (V.frame.equivFun x) (V.frame.equivFun y) = V.hT x y := by
  conv_rhs => rw [← V.frame.sum_equivFun x, ← V.frame.sum_equivFun y]
  simp only [hE, Formalism.UG.hform, HSpace.gram, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul,
    LinearMap.smul_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  change star _ * _ * _ = _ * (star _ * _)
  ring

theorem wittIdx_eq (V : HSp D) : GramMatrixBlocks.wittIdx V.gram = Formalism.MainNotions.SchurIrreducible.wittIdx V := by
  unfold GramMatrixBlocks.wittIdx Formalism.MainNotions.SchurIrreducible.wittIdx
  refine congrArg sSup (Set.ext fun r => ⟨?_, ?_⟩)
  · rintro ⟨W, hW, hr⟩
    refine ⟨W.map V.frame.equivFun.symm.toLinearMap, (LinearEquiv.finrank_map_eq V.frame.equivFun.symm W).trans hr, ?_⟩
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    refine (hE_equivFun V _ _).symm.trans ?_
    rw [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    exact hW x hx y hy
  · rintro ⟨W, hr, hW⟩
    refine ⟨W.map V.frame.equivFun.toLinearMap, ?_, (LinearEquiv.finrank_map_eq V.frame.equivFun W).trans hr⟩
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact (hE_equivFun V x y).trans (hW x hx y hy)

variable {V : HSp D} {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle}

theorem gramQ_eq (x y : Mx D V.rank n) : GramMatrixBlocks.gramQ V.gram x y = StdUnn.inner V x y := Matrix.mul_assoc _ _ _

def resG (ω : GramMatrixBlocks.Rep θ n V.gram) : G D n →* Module.End ℂ (schwartzA θ V.rank n) := ω.comp (MonoidHom.inl _ _)

theorem isWeilSch_unique {μ : Measure (Mx D V.rank n)} {ω ω' : G D n →* Module.End ℂ (schwartzA θ V.rank n)}
    (h : IsWeilSch ψ χ θ V μ ω) (h' : IsWeilSch ψ χ θ V μ ω') : ω = ω' := by
  have := GlobalTheory.T.unitaryUnn_subgroup_eq_top_of_leviUnipotentWeyl D n (ω.toHomUnits.eqLocus ω'.toHomUnits)
    (fun g a hg => Units.ext (LinearMap.ext fun Φ => Subtype.ext (funext fun x =>
      (h.levi g a hg Φ x).trans (h'.levi g a hg Φ x).symm)))
    (fun g b hg => Units.ext (LinearMap.ext fun Φ => Subtype.ext (funext fun x =>
      (h.unip g b hg Φ x).trans (h'.unip g b hg Φ x).symm)))
    (fun g hg => Units.ext (LinearMap.ext fun Φ => Subtype.ext (funext fun x =>
      (h.weyl g hg Φ x).trans (h'.weyl g hg Φ x).symm)))
  refine MonoidHom.ext fun g => ?_
  have hg : g ∈ ω.toHomUnits.eqLocus ω'.toHomUnits := this ▸ Subgroup.mem_top g
  exact congrArg Units.val hg

theorem sect_eq (ω : GramMatrixBlocks.Rep θ n V.gram) (H : G D n → ℝ≥0) (Φ : schwartzA θ V.rank n) (z : ℂ) :
    GramMatrixBlocks.sect H ω Φ z = sect (resG ω) H Φ z := rfl

theorem summable_iff (ω : GramMatrixBlocks.Rep θ n V.gram) (H : G D n → ℝ≥0) (Φ : schwartzA θ V.rank n) (g : G D n) (z : ℂ) :
    (Summable fun γ => ‖GramMatrixBlocks.eisTerm H ω Φ g z γ‖) ↔ Eis.CosetConv (P D n) (GF D n) (sect (resG ω) H Φ z) g := by
  rw [← siegel_eq]
  rfl

theorem tsum_eq (ω : GramMatrixBlocks.Rep θ n V.gram) (H : G D n → ℝ≥0) (Φ : schwartzA θ V.rank n) (g : G D n) (z : ℂ) :
    ∑' γ, GramMatrixBlocks.eisTerm H ω Φ g z γ = Eis.cosetSum (P D n) (GF D n) (sect (resG ω) H Φ z) g := by
  rw [← siegel_eq]
  rfl

theorem leftInv_theta (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) (Φ : schwartzA θ V.rank n) (g : G D n) :
    LeftInv (GQ V) (theta ω Φ g) := by
  intro γ hγ h
  obtain ⟨u, hu⟩ : ∃ u : GL (Fin V.rank) D.host.E, mt V γ⁻¹ = rat u.1 := by
    obtain ⟨u, -, hu⟩ := (GQ V).inv_mem hγ
    exact ⟨u, (congrArg Units.val hu).symm⟩
  let e : Matrix (Fin V.rank) (Fin n) D.host.E ≃ Matrix (Fin V.rank) (Fin n) D.host.E :=
    ⟨fun ξ => u.1 * ξ, fun ξ => (u⁻¹).1 * ξ, fun ξ => by simp [← Matrix.mul_assoc], fun ξ => by simp [← Matrix.mul_assoc]⟩
  refine (tsum_congr fun ξ => ?_).trans (e.tsum_eq _)
  have : mt V (γ * h)⁻¹ = mt V h⁻¹ * mt V γ⁻¹ := by rw [mul_inv_rev]; rfl
  rw [this, hu, Matrix.mul_assoc, ← rat_mul]
  rfl

def ContinuesAt {m : ℕ} {T : Matrix (Fin m) (Fin m) D.host.E} (α : GramMatrixBlocks.GG D n → ℝ≥0) (ω : GramMatrixBlocks.Rep θ n T)
    (Φ : GramMatrixBlocks.Sch θ m n) (g : GramMatrixBlocks.GG D n) : Prop :=
  ∃ E : ℂ → ℂ, MeromorphicOn E Set.univ ∧ ∀ s : ℂ, (n : ℝ) / 2 < s.re → E s = ∑' γ, GramMatrixBlocks.eisTerm α ω Φ g s γ

def SecondOnCommonRange : Prop :=
  ∀ (D : D7) (n : ℕ) (V : HSp D), n < V.rank → V.rank ≤ 2 * n → n + Formalism.MainNotions.SchurIrreducible.wittIdx V < V.rank →
    GramMatrixBlocks.FormulaFor n V.gram

def WeilExists : Prop :=
  ∀ (D : D7) (n : ℕ) (V : HSp D), n < V.rank → V.rank ≤ 2 * n → n + Formalism.MainNotions.SchurIrreducible.wittIdx V < V.rank →
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (θ : InfFam D),
    IsCharAF D.host.F ψ → IsHeckeChar D χ → ResEta D χ V.rank → IsInfFam θ →
    ∃ ω : GramMatrixBlocks.Rep θ n V.gram, GramMatrixBlocks.IsWeil ψ χ ω

def PlaneContinuation : Prop :=
  ∀ (D : D7) (n : ℕ) (V : HSp D), n < V.rank → V.rank ≤ 2 * n → n + Formalism.MainNotions.SchurIrreducible.wittIdx V < V.rank →
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (θ : InfFam D),
    IsCharAF D.host.F ψ → IsHeckeChar D χ → ResEta D χ V.rank → IsInfFam θ →
  ∀ ω : GramMatrixBlocks.Rep θ n V.gram, GramMatrixBlocks.IsWeil ψ χ ω → ∀ α : GramMatrixBlocks.GG D n → ℝ≥0, GramMatrixBlocks.IsAbsLevi α →
  ∀ c : D.what₂.Tau → ℝ, GramMatrixBlocks.IsRealPart ψ θ c →
  ∀ s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, IsCartanInv (V.gram.map (tauE D τ)) (s τ)) →
  ∀ Φ : GramMatrixBlocks.Sch θ V.rank n, Φ.1 ∈ GramMatrixBlocks.fockSpace θ n V.gram c s → ∀ g, ContinuesAt α ω Φ g

end GlobalTheory.SiegelWeilLitCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SemicharacterSqEqOneOnHalfAStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semicharacter_sq_eq_one_on_halfA : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ (c : ℕ), 0 < c → Odd c → ∀ x' ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, alV D.host.d sc (embH (tauE D) δ x') * alV D.host.d sc (embH (tauE D) δ x') = 1 := by
  first | exact @GlobalTheory.AdForm.HalfASign.alV_mul_self_halfA | exact GlobalTheory.AdForm.HalfASign.alV_mul_self_halfA | (intros; apply GlobalTheory.AdForm.HalfASign.alV_mul_self_halfA <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitComponentIntegerResidueZeroIffMemPrime
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PhiOneVal

noncomputable section

namespace GlobalTheory.PhiOneVal

theorem residue_pr_int_eq_zero_iff : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)
    (P : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e P → ∀ c : 𝓞 D.host.E,
    ∃ h : p.pr (incA D (algebraMap (𝓞 D.host.E) D.host.E c)) ∈ 𝒪[k], (residue 𝒪[k] ⟨_, h⟩ = 0 ↔ c ∈ P.asIdeal) := by
  intro D k _ _ _ _ p P hP c
  have h : p.pr (incA D (c : D.host.E)) ∈ 𝒪[k] := GlobalTheory.LocMod.FullLatFrame.pr_int_mem p c
  refine ⟨h, ?_⟩
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  by_cases hc : c = 0
  · subst hc
    have h0 : (⟨_, h⟩ : 𝒪[k]) = 0 := by
      apply Subtype.ext
      simp
    refine ⟨fun _ => zero_mem _, fun _ hu => ?_⟩
    exact not_isUnit_zero (h0 ▸ hu)
  have hc' : (c : D.host.E) ≠ 0 := fun h0 => hc (Subtype.ext h0)
  have hinv : p.pr (incA D (c : D.host.E)) * p.pr (incA D (c : D.host.E)⁻¹) = 1 := by
    rw [← RingHom.map_mul, ← map_mul (incA D), mul_inv_cancel₀ hc', map_one, map_one]
  rw [hP.2 c hc, ← p.sec_pr, ← p.int_iff]
  apply not_congr
  constructor
  · intro hu
    obtain ⟨y, hy⟩ := hu.exists_right_inv
    have hy' : p.pr (incA D (c : D.host.E)) * (y : k) = 1 := congrArg Subtype.val hy
    have hne : p.pr (incA D (c : D.host.E)) ≠ 0 := left_ne_zero_of_mul_eq_one hinv
    have : p.pr (incA D (c : D.host.E)⁻¹) = y := mul_left_cancel₀ hne (hinv.trans hy'.symm)
    rw [this]; exact y.2
  · intro hi
    exact IsUnit.of_mul_eq_one (⟨_, hi⟩ : 𝒪[k]) (Subtype.ext hinv)

end GlobalTheory.PhiOneVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceChartParahoricLevelStabiliserHeightStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaceChart_parahoric_level_stabiliser_height : ∀ D : D7, ForStageQ D fun c w j s => ∀ PP ∈ w.Q, ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → v = PP.under (𝓞 D.host.F) ∧ GlobalTheory.SplitWeil.resCard (Fv D.host.F v) = Ideal.absNorm PP.asIdeal ∧ (∀ ξl, LiftsChar φ PP ξl (w.ξ PP) → GlobalTheory.SplitWeil.IsTame ξl ∧ ¬ GlobalTheory.SplitWeil.IsUnram ξl) ∧ (∀ k < D.R.m, ∀ μ : (Fv D.host.F v)ˣ →* ℂˣ, ((∀ (x : (AE D)ˣ) (y : (Fv D.host.F v)ˣ), (∃ e, IsIdemOf φ e ∧ (1 - e) * (x : AE D) = 1 - e ∧ rdA φ (x : AE D) = y) → μ y = Circle.toUnits (c.chS (k + 1) x)) ∨ (∀ (x : (AE D)ˣ) (y : (Fv D.host.F v)ˣ), (∃ e, IsIdemOf φ e ∧ (1 - e) * (x : AE D) = 1 - e ∧ rdA φ (x : AE D) = y) → μ y = Circle.toUnits (c.chT (k + 1) x))) → LiftsChar φ PP μ (w.ξ PP)) ∧ ∀ ι, IsChart s j φ ι → (∃ e : GL (Fin D.R.r ⊕ Blocks j D.R.t) (Fv D.host.F v) ≃ₜ* GlobalTheory.FinZeta.Gv s.V v, (∀ y, ι y = GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v (e y)) ∧ (∀ y, e y ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v ↔ y ∈ GlobalTheory.SplitWeil.KO (Fv D.host.F v) _) ∧ ∀ x ϖ, IsLocUnif φ x ϖ → GlobalTheory.ParHecke.IsHgt ϖ fun y => GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV s.V s.Λ v (e y)) ∧ (∀ y, ι y ∈ Lev.levG s.V s.β s.L ↔ y ∈ parahoric (Fv D.host.F v) _ _) ∧ ∀ ξl, LiftsChar φ PP ξl (w.ξ PP) → ∀ y ∈ parahoric (Fv D.host.F v) _ _, ∀ d : (Fv D.host.F v)ˣ, (d : Fv D.host.F v) = y.1.toBlocks₂₂.det → Lev.levChi s.V s.β s.L (ι y) = (((ξl d)⁻¹ : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.ChartTwist.chart_dict | exact GlobalTheory.ChartTwist.chart_dict | (intros; apply GlobalTheory.ChartTwist.chart_dict <;> assumption)
end

