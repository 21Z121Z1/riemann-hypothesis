import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0527
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0500
import Development.AutomorphicSpectrum.Proofs.HermitianForms.CasOfCapelliVec
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0513
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0523
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0011
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSmoothHermConstLine
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0508
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0018
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0019
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0520

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmegaOperatorEqCasimirSumStatement
section
set_option maxSynthPendingDepth 1
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.omega_operator_eq_casimir_sum : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a d : ℕ)
    (b : Module.Basis (Fin d) ℝ (AutomorphicForm.isExpLieAlgebra E a).lieSubalgebra) (ε : Fin d → ℝ),
    (∀ i, ε i = 1 ∨ ε i = -1) →
    (∀ i j, AutomorphicForm.archTraceForm E a (b i) (b j) = if i = j then ε i else 0) →
    GlobalTheory.CompanionTheory.HCRep.omegaOp (⇑b) ε = (2 : ℂ) • ∑ w : InfinitePlace E,
      (Formalism.REAL.Cas (Eop (a := a) w.embedding) +
        Formalism.REAL.Cas (Eop (a := a) (ComplexEmbedding.conjugate w.embedding))) := by
  first | exact @GlobalTheory.CompanionTheory.HCRep.TraceCas.omegaOp_eq_two_cas | exact GlobalTheory.CompanionTheory.HCRep.TraceCas.omegaOp_eq_two_cas | (intros; apply GlobalTheory.CompanionTheory.HCRep.TraceCas.omegaOp_eq_two_cas <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PointIdealHorizontalIffCharZero
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict

private theorem C_mem_ptIdeal_iff_intCast_residueField_eq_zero (m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ m n) (c : ℤ) :
    (MvPolynomial.C c : Geo.MRing (Bk n)) ∈ ptIdeal x ↔ ((c : ℤ) : (MP ℤ m n).residueField x) = 0 := by
  rw [ptIdeal, Geo.mCoordIdeal, RingHom.mem_ker, Geo.mConeMap, MvPolynomial.aeval_C, eq_intCast,
    ← map_intCast (MvPolynomial.C : (MP ℤ m n).residueField x →+* MvPolynomial (Fin (m + 1)) ((MP ℤ m n).residueField x)) c,
    MvPolynomial.C_eq_zero]

theorem ptIdeal_isHorizontal_iff (m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ m n) :
    Geo.IsHorizontal (ptIdeal x) ↔ CharZero ((MP ℤ m n).residueField x) := by
  constructor
  · intro h
    have h' : (ptIdeal x).comap (MvPolynomial.C : ℤ →+* Geo.MRing (Bk n)) = ⊥ := h
    refine charZero_of_inj_zero fun k hk => ?_
    have hm : ((k : ℤ)) ∈ (ptIdeal x).comap (MvPolynomial.C : ℤ →+* Geo.MRing (Bk n)) := by
      rw [Ideal.mem_comap, C_mem_ptIdeal_iff_intCast_residueField_eq_zero]
      exact_mod_cast hk
    rw [h', Ideal.mem_bot] at hm
    exact_mod_cast hm
  · intro h
    show (ptIdeal x).comap (MvPolynomial.C : ℤ →+* Geo.MRing (Bk n)) = ⊥
    rw [eq_bot_iff]
    intro c hc
    rw [Ideal.mem_bot]
    rw [Ideal.mem_comap, C_mem_ptIdeal_iff_intCast_residueField_eq_zero] at hc
    exact Int.cast_eq_zero.mp hc

end GlobalTheory.CompanionTheory.MPDict
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PointIdealMultiprojectivePrime
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem ptCoord_ptChart (x : MP ℤ m n) (k : Fin (m + 1)) : ptCoord x ⟨k, ptChart x k⟩ = 1 := by
  simp [ptCoord]

theorem isMultiProjPrime_ptIdeal (m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ m n) :
    Geo.IsMultiProjPrime (ptIdeal x) :=
  ⟨RingHom.ker_isPrime _, GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal (ptCoord x),
    GroundTheory.Heights₂.Heights.CoordinateConeArithVar.relevant (ptCoord x) (ptChart x) fun k => by
      rw [ptCoord_ptChart]; exact one_ne_zero⟩

end GlobalTheory.CompanionTheory.MPDict
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PositivityPullsBackToSubspaceStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.positivity_pulls_back_to_subspace : ∀ (m n : ℕ) (G : Matrix (Fin m) (Fin m) ℂ) (y : Matrix (Fin m) (Fin n) ℂ) (ε : ℝ) (S : Submodule ℂ (Fin n → ℂ)), GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.PosOn ε (y.conjTranspose * G * y) S → ∃ T : Submodule ℂ (Fin m → ℂ), GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.PosOn ε G T ∧ Module.finrank ℂ T = Module.finrank ℂ S := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.exists_posOn_of_gram | exact GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.exists_posOn_of_gram | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.exists_posOn_of_gram <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdNormPull
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.PullRep

def plU {X Y : Scheme.{0}} (f : Y ⟶ X) {U : X.Opens} {W : Y.Opens} (h : W ≤ f ⁻¹ᵁ U) :
    Γ(X, U)ˣ →* Γ(Y, W)ˣ := (res h).comp (pullU f U)

theorem res_plU {X Y : Scheme.{0}} (f : Y ⟶ X) {U : X.Opens} {W V : Y.Opens} (h : W ≤ f ⁻¹ᵁ U)
    (l : V ≤ W) (x : Γ(X, U)ˣ) : res l (plU f h x) = plU f (l.trans h) x :=
  Units.ext (resG_appLE f h l (x : Γ(X, U)))

theorem plU_res {X Y : Scheme.{0}} (f : Y ⟶ X) {U U' : X.Opens} {W : Y.Opens} (l : U' ≤ U)
    (h : W ≤ f ⁻¹ᵁ U') (x : Γ(X, U)ˣ) : plU f h (res l x) = plU f (h.trans (f.preimage_mono l)) x :=
  Units.ext (appLE_resG f l h (x : Γ(X, U)))

theorem plU_plU {X Y Z : Scheme.{0}} (g : Z ⟶ Y) (f : Y ⟶ X) {U : X.Opens} {V : Y.Opens} {W : Z.Opens}
    (h : V ≤ f ⁻¹ᵁ U) (h' : W ≤ g ⁻¹ᵁ V) (x : Γ(X, U)ˣ) :
    plU g h' (plU f h x) = plU (g ≫ f) (h'.trans (g.preimage_mono h)) x :=
  Units.ext (appLE_appLE g f h h' (x : Γ(X, U)))

theorem lbPull_g {X Y : Scheme.{0}} (B : LB X) (f : Y ⟶ X) (i j : PUnit → B.ι) :
    (B.pull f).g i j = plU f (le_inf (inf_le_left.trans (LB.wchart_le B (fun _ => f) i PUnit.unit))
      (inf_le_right.trans (LB.wchart_le B (fun _ => f) j PUnit.unit)) :
        (B.pull f).U i ⊓ (B.pull f).U j ≤ f ⁻¹ᵁ (B.U (i PUnit.unit) ⊓ B.U (j PUnit.unit)))
      (B.g (i PUnit.unit) (j PUnit.unit)) := by
  show ∏ k : PUnit, (plU f _ (B.g (i k) (j k))) ^ ((fun _ => (1 : ℤ)) k) = _
  rw [Fintype.prod_unique]
  exact zpow_one _

variable {n' m : ℕ} {n : Fin (m + 1) → ℕ}

abbrev qq (n' m : ℕ) (n : Fin (m + 1) → ℕ) : MP ℤ (m + 1) (consN n' n) ⟶ MP ℤ m n := qpSnd n' m n

theorem qq_str (n' m : ℕ) (n : Fin (m + 1) → ℕ) : qq n' m n ≫ mpStr ℤ m n = mpStr ℤ (m + 1) (consN n' n) :=
  qpSnd_str n' m n

def tl (c : ∀ k, Bk (consN n' n) k) : ∀ k, Bk n k := fun k => c k.succ

theorem mchart_le_pull (c : ∀ k, Bk (consN n' n) k) :
    mchart c ≤ qq n' m n ⁻¹ᵁ mchart (tl c) :=
  fun _ hx => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx k.succ

theorem pullDeg_zero (a : Fin (m + 1) → ℤ) : pullDeg (Fin.succ : Fin (m + 1) → Fin (m + 2)) a 0 = 0 := by
  unfold pullDeg
  rw [Function.extend_apply']
  · rfl
  · rintro ⟨k, hk⟩
    exact Fin.succ_ne_zero k hk

theorem pullDeg_succ (a : Fin (m + 1) → ℤ) (k : Fin (m + 1)) :
    pullDeg (Fin.succ : Fin (m + 1) → Fin (m + 2)) a k.succ = a k :=
  (Fin.succ_injective _).extend_apply _ _ _

theorem blockUnit_succ {k : Fin (m + 1)} (i j : Bk n k) {W : (MP ℤ (m + 1) (consN n' n)).Opens}
    {W₀ : (MP ℤ m n).Opens} (h : W ≤ prB (consN n' n) k.succ ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) j))
    (H : W ≤ qq n' m n ⁻¹ᵁ W₀) (h₀ : W₀ ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) j)) :
    blockUnit (n := consN n' n) (k := k.succ) i j h = plU (qq n' m n) H (blockUnit i j h₀) :=
  (plU_plU (qq n' m n) (prB n k) h₀ H _).symm

theorem prod_blockUnit (c c' : ∀ k, Bk (consN n' n) k) {W : (MP ℤ (m + 1) (consN n' n)).Opens}
    {V : (MP ℤ m n).Opens} (HV : W ≤ qq n' m n ⁻¹ᵁ V) (hW : W ≤ mchart c ⊓ mchart c')
    (hV : V ≤ mchart (tl c) ⊓ mchart (tl c')) (a : Fin (m + 1) → ℤ) :
    ∏ k, blockUnit (c k) (c' k) (fun _ hx => ⟨mchart_le c k (hW hx).1, mchart_le c' k (hW hx).2⟩ :
        W ≤ prB (consN n' n) k ⁻¹ᵁ (chart ℤ (consN n' n k) (c k) ⊓ chart ℤ (consN n' n k) (c' k))) ^
          pullDeg (Fin.succ : Fin (m + 1) → Fin (m + 2)) a k =
      plU (qq n' m n) HV (∏ k, blockUnit (tl c k) (tl c' k)
        (fun _ hx => ⟨mchart_le (tl c) k (hV hx).1, mchart_le (tl c') k (hV hx).2⟩ :
          V ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (tl c k) ⊓ chart ℤ (n k) (tl c' k))) ^ a k) := by
  rw [map_prod, Fin.prod_univ_succ, pullDeg_zero, zpow_zero, one_mul]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_zpow, pullDeg_succ]
  exact congrArg (· ^ a k) (blockUnit_succ _ _ _ HV _)

theorem prod_norm_pull (z : (Σ k, Bk (consN n' n) k) → ℂ) (c : ∀ k, Bk (consN n' n) k) (a : Fin (m + 1) → ℤ) :
    ∏ k, ‖z ⟨k, c k⟩‖ ^ pullDeg (Fin.succ : Fin (m + 1) → Fin (m + 2)) a k =
      ∏ k, ‖z (sv n' n ⟨k, tl c k⟩)‖ ^ a k := by
  rw [Fin.prod_univ_succ, pullDeg_zero, zpow_zero, one_mul]
  simp only [pullDeg_succ]
  rfl

theorem isUnder_map {y' : CxPts (mpStr ℤ (m + 1) (consN n' n)) σ₀} {z' : (Σ k, Bk (consN n' n) k) → ℂ}
    (h : IsUnder y' z') :
    IsUnder (Points.PtsOver.map (qq n' m n) (qq_str n' m n) _ y') (fun p => z' (sv n' n p)) := by
  intro k i
  refine ⟨(h k.succ i).1, fun j hy => ?_⟩
  have e := (h k.succ i).2 j hy
  calc CxPts.ev (mpStr ℤ m n) σ₀ (blockChart n k i) (pullRatio (prB n k) _ i le_rfl j)
        (Points.PtsOver.map (qq n' m n) (qq_str n' m n) _ y')
      = CxPts.ev (mpStr ℤ (m + 1) (consN n' n)) σ₀ (qq n' m n ⁻¹ᵁ blockChart n k i)
          ((qq n' m n).app _ (pullRatio (prB n k) _ i le_rfl j)) y' :=
        (ev_app (qq n' m n) (qq_str n' m n) _ _ y').symm
    _ = CxPts.ev (mpStr ℤ (m + 1) (consN n' n)) σ₀ (qq n' m n ⁻¹ᵁ blockChart n k i)
          (pullRatio (qq n' m n ≫ prB n k) _ i le_rfl j) y' := by
        rw [Scheme.Hom.app_eq_appLE, appLE_pullRatio]
    _ = _ := e

theorem ev_plU {y' : CxPts (mpStr ℤ (m + 1) (consN n' n)) σ₀} {U : (MP ℤ m n).Opens}
    {W : (MP ℤ (m + 1) (consN n' n)).Opens} (H : W ≤ qq n' m n ⁻¹ᵁ U)
    (hy : y' ∈ ptsIn (mpStr ℤ (m + 1) (consN n' n)) σ₀ W) (x : Γ(MP ℤ m n, U)ˣ) :
    CxPts.ev (mpStr ℤ (m + 1) (consN n' n)) σ₀ W (plU (qq n' m n) H x : Γ(MP ℤ (m + 1) (consN n' n), W)) y' =
      CxPts.ev (mpStr ℤ m n) σ₀ U (x : Γ(MP ℤ m n, U)) (Points.PtsOver.map (qq n' m n) (qq_str n' m n) _ y') :=
  (ev_res H hy _).trans (ev_app (qq n' m n) (qq_str n' m n) U _ y')

end GlobalTheory.CompanionTheory.MPDict.PullRep

namespace GlobalTheory.CompanionTheory.MPDict

open GlobalTheory.CompanionTheory.MPDict.PullRep

theorem isHermRep_pull (n' m : ℕ) (n : Fin (m + 1) → ℕ) (M : HermLB (mpStr ℤ m n)) (A : Geo.HermLine (Bk n))
    (hM : IsHermRep M A) :
    IsHermRep (m := m + 1) (n := consN n' n) (M.pull (qpSnd n' m n) (qpSnd_str n' m n)) (pullLine n' A) := by
  show IsHermRep (M.pull (qq n' m n) (qq_str n' m n)) (pullLine n' A)
  obtain ⟨u, h1, h2, h3⟩ := hM
  have Hu : ∀ (i : PUnit → M.B.ι) (c : ∀ k, Bk (consN n' n) k),
      (M.pull (qq n' m n) (qq_str n' m n)).B.U i ⊓ mchart c ≤
        qq n' m n ⁻¹ᵁ (M.B.U (i PUnit.unit) ⊓ mchart (tl c)) := fun i c x hx =>
    ⟨LB.wchart_le M.B (fun _ => qq n' m n) i PUnit.unit hx.1, mchart_le_pull c hx.2⟩
  refine ⟨fun i c => plU (qq n' m n) (Hu i c) (u (i PUnit.unit) (tl c)), ?_, ?_, ?_⟩
  · intro i j c
    have HV : (M.pull (qq n' m n) (qq_str n' m n)).B.U i ⊓
        (M.pull (qq n' m n) (qq_str n' m n)).B.U j ⊓ mchart c ≤
          qq n' m n ⁻¹ᵁ (M.B.U (i PUnit.unit) ⊓ M.B.U (j PUnit.unit) ⊓ mchart (tl c)) := fun x hx =>
      ⟨⟨LB.wchart_le M.B (fun _ => qq n' m n) i PUnit.unit hx.1.1,
        LB.wchart_le M.B (fun _ => qq n' m n) j PUnit.unit hx.1.2⟩, mchart_le_pull c hx.2⟩
    have e := congrArg (plU (qq n' m n) HV) (h1 (i PUnit.unit) (j PUnit.unit) (tl c))
    rw [map_mul, plU_res, plU_res, plU_res] at e
    exact (res_plU _ _ _ _).trans (e.trans (congrArg₂ (· * ·)
      ((congrArg (Semi.res _) (lbPull_g M.B (qq n' m n) i j)).trans (res_plU _ _ _ _)).symm
      (res_plU _ _ _ _).symm))
  · intro i c c'
    have HV : (M.pull (qq n' m n) (qq_str n' m n)).B.U i ⊓
        (mchart c ⊓ mchart c') ≤ qq n' m n ⁻¹ᵁ (M.B.U (i PUnit.unit) ⊓ (mchart (tl c) ⊓ mchart (tl c'))) :=
      fun x hx => ⟨LB.wchart_le M.B (fun _ => qq n' m n) i PUnit.unit hx.1, mchart_le_pull c hx.2.1,
        mchart_le_pull c' hx.2.2⟩
    have e := congrArg (plU (qq n' m n) HV) (h2 (i PUnit.unit) (tl c) (tl c'))
    rw [map_mul, plU_res, plU_res] at e
    rw [res_plU, res_plU]
    refine e.trans (congrArg₂ (· * ·) rfl ?_)
    exact (prod_blockUnit c c' HV (fun _ hx => hx.2) (fun _ hx => hx.2) A.a).symm
  · intro i c y z hz hy
    have hy0 : Points.PtsOver.map (qq n' m n) (qq_str n' m n) _ y ∈
        ptsIn (mpStr ℤ m n) σ₀ (M.B.U (i PUnit.unit) ⊓ mchart (tl c)) :=
      Points.le_preimage_comp y.1 (qq n' m n) (Hu i c) hy
    have e := h3 (i PUnit.unit) (tl c) _ _ (isUnder_map hz) hy0
    have ev_e := ev_plU (Hu i c) hy (u (i PUnit.unit) (tl c))
    have φ_e := (M.φ σ₀).pull_φ (qq n' m n) (qq_str n' m n) i y
    show A.h (fun p => z (sv n' n p)) = _
    rw [e]
    refine congrArg₂ (· * ·) (congrArg₂ (· * ·) (prod_norm_pull z c A.a).symm ?_) ?_
    · exact congrArg (‖·‖) ev_e.symm
    · exact congrArg (fun t => Real.exp (t / 2)) φ_e.symm

end GlobalTheory.CompanionTheory.MPDict
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdZpowSingle
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.TwUnits

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem res_res' {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (h'' : W ≤ U) (x : Γ(X, U)ˣ) :
    Semi.res h' (Semi.res h x) = Semi.res h'' x := by
  apply Units.ext
  change (X.presheaf.map (homOfLE h').op).hom ((X.presheaf.map (homOfLE h).op).hom x.val) = _
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem res_div_g {X : Scheme.{0}} (T L : LB X) (p q : T.ι × L.ι) {W : X.Opens}
    (h : W ≤ (T.U p.1 ⊓ L.U p.2) ⊓ (T.U q.1 ⊓ L.U q.2)) (h₁ : W ≤ T.U p.1 ⊓ T.U q.1) (h₂ : W ≤ L.U p.2 ⊓ L.U q.2) :
    Semi.res h ((LB.div T L).g p q) = Semi.res h₁ (T.g p.1 q.1) * (Semi.res h₂ (L.g p.2 q.2))⁻¹ :=
  (map_mul (Semi.res h) _ _).trans (congrArg₂ (· * ·) (res_res' _ _ h₁ _)
    ((map_inv (Semi.res h) _).trans (congrArg (·⁻¹) (res_res' _ _ h₂ _))))

theorem iso_law {X : Scheme.{0}} {L T : LB X} {w : LB.Iso L T} (hw : w.IsGen) (p q : T.ι × L.ι) {W : X.Opens}
    (hp : W ≤ T.U p.1 ⊓ L.U p.2) (hq : W ≤ T.U q.1 ⊓ L.U q.2) (h₁ : W ≤ T.U p.1 ⊓ T.U q.1)
    (h₂ : W ≤ L.U p.2 ⊓ L.U q.2) :
    Semi.res hp (w.s p) = Semi.res h₁ (T.g p.1 q.1) * (Semi.res h₂ (L.g p.2 q.2))⁻¹ * Semi.res hq (w.s q) := by
  have e := congrArg (Semi.res (le_inf hp hq)) (hw p q)
  exact ((res_res' _ _ hp _).symm.trans e).trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (res_div_g T L p q (le_inf hp hq) h₁ h₂) (res_res' _ _ hq _)))

theorem res_pull_g (k : Fin (m + 1)) (j j' : PUnit → Bk n k) {W : (MP ℤ m n).Opens}
    (h : W ≤ ((O1 ℤ (n k)).pull (pr ℤ m n k)).U j ⊓ ((O1 ℤ (n k)).pull (pr ℤ m n k)).U j')
    (h' : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (j PUnit.unit) ⊓ chart ℤ (n k) (j' PUnit.unit))) :
    Semi.res h (((O1 ℤ (n k)).pull (pr ℤ m n k)).g j j') = blockUnit (j PUnit.unit) (j' PUnit.unit) h' := by
  have e := linComb_punit_g (O1 ℤ (n k)) (pr ℤ m n k) 1 j j'
  rw [zpow_one] at e
  exact (congrArg (Semi.res h) e).trans (res_res' _ _ h' _)

def twIdx (b : Fin m) (t : ℤ) (c : ∀ k, Bk n k) : (twB m n b t).ι :=
  Prod.mk (fun _ => c b.succ) (fun _ => c 0)

theorem mchart_le_U (b : Fin m) (t : ℤ) (c : ∀ k, Bk n k) : mchart c ≤ (twB m n b t).U (twIdx b t c) :=
  fun _ hx => ⟨Set.mem_iInter.2 fun _ => mchart_le c _ hx, Set.mem_iInter.2 fun _ => mchart_le c _ hx⟩

theorem blk_le {c c' : ∀ k, Bk n k} {W : (MP ℤ m n).Opens} (hW : W ≤ mchart c ⊓ mchart c') (k : Fin (m + 1)) :
    W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c k) ⊓ chart ℤ (n k) (c' k)) :=
  fun _ hx => ⟨mchart_le c k (hW hx).1, mchart_le c' k (hW hx).2⟩

theorem res_twB_g (b : Fin m) (t : ℤ) (c c' : ∀ k, Bk n k) {W : (MP ℤ m n).Opens} (hW : W ≤ mchart c ⊓ mchart c')
    (h : W ≤ (twB m n b t).U (twIdx b t c) ⊓ (twB m n b t).U (twIdx b t c')) :
    Semi.res h ((twB m n b t).g (twIdx b t c) (twIdx b t c')) =
      blockUnit (c b.succ) (c' b.succ) (blk_le hW b.succ) * blockUnit (c 0) (c' 0) (blk_le hW 0) ^ t := by
  have h₁ : W ≤ ((O1 ℤ (n b.succ)).pull (pr ℤ m n b.succ)).U (fun _ => c b.succ) ⊓
      ((O1 ℤ (n b.succ)).pull (pr ℤ m n b.succ)).U (fun _ => c' b.succ) :=
    le_inf (fun _ hx => h hx |>.1.1) (fun _ hx => h hx |>.2.1)
  have h₂ : W ≤ ((O1 ℤ (n 0)).pull (pr ℤ m n 0)).U (fun _ => c 0) ⊓
      ((O1 ℤ (n 0)).pull (pr ℤ m n 0)).U (fun _ => c' 0) :=
    le_inf (fun _ hx => h hx |>.1.2) (fun _ hx => h hx |>.2.2)
  have e₁ := res_pull_g b.succ (fun _ => c b.succ) (fun _ => c' b.succ) h₁ (blk_le hW b.succ)
  have e₂ := res_pull_g 0 (fun _ => c 0) (fun _ => c' 0) h₂ (blk_le hW 0)
  have e₃ : (Semi.res h₂ (((O1 ℤ (n 0)).pull (pr ℤ m n 0)).g (fun _ => c 0) (fun _ => c' 0)) ^ (-t))⁻¹ =
      blockUnit (c 0) (c' 0) (blk_le hW 0) ^ t := by
    rw [zpow_neg, inv_inv]
    exact congrArg (· ^ t) e₂
  exact (res_div_g _ _ (twIdx b t c) (twIdx b t c') h h₁ h₂).trans (congrArg₂ (· * ·) e₁
    ((congrArg (·⁻¹) (map_zpow (Semi.res h₂) _ (-t))).trans e₃))

theorem blockUnit_self {k : Fin (m + 1)} (i : Bk n k) {W : (MP ℤ m n).Opens}
    (h : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) i)) : blockUnit i i h = 1 := by
  rw [blockUnit, ratioUnit_self, map_one, map_one]

theorem prod_zpow_single {G : Type*} [CommGroup G] (f : Fin (m + 1) → G) (p q : Fin (m + 1)) (t : ℤ) :
    ∏ k, f k ^ ((Pi.single p 1 + t • Pi.single q 1 : Fin (m + 1) → ℤ) k) = f p * f q ^ t := by
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, zpow_add, Finset.prod_mul_distrib]
  congr 1
  · rw [Finset.prod_eq_single p (fun k _ hk => by simp [Pi.single_apply, hk]) (by simp)]
    simp
  · rw [Finset.prod_eq_single q (fun k _ hk => by simp [Pi.single_apply, hk]) (by simp)]
    simp

variable {B : LB (MP ℤ m n)} {b : Fin m} {t : ℤ}

def uOf (w : LB.Iso B (twB m n b t)) (i : B.ι) (c : ∀ k, Bk n k) : Γ(MP ℤ m n, B.U i ⊓ mchart c)ˣ :=
  Semi.res (le_inf (inf_le_right.trans (mchart_le_U b t c)) inf_le_left) (w.s (twIdx b t c, i))

theorem res_uOf (w : LB.Iso B (twB m n b t)) (i : B.ι) (c : ∀ k, Bk n k) {W : (MP ℤ m n).Opens}
    (h : W ≤ B.U i ⊓ mchart c) (h' : W ≤ (twB m n b t).U (twIdx b t c) ⊓ B.U i) :
    Semi.res h (uOf w i c) = Semi.res h' (w.s (twIdx b t c, i)) :=
  res_res' _ _ h' _

theorem frame_uOf {w : LB.Iso B (twB m n b t)} (hw : w.IsGen) (i j : B.ι) (c : ∀ k, Bk n k) :
    Semi.res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        B.U i ⊓ B.U j ⊓ mchart c ≤ B.U j ⊓ mchart c) (uOf w j c) =
      Semi.res (inf_le_left : B.U i ⊓ B.U j ⊓ mchart c ≤ B.U i ⊓ B.U j) (B.g i j) *
        Semi.res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          B.U i ⊓ B.U j ⊓ mchart c ≤ B.U i ⊓ mchart c) (uOf w i c) := by
  have hc : B.U i ⊓ B.U j ⊓ mchart c ≤ mchart c ⊓ mchart c := le_inf inf_le_right inf_le_right
  have hU := (inf_le_right : B.U i ⊓ B.U j ⊓ mchart c ≤ mchart c).trans (mchart_le_U b t c)
  have hi : B.U i ⊓ B.U j ⊓ mchart c ≤ (twB m n b t).U (twIdx b t c) ⊓ B.U i :=
    le_inf hU (inf_le_left.trans inf_le_left)
  have hj : B.U i ⊓ B.U j ⊓ mchart c ≤ (twB m n b t).U (twIdx b t c) ⊓ B.U j :=
    le_inf hU (inf_le_left.trans inf_le_right)
  have e := iso_law hw (twIdx b t c, i) (twIdx b t c, j) hi hj (le_inf hU hU) inf_le_left
  rw [res_twB_g b t c c hc, blockUnit_self, blockUnit_self, one_zpow, one_mul, one_mul] at e
  rw [res_uOf w j c _ hj, res_uOf w i c _ hi]
  exact (eq_inv_mul_iff_mul_eq.1 e).symm

theorem mono_uOf (hB : B.IsLB) {w : LB.Iso B (twB m n b t)} (hw : w.IsGen) (i : B.ι) (c c' : ∀ k, Bk n k) :
    Semi.res (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
        B.U i ⊓ (mchart c ⊓ mchart c') ≤ B.U i ⊓ mchart c) (uOf w i c) =
      Semi.res (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
        B.U i ⊓ (mchart c ⊓ mchart c') ≤ B.U i ⊓ mchart c') (uOf w i c') *
      ∏ k, blockUnit (c k) (c' k) (fun _ hx =>
        ⟨mchart_le c k hx.2.1, mchart_le c' k hx.2.2⟩ :
          B.U i ⊓ (mchart c ⊓ mchart c') ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c k) ⊓ chart ℤ (n k) (c' k))) ^
        (Pi.single b.succ 1 + t • Pi.single 0 1 : Fin (m + 1) → ℤ) k := by
  have hc : B.U i ⊓ (mchart c ⊓ mchart c') ≤ mchart c ⊓ mchart c' := inf_le_right
  have hU := (inf_le_right.trans inf_le_left : B.U i ⊓ (mchart c ⊓ mchart c') ≤ mchart c).trans (mchart_le_U b t c)
  have hU' := (inf_le_right.trans inf_le_right : B.U i ⊓ (mchart c ⊓ mchart c') ≤ mchart c').trans (mchart_le_U b t c')
  have hs : Semi.res (le_inf inf_le_left inf_le_left : B.U i ⊓ (mchart c ⊓ mchart c') ≤ B.U i ⊓ B.U i) (B.g i i) = 1 :=
    Units.ext (LB.resG_g_self hB i _)
  have hi : B.U i ⊓ (mchart c ⊓ mchart c') ≤ (twB m n b t).U (twIdx b t c) ⊓ B.U i := le_inf hU inf_le_left
  have hi' : B.U i ⊓ (mchart c ⊓ mchart c') ≤ (twB m n b t).U (twIdx b t c') ⊓ B.U i := le_inf hU' inf_le_left
  have e := iso_law hw (twIdx b t c, i) (twIdx b t c', i) hi hi' (le_inf hU hU') (le_inf inf_le_left inf_le_left)
  rw [res_twB_g b t c c' hc] at e
  change _ = _ * (Semi.res _ (B.g i i))⁻¹ * _ at e
  rw [hs, inv_one, mul_one] at e
  rw [res_uOf w i c _ hi, res_uOf w i c' _ hi',
    prod_zpow_single (fun k => blockUnit (c k) (c' k) (blk_le hc k)) b.succ 0 t]
  exact e.trans (mul_comm _ _)

theorem exists_units : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (B : LB (MP ℤ m n)) (c : Fin m) (t : ℤ), B.IsLB → LBIso B (twB m n c t) →
  ∃ u : ∀ (i : B.ι) (c' : ∀ k, Bk n k), Γ(MP ℤ m n, B.U i ⊓ mchart c')ˣ,
    (∀ i j c',
      res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          B.U i ⊓ B.U j ⊓ mchart c' ≤ B.U j ⊓ mchart c') (u j c') =
        res (inf_le_left : B.U i ⊓ B.U j ⊓ mchart c' ≤ B.U i ⊓ B.U j) (B.g i j) *
          res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
            B.U i ⊓ B.U j ⊓ mchart c' ≤ B.U i ⊓ mchart c') (u i c')) ∧
    (∀ i (c' c'' : ∀ k, Bk n k),
      res (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
          B.U i ⊓ (mchart c' ⊓ mchart c'') ≤ B.U i ⊓ mchart c') (u i c') =
        res (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
          B.U i ⊓ (mchart c' ⊓ mchart c'') ≤ B.U i ⊓ mchart c'') (u i c'') *
        ∏ k, blockUnit (c' k) (c'' k) (fun _ hx =>
          ⟨mchart_le c' k hx.2.1, mchart_le c'' k hx.2.2⟩ :
            B.U i ⊓ (mchart c' ⊓ mchart c'') ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c' k) ⊓ chart ℤ (n k) (c'' k))) ^ (Pi.single c.succ 1 + t • Pi.single 0 1 : Fin (m + 1) → ℤ) k) := by
  rintro m n B c t hB ⟨w, hw⟩
  exact ⟨uOf w, frame_uOf hw, mono_uOf hB hw⟩

end GlobalTheory.CompanionTheory.MPDict.TwUnits
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductLanglandsSubquotientSegments
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

noncomputable section

namespace GlobalTheory.CompanionTheory.LProd

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isLSeg_append {p q : ℕ} (x : Fin p → IrrGL k) (y : Fin q → IrrGL k) (Δ₁ : Fin p → Segment k)
    (Δ₂ : Fin q → Segment k) (h₁ : ∀ i, IsLSeg (Δ₁ i) (x i).rep) (h₂ : ∀ i, IsLSeg (Δ₂ i) (y i).rep)
    (i : Fin (p + q)) : IsLSeg (Fin.append Δ₁ Δ₂ i) (Fin.append x y i).rep := by
  induction i using Fin.addCases with
  | left i => rw [Fin.append_left, Fin.append_left]; exact h₁ i
  | right i => rw [Fin.append_right, Fin.append_right]; exact h₂ i

theorem map_append {p q : ℕ} (Δ₁ : Fin p → Segment k) (Δ₂ : Fin q → Segment k) :
    Finset.univ.val.map (Fin.append Δ₁ Δ₂) = Finset.univ.val.map Δ₁ + Finset.univ.val.map Δ₂ := by
  rw [Fin.univ_val_map, Fin.univ_val_map, Fin.univ_val_map, List.ofFn_fin_append]
  rfl

theorem prod₂_isSubquotient_append {r t p q : ℕ} {U W : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup W]
    [Module ℂ W] (σ : Representation ℂ (GL (Fin r) k) U) (ρ : Representation ℂ (GL (Fin t) k) W)
    (x : Fin p → IrrGL k) (y : Fin q → IrrGL k) (hx : ∑ a, (x a).1 = r) (hy : ∑ a, (y a).1 = t)
    (hd : ∑ i, (Fin.append x y i).1 = r + t) (h₁ : IsSubquotient σ (prodIrr x hx))
    (h₂ : IsSubquotient ρ (prodIrr y hy)) : IsSubquotient (prod₂ σ ρ) (prodIrr (Fin.append x y) hd) := by
  obtain ⟨F⟩ := GlobalTheory.T.product_irreducible_append_equiv k p q r t x y hx hy hd
  exact GlobalTheory.CompanionTheory.Ysupp.isSubquotient_of_prod₂_equiv (isSmooth_prodIrr _ _) (isSmooth_prodIrr _ _)
    h₁ h₂ (Representation.Equiv.refl _) F

end GlobalTheory.CompanionTheory.LProd

theorem GlobalTheory.CompanionTheory.LProd.prod₂_isSubquotient_prodIrr_lseg : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), ∀ (𝔪 𝔫 : Multiset (Segment k)) (a b : IrrGL k), IsL 𝔪 a.rep → IsL 𝔫 b.rep → ∃ (h : ℕ) (z : Fin h → IrrGL k) (Δ : Fin h → Segment k) (hd : ∑ i, (z i).1 = a.1 + b.1), (∀ i, IsLSeg (Δ i) (z i).rep) ∧ Finset.univ.val.map Δ = 𝔪 + 𝔫 ∧ IsSubquotient (prod₂ a.rep b.rep) (prodIrr z hd) := by
  intro k _ _ _ _ _ 𝔪 𝔫 a b ha hb
  obtain ⟨p, x, hx, ⟨Δ₁, hO₁, hL₁⟩, hc₁⟩ := ha
  obtain ⟨q, y, hy, ⟨Δ₂, hO₂, hL₂⟩, hc₂⟩ := hb
  have hd : ∑ i, (Fin.append x y i).1 = a.1 + b.1 := by
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, hx, hy]
  refine ⟨p + q, Fin.append x y, Fin.append Δ₁ Δ₂, hd, GlobalTheory.CompanionTheory.LProd.isLSeg_append x y Δ₁ Δ₂ hL₁ hL₂, ?_, ?_⟩
  · rw [GlobalTheory.CompanionTheory.LProd.map_append, hO₁.1, hO₂.1]
  · exact GlobalTheory.CompanionTheory.LProd.prod₂_isSubquotient_append _ _ x y hx hy hd hc₁.isSubquotient hc₂.isSubquotient

end
end

