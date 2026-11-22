import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0800
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0061
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0012
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0029
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0014
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0803
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0799
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0024
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0022
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0757
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0062
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0761

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RationalTranslateAlgebraicCombination
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section
namespace GlobalTheory.RatMovedAlg
theorem rational_moved_scalar_algebraic : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ (t : T), ∀ γ ∈ Formalism.L2.Theta.GQ A, ∀ a ∈ GinfC A, ∀ γ' ∈ Formalism.L2.Theta.GQ WW, ∀ a' ∈ GinfC WW,
      γ * a ∈ GfC A → γ' * a' ∈ GfC WW →
      ∀ (κ : ℂ) (F : WO (GlobalTheory.Grid.neg A) WW → ℂ), GlobalTheory.MovedAlg.IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac F →
        X.ω t (γ, γ') X.vac = κ • F → IsAlgebraic ℚ κ := by
  intro D T _ L μ₀ sc G W i j A A' WW X hP hI hL hX t γ hγ a ha γ' hγ' a' ha' h1 h2 κ F hF e
  obtain ⟨k, hk⟩ := _root_.GlobalTheory.T.jet_of_moved_vacuum_nonvanishing hP hI hL hX t γ hγ a ha γ' hγ' a' ha' h1 h2
  obtain ⟨Ω, hΩ, hJ⟩ := _root_.GlobalTheory.T.bottom_translate_jets_algebraic hP hI hL hX (Finsupp.mapDomain Prod.fst k)
  obtain ⟨n', c', k', hc', hk', he'⟩ := _root_.GlobalTheory.T.moved_vacuum_jet_algebraic_combination hP hI hL hX t γ hγ a ha γ' hγ' a' ha' h1 h2 k
  have hψ : IsStdChar D W.ψ (-1) := (hX.is.weil t).std
  have hθ : IsInfFam W.θ := hX.is.isVac.2.inf
  have hv : IsThetaFunO W.ψ (GlobalTheory.Grid.neg A) WW X.vac := hX.is.isVac.2.theta
  have h0 : heisO W.ψ (GlobalTheory.Grid.neg A) WW 0 X.vac = X.vac := by
    funext w; simp [heisO, symplOH, symplO, hO]
  have alg : ∀ x : ℂ, IsAlgebraic ℚ x ↔ x ∈ algebraicClosure ℚ ℂ := fun x => (mem_algebraicClosure_iff).symm
  have hg : IsAlgebraic ℚ (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.ω t (γ, γ') X.vac) (MvPolynomial.monomial k 1) 0 / Ω) := by
    rw [he', Finset.sum_div, alg]
    refine sum_mem fun p _ => ?_
    rw [mul_div_assoc]
    refine mul_mem ((alg _).1 (hc' p)) ((alg _).1 ?_)
    have := hJ 0 (by simp) (k' p) (hk' p)
    rwa [h0] at this
  obtain ⟨n, c, w, hc, hw, rfl⟩ := hF
  have hsum : pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (∑ p, c p • heisO W.ψ (GlobalTheory.Grid.neg A) WW (w p) X.vac) (MvPolynomial.monomial k 1) 0 =
      ∑ p, c p * pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (heisO W.ψ (GlobalTheory.Grid.neg A) WW (w p) X.vac) (MvPolynomial.monomial k 1) 0 := by
    rw [GlobalTheory.SpecFac.pureTensorO_sum hψ hθ _ _ _ _ Finset.univ c _
      (fun p _ => GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hv (w p))]
    simp [Finset.sum_apply]
  have hF' : IsAlgebraic ℚ (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (∑ p, c p • heisO W.ψ (GlobalTheory.Grid.neg A) WW (w p) X.vac) (MvPolynomial.monomial k 1) 0 / Ω) := by
    rw [hsum, Finset.sum_div, alg]
    refine sum_mem fun p _ => ?_
    rw [mul_div_assoc]
    exact mul_mem ((alg _).1 (hc p)) ((alg _).1 (hJ (w p) (hw p) k rfl))
  have hsm : pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.ω t (γ, γ') X.vac) (MvPolynomial.monomial k 1) 0 = κ * pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (∑ p, c p • heisO W.ψ (GlobalTheory.Grid.neg A) WW (w p) X.vac) (MvPolynomial.monomial k 1) 0 := by
    rw [e, GlobalTheory.FiniteFock.pureTensorO_smul]; rfl
  have hne : pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (∑ p, c p • heisO W.ψ (GlobalTheory.Grid.neg A) WW (w p) X.vac) (MvPolynomial.monomial k 1) 0 ≠ 0 := by
    intro h0'; rw [h0', mul_zero] at hsm; exact hk hsm
  have hκ : κ = (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.ω t (γ, γ') X.vac) (MvPolynomial.monomial k 1) 0 / Ω) / (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (∑ p, c p • heisO W.ψ (GlobalTheory.Grid.neg A) WW (w p) X.vac) (MvPolynomial.monomial k 1) 0 / Ω) := by
    rw [hsm]; field_simp
  rw [hκ, alg]
  exact div_mem ((alg _).1 hg) ((alg _).1 hF')
theorem rational_translate_algebraic_combination : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ (t : T), ∀ γ ∈ Formalism.L2.Theta.GQ A, ∀ a ∈ GinfC A, ∀ γ' ∈ Formalism.L2.Theta.GQ WW, ∀ a' ∈ GinfC WW,
      γ * a ∈ GfC A → γ' * a' ∈ GfC WW →
      ∃ (n : ℕ) (c : Fin n → ℂ) (w : Fin n → WO (GlobalTheory.Grid.neg A) WW), (∀ p, IsAlgebraic ℚ (c p)) ∧
        (∀ p, (w p).map (infPart D) = 0) ∧
        X.ω t (γ, γ') X.vac = ∑ p, c p • heisO W.ψ (GlobalTheory.Grid.neg A) WW (w p) X.vac := by
  intro D T _ L μ₀ sc G W i j A A' WW X hP hI hL hX t γ hγ a ha γ' hγ' a' ha' h1 h2
  obtain ⟨κ, F, hF, e⟩ := _root_.GlobalTheory.T.rational_vacuum_algebraic_combination hP hI hL hX t γ hγ a ha γ' hγ' a' ha' h1 h2
  have hk := _root_.GlobalTheory.RatMovedAlg.rational_moved_scalar_algebraic hP hI hL hX t γ hγ a ha γ' hγ' a' ha' h1 h2 κ F hF e
  obtain ⟨n, c, w, hc, hw, he⟩ := hF.smul hk
  exact ⟨n, c, w, hc, hw, e.trans he⟩
end GlobalTheory.RatMovedAlg
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationally_moved_vector_algebraic : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ (t : T), ∀ γ ∈ Formalism.L2.Theta.GQ A, ∀ a ∈ GinfC A, ∀ γ' ∈ Formalism.L2.Theta.GQ WW, ∀ a' ∈ GinfC WW,
      γ * a ∈ GfC A → γ' * a' ∈ GfC WW →
      ∃ (n : ℕ) (c : Fin n → ℂ) (w : Fin n → WO (GlobalTheory.Grid.neg A) WW), (∀ p, IsAlgebraic ℚ (c p)) ∧
        (∀ p, (w p).map (infPart D) = 0) ∧
        X.ω t (γ, γ') X.vac = ∑ p, c p • heisO W.ψ (GlobalTheory.Grid.neg A) WW (w p) X.vac := by
  first | exact @_root_.GlobalTheory.RatMovedAlg.rational_translate_algebraic_combination | exact _root_.GlobalTheory.RatMovedAlg.rational_translate_algebraic_combination | (intros; apply _root_.GlobalTheory.RatMovedAlg.rational_translate_algebraic_combination <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedThetaLiftOfCuspFormIsCuspidal
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
theorem GlobalTheory.ThLiftCusp.theta_lift_of_cusp_form_isCuspidal : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.V i j).V (G.V i (j + 1)).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i (j + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.th t i j).ω h g Φ * φ g) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν) → IsCuspFun (G.V i j).V (fun h => ∫ g in (G.meas t i (j + 1)).fd, thetaKO (G.th t i j).ω h g Φ * φ g ∂(G.meas t i (j + 1)).ν) := by
  intro hL hP D hS G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG t i j hi hj Φ hΦ φ hφ hint
  have haut := _root_.GlobalTheory.T.twisted_theta_lift_of_cusp_form_isSmoothAutomorphic hL hP D hS G₀ Pl0 T A Ks R G hR hG t i j hi hj Φ hΦ φ hφ hint
  obtain ⟨a1, b1, C, hC0, hK1⟩ := _root_.GlobalTheory.T.twist_thetaLift_le_quotientHeight hL hP D hS G₀ Pl0 T A Ks R G hR hG t i j hi hj Φ hΦ
  obtain ⟨a2, b2, happ2⟩ := _root_.GlobalTheory.T.twist_thetaLift_approx_fockSpace hL hP D hS G₀ Pl0 T A Ks R G hR hG t i j hi hj Φ hΦ
  set a := max a1 a2
  set b := max b1 b2
  have hqB : ∀ h, ∀ c, c ≤ a → GlobalTheory.Grow.quotHeight (G.V i j).V h ^ c ≤ GlobalTheory.Grow.quotHeight (G.V i j).V h ^ a :=
    fun h c hc => pow_le_pow_right₀ (GlobalTheory.Grow.one_le_quotHeight _ h) hc
  have hqA : ∀ g, ∀ c, c ≤ b → GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ c ≤ GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ b :=
    fun g c hc => pow_le_pow_right₀ (GlobalTheory.Grow.one_le_quotHeight _ g) hc
  have hK : ∀ h g, ‖thetaKO (G.th t i j).ω h g Φ‖ ≤
      C * GlobalTheory.Grow.quotHeight (G.V i j).V h ^ a * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ b := fun h g =>
    (hK1 h g).trans (mul_le_mul (mul_le_mul_of_nonneg_left (hqB h a1 (le_max_left _ _)) hC0)
      (hqA g b1 (le_max_left _ _)) (pow_nonneg (GlobalTheory.Grow.quotHeight_pos _ g).le _)
      (mul_nonneg hC0 (pow_nonneg (GlobalTheory.Grow.quotHeight_pos _ h).le _)))
  have happ : ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (fs : Fin n → (WO (G.V i j).V (G.V i (j + 1)).V → ℂ))
      (ps : Fin n → PolF D (G.V i (j + 1)).V.rank (G.V i j).V.rank),
      (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l)) ∧ ∀ h g,
        ‖thetaKO (G.th t i j).ω h g (∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l) (ps l)) - thetaKO (G.th t i j).ω h g Φ‖ ≤
          ε * GlobalTheory.Grow.quotHeight (G.V i j).V h ^ a * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ b := by
    intro ε hε
    obtain ⟨n, fs, ps, hfs, hb⟩ := happ2 ε hε
    exact ⟨n, fs, ps, hfs, fun h g => (hb h g).trans (mul_le_mul
      (mul_le_mul_of_nonneg_left (hqB h a2 (le_max_right _ _)) hε.le) (hqA g b2 (le_max_right _ _))
      (pow_nonneg (GlobalTheory.Grow.quotHeight_pos _ g).le _)
      (mul_nonneg hε.le (pow_nonneg (GlobalTheory.Grow.quotHeight_pos _ h).le _)))⟩
  obtain ⟨hI1, hform⟩ := _root_.GlobalTheory.T.twist_cuspForm_approx_thetaLift hL hP D hS G₀ Pl0 T A Ks R G hR hG t i j hi hj φ hφ b
  refine GlobalTheory.ThLiftCusp.isCuspFun_of_approx _ _ haut.cont haut.left a fun η hη => ?_
  set I1 := ∫ g in (G.meas t i (j + 1)).fd, GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ b * ‖φ g‖ ∂(G.meas t i (j + 1)).ν
    with hI1def
  have hI1nn : 0 ≤ I1 := setIntegral_nonneg_of_ae_restrict (Filter.Eventually.of_forall fun g =>
    mul_nonneg (pow_nonneg (GlobalTheory.Grow.quotHeight_pos _ g).le _) (norm_nonneg _))
  have hden : 0 < I1 + 1 + C := by linarith
  set e := min 1 (η / (I1 + 1 + C)) with hedef
  have he : 0 < e := lt_min one_pos (div_pos hη hden)
  obtain ⟨n, fs, ps, hfs, hKK⟩ := happ e he
  obtain ⟨n', Fs, vs, hFs, hI2, hδ⟩ := hform e he
  obtain ⟨hint', haut', hcusp'⟩ := _root_.GlobalTheory.T.exists_finite_level_lift_of_twist hL hP D hS G₀ Pl0 T A Ks R G hR hG t i j hi hj n fs ps hfs n' Fs vs hFs
  refine ⟨_, haut'.cont, haut'.left, hcusp', fun h => ?_⟩
  have key := GlobalTheory.ThLiftCusp.norm_lift_sub_le ((G.meas t i (j + 1)).ν.restrict (G.meas t i (j + 1)).fd)
    (fun h g => thetaKO (G.th t i j).ω h g Φ)
    (fun h g => thetaKO (G.th t i j).ω h g (∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l) (ps l)))
    φ (fun g => ∑ k, Fs k (vs k) g) (fun h => GlobalTheory.Grow.quotHeight (G.V i j).V h ^ a)
    (fun g => GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ b) C e e hC0 he.le
    (fun h => pow_nonneg (GlobalTheory.Grow.quotHeight_pos _ h).le _) hK hKK hI1 hI2 hδ hint' hint h
  refine key.trans ?_
  have hq : GlobalTheory.Grow.quotHeight (G.V i j).V h ^ a ≤ GlobalTheory.Grow.height (G.V i j).V h ^ a :=
    pow_le_pow_left₀ (GlobalTheory.Grow.quotHeight_pos _ h).le (GlobalTheory.Grow.quotHeight_le_height _ h) a
  have he1 : e ≤ 1 := min_le_left _ _
  have he2 : e ≤ η / (I1 + 1 + C) := min_le_right _ _
  have hb : e * I1 + (e + C) * e ≤ η := by
    have : e * (I1 + 1 + C) ≤ η := (le_div_iff₀ hden).1 he2
    nlinarith
  have h0 : 0 ≤ e * I1 + (e + C) * e := by positivity
  calc GlobalTheory.Grow.quotHeight (G.V i j).V h ^ a * (e * I1 + (e + C) * e)
      ≤ GlobalTheory.Grow.height (G.V i j).V h ^ a * η :=
        mul_le_mul hq hb h0 (pow_nonneg ((GlobalTheory.Grow.quotHeight_pos _ h).le.trans (GlobalTheory.Grow.quotHeight_le_height _ h)) _)
    _ = η * GlobalTheory.Grow.height (G.V i j).V h ^ a := mul_comm _ _
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_theta_lift_of_cusp_form_isCuspidal : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.V i j).V (G.V i (j + 1)).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i (j + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.th t i j).ω h g Φ * φ g) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν) → IsCuspFun (G.V i j).V (fun h => ∫ g in (G.meas t i (j + 1)).fd, thetaKO (G.th t i j).ω h g Φ * φ g ∂(G.meas t i (j + 1)).ν) := by
  first | exact @_root_.GlobalTheory.ThLiftCusp.theta_lift_of_cusp_form_isCuspidal | exact _root_.GlobalTheory.ThLiftCusp.theta_lift_of_cusp_form_isCuspidal | (intros; apply _root_.GlobalTheory.ThLiftCusp.theta_lift_of_cusp_form_isCuspidal <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedUpwardThetaLiftHasKType
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.UpTypeLift
theorem upward_theta_lift_hasKType : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P i) φ → (∀ h, IntegrableOn (fun g => starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g) (G.mP i).fd (G.mP i).ν) → ∀ τ, IsTypeAt R.θ (G.P (i + 1)).V τ ((G.P (i + 1)).S τ) (fun h => ∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g ∂(G.mP i).ν) := by
  intro hL hP D hS G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG i hi Φ hΦ φ hφ hc τ
  have hN := hG.spaces.P (i + 1) (by omega)
  exact GlobalTheory.T.automorphicForm_uniformLimit_discreteSeries_series R.θ (G.P (i + 1)).V τ ((G.P (i + 1)).S τ) _ hP.discreteSeriesUpqExists
    (GlobalTheory.Published.discreteSeriesHermitianUnique_iff.1 hP.discreteSeriesHermitianUnique) hP.harishChandraModules
    hP.casselmanWallach hR.inf hN.sigOK (GlobalTheory.NodePar.goodPar_of_sigOK (G.P (i + 1)) hN.sigOK τ)
    (_root_.GlobalTheory.T.twisted_upward_theta_lift_isSmoothAutomorphic hL hP D hS G₀ Pl0 T A Ks R G hR hG i hi Φ hΦ φ hφ hc)
    (_root_.GlobalTheory.T.theta_lift_preserves_type hL hP D hS G₀ Pl0 T A Ks R G hR hG i hi Φ hΦ φ hφ hc τ)
end GlobalTheory.UpTypeLift
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_upward_theta_lift_hasKType : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P i) φ → (∀ h, IntegrableOn (fun g => starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g) (G.mP i).fd (G.mP i).ν) → ∀ τ, IsTypeAt R.θ (G.P (i + 1)).V τ ((G.P (i + 1)).S τ) (fun h => ∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g ∂(G.mP i).ν) := by
  first | exact @_root_.GlobalTheory.UpTypeLift.upward_theta_lift_hasKType | exact _root_.GlobalTheory.UpTypeLift.upward_theta_lift_hasKType | (intros; apply _root_.GlobalTheory.UpTypeLift.upward_theta_lift_hasKType <;> assumption)
end
end

