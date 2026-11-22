import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GkGeneratedCuspFormsOfType
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0593
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0573
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0590
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0370
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0384
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactElementGaussianList
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0506
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0535
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0553
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0546
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0563

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.IsKFiniteCuspOfTypeOfMemGKGenerated
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
noncomputable section
namespace GlobalTheory.CuspGKForms
open Matrix Filter Topology GlobalTheory.TypeSum GlobalTheory.PointAtPlaceHom GlobalTheory.Mem.AutSpace GlobalTheory.Mem.RealTranslate GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes GlobalTheory.CuspGK
open Formalism.IndefR.Mult
variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}
section Sig
variable (hPr : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hθ : IsInfFam θ) {τ τ' : D.what₂.Tau} {S : SPar} {φ ψ : GA D V → ℂ}
include hPr hθ
theorem hasTypeAt_of_cuspForm_gK (hV : V.SigOK) (hφ : IsAutFunSm θ V φ) (h : IsTypeAt θ V τ S φ) : φ ∈ typeSub θ V τ S :=
  GlobalTheory.SeriesToClosure.hasTypeAt_of_isTypeAt θ V τ S φ hPr.discreteSeriesUpqExists
    (GlobalTheory.Published.discreteSeriesHermitianUnique_iff.1 hPr.discreteSeriesHermitianUnique) hPr.harishChandraModules
    hPr.casselmanWallach hθ hV (goodPar_of_isTypeAt hV h) hφ h
theorem isTypeAt_of_cuspForm_gK (hV : V.SigOK) (h : IsTypeAt θ V τ S φ) (hψ : IsAutFunSm θ V ψ) (h' : ψ ∈ typeSub θ V τ S) :
    IsTypeAt θ V τ S ψ :=
  GlobalTheory.T.automorphicForm_uniformLimit_discreteSeries_series θ V τ S ψ hPr.discreteSeriesUpqExists
    (GlobalTheory.Published.discreteSeriesHermitianUnique_iff.1 hPr.discreteSeriesHermitianUnique) hPr.harishChandraModules
    hPr.casselmanWallach hθ hV (goodPar_of_isTypeAt hV h) hψ h'
theorem isTypeAt_add_of_sigma (hV : V.SigOK) (hφ : IsAutFunSm θ V φ) (hψ : IsAutFunSm θ V ψ) (h : IsTypeAt θ V τ S φ)
    (h' : IsTypeAt θ V τ S ψ) : IsTypeAt θ V τ S (φ + ψ) :=
  _root_.GlobalTheory.CuspGKForms.isTypeAt_of_cuspForm_gK hPr hθ hV h (GlobalTheory.Mem.AutSpace.isAutFunSm_add hφ hψ)
    (add_mem (_root_.GlobalTheory.CuspGKForms.hasTypeAt_of_cuspForm_gK hPr hθ hV hφ h) (_root_.GlobalTheory.CuspGKForms.hasTypeAt_of_cuspForm_gK hPr hθ hV hψ h'))
theorem isTypeAt_liftDeriv_of_sigma (hV : V.SigOK) {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ)
    (hφ : IsAutFunSm θ V φ) (h : IsTypeAt θ V τ' S φ) : IsTypeAt θ V τ' S (Rder θ V τ X φ) := by
  refine _root_.GlobalTheory.CuspGKForms.isTypeAt_of_cuspForm_gK hPr hθ hV h (GlobalTheory.CuspLie.isAutFunSm_Rder hθ hX hφ) fun C hC δ hδ => ?_
  obtain ⟨t, ht⟩ := exists_quotient_near hθ hX hφ hC (half_pos hδ)
  have hk := GlobalTheory.Mem.Lift.exp_mem hX t
  have m1 : rTr V (oneP θ V τ X t) φ ∈ typeSub θ V τ' S :=
    _root_.GlobalTheory.CuspGKForms.hasTypeAt_of_cuspForm_gK hPr hθ hV (isAutFunSm_rTr_atTau D θ hθ V φ hφ τ _ hk) (isTypeAt_rTr hθ h hk)
  have m2 : ((t : ℂ)⁻¹) • (rTr V (oneP θ V τ X t) φ + (-1 : ℂ) • φ) ∈ typeSub θ V τ' S :=
    Submodule.smul_mem _ _ (add_mem m1 (Submodule.smul_mem _ _ (_root_.GlobalTheory.CuspGKForms.hasTypeAt_of_cuspForm_gK hPr hθ hV hφ h)))
  obtain ⟨χ, hχ, h2⟩ := m2 C hC (δ / 2) (half_pos hδ)
  refine ⟨χ, hχ, fun x hx => ?_⟩
  have := norm_sub_le_norm_sub_add_norm_sub (Rder θ V τ X φ x)
    ((((t : ℂ)⁻¹) • (rTr V (oneP θ V τ X t) φ + (-1 : ℂ) • φ)) x) (χ x)
  linarith [ht x hx, h2 x hx]
theorem isTypeAt_add_cuspForm (hφ : IsAutFunSm θ V φ) (hψ : IsAutFunSm θ V ψ) (h : IsTypeAt θ V τ S φ)
    (h' : IsTypeAt θ V τ S ψ) : IsTypeAt θ V τ S (φ + ψ) := by
  obtain ⟨s, hs⟩ := exists_sigOK V
  exact _root_.GlobalTheory.CuspGKForms.isTypeAt_add_of_sigma (V := GlobalTheory.SmoothAutCheck.reSig V s) hPr hθ hs
    ((GlobalTheory.SmoothAutCheck.isAutFunSm_reSig θ V s φ).2 hφ) ((GlobalTheory.SmoothAutCheck.isAutFunSm_reSig θ V s ψ).2 hψ) h h'
theorem isTypeAt_liftDeriv_cuspForm {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ)
    (hφ : IsAutFunSm θ V φ) (h : IsTypeAt θ V τ' S φ) : IsTypeAt θ V τ' S (Rder θ V τ X φ) := by
  obtain ⟨s, hs⟩ := exists_sigOK V
  exact _root_.GlobalTheory.CuspGKForms.isTypeAt_liftDeriv_of_sigma (V := GlobalTheory.SmoothAutCheck.reSig V s) hPr hθ hs hX
    ((GlobalTheory.SmoothAutCheck.isAutFunSm_reSig θ V s φ).2 hφ) h
end Sig
variable {S : D.what₂.Tau → SPar}
def cuspFormGKSubmodule (hPr : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hθ : IsInfFam θ) (M : DSModel V S) : Submodule ℂ (GA D V → ℂ) where
  carrier := {f | IsKFinCuspOfType θ M f}
  zero_mem' := ⟨Formalism.IndefR.Mult.isAutFunSm_zero θ V, Formalism.IndefR.Mult.isCuspFun_zero V,
    fun τ => (GlobalTheory.TypeAtTest.isTypeAt_zero θ V).2
      ⟨M.H τ, _, _, M.σ τ, M.lam τ, M.ε τ, M.fr τ, M.enum τ, M.ds τ, M.fr_unit τ, M.fr_gram τ⟩,
    ⊥, inferInstance, zero_mem _, fun τ g _ _ h hh => by
      rw [Submodule.mem_bot] at hh ⊢
      subst hh
      rfl⟩
  add_mem' := by
    rintro a b ⟨a1, a2, a3, W, hW, a4, a5⟩ ⟨b1, b2, b3, W', hW', b4, b5⟩
    refine ⟨GlobalTheory.Mem.AutSpace.isAutFunSm_add a1 b1, GlobalTheory.MultMem.isCuspFun_add a1.toIsAutFun b1.toIsAutFun a2 b2,
      fun τ => _root_.GlobalTheory.CuspGKForms.isTypeAt_add_cuspForm hPr hθ a1 b1 (a3 τ) (b3 τ), W ⊔ W', inferInstance, Submodule.add_mem_sup a4 b4,
      fun τ g hg hk h hh => ?_⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hh
    exact Submodule.add_mem_sup (a5 τ g hg hk y hy) (b5 τ g hg hk z hz)
  smul_mem' := by
    rintro c a ⟨a1, a2, a3, W, hW, a4, a5⟩
    exact ⟨GlobalTheory.Mem.AutSpace.isAutFunSm_smul c a1, Formalism.IndefR.Mult.isCuspFun_smul V a2 c,
      fun τ => GlobalTheory.Mem.Th.isTypeAt_smul c (a3 τ), W, hW, W.smul_mem c a4, a5⟩
theorem isGKSubmodule_cuspFormGKSubmodule (hPr : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hθ : IsInfFam θ) (M : DSModel V S) :
    IsGKSub θ M (_root_.GlobalTheory.CuspGKForms.cuspFormGKSubmodule hPr hθ M) where
  k τ g hg f hf := by
    obtain ⟨a1, a2, a3, W, hW, a4, a5⟩ := hf
    exact ⟨isAutFunSm_rTr_atTau D θ hθ V f a1 τ g hg.1, GlobalTheory.Cusp.isCuspFun_rTr a2 _,
      fun τ' => isTypeAt_rTr hθ (a3 τ') hg.1, W, hW, a5 τ g hg.1 hg.2 f a4, a5⟩
  lie τ X hX f hf := by
    obtain ⟨a1, a2, a3, W, hW, a4, a5⟩ := hf
    refine ⟨GlobalTheory.CuspLie.isAutFunSm_Rder hθ hX a1, GlobalTheory.CuspLie.isCuspFun_Rder hθ hX a1 a2,
      fun τ' => _root_.GlobalTheory.CuspGKForms.isTypeAt_liftDeriv_cuspForm hPr hθ hX a1 (a3 τ'),
      (Submodule.map₂ (derEnd hθ τ) ⊤ (W.comap (SmFun θ V).subtype)).map (SmFun θ V).subtype,
      Module.Finite.iff_fg.2 ((Submodule.FG.map₂ _ Module.Finite.fg_top (GlobalTheory.CuspLie.fg_comap hW)).map _),
      ⟨derEnd hθ τ X ⟨f, a1.smooth⟩,
        Submodule.apply_mem_map₂ _ (Submodule.mem_top (x := X)) (n := (⟨f, a1.smooth⟩ : SmFun θ V)) a4,
        GlobalTheory.CuspLie.derEnd_coe hθ hX ⟨f, a1.smooth⟩⟩, fun τ' g hg hk => ?_⟩
    have hr := isRealPt_atTau hθ τ' hg
    have hi : IsRealPt θ (atTau θ V τ' g)⁻¹ :=
      ⟨inv_mem hr.1, GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V _⟩
    set k := atTau θ V τ' g
    have hle : Submodule.map₂ (derEnd hθ τ) ⊤ (W.comap (SmFun θ V).subtype) ≤
        (((Submodule.map₂ (derEnd hθ τ) ⊤ (W.comap (SmFun θ V).subtype)).map (SmFun θ V).subtype).comap
          (rTrLin k)).comap (SmFun θ V).subtype := by
      refine Submodule.map₂_le.2 fun Z _ u hu => ?_
      refine ⟨_, Submodule.apply_mem_map₂ _ (Submodule.mem_top (x := adAt θ k⁻¹ τ Z))
        (n := ⟨rTr V k u.1, rTr_mem hθ hr u.2⟩) (a5 τ' g hg hk _ hu), ?_⟩
      show RderC θ V τ (adAt θ k⁻¹ τ Z) (rTr V k u.1) = rTr V k (RderC θ V τ Z u.1)
      funext y
      have := congrFun (RderC_rTr hθ hi τ Z (rTr V k u.1)) (y * k)
      rw [show rTr V k⁻¹ (rTr V k u.1) = u.1 from funext fun y => by simp [rTr]] at this
      rw [rTr, this, rTr, mul_inv_cancel_right]
    rintro _ ⟨u, hu, rfl⟩
    exact hle hu
theorem isKFiniteCuspOfType_of_mem_gKGenerated : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ ψ : GA D V → ℂ, GlobalTheory.CuspGK.IsKFinCuspOfType θ M ψ → ∀ f ∈ GlobalTheory.CuspGK.gkGen θ M ψ, GlobalTheory.CuspGK.IsKFinCuspOfType θ M f :=
  fun hPr _ θ _ _ M hθ _ hψ _ hf => gkGen_le θ M (A := _root_.GlobalTheory.CuspGKForms.cuspFormGKSubmodule hPr hθ M) hψ (_root_.GlobalTheory.CuspGKForms.isGKSubmodule_cuspFormGKSubmodule hPr hθ M) hf
end GlobalTheory.CuspGKForms
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_gK_submodule_of_type : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ ψ : GA D V → ℂ, GlobalTheory.CuspGK.IsKFinCuspOfType θ M ψ → ∀ f ∈ GlobalTheory.CuspGK.gkGen θ M ψ, GlobalTheory.CuspGK.IsKFinCuspOfType θ M f := by
  first | exact @_root_.GlobalTheory.CuspGKForms.isKFiniteCuspOfType_of_mem_gKGenerated | exact _root_.GlobalTheory.CuspGKForms.isKFiniteCuspOfType_of_mem_gKGenerated | (intros; apply _root_.GlobalTheory.CuspGKForms.isKFiniteCuspOfType_of_mem_gKGenerated <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.JetOfMovedVacuumNonvanishing
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section
namespace GlobalTheory.MovedJetNZ
open GlobalTheory.Grid (neg ofSgn)
end GlobalTheory.MovedJetNZ
end
namespace GlobalTheory.MovedJetNZ
open GlobalTheory.Grid (neg ofSgn)
theorem moved_vacuum_jet_ne_zero : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ (t : T), ∀ γ ∈ Formalism.L2.Theta.GQ A, ∀ a ∈ GinfC A, ∀ γ' ∈ Formalism.L2.Theta.GQ WW, ∀ a' ∈ GinfC WW,
      γ * a ∈ GfC A → γ' * a' ∈ GfC WW →
      ∃ k : FVar D WW.rank A.rank →₀ ℕ, pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.ω t (γ, γ') X.vac) (MvPolynomial.monomial k 1) 0 ≠ 0 := by
  intro D T _ L μ₀ sc G W i j A A' WW X _ hI _ hX t γ hγ _ _ γ' hγ' _ _ _ _
  classical
  have hIs := hX.is
  have hψ : IsStdChar D W.ψ (-1) := hIs.isVac.1
  have hθ : IsInfFam W.θ := hIs.isVac.2.inf
  set om' := (X.ω t).toSgn true with hom'
  have hom := hIs.weil t
  have hsA : ∀ τ, X.rA.s τ = 1 := fun τ => (hX.std.2.2 τ).1
  have hsW : ∀ τ, X.rW.s τ = 1 := fun τ => (hX.stdW.2.2 τ).1
  have hBA : ∀ τ, X.rA.B τ = 1 := fun τ => by rw [(hX.std.2.2 τ).2]
  obtain ⟨k₀, hk₀⟩ := vac_jet_ne_zero hI hX
  by_contra hall
  push_neg at hall
  set γs := (ofSgn true A).symm γ with hγs
  have hγsQ : γs ∈ GQ (neg A) :=
    (GlobalTheory.SgnIdent.mem_GQ_sgn true A γs).2 (by rw [hγs, MulEquiv.apply_symm_apply]; exact hγ)
  have hg : X.ω t (γ, γ') X.vac = om' (γs, γ') X.vac := by
    show _ = (X.ω t) ((ofSgn true A) ((ofSgn true A).symm γ), γ') X.vac
    rw [MulEquiv.apply_symm_apply]
  simp only [hg] at hall
  have hvθ : IsThetaFunO W.ψ (neg A) WW X.vac := hIs.isVac.2.theta
  have hgθ : IsThetaFunO W.ψ (neg A) WW (om' (γs, γ') X.vac) := hom.om_pres _ _ hvθ
  have hzero : ∀ P, pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (om' (γs, γ') X.vac) P 0 = 0 := by
    intro P
    rw [P.as_sum, map_sum, Finset.sum_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    have e : MvPolynomial.monomial k (P.coeff k) = P.coeff k • MvPolynomial.monomial k 1 := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [e, map_smul, Pi.smul_apply, hall k, smul_zero]
  have hop := GlobalTheory.OrientedHeis.om_pureTensorO D W.ψ W.θ (neg A) WW _ _ om' hom hθ (fun τ => -X.rA.s τ) (fun τ => -X.rA.s τ)
    X.rA.B (fun τ => compAt W.θ τ (Formalism.L2.Theta.mt (neg A) γs) * X.rA.B τ) X.rW.s X.rW.s X.rW.B
    (fun τ => compAt W.θ τ (Formalism.L2.Theta.mt WW γ') * X.rW.B τ) γs γ' (fun τ => by rw [hsA]; simp) (fun τ => by rw [hsW]; simp)
    (fun τ => rfl) (fun τ => rfl) X.vac hvθ (MvPolynomial.monomial k₀ 1)
  have haut := hom.om_aut γs hγsQ γ' hγ' _ hop.1
  apply hk₀
  rw [← haut, hop.2]
  have hBW : ∀ τ, X.rW.B τ = 1 := fun τ => by rw [(hX.stdW.2.2 τ).2]
  have e1 : (fun τ => compAt W.θ τ (Formalism.L2.Theta.mt (neg A) γs) * X.rA.B τ) =
      fun τ => X.rA.B τ * compAt W.θ τ (Formalism.L2.Theta.mt (neg A) γs) := by
    funext τ; rw [hBA, Matrix.mul_one, Matrix.one_mul]
  have e2 : (fun τ => compAt W.θ τ (Formalism.L2.Theta.mt WW γ') * X.rW.B τ) =
      fun τ => X.rW.B τ * compAt W.θ τ (Formalism.L2.Theta.mt WW γ') := by
    funext τ; rw [hBW, Matrix.mul_one, Matrix.one_mul]
  have es : (fun τ => -X.rA.s τ) = fun _ => (-1 : Matrix (Fin A.rank) (Fin A.rank) ℂ) := funext fun τ => by rw [hsA]
  have et : X.rW.s = fun _ => (1 : Matrix (Fin WW.rank) (Fin WW.rank) ℂ) := funext hsW
  rw [e1, e2]
  rw [es, et] at hzero ⊢
  change pureTensorO W.ψ W.θ (negSp A) WW (fun _ => -1) (fun _ => 1) _ _ _ _ _ = _
  rw [GlobalTheory.FockNegSubst.pureTensorO_negSp_subst D W.ψ W.θ A WW hψ hθ _ _ _ _ _ hgθ]
  exact hzero _
end GlobalTheory.MovedJetNZ
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_of_moved_vacuum_nonvanishing : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ (t : T), ∀ γ ∈ Formalism.L2.Theta.GQ A, ∀ a ∈ GinfC A, ∀ γ' ∈ Formalism.L2.Theta.GQ WW, ∀ a' ∈ GinfC WW,
      γ * a ∈ GfC A → γ' * a' ∈ GfC WW →
      ∃ k : FVar D WW.rank A.rank →₀ ℕ, pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.ω t (γ, γ') X.vac) (MvPolynomial.monomial k 1) 0 ≠ 0 := by
  first | exact @_root_.GlobalTheory.MovedJetNZ.moved_vacuum_jet_ne_zero | exact _root_.GlobalTheory.MovedJetNZ.moved_vacuum_jet_ne_zero | (intros; apply _root_.GlobalTheory.MovedJetNZ.moved_vacuum_jet_ne_zero <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.KFiniteCuspAverageHasKType
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.KFinCuspAvgType
open Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.TypeSum GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined
variable {n : ℕ}
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool} {σ : Mx n → (H →L[ℂ] H)}
end GlobalTheory.KFinCuspAvgType
end
namespace GlobalTheory.KFinCuspAvgType
open Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.TypeSum GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined
theorem kFinite_average_isTypeAt : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ N : GlobalTheory.Grid.Node D, N.V.SigOK →
    ∀ (τ : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), Continuous e → GlobalTheory.TypeSum.KFinFun (N.M.ε τ) e →
    ∀ φ : GA D N.V → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ →
    IsTypeAt θ N.V τ (N.S τ) (GlobalTheory.KFinCuspApprox.avgN θ N τ e φ) := by
  intro hPr D θ hθ N _ τ e _ he φ hφ
  obtain ⟨H, i1, i2, σ, lam, ε', P, hE, hD, hP, hJ, hx⟩ := hφ.2.2 τ
  obtain ⟨-, hε⟩ := GlobalTheory.SignedParTest.isEnum_unique hE (N.M.enum τ)
  subst hε
  haveI : CompleteSpace H := hD.1
  have hσ : Std (N.M.ε τ) σ := std_of_isDS hPr.harishChandraModules hD
  have hσ1 := hσ.1
  set fr := N.M.fr τ with hfr
  have hf := N.M.fr_unit τ
  have hfJ := N.M.fr_gram τ
  rw [← hfr] at hf hfJ
  have hdP := (isUnit_iff_isUnit_det _).1 hP
  have hdf := (isUnit_iff_isUnit_det _).1 hf
  have hG : IsUnit (gramAt D N.V τ) := isUnit_gram hP hJ
  have hc1 : fr * P⁻¹ ∈ UJset (N.M.ε τ) := mul_inv_mem_UH hP hfJ hJ
  have hc2 : P * fr⁻¹ ∈ UJset (N.M.ε τ) := mul_inv_mem_UH hf hJ hfJ
  have e12 : fr * P⁻¹ * (P * fr⁻¹) = 1 := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hdP, Matrix.mul_nonsing_inv _ hdf]
  have e21 : P * fr⁻¹ * (fr * P⁻¹) = 1 := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hdf, Matrix.mul_nonsing_inv _ hdP]
  have hconj : ∀ {Q : Mx N.V.rank}, IsUnit Q → Qᴴ * Jm (N.M.ε τ) * Q = gramAt D N.V τ →
      ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ), Q * g * Q⁻¹ ∈ UJset (N.M.ε τ) := fun {Q} hQ hQJ g hg =>
    mul_inv_mem_UH hQ (by
      calc (Q * g)ᴴ * Jm (N.M.ε τ) * (Q * g) = gᴴ * (Qᴴ * Jm (N.M.ε τ) * Q) * g := by
            simp only [conjTranspose_mul, Matrix.mul_assoc]
        _ = gramAt D N.V τ := by rw [hQJ]; exact hg) hQJ
  refine ⟨H, i1, i2, σ, lam, N.M.ε τ, fr, hE, hD, hf, hfJ, fun x => ?_⟩
  have h1 := hasTypeAll_iff.2 (hx x)
  have h2 := hasTypeAll_transport _ H H (fun g => σ (P * g * P⁻¹)) σ (gramAt D N.V τ) (Jm (N.M.ε τ)) fr hG hf hfJ
    (uIso hσ1 hc1 hc2 e12 e21) (fun g hg v => by
      rw [uIso_apply, uIso_apply, ← sigma_mul hσ1 hc1 (hconj hP hJ g hg), ← sigma_mul hσ1 (hconj hf hfJ g hg) hc1]
      congr 2
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hdP, Matrix.nonsing_inv_mul_cancel_left _ _ hdf]) _ h1
  obtain ⟨S, hS, hc, v, ℓ, C, h⟩ := h2
  have h3 := GlobalTheory.SeriesToClosure.moves_avg hθ hf hfJ hσ he φ x S v ℓ C hS hc h
  have h4 : HasTypeAll (lieSet (N.M.ε τ)) (UJset (N.M.ε τ)) σ
      (GlobalTheory.SeriesToClosure.res θ N.V τ fr (GlobalTheory.KFinCuspApprox.avgN θ N τ e φ) x) := ⟨S, hS, hc, _, ℓ, C, h3⟩
  have hfi : IsUnit fr⁻¹ := (isUnit_iff_isUnit_det _).2 (Matrix.isUnit_nonsing_inv_det _ hdf)
  have hfiJ : (fr⁻¹)ᴴ * gramAt D N.V τ * fr⁻¹ = Jm (N.M.ε τ) := by
    rw [← hfJ]
    calc (fr⁻¹)ᴴ * (frᴴ * Jm (N.M.ε τ) * fr) * fr⁻¹ = (fr * fr⁻¹)ᴴ * Jm (N.M.ε τ) * (fr * fr⁻¹) := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [Matrix.mul_nonsing_inv _ hdf]; simp
  have h5 := hasTypeAll_transport _ H H σ (fun g => σ (fr * g * fr⁻¹)) (Jm (N.M.ε τ)) (gramAt D N.V τ) fr⁻¹
    (isUnit_Jm _) hfi hfiJ (LinearIsometryEquiv.refl ℂ H) (fun g _ w => by
      show σ g w = σ (fr * (fr⁻¹ * g * fr⁻¹⁻¹) * fr⁻¹) w
      rw [Matrix.nonsing_inv_nonsing_inv _ hdf]
      simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hdf, Matrix.mul_nonsing_inv _ hdf,
        Matrix.mul_one]) _ h4
  have e5 : (fun y => GlobalTheory.SeriesToClosure.res θ N.V τ fr (GlobalTheory.KFinCuspApprox.avgN θ N τ e φ) x (fr⁻¹⁻¹ * y * fr⁻¹)) =
      fun y => GlobalTheory.KFinCuspApprox.avgN θ N τ e φ (x * atTau θ N.V τ y) := funext fun y => by
    rw [Matrix.nonsing_inv_nonsing_inv _ hdf, GlobalTheory.SeriesToClosure.res_conj hf]
  rw [e5] at h5
  exact hasTypeAll_iff.1 h5
end GlobalTheory.KFinCuspAvgType
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kFinite_cusp_average_hasKType : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ N : GlobalTheory.Grid.Node D, N.V.SigOK → ∀ (τ : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), Continuous e → GlobalTheory.TypeSum.KFinFun (N.M.ε τ) e → ∀ φ : GA D N.V → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ → IsTypeAt θ N.V τ (N.S τ) (GlobalTheory.KFinCuspApprox.avgN θ N τ e φ) := by
  first | exact @_root_.GlobalTheory.KFinCuspAvgType.kFinite_average_isTypeAt | exact _root_.GlobalTheory.KFinCuspAvgType.kFinite_average_isTypeAt | (intros; apply _root_.GlobalTheory.KFinCuspAvgType.kFinite_average_isTypeAt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.KInfinityActionProdLines
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open scoped ComplexConjugate
noncomputable section
namespace GlobalTheory.KInfLines
variable {D : D7}
end GlobalTheory.KInfLines
namespace GlobalTheory.KInfLines
variable {D : D7}
end GlobalTheory.KInfLines
namespace GlobalTheory.KInfLines
variable {D : D7} {W : HSp D} {V : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E W.rank}
end GlobalTheory.KInfLines
namespace GlobalTheory.KInfLines
variable {D : D7} {W : HSp D} {V : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E W.rank}
theorem kInfinity_prod_lines : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (θ : InfFam D) (W : HSp D) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
    (V : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E W.rank) (r s : ℕ) (hJ : V.J = (1 : D.host.E) • W.gram),
    IsInfFam θ → Bs.IsGood D.sp.cm.sig → V.IsHerm D.sp.cm.sig Bs r s →
    ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf D.sp.cm.sig V Bs.emb,
    ∃ l : List (D.what₂.Tau × Matrix (Fin W.rank) (Fin W.rank) ℂ),
      (∀ q ∈ l, q.2 ∈ lieAt W q.1 ∧ ∀ t : ℝ,
        GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hJ (oneP θ W q.1 q.2 t) ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf D.sp.cm.sig V Bs.emb) ∧
      k = (l.map fun q => GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hJ (oneP θ W q.1 q.2 1)).prod := by
  intro _ D θ W Bs V r s hJ hθ _ hV k hk
  obtain rfl := Eqv.eq_thetaC D hθ
  choose C hC using cartan_data hJ Bs hV hk
  choose Z hZ using fun t => exists_log_of_cartan (GlobalTheory.SmoothForms.RealPts.gramAt_herm W t) (hC t).1
    (unitFam_gsOf hJ k t) (hC t).2.1
  refine ⟨Finset.univ.toList.map fun t => (t, Z t), ?_, prod_eq hJ hk.1 Z fun t => ⟨(hZ t).1, (hZ t).2.2⟩⟩
  intro q hq
  obtain ⟨t, -, rfl⟩ := List.mem_map.1 hq
  exact ⟨(hZ t).1, line_mem hJ Bs C (fun t => (hC t).2.2) (hZ t).1 (hZ t).2.1⟩
end GlobalTheory.KInfLines
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kInfinity_action_prod_lines : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (θ : InfFam D) (W : HSp D) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
    (V : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E W.rank) (r s : ℕ) (hJ : V.J = (1 : D.host.E) • W.gram),
    IsInfFam θ → Bs.IsGood D.sp.cm.sig → V.IsHerm D.sp.cm.sig Bs r s →
    ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf D.sp.cm.sig V Bs.emb,
    ∃ l : List (D.what₂.Tau × Matrix (Fin W.rank) (Fin W.rank) ℂ),
      (∀ q ∈ l, q.2 ∈ lieAt W q.1 ∧ ∀ t : ℝ,
        GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hJ (oneP θ W q.1 q.2 t) ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf D.sp.cm.sig V Bs.emb) ∧
      k = (l.map fun q => GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hJ (oneP θ W q.1 q.2 1)).prod := by
  first | exact @_root_.GlobalTheory.KInfLines.kInfinity_prod_lines | exact _root_.GlobalTheory.KInfLines.kInfinity_prod_lines | (intros; apply _root_.GlobalTheory.KInfLines.kInfinity_prod_lines <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.KTypePreservedAverageOtherPlace
section
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.AvgOtherPlace
open Formalism.MainNotions.S Formalism.REAL MeasureTheory Matrix GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.PointAtPlaceHom
open GlobalTheory.Mem.AutSpace GlobalTheory.Mem.RealTranslate GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes
open scoped TensorProduct
variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}
section Avg
variable {K : Type} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K)
  [IsFiniteMeasure μ] {τ τ' : D.what₂.Tau} {κ : K → Matrix (Fin V.rank) (Fin V.rank) ℂ} {e : K → ℂ}
end Avg
section Closure
variable {K : Type} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K)
  [IsFiniteMeasure μ] {τ τ' : D.what₂.Tau} {κ : K → Matrix (Fin V.rank) (Fin V.rank) ℂ} {e : K → ℂ}
end Closure
theorem kFinite_average_isTypeAt : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ N : GlobalTheory.Grid.Node D, N.V.SigOK →
    ∀ (τ τ' : D.what₂.Tau), τ' ≠ τ → ∀ e : Formalism.REAL.KG (N.M.ε τ) → ℂ, Continuous e → GlobalTheory.TypeSum.KFinFun (N.M.ε τ) e →
    ∀ φ : GA D N.V → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ →
    IsTypeAt θ N.V τ' (N.S τ') (GlobalTheory.KFinCuspApprox.avgN θ N τ e φ) := by
  intro hPr D θ hθ N hN τ τ' hne e he _ φ hφ
  have hP := N.M.fr_unit τ
  have hJ := N.M.fr_gram τ
  have hU : ∀ k, (N.M.fr τ)⁻¹ * toMK k * N.M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ) :=
    fun k => conj_inv_mem hP hJ (K_le_UJ (toMK_mem_K k))
  have hκ := GlobalTheory.SeriesToClosure.continuous_conjK (ε := N.M.ε τ) (P := N.M.fr τ)
  have p1 := hPr.discreteSeriesUpqExists
  have p2 := GlobalTheory.Published.discreteSeriesHermitianUnique_iff.1 hPr.discreteSeriesHermitianUnique
  have p3 := hPr.harishChandraModules
  have p4 := hPr.casselmanWallach
  have hT := GlobalTheory.SeriesToClosure.hasTypeAt_of_isTypeAt θ N.V τ' (N.S τ') φ p1 p2 p3 p4 hθ hN
    (GlobalTheory.NodePar.goodPar_of_sigOK N hN τ') hφ.1 (hφ.2.2 τ')
  have hA := GlobalTheory.RealAverage.isAutFunSm_average D θ hθ N.V τ (KG (N.M.ε τ)) (muK (N.M.ε τ)) _ hκ hU e he φ hφ.1
  exact GlobalTheory.T.automorphicForm_uniformLimit_discreteSeries_series θ N.V τ' (N.S τ') _ p1 p2 p3 p4 hθ hN (GlobalTheory.NodePar.goodPar_of_sigOK N hN τ') hA
    (hasTypeAt_avgF (muK (N.M.ε τ)) hθ hne hκ hU he hφ.1.cont hT)
end GlobalTheory.AvgOtherPlace
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kType_preserved_average_other_place : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ N : GlobalTheory.Grid.Node D, N.V.SigOK → ∀ (τ τ' : D.what₂.Tau), τ' ≠ τ → ∀ e : Formalism.REAL.KG (N.M.ε τ) → ℂ, Continuous e → GlobalTheory.TypeSum.KFinFun (N.M.ε τ) e → ∀ φ : GA D N.V → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ → IsTypeAt θ N.V τ' (N.S τ') (GlobalTheory.KFinCuspApprox.avgN θ N τ e φ) := by
  first | exact @_root_.GlobalTheory.AvgOtherPlace.kFinite_average_isTypeAt | exact _root_.GlobalTheory.AvgOtherPlace.kFinite_average_isTypeAt | (intros; apply _root_.GlobalTheory.AvgOtherPlace.kFinite_average_isTypeAt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.KerPolarizationProjectionStabilizerFinite
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section
namespace GlobalTheory.SquareAgree.KerStabFin
theorem stabilizer_finite_ker_polarization : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F), ∀ h ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt D.sp.cm.sig Γ.W (GlobalTheory.AdelicU.evFin D.host.F v), ∀ Φ ∈ kerPD ψ θ A₁ B Bs Γ cB p', om' (1, h) Φ ∈ kerPD ψ θ A₁ B Bs Γ cB p' := by
  intro _ D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB _ _ hO hT Pi rf rl p p' hM v h hh Φ hΦ
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := hO.psi ▸ hT.base.std
  obtain ⟨g, hg, rfl⟩ := GlobalTheory.SquareAgree.KapOnto.kapX_onto D X e Γ.W hO.JX v h hh
  rw [mem_kerPD hstd] at hΦ ⊢
  obtain ⟨_, Φ₀, hΦ₀, hDat, hp⟩ := hΦ
  have hW := hO.weilB Φ Φ₀ hDat 1 g
  have h1 : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) hO.JW₁ 1 = 1 :=
    Subtype.ext (by simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU, map_one])
  rw [h1] at hW
  have hmem : ωB (1, g) Φ₀ ∈ algF ψ θ false A₁ B := hM.mapB.stabX.1 g hg Φ₀ hΦ₀
  obtain ⟨ΦD, hΦD, hD'⟩ := hO.algB _ hmem
  have heq := GlobalTheory.ThetaInj.theta_inj Γ.M' ψ hstd cB _ _ _ hW hD'
  refine ⟨heq ▸ hΦD, _, hmem, hW, ?_⟩
  rw [hM.mapB.eqf g hg Φ₀ hΦ₀, hp, map_zero]
end GlobalTheory.SquareAgree.KerStabFin
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ker_polarizationProjection_stabilizer_finite : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F), ∀ h ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt D.sp.cm.sig Γ.W (GlobalTheory.AdelicU.evFin D.host.F v), ∀ Φ ∈ kerPD ψ θ A₁ B Bs Γ cB p', om' (1, h) Φ ∈ kerPD ψ θ A₁ B Bs Γ cB p' := by
  first | exact @_root_.GlobalTheory.SquareAgree.KerStabFin.stabilizer_finite_ker_polarization | exact _root_.GlobalTheory.SquareAgree.KerStabFin.stabilizer_finite_ker_polarization | (intros; apply _root_.GlobalTheory.SquareAgree.KerStabFin.stabilizer_finite_ker_polarization <;> assumption)
end
end

