import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0691
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0047
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0703
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0678
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0043
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0696
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ResidueVanishing.Rethread
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.ResCore
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0689
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0045
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0701
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0729
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0044
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0733

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.HasDerivAtThetaIntegralInterchange
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
open scoped Classical
namespace GlobalTheory.ThetaInterchange
open Filter Topology GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {Y : Spc F E n} {Wd : Spc F E d}
theorem thetaInterchange_isPure (hPr : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (M : Model σ Y Wd) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ Y Wd)
    (hcm : IsCMExt F E σ) (hψ : IsStd ψ)
    (hG : M.IsGood ψ) (hW : M.IsWeil ψ χX χW om) (γ : Multiplicative ℝ →* UA σ Wd.J) (hγ : γ ∈ Lines σ Wd)
    (f : SInf F (Fin n × Fin d)) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Fv F v) → ℂ) (hφ : ∀ v, φ v ∈ SB _)
    (hs : ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) :
    Good M ψ (fun t => om (1, γ (Multiplicative.ofAdd t))) (pure f φ) := by
  have hv : ∀ᶠ v in cofinite, φ v = M.vac v := (hs.and hG.std).mono fun v h => h.1.trans h.2.symm
  obtain ⟨c, g, hc, hlim⟩ := _root_.GlobalTheory.T.twisted_smoothLine_pure_weight hPr M ψ χX χW om hcm hψ hG hW γ hγ f φ hφ hv
  refine ⟨GlobalTheory.TensUniq.pure_mem_schA f φ hφ hs, pure g φ, GlobalTheory.TensUniq.pure_mem_schA g φ hφ hs, fun x => ?_, fun w => ?_⟩
  · have ev : Continuous fun s : SInf F (Fin n × Fin d) => s (fun j => evI F (x j)) := by
      have h1 := (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ).continuous
      exact (continuous_eval_const (F := BoundedContinuousFunction (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ)
        (fun j => evI F (x j))).comp h1
    simp only [hc]
    rw [hasDerivAt_iff_tendsto_slope]
    refine (((ev.tendsto g).comp hlim).mul_const (∏ᶠ v, φ v fun j => evFin F v (x j))).congr'
      (Eventually.of_forall fun t => ?_)
    rw [slope_def_module]
    simp only [Function.comp_apply, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, SchwartzMap.smul_apply, SchwartzMap.sub_apply, sub_zero, Complex.real_smul]
    ring
  · obtain ⟨Λ, hΛ⟩ := GlobalTheory.ThetaHeisCLM.exists_clm_thetaSum_rho_pure M ψ hψ hG w φ hφ hv
    simp only [hc, hΛ]
    rw [hasDerivAt_iff_tendsto_slope]
    refine ((Λ.continuous.tendsto g).comp hlim).congr' (Eventually.of_forall fun t => ?_)
    simp [slope_def_module, map_sub, map_smul]
end GlobalTheory.ThetaInterchange
open GlobalTheory.ThetaInterchange in
theorem GlobalTheory.ThetaInterchange.hasDerivAt_theta_integral_interchange : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) {n k : ℕ} (Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E n) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E k)
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Xs Ws) (ψ' : AddChar (AF D.host.F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Xs Ws)
    (τ : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w),
    GlobalTheory.RealDict.PublishedHyps D Xs Ws Mo ψ' χX χW om τ → Mo.IsGood ψ' →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Ws,
    ∀ (f f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin n × Fin k)) (r : (Fin n × Fin k → AF D.host.F) → ℂ),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) f r → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) f₁ r →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ →
      ∀ {d : ℕ} (G : Matrix (Fin n) (Fin n) D.host.E) (e : Fin k ≃ Fin d) (x : Matrix (Fin d) (Fin n) (AE D)),
        HasDerivAt (fun t : ℝ => GlobalTheory.TripleRead.thO Mo ψ' G e
            (om (1, γ (Multiplicative.ofAdd t)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) f r)) x)
          (GlobalTheory.TripleRead.thO Mo ψ' G e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) f₁ r) x) 0 := by
  intro hPr D n k Xs Ws Mo ψ' χX χW om τ hP hG γ hγ f f₁ r hr hr₁ hD d G e x
  obtain ⟨hcm, hψ, -, -, -, -, -, -, -, -, hW, -, -⟩ := hP
  have hT : ∀ t : ℝ, ∀ Φ ∈ schA D.host.F (Fin n × Fin k), om (1, γ (Multiplicative.ofAdd t)) Φ ∈ schA D.host.F _ :=
    fun t Φ hΦ => (GlobalTheory.WeilM.IsUWeilPair.isUSplitting hW).pres _ Φ hΦ
  let N : Submodule ℂ ((Fin n × Fin k → AF D.host.F) → ℂ) :=
    { carrier := {Φ | Good Mo ψ' (fun t => om (1, γ (Multiplicative.ofAdd t))) Φ}
      zero_mem' := good_zero Mo ψ' _
      add_mem' := fun ha hb => good_add Mo hψ hT ha hb
      smul_mem' := fun c _ ha => good_smul Mo ψ' _ c ha }
  have hle : schA D.host.F (Fin n × Fin k) ≤ N :=
    schA_le_of_pure fun f φ hφ hs => _root_.GlobalTheory.ThetaInterchange.thetaInterchange_isPure hPr Mo ψ' χX χW om hcm hψ hG hW γ hγ f φ hφ hs
  obtain ⟨-, Φ', -, hpt, hth⟩ := hle hr.2
  have hΦ' : Φ' = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) f₁ r :=
    funext fun y => (hpt y).unique (hD r hr y)
  have := hth (GlobalTheory.TripleRead.ptO G e x)
  rw [hΦ'] at this
  exact this
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_interchange_derivative_pure : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) {n k : ℕ} (Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E n) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E k)
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Xs Ws) (ψ' : AddChar (AF D.host.F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Xs Ws)
    (τ : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w),
    GlobalTheory.RealDict.PublishedHyps D Xs Ws Mo ψ' χX χW om τ → Mo.IsGood ψ' →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Ws,
    ∀ (f f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin n × Fin k)) (r : (Fin n × Fin k → AF D.host.F) → ℂ),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) f r → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) f₁ r →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ →
      ∀ {d : ℕ} (G : Matrix (Fin n) (Fin n) D.host.E) (e : Fin k ≃ Fin d) (x : Matrix (Fin d) (Fin n) (AE D)),
        HasDerivAt (fun t : ℝ => GlobalTheory.TripleRead.thO Mo ψ' G e
            (om (1, γ (Multiplicative.ofAdd t)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) f r)) x)
          (GlobalTheory.TripleRead.thO Mo ψ' G e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) f₁ r) x) 0 := by
  first | exact @_root_.GlobalTheory.ThetaInterchange.hasDerivAt_theta_integral_interchange | exact _root_.GlobalTheory.ThetaInterchange.hasDerivAt_theta_integral_interchange | (intros; apply _root_.GlobalTheory.ThetaInterchange.hasDerivAt_theta_integral_interchange <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.KFiniteAlgebraClosedUnderDerivation
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
namespace GlobalTheory.SquareAgree.KFinAlg
theorem polynomial_vector_kFinite (fockFirst : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∃ (A : InfinitePlace F → Matrix (Fin a) (Formalism.BasicNotions.TH.Ix (a - Γ.p) Γ.p) ℂ)
      (Φ : GlobalTheory.RealLift.Tens F (a - Γ.p) Γ.p (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q) →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')))
      (c : InfinitePlace F → ℂ),
      (∀ w, GlobalTheory.RealLift.IsFrame ((1 : ℂ) • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Γ.V.J).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w))) (A w)) ∧
      (∀ w, Γ.V.θ w * A w = A w * Formalism.BasicNotions.TH.Jm (a - Γ.p) Γ.p) ∧
      LinearMap.range Φ = Γ.M.Pol Bs.ψ Bs.emb ∧
      GlobalTheory.RealLift.ActsBy Bs.emb A (om.comp (MonoidHom.inl _ _)) Φ
        (Formalism.BasicNotions.TH.fockAct1 (a - Γ.p) Γ.p (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q)) c) : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' → ∀ f ∈ Γ.M.Pol Bs.ψ Bs.emb,
    ∃ P : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a'))), FiniteDimensional ℂ P ∧ P ≤ Γ.M.Pol Bs.ψ Bs.emb ∧
      f ∈ P ∧ ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ Γ.V Bs.emb, ∀ g ∈ P, ∃ g₁ ∈ P,
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (om (k, 1)) (⇑g) (⇑g₁) := by
  intro hPr F E _ _ _ _ _ σ Bs a a' Γ Xc om om' hT f hf
  classical
  obtain ⟨A, Φ, c, hA, hAθ, hr, hact⟩ := fockFirst hPr F E σ Bs a a' Γ Xc om om' hT
  have hb := hT.base
  have hwp : GlobalTheory.WeilM.IsUWeilPair (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.WeilM.adeleClass F) Bs.ψ (-1)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Γ.V.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Γ.W.J) Γ.M.co Xc.β (Xc.β / Xc.α) om := hT.weil
  have hadm := fun g => (hwp.isUSplitting).adm g
  rw [← hr] at hf
  obtain ⟨T, rfl⟩ := hf
  obtain ⟨D, hD⟩ := exists_tensDeg T
  haveI : FiniteDimensional ℂ (tensDeg F (a - Γ.p) Γ.p (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q) D) :=
    LinearMap.finiteDimensional_range _
  refine ⟨(tensDeg F _ _ _ _ D).map Φ, inferInstance, hr ▸ LinearMap.map_le_range, ⟨T, hD, rfl⟩, ?_⟩
  rintro k hk _ ⟨T', hT', rfl⟩
  obtain ⟨γ, hγ, Yg, hgen, hKC, hγ1⟩ := GlobalTheory.RealLift.kLine_of_lineEx GlobalTheory.T.unitaryLieElements_generate_oneParamLines F E σ (Fin a) _ _ Bs.emb
    (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Γ.V.J) 1 A Γ.V.θ hb.cm hA hAθ k hk.1 hk.2
  let L := GlobalTheory.RealLift.sumPl (fun w => Formalism.BasicNotions.TH.fockAct1 (a - Γ.p) Γ.p (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q) (Yg w) +
    (c w * (Yg w).trace) • (1 : Module.End ℂ _))
  have hloc : GlobalTheory.RealLift.LocFin L := GlobalTheory.RealLift.locFin_sumPl _ _ _ fun w v => by
    obtain ⟨⟨W, hW, hv, hs⟩, -⟩ := (GlobalTheory.FockPolGK.pol_locFin_weights _ _ _ _).1 v
    exact ⟨W, hW, hv, fun y hy => W.add_mem (hs (Yg w) (hKC w) y hy) (W.smul_mem _ hy)⟩
  obtain ⟨U, hexp, hSA⟩ := GlobalTheory.T.weakExponential_action_on_fockVectors F (Fin a × Fin (a + a')) _ Φ L ((om.comp (MonoidHom.inl _ _)).comp γ) hloc
    (fun t l hl => hadm _ l hl) (fun T => hact γ hγ Yg hgen T)
  let Lw : ∀ w : InfinitePlace F, Module.End ℂ (Formalism.BasicNotions.TH.Pol (a - Γ.p) Γ.p (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q)) :=
    fun w => Formalism.BasicNotions.TH.fockAct1 (a - Γ.p) Γ.p (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q) (Yg w) +
      (c w * (Yg w).trace) • (1 : Module.End ℂ _)
  let Nw : ∀ w : InfinitePlace F, Submodule ℂ (Formalism.BasicNotions.TH.Pol (a - Γ.p) Γ.p (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q)) :=
    fun _ => MvPolynomial.restrictTotalDegree _ ℂ D
  have hN : ∀ i, ∀ z ∈ Nw i, Lw i z ∈ Nw i := by
    intro i z hz
    simp only [Lw, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]
    exact Submodule.add_mem _ (GlobalTheory.FockPolGK.kStable1 _ _ _ _ D (Yg i) (hKC i) z hz) (Submodule.smul_mem _ _ hz)
  have hLst : ∀ y ∈ tensDeg F _ _ _ _ D, L y ∈ tensDeg F _ _ _ _ D := by
    intro y hy
    change GlobalTheory.RealLift.sumPl Lw y ∈ _
    rw [GlobalTheory.RealLift.sumPl, LinearMap.sum_apply]
    exact Submodule.sum_mem _ fun w _ => GlobalTheory.RealLift.atPl_mem_range_map Lw Nw hN w y hy
  refine ⟨Φ (U T'), ⟨U T', exp_stable hexp _ hLst T' hT', rfl⟩, ?_⟩
  have h1 := hSA T'
  rw [MonoidHom.comp_apply, hγ1] at h1
  exact (GlobalTheory.RealLift.actsLaws F _ (Φ T') (Φ (U T')) (Φ (U T'))).2.1 _ (map_zero _) h1
theorem derivation_algebra_kFinite : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' → ∀ ΦD ∈ GlobalTheory.SquareAgree.algD Γ.M Bs.ψ Bs.emb,
    ∃ U : Submodule ℂ ((Fin a × Fin (a + a') → AF F) → ℂ), FiniteDimensional ℂ U ∧
      U ≤ GlobalTheory.SquareAgree.algD Γ.M Bs.ψ Bs.emb ∧ ΦD ∈ U ∧
      ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ Γ.V Bs.emb, ∀ x ∈ U, om (k, 1) x ∈ U := by
  intro hPr F E _ _ _ _ _ σ Bs a a' Γ Xc om om' hT ΦD hΦ
  have hPair := GlobalTheory.ThK.RealUniq.isPair_V hT
  have hstdM := hPair.good.std
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, φ, hf, hSB, hcof, rfl⟩ := hx
    obtain ⟨P, hPfin, hPle, hfP, hPst⟩ := _root_.GlobalTheory.SquareAgree.KFinAlg.polynomial_vector_kFinite _root_.GlobalTheory.T.real_lift_exists_fock_map hPr F E σ Bs a a' Γ Xc om om' hT f hf
    have hstd : ∀ᶠ v in Filter.cofinite,
        φ v = Set.indicator {x : Fin a × Fin (a + a') → Fv F v |
          ∀ j, x j ∈ v.adicCompletionIntegers F} 1 := by
      filter_upwards [hcof, hstdM] with v h1 h2
      rw [h1, h2]
    refine ⟨P.map (pureL φ), inferInstance, ?_, ⟨f, hfP, rfl⟩, ?_⟩
    · rintro _ ⟨g, hg, rfl⟩
      exact Submodule.subset_span ⟨g, φ, hPle hg, hSB, hcof, rfl⟩
    · rintro k hk _ ⟨g, hg, rfl⟩
      obtain ⟨g₁, hg₁, hA⟩ := hPst k hk g hg
      have key : om (k, 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g₁ φ :=
        hA _ (GlobalTheory.ThK.EvUniqInf.rest_pure _ _ hSB hstd)
      exact ⟨g₁, hg₁, key.symm⟩
  | zero =>
    exact ⟨⊥, inferInstance, bot_le, Submodule.zero_mem _, fun k _ x hx => by
      rw [Submodule.mem_bot] at hx; subst hx; rw [map_zero]; exact Submodule.zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨U₁, h1, l1, m1, s1⟩ := hx
    obtain ⟨U₂, h2, l2, m2, s2⟩ := hy
    refine ⟨U₁ ⊔ U₂, inferInstance, sup_le l1 l2, Submodule.add_mem_sup m1 m2, fun k hk z hz => ?_⟩
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.1 hz
    rw [map_add]
    exact Submodule.add_mem_sup (s1 k hk y₁ hy₁) (s2 k hk y₂ hy₂)
  | smul c x _ hx =>
    obtain ⟨U, h, l, m, s⟩ := hx
    exact ⟨U, h, l, U.smul_mem c m, s⟩
end GlobalTheory.SquareAgree.KFinAlg
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
theorem _root_.GlobalTheory.T.kFinite_algebra_closed_under_derivation : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' → ∀ ΦD ∈ GlobalTheory.SquareAgree.algD Γ.M Bs.ψ Bs.emb,
    ∃ U : Submodule ℂ ((Fin a × Fin (a + a') → AF F) → ℂ), FiniteDimensional ℂ U ∧
      U ≤ GlobalTheory.SquareAgree.algD Γ.M Bs.ψ Bs.emb ∧ ΦD ∈ U ∧
      ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ Γ.V Bs.emb, ∀ x ∈ U, om (k, 1) x ∈ U := by
  first | exact @_root_.GlobalTheory.SquareAgree.KFinAlg.derivation_algebra_kFinite | exact _root_.GlobalTheory.SquareAgree.KFinAlg.derivation_algebra_kFinite | (intros; apply _root_.GlobalTheory.SquareAgree.KFinAlg.derivation_algebra_kFinite <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.KplugFill
section
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
noncomputable section
namespace GlobalTheory.Core.Rk.Exh.Top
theorem downNe_k_of_hypotheses' : ResidueKilled.DM → GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.SimplePole → ∀ D : D7, EulerRight D → DownNe D :=
  fun hDM hSP => downNe_of_core hDM PositivityTheory.Rg.Rsw.resCore hSP
end GlobalTheory.Core.Rk.Exh.Top
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.LieAlgebraPreservesPolynomialKernel
section
section
open NumberField IsDedekindDomain
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.PolKerLie
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PolKer
theorem polynomialKernel_constTerm_lieDeriv : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.W, ∀ Φ Φ₁, GlobalTheory.PolKer.PolZero Bs G Xc R Rf (Φ) →
    (∀ x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0) → GlobalTheory.PolKer.PolZero Bs G Xc R Rf (Φ₁) := by
  intro hP F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM γ hγ Φ Φ₁ hΦ hd
  obtain ⟨T, hT, m, f, φ, hf, rfl, hz⟩ := hΦ
  have act := _root_.GlobalTheory.T.dualPair_preserves_polarization hP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (GlobalTheory.ThK.RealUniq.isPair_V hM.triple)
  obtain ⟨D, hDm, hDi⟩ := act.2.2.1 γ hγ
  have hstd : ∀ i, ∀ᶠ v in Filter.cofinite,
      φ i v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers F} 1 := by
    intro i
    filter_upwards [T.finite_toSet.compl_mem_cofinite, hM.triple.geo.hM.std] with v hv hs
    rw [(hf i).2.2 v hv, hs]
  have hder : ∀ i x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) (pure (f i) (φ i)) x)
      (pure (D (f i)) (φ i) x) 0 := fun i x =>
    (hDi (f i) (hf i).1 (D (f i))).2 rfl _
      (GlobalTheory.ThK.EvUniqInf.rest_pure (f i) (φ i) (hf i).2.1 (hstd i)) x
  have hsum : ∀ x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) (∑ i, pure (f i) (φ i)) x)
      (∑ i, pure (D (f i)) (φ i) x) 0 := by
    intro x
    have eq : (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) (∑ i, pure (f i) (φ i)) x) =
        fun t : ℝ => ∑ i ∈ Finset.univ, om (1, γ (Multiplicative.ofAdd t)) (pure (f i) (φ i)) x := by
      funext t
      simp [map_sum, Finset.sum_apply]
    rw [eq]
    exact HasDerivAt.fun_sum (fun i _ => hder i x)
  have e1 : Φ₁ = ∑ i, pure (D (f i)) (φ i) := by
    funext x
    rw [Finset.sum_apply]
    exact (hd x).unique (hsum x)
  refine ⟨T, hT, m, fun i => D (f i), φ, fun i => ⟨hDm _ (hf i).1, (hf i).2⟩, e1, ?_⟩
  let π : G.M.Pol Bs.ψ Bs.emb →ₗ[ℂ] R.Pi := R.p ∘ₗ (G.M.Pol Bs.ψ Bs.emb).subtype
  have hπ : Function.Surjective π := fun y => by
    have : y ∈ (G.M.Pol Bs.ψ Bs.emb).map R.p := hM.real.quot.onto ▸ Submodule.mem_top
    obtain ⟨g, hg, e⟩ := Submodule.mem_map.1 this
    exact ⟨⟨g, hg⟩, e⟩
  have ker0 : ∀ g ∈ G.M.Pol Bs.ψ Bs.emb, R.p g = 0 → R.p (D g) = 0 := fun g hg h0 => by
    have := hM.real.lie γ hγ g hg 0 (zero_mem _) (D g) 0 ((hDi g hg _).2 rfl)
      (GlobalTheory.ThK.RealUniq.actsD_zero _) (by rw [h0, map_zero])
    rwa [map_zero] at this
  let A := GlobalTheory.ThK.RealUniq.induced π hπ (D.restrict hDm) (fun u hu => ker0 u.1 u.2 hu)
  have hA : ∀ i, R.p (D (f i)) = A (R.p (f i)) := fun i =>
    (GlobalTheory.ThK.RealUniq.induced_apply π hπ (D.restrict hDm) (fun u hu => ker0 u.1 u.2 hu) ⟨f i, (hf i).1⟩).symm
  have := congrArg (A.rTensor _) hz
  simpa [map_sum, hA] using this
end GlobalTheory.PolKerLie
end
end

section
open NumberField IsDedekindDomain
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieAlgebra_preserves_polynomialKernel : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.W, ∀ Φ Φ₁, GlobalTheory.PolKer.PolZero Bs G Xc R Rf (Φ) →
    (∀ x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0) → GlobalTheory.PolKer.PolZero Bs G Xc R Rf (Φ₁) := by
  first | exact @_root_.GlobalTheory.PolKerLie.polynomialKernel_constTerm_lieDeriv | exact _root_.GlobalTheory.PolKerLie.polynomialKernel_constTerm_lieDeriv | (intros; apply _root_.GlobalTheory.PolKerLie.polynomialKernel_constTerm_lieDeriv <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.LineDerivativeSplitEqSum
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
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
namespace GlobalTheory.LineDerivSplit
theorem line_derivative_split_eq_sum : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n d : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' →
    ∀ {ι : Type} (l : List ι) (γs : ι → (Multiplicative ℝ →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J)),
    (∀ i, γs i ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ X) → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ X, (∀ t, γ t = (l.map fun i => γs i t).prod) →
    ∀ ΦD ∈ GlobalTheory.SquareAgree.algD M B.ψ B.emb, ∀ Φ₁D : (Fin n × Fin d → AF F) → ℂ,
    (∀ x, HasDerivAt (fun t : ℝ => om (γ (Multiplicative.ofAdd t), 1) ΦD x) (Φ₁D x) 0) →
    ∃ Ψ : ι → ((Fin n × Fin d → AF F) → ℂ), (∀ i, Ψ i ∈ GlobalTheory.SquareAgree.algD M B.ψ B.emb) ∧
      (∀ i, ∀ u, HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (M.co.rho B.ψ u (om (γs i (Multiplicative.ofAdd t), 1) ΦD)))
        (GlobalTheory.WeilM.thetaSum F (M.co.rho B.ψ u (Ψ i))) 0) ∧ Φ₁D = (l.map Ψ).sum := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP ι l γs hγs γ hγ hprod ΦD hΦD Φ₁D hΦ₁
  have hact := _root_.GlobalTheory.T.dualPair_preserves_polarization hPr F E σ B n d X W M χX χW om r s r' s' hP
  choose Ds hDsP hDs using fun i => hact.1 (γs i) (hγs i)
  obtain ⟨Dγ, -, hDγ⟩ := hact.1 γ hγ
  obtain ⟨m, c, g, hg⟩ := (Submodule.mem_span_set').1 hΦD
  choose f φ hf hSB hcof hgf using fun j => (g j).2
  have hstd : ∀ j, ∀ᶠ v in Filter.cofinite,
      φ j v = Set.indicator {x : Fin n × Fin d → Fv F v | ∀ k, x k ∈ v.adicCompletionIntegers F} 1 := by
    intro j
    filter_upwards [hcof j, hP.good.std] with v h1 h2
    rw [h1, h2]
  have hmem : ∀ j, c j • f j ∈ M.Pol B.ψ B.emb := fun j => Submodule.smul_mem _ _ (hf j)
  have hΦ : ΦD = ∑ j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c j • f j) (φ j) := by
    rw [← hg]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hgf j, pure_smul₀]
  refine ⟨fun i => ∑ j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Ds i (c j • f j)) (φ j), fun i => ?_, fun i u => ?_, ?_⟩
  · refine Submodule.sum_mem _ fun j _ => Submodule.subset_span ?_
    exact ⟨_, φ j, hDsP i _ (hmem j), hSB j, hcof j, rfl⟩
  · rw [hΦ]
    exact _root_.GlobalTheory.ThetaLineDerFirst.hasDerivAt_thetaSum_along_line hPr M B.ψ χX χW om hP.base.std hP.good hP.weil (γs i) (hγs i) m
      (fun j => c j • f j) (fun j => Ds i (c j • f j)) φ (fun j => ⟨hSB j, hcof j⟩)
      (fun j => (hDs i _ (hmem j) _).2 rfl) u
  · have hpt : ∀ x, Φ₁D x = ∑ j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Dγ (c j • f j)) (φ j) x := by
      intro x
      have h2 : HasDerivAt (fun t : ℝ => om (γ (Multiplicative.ofAdd t), 1) ΦD x)
          (∑ j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Dγ (c j • f j)) (φ j) x) 0 := by
        have e : (fun t : ℝ => om (γ (Multiplicative.ofAdd t), 1) ΦD x) =
            fun t => ∑ j, om (γ (Multiplicative.ofAdd t), 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c j • f j) (φ j)) x := by
          funext t
          rw [hΦ, map_sum, Finset.sum_apply]
        rw [e]
        have hs := HasDerivAt.sum (u := Finset.univ) fun j _ => GlobalTheory.ThetaFacInf.Fib.hasDerivAt_pure (φ j) (hSB j) (hstd j)
          ((hDγ _ (hmem j) _).2 rfl) x
        simpa [Finset.sum_fn] using hs
      exact (hΦ₁ x).unique h2
    have hadd : ∀ j, Dγ (c j • f j) = (l.map fun i => Ds i (c j • f j)).sum := fun j =>
      _root_.GlobalTheory.T.line_derivative_additive_in_lines hPr F E σ B n d X W M χX χW om r s r' s' hP l γs hγs γ hγ hprod _ (hmem j) _ _
        ((hDγ _ (hmem j) _).2 rfl) (fun i => (hDs i _ (hmem j) _).2 rfl)
    calc Φ₁D = ∑ j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Dγ (c j • f j)) (φ j) :=
          funext fun x => (hpt x).trans (Finset.sum_apply x _ _).symm
      _ = ∑ j, (l.map fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Ds i (c j • f j)) (φ j)).sum := by
          simp only [hadd, pure_listSum]
      _ = (l.map fun i => ∑ j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Ds i (c j • f j)) (φ j)).sum :=
          sum_listSum l (fun j i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Ds i (c j • f j)) (φ j))
end GlobalTheory.LineDerivSplit
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
theorem _root_.GlobalTheory.T.line_derivative_splits : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n d : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' →
    ∀ {ι : Type} (l : List ι) (γs : ι → (Multiplicative ℝ →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J)),
    (∀ i, γs i ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ X) → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ X, (∀ t, γ t = (l.map fun i => γs i t).prod) →
    ∀ ΦD ∈ GlobalTheory.SquareAgree.algD M B.ψ B.emb, ∀ Φ₁D : (Fin n × Fin d → AF F) → ℂ,
    (∀ x, HasDerivAt (fun t : ℝ => om (γ (Multiplicative.ofAdd t), 1) ΦD x) (Φ₁D x) 0) →
    ∃ Ψ : ι → ((Fin n × Fin d → AF F) → ℂ), (∀ i, Ψ i ∈ GlobalTheory.SquareAgree.algD M B.ψ B.emb) ∧
      (∀ i, ∀ u, HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (M.co.rho B.ψ u (om (γs i (Multiplicative.ofAdd t), 1) ΦD)))
        (GlobalTheory.WeilM.thetaSum F (M.co.rho B.ψ u (Ψ i))) 0) ∧ Φ₁D = (l.map Ψ).sum := by
  first | exact @_root_.GlobalTheory.LineDerivSplit.line_derivative_split_eq_sum | exact _root_.GlobalTheory.LineDerivSplit.line_derivative_split_eq_sum | (intros; apply _root_.GlobalTheory.LineDerivSplit.line_derivative_split_eq_sum <;> assumption)
end
end

