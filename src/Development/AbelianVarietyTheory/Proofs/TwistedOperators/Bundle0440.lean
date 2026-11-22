import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0405
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0418
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0427
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0426
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0429
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0105
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0163
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0109
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0289
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0147
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1051
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1533

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilGeneratorQuadraticOneParameterAtPlace
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped Classical

namespace GlobalTheory.ArchRec.Gen

theorem xOp_dOp {ι : Type} [Fintype ι] [DecidableEq ι] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
    (ρ : (ι → ℂ) → B →L[ℂ] B) (H : Matrix ι ι ℂ) (k l : ι) {f : B} (hd : ∀ v, GlobalTheory.RealWeil.Sm ρ (dH ρ v f)) :
    xOp ρ k (dOp ρ H l f) = ∑ b : Bool × Bool,
      (-(1 / (4 * Real.pi)) * (if b.1 then -Complex.I else 1) * (if b.2 then Complex.I else 1) : ℂ) •
        dH ρ ((if b.1 then Complex.I else 1) • Pi.single k 1)
          (dH ρ ((if b.2 then Complex.I else 1) • H⁻¹ *ᵥ Pi.single l 1) f) := by
  have hs : ∀ (a : ℂ) v, GlobalTheory.RealWeil.Sm ρ (a • dH ρ v f) := fun a v => (smS ρ).smul_mem a (hd v)
  have ha : ∀ (a : ℂ) u v, GlobalTheory.RealWeil.Sm ρ (dH ρ u f + a • dH ρ v f) := fun a u v => (smS ρ).add_mem (hd u) (hs a v)
  simp only [xOp, dOp, dH_smul _ _ (ha _ _ _), dH_add _ (hd _) (hs _ _), dH_smul _ _ (hd _), Fintype.sum_prod_type,
    Fintype.sum_bool, if_true, Bool.false_eq_true, if_false, one_smul]
  module

variable {D : D7} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ Formalism.L2.Theta.AE D} {ψ : AddChar (AF D.host.F) ℂ}
  {S T : HSp D}

theorem coe_dH_at (h : GlobalTheory.FockCompare.Chart θ σ) (hψ : IsStdChar D ψ (-1)) (F : BB ψ S T)
    (hF : IsThetaFunO ψ S T F.1) (τ : D.what₂.Tau) (v : GlobalTheory.RealWeil.Ix S T → ℂ) (hv : ∀ k, k.2 ≠ τ → v k = 0) :
    ((dH (rhoV hψ σ S T) v F).1 : WO S T → ℂ) = Datum.dRho (heisO ψ S T) θ τ (cpt v τ) F.1 := by
  have e : v = vecL (Pi.single τ (cpt v τ) : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ) := by
    funext ⟨⟨a, a'⟩, t⟩
    change _ = (Pi.single τ (cpt v τ) : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ) t a a'
    by_cases ht : t = τ
    · subst ht
      rw [Pi.single_eq_same]
      rfl
    · rw [Pi.single_eq_of_ne ht]
      exact hv _ ht
  rw [← GlobalTheory.DefLift.Gen.coe_dH h hψ F hF, ← e]

open scoped ComplexOrder in

theorem HM_inv_apply (k l : GlobalTheory.RealWeil.Ix S T) (hkl : k.2 ≠ l.2) : (HM S T)⁻¹ k l = 0 := by
  have : HM S T * blk (fun τ => ((2 * (tauE D τ D.host.xi0).im : ℝ) : ℂ)⁻¹ • (gramAt D T τ)⁻¹) (gramAt D S) = 1 := by
    unfold HM
    rw [blk_mul, ← blk_one]
    congr 1 <;> funext τ
    · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ (two_im_pos τ).ne', one_smul,
        mul_nonsing_inv _ (GlobalTheory.SmoothForms.RealPts.gramAt_unit T τ)]
    · rw [mul_nonsing_inv _ (GlobalTheory.SmoothForms.RealPts.gramAt_unit S τ)]
  rw [inv_eq_right_inv this, WeylAction.blk_apply, if_neg hkl]

theorem nOp_at (h : GlobalTheory.FockCompare.Chart θ σ) (hψ : IsStdChar D ψ (-1)) (τ : D.what₂.Tau)
    (X : Matrix (GlobalTheory.RealWeil.Ix S T) (GlobalTheory.RealWeil.Ix S T) ℂ) (hX : ∀ k l, k.2 ≠ τ ∨ l.2 ≠ τ → X k l = 0) :
    ∃ (n : ℕ) (c : Fin n → ℂ) (z z' : Fin n → Matrix (Fin T.rank) (Fin S.rank) ℂ), ∀ F : BB ψ S T,
      IsThetaFunO ψ S T F.1 → ((nOp (rhoV hψ σ S T) (HM S T) X F).1 : WO S T → ℂ) =
        ∑ i, c i • Datum.dRho (heisO ψ S T) θ τ (z i) (Datum.dRho (heisO ψ S T) θ τ (z' i) F.1) := by
  let e := (Fintype.equivFin (GlobalTheory.RealWeil.Ix S T × GlobalTheory.RealWeil.Ix S T × Bool × Bool)).symm
  let c : GlobalTheory.RealWeil.Ix S T × GlobalTheory.RealWeil.Ix S T × Bool × Bool → ℂ := fun a => X a.1 a.2.1 *
    (-(1 / (4 * Real.pi)) * (if a.2.2.1 then -Complex.I else 1) * (if a.2.2.2 then Complex.I else 1))
  let u : GlobalTheory.RealWeil.Ix S T × GlobalTheory.RealWeil.Ix S T × Bool × Bool → GlobalTheory.RealWeil.Ix S T → ℂ := fun a =>
    (if a.2.2.1 then Complex.I else 1) • Pi.single a.1 1
  let u' : GlobalTheory.RealWeil.Ix S T × GlobalTheory.RealWeil.Ix S T × Bool × Bool → GlobalTheory.RealWeil.Ix S T → ℂ := fun a =>
    (if a.2.2.2 then Complex.I else 1) • (HM S T)⁻¹ *ᵥ Pi.single a.2.1 1
  refine ⟨_, c ∘ e, fun i => cpt (u (e i)) τ, fun i => cpt (u' (e i)) τ, fun F hF => ?_⟩
  have th := GlobalTheory.DefLift.Gen.theta_dH h hψ F hF
  have e1 : nOp (rhoV hψ σ S T) (HM S T) X F =
      ∑ a, c a • dH (rhoV hψ σ S T) (u a) (dH (rhoV hψ σ S T) (u' a) F) := by
    rw [nOp, Fintype.sum_prod_type (f := fun a => c a • dH (rhoV hψ σ S T) (u a) (dH (rhoV hψ σ S T) (u' a) F))]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Fintype.sum_prod_type (f := fun a => c (k, a) • dH (rhoV hψ σ S T) (u (k, a))
      (dH (rhoV hψ σ S T) (u' (k, a)) F))]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [xOp_dOp _ _ _ _ fun v => sm_of_theta h hψ _ (th v), Finset.smul_sum]
    exact Finset.sum_congr rfl fun b _ => smul_smul _ _ _
  let j : BB ψ S T →ₗ[ℂ] (WO S T → ℂ) := ⟨⟨fun G => G.1, fun _ _ => rfl⟩, fun _ _ => rfl⟩
  change j _ = _
  rw [e1, map_sum, ← e.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Function.comp_apply]
  beta_reduce
  generalize e i = a
  by_cases ha : a.1.2 ≠ τ ∨ a.2.1.2 ≠ τ
  · have : c a = 0 := by simp only [c, hX _ _ ha, zero_mul]
    rw [this, zero_smul, zero_smul]
  · push Not at ha
    have h1 : ∀ k, k.2 ≠ τ → u a k = 0 := fun k hk => by
      have : k ≠ a.1 := fun e => hk (e ▸ ha.1)
      simp only [u, Pi.smul_apply, Pi.single_eq_of_ne this, smul_zero]
    have h2 : ∀ k, k.2 ≠ τ → u' a k = 0 := fun k hk => by
      simp only [u', Pi.smul_apply, mulVec_single_one, col_apply, HM_inv_apply k a.2.1 (ha.2 ▸ hk), smul_zero]
    rw [← coe_dH_at h hψ F hF τ _ h2, ← coe_dH_at h hψ _ (th _) τ _ h1]
    rfl

variable {χS χT : (AE D)ˣ →* Circle} {ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem quadGen_of_supp (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ S T χS χT ω) (τ : D.what₂.Tau)
    (γ : ℝ → GA D S × GA D T) (h1 : Continuous γ) (h2 : ∀ s t, γ (s + t) = γ s * γ t)
    (h3 : ∀ t, (γ t).1 ∈ GinfC S ∧ (γ t).2 ∈ GinfC T) (X : Matrix (GlobalTheory.RealWeil.Ix S T) (GlobalTheory.RealWeil.Ix S T) ℂ)
    (h4 : ∀ k l, HasDerivAt (fun t => mM θ S T (γ t) k l) (X k l) 0) (hX : ∀ k l, k.2 ≠ τ ∨ l.2 ≠ τ → X k l = 0) :
    QuadGen ψ θ τ ω γ := by
  have hψ := hω.std
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hW := GlobalTheory.Ker.isWeak_of_datum hω
  obtain ⟨lam, hl⟩ := GenZero.exists_generator D θ σ h ψ hψ S T ω hW hω.om_cont γ h1 h2 h3 X h4
  obtain ⟨lam', hl'⟩ := GlobalTheory.Mem.LiftGen.hasDerivAt_om D θ σ h ψ hψ S T ω hW hω.om_cont γ h1 h2 h3 X h4
  obtain ⟨n, c, z, z', hq⟩ := nOp_at h hψ τ X hX
  refine ⟨n, c, z, z', lam, fun f hf => ?_⟩
  obtain ⟨F, rfl⟩ : ∃ F : BB ψ S T, (F.1 : WO S T → ℂ) = f := ⟨toB hψ f hf, coe_toB hψ f hf⟩
  obtain ⟨u, hu, hud⟩ := hl F hf
  rw [← hq F hf, GlobalTheory.DefLift.Gen.coe_add_smul]
  have hl2 := hl' F hf
  generalize nOp (rhoV hψ σ S T) (HM S T) X F + lam • F = G at hud ⊢
  generalize nOp (rhoV hψ σ S T) (HM S T) X F + lam' • F = G' at hl2
  have e : (G.1 : WO S T → ℂ) = G'.1 := funext fun w => by
    have a1 := ((ev _ _ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hud
    have a2 := hl2 1 w
    simp only [one_mul, map_one, Module.End.one_apply] at a2
    refine HasDerivAt.unique ?_ a2
    exact a1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => (congrFun (hu t) w).symm)
  refine ⟨fun g w => by rw [e]; exact hl2 g w, fun μ 𝓕 hμ h𝓕 E hE => ?_⟩
  obtain ⟨E, rfl⟩ : ∃ F : BB ψ S T, (F.1 : WO S T → ℂ) = E := ⟨toB hψ E hE, coe_toB hψ E hE⟩
  obtain ⟨i1, i2, i3, -⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have i6 : BorelSpace (WO S T) := ⟨rfl⟩
  have : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 (GlobalTheory.Size.measure_dom hμ h𝓕).2
  let Φ : BB ψ S T →L[ℂ] ℂ := (innerSL ℂ (toL2 _ _ (μ.restrict 𝓕) E)).comp (toL2 _ _ (μ.restrict 𝓕))
  have hΦ : ∀ A : BB ψ S T, ipTh μ 𝓕 A.1 E.1 = Φ A := fun A =>
    (BoundedContinuousFunction.inner_toLp (μ.restrict 𝓕) E.1 A.1).symm
  simp only [← hu, hΦ]
  exact (Φ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hud

theorem quadGen_oneP : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (τ : D.what₂.Tau), IsInfFam θ → IsWeilDatumO ψ S T χS χT ω → (∀ X ∈ lieAt S τ, QuadGen ψ θ τ ω fun t => (oneP θ S τ X t, 1)) ∧ ∀ Y ∈ lieAt T τ, QuadGen ψ θ τ ω fun t => (1, oneP θ T τ Y t) := by
  intro D ψ θ S T χS χT ω τ hθ hω
  have supp : ∀ (b : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
      (a : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ), (∀ t, t ≠ τ → b t = 0 ∨ a t = 0) →
      ∀ k l : GlobalTheory.RealWeil.Ix S T, k.2 ≠ τ ∨ l.2 ≠ τ → blk b a k l = 0 := by
    intro b a hab k l hkl
    rw [WeylAction.blk_apply]
    split_ifs with e
    · rcases hab k.2 (hkl.elim id fun h => e ▸ h) with h | h <;> simp [h]
    · rfl
  refine ⟨fun X hX => ?_, fun Y hY => ?_⟩
  · refine quadGen_of_supp hθ hω τ _ ((continuous_oneP hθ hX).prodMk continuous_const)
      (fun s t => by rw [oneP_add hθ hX, Prod.mk_mul_mk, one_mul])
      (fun t => ⟨(isAtTau_oneP hθ hX t).1, one_mem _⟩) (blk (fun _ => 1) (Pi.single τ (-X))) (fun k l => ?_)
      (supp _ _ fun t ht => Or.inr (Pi.single_eq_of_ne ht _))
    simp only [mM_apply, WeylAction.oneP_inv hθ hX, GlobalTheory.WeilVacMove.mt_one, GlobalTheory.WeilVacMove.compAt_one,
      WeylAction.blk_apply]
    split_ifs
    · exact (WeylAction.hasDerivAt_comp hθ (WeylAction.neg_mem_lieAt hX) _ _ _).const_mul _
    · exact hasDerivAt_const _ _
  · refine quadGen_of_supp hθ hω τ _ (continuous_const.prodMk (continuous_oneP hθ hY))
      (fun s t => by rw [oneP_add hθ hY, Prod.mk_mul_mk, one_mul])
      (fun t => ⟨one_mem _, (isAtTau_oneP hθ hY t).1⟩) (blk (Pi.single τ Y) fun _ => 1) (fun k l => ?_)
      (supp _ _ fun t ht => Or.inl (Pi.single_eq_of_ne ht _))
    simp only [mM_apply, inv_one, GlobalTheory.WeilVacMove.mt_one, GlobalTheory.WeilVacMove.compAt_one, WeylAction.blk_apply]
    split_ifs
    · exact (WeylAction.hasDerivAt_comp hθ hY _ _ _).mul_const _
    · exact hasDerivAt_const _ _

end GlobalTheory.ArchRec.Gen

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilKernelFunctionalSuperpositionIsTame
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.KerTame

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}

theorem om_heis_apply (hom : IsWeilDatumO ψ S T χS χT om) (p : GA D S × GA D T) (u : WO S T) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (x : WO S T) :
    om p (heisO ψ S T u f) x = ψ (symplOH S T x (actO S T p.1 p.2 u)) * om p f (x + actO S T p.1 p.2 u) := by
  obtain ⟨g, h⟩ := p
  rw [hom.om_heis g h u f hf]; rfl

theorem om_heis_bound (hom : IsWeilDatumO ψ S T χS χT om) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    ∃ (C : ℝ) (A : ℕ), ∀ g h u x, ‖om (g, h) (heisO ψ S T u f) x‖ ≤ C * (quotHeight S g * quotHeight T h) ^ A := by
  obtain ⟨C, A, hC⟩ := GlobalTheory.T.weilRepresentation_thetaFunction_sup_le_quotientHeight D ψ S T χS χT om hom f hf
  refine ⟨C, A, fun g h u x => ?_⟩
  rw [om_heis_apply hom (g, h) u hf x, norm_mul, hom.std.1.2.1, one_mul]
  exact hC g h _

theorem continuous_actO_gen {X : Type} [TopologicalSpace X] {g : X → GA D S} {h : X → GA D T} {u : X → WO S T}
    (hg : Continuous g) (hh : Continuous h) (hu : Continuous u) : Continuous fun t => actO S T (g t) (h t) (u t) := by
  have hmt : ∀ V : HSp D, Continuous (Formalism.L2.Theta.mt V) := fun V =>
    Units.continuous_val.comp continuous_subtype_val
  have hmti : ∀ V : HSp D, Continuous fun g : GA D V => Formalism.L2.Theta.mt V g⁻¹ := fun V =>
    Units.continuous_coe_inv.comp continuous_subtype_val
  unfold actO
  exact (((hmt T).comp hh).matrix_mul hu).matrix_mul ((hmti S).comp hg)

theorem continuous_om_heis (hom : IsWeilDatumO ψ S T χS χT om) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    Continuous fun q : ((GA D S × GA D T) × WO S T) × WO S T => om q.1.1 (heisO ψ S T q.2 f) q.1.2 := by
  have hJ : Continuous fun p : (GA D S × GA D T) × WO S T => om p.1 f p.2 :=
    (@GlobalTheory.Unf.jointCont_all D) ψ S T χS χT om hom f hf
  have hA : Continuous fun q : ((GA D S × GA D T) × WO S T) × WO S T => actO S T q.1.1.1 q.1.1.2 q.2 := by
    exact continuous_actO_gen (continuous_fst.comp (continuous_fst.comp continuous_fst))
      (continuous_snd.comp (continuous_fst.comp continuous_fst)) continuous_snd
  have hB : Continuous fun q : ((GA D S × GA D T) × WO S T) × WO S T =>
      ((q.1.1, q.1.2 + actO S T q.1.1.1 q.1.1.2 q.2) : (GA D S × GA D T) × WO S T) :=
    (continuous_fst.comp continuous_fst).prodMk ((continuous_snd.comp continuous_fst).add hA)
  have hc : Continuous fun q : ((GA D S × GA D T) × WO S T) × WO S T =>
      ψ (symplOH S T q.1.2 (actO S T q.1.1.1 q.1.1.2 q.2)) * om q.1.1 f (q.1.2 + actO S T q.1.1.1 q.1.1.2 q.2) :=
    (hom.std.1.1.comp (GlobalTheory.OrientedHeis.continuous_symplOH (continuous_snd.comp continuous_fst) hA)).mul (hJ.comp hB)
  exact hc.congr fun q => (om_heis_apply hom q.1.1 q.2 hf q.1.2).symm

end GlobalTheory.KerTame

namespace GlobalTheory.KerTame

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}

theorem om_superpos (hom : IsWeilDatumO ψ S T χS χT om) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (p : GA D S × GA D T) (m' : Measure (WO S T)) [SFinite m'] (α : WO S T → ℂ) (hα : Integrable α m')
    (hI : IsThetaFunO ψ S T (fun x => ∫ u, α u * heisO ψ S T u f x ∂m')) (x : WO S T) :
    om p (fun x => ∫ u, α u * heisO ψ S T u f x ∂m') x = ∫ u, α u * om p (heisO ψ S T u f) x ∂m' := by
  obtain ⟨-, -, i3, -, -, -⟩ := GlobalTheory.MixModel.lattice_Mx D T.rank S.rank
  haveI : SecondCountableTopology (WO S T) := i3
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  have hφ : AEMeasurable (fun u : WO S T => (u, α u)) m' := measurable_id.aemeasurable.prodMk hα.aemeasurable
  set ν : Measure (WO S T × ℂ) := m'.map (fun u => (u, α u)) with hν
  obtain ⟨C1, hC1⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hom.std f hf
  obtain ⟨C2, hC2⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hom.std _ (hom.om_pres p f hf)
  set F : WO S T × ℂ → WO S T → ℂ := fun z => z.2 • heisO ψ S T z.1 f with hF
  have hFth : ∀ z, IsThetaFunO ψ S T (F z) := fun z =>
    GlobalTheory.WeilVacMove.isTheta_smul _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hom.std hf z.1)
  have hc1 : Continuous (Function.uncurry F) := by
    have e : Function.uncurry F = fun q : (WO S T × ℂ) × WO S T => q.1.2 * (ψ (symplOH S T q.2 q.1.1) * f (q.2 + q.1.1)) := by
      funext q; rfl
    rw [e]
    exact (continuous_snd.comp continuous_fst).mul ((hom.std.1.1.comp (GlobalTheory.OrientedHeis.continuous_symplOH continuous_snd
      (continuous_fst.comp continuous_fst))).mul (hf.cont.comp (continuous_snd.add (continuous_fst.comp continuous_fst))))
  have hc2 : Continuous fun q : (WO S T × ℂ) × WO S T => om p (F q.1) q.2 := by
    have e : (fun q : (WO S T × ℂ) × WO S T => om p (F q.1) q.2) =
        fun q => q.1.2 * om p (heisO ψ S T q.1.1 f) q.2 := by
      funext q; simp only [hF, map_smul, Pi.smul_apply, smul_eq_mul]
    rw [e]
    exact (continuous_snd.comp continuous_fst).mul ((continuous_om_heis hom hf).comp
      ((continuous_const.prodMk continuous_snd).prodMk (continuous_fst.comp continuous_fst)))
  have hβ : Integrable (fun z : WO S T × ℂ => ‖z.2‖ * max C1 C2) ν := by
    have hm : Continuous fun z : WO S T × ℂ => ‖z.2‖ * max C1 C2 := (continuous_norm.comp continuous_snd).mul continuous_const
    rw [hν, integrable_map_measure hm.measurable.aestronglyMeasurable hφ]
    exact hα.norm.mul_const _
  have hdom : ∀ z y, ‖F z y‖ ≤ ‖z.2‖ * max C1 C2 ∧ ‖om p (F z) y‖ ≤ ‖z.2‖ * max C1 C2 := by
    intro z y
    constructor
    · show ‖z.2 * (ψ (symplOH S T y z.1) * f (y + z.1))‖ ≤ _
      rw [norm_mul, norm_mul, hom.std.1.2.1, one_mul]
      exact mul_le_mul_of_nonneg_left ((hC1 _).trans (le_max_left _ _)) (norm_nonneg _)
    · simp only [hF, map_smul, Pi.smul_apply, smul_eq_mul]
      obtain ⟨g, h⟩ := p
      rw [norm_mul, om_heis_apply hom (g, h) z.1 hf y, norm_mul, hom.std.1.2.1, one_mul]
      exact mul_le_mul_of_nonneg_left ((hC2 _).trans (le_max_right _ _)) (norm_nonneg _)
  have hint : ∀ y, ∫ z, F z y ∂ν = ∫ u, α u * heisO ψ S T u f y ∂m' := by
    intro y
    rw [hν, integral_map hφ]
    · rfl
    · exact (hc1.comp (continuous_id.prodMk continuous_const)).measurable.aestronglyMeasurable
  have hint2 : ∫ z, om p (F z) x ∂ν = ∫ u, α u * om p (heisO ψ S T u f) x ∂m' := by
    rw [hν, integral_map hφ]
    · simp only [hF, map_smul, Pi.smul_apply, smul_eq_mul]
    · exact (hc2.comp (continuous_id.prodMk continuous_const)).measurable.aestronglyMeasurable
  have hI' : IsThetaFunO ψ S T (fun y => ∫ z, F z y ∂ν) := by
    simp only [hint]; exact hI
  have key := GlobalTheory.CommIntBdd.om_integral_comm_dom D ψ S T χS χT om hom (WO S T × ℂ) ν F p
    (fun z => ‖z.2‖ * max C1 C2) hFth hc1 hc2 hβ hdom hI' x
  have e : (fun w' => ∫ z, F z w' ∂ν) = fun y => ∫ u, α u * heisO ψ S T u f y ∂m' := funext hint
  rw [← hint2, ← key, e]

end GlobalTheory.KerTame

namespace GlobalTheory.KerTame

theorem kernel_tame : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T),
    IsWeilDatumO ψ S T χS χT om → ∀ (Y : Type) [TopologicalSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y]
    [BorelSpace Y] (m : Measure Y) [SFinite m] (c : Y → ℂ) (g : Y → GA D S) (h : Y → GA D T) (w : Y → WO S T),
    Measurable c → Continuous g → Continuous h → Continuous w →
    (∀ k : ℕ, Integrable (fun y => ‖c y‖ * (quotHeight S (g y) * quotHeight T (h y)) ^ k) m) →
    (∀ f, IsThetaFunO ψ S T f → Integrable (fun y => c y * om (g y, h y) f (w y)) m) ∧
      Tame ψ S T fun f => ∫ y, c y * om (g y, h y) f (w y) ∂m := by
  intro D ψ S T χS χT om hom Y _ _ _ _ m _ c g h w hc hg hh hw hint
  obtain ⟨-, -, i3, -, -, -⟩ := GlobalTheory.MixModel.lattice_Mx D T.rank S.rank
  haveI : SecondCountableTopology (WO S T) := i3
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : FirstCountableTopology (WO S T) := @TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _ _ i3
  have hgh : Continuous fun y => ((g y, h y) : GA D S × GA D T) := hg.prodMk hh

  have hK : ∀ f, IsThetaFunO ψ S T f →
      Continuous fun q : Y × WO S T => om (g q.1, h q.1) (heisO ψ S T q.2 f) (w q.1) := fun f hf =>
    (continuous_om_heis hom hf).comp (((hgh.comp continuous_fst).prodMk (hw.comp continuous_fst)).prodMk continuous_snd)
  have hbd : ∀ f, IsThetaFunO ψ S T f → ∃ (C : ℝ) (A : ℕ), ∀ y u,
      ‖c y * om (g y, h y) (heisO ψ S T u f) (w y)‖ ≤ C * (‖c y‖ * (quotHeight S (g y) * quotHeight T (h y)) ^ A) := by
    intro f hf
    obtain ⟨C, A, hC⟩ := om_heis_bound hom hf
    refine ⟨C, A, fun y u => ?_⟩
    rw [norm_mul]
    calc ‖c y‖ * ‖om (g y, h y) (heisO ψ S T u f) (w y)‖
        ≤ ‖c y‖ * (C * (quotHeight S (g y) * quotHeight T (h y)) ^ A) :=
          mul_le_mul_of_nonneg_left (hC _ _ _ _) (norm_nonneg _)
      _ = C * (‖c y‖ * (quotHeight S (g y) * quotHeight T (h y)) ^ A) := by ring
  have hintH : ∀ f, IsThetaFunO ψ S T f → ∀ u,
      Integrable (fun y => c y * om (g y, h y) (heisO ψ S T u f) (w y)) m := by
    intro f hf u
    obtain ⟨C, A, hC⟩ := hbd f hf
    exact Integrable.mono' ((hint A).const_mul C)
      (hc.aestronglyMeasurable.mul ((hK f hf).comp (continuous_id.prodMk continuous_const)).measurable.aestronglyMeasurable)
      (ae_of_all _ fun y => hC y u)
  have hzero : ∀ f : WO S T → ℂ, heisO ψ S T 0 f = f := by
    intro f; funext x; simp [heisO, symplOH, symplO, hO]
  have hintK : ∀ f, IsThetaFunO ψ S T f → Integrable (fun y => c y * om (g y, h y) f (w y)) m := by
    intro f hf
    simpa only [hzero] using hintH f hf 0
  refine ⟨hintK, ?_, ?_, ?_, ?_, ?_⟩
  · intro f f' hf hf'
    simp only [map_add, Pi.add_apply, mul_add]
    exact integral_add (hintK f hf) (hintK f' hf')
  · intro a f hf
    simp only [map_smul, Pi.smul_apply, smul_eq_mul]
    rw [← integral_const_mul]
    congr 1
    funext y
    ring
  · intro f hf
    obtain ⟨C, A, hC⟩ := hbd f hf
    refine continuous_of_dominated (bound := fun y => C * (‖c y‖ * (quotHeight S (g y) * quotHeight T (h y)) ^ A))
      (fun u => (hintH f hf u).aestronglyMeasurable) (fun u => ae_of_all _ fun y => hC y u) ((hint A).const_mul C)
      (ae_of_all _ fun y => ?_)
    exact continuous_const.mul ((hK f hf).comp (continuous_const.prodMk continuous_id))
  · intro f hf
    obtain ⟨C, A, hC⟩ := hbd f hf
    exact ⟨∫ y, C * (‖c y‖ * (quotHeight S (g y) * quotHeight T (h y)) ^ A) ∂m, fun u =>
      norm_integral_le_of_norm_le ((hint A).const_mul C) (ae_of_all _ fun y => hC y u)⟩
  · intro f hf m' _ α hα hI
    have e1 : ∀ y, om (g y, h y) (fun x => ∫ u, α u * heisO ψ S T u f x ∂m') (w y) =
        ∫ u, α u * om (g y, h y) (heisO ψ S T u f) (w y) ∂m' := fun y =>
      om_superpos hom hf (g y, h y) m' α hα hI (w y)
    simp only [e1]
    simp only [← integral_const_mul]
    rw [integral_integral_swap]
    · refine integral_congr_ae (ae_of_all _ fun u => ?_)
      refine integral_congr_ae (ae_of_all _ fun y => ?_)
      simp only
      ring
    · obtain ⟨C, A, hC⟩ := hbd f hf
      refine Integrable.mono' (((hint A).const_mul C).mul_prod hα.norm) ?_ (ae_of_all _ fun q => ?_)
      · exact (hc.aestronglyMeasurable.comp_fst).mul (hα.aestronglyMeasurable.comp_snd.mul
          (hK f hf).measurable.aestronglyMeasurable)
      · calc ‖c q.1 * (α q.2 * om (g q.1, h q.1) (heisO ψ S T q.2 f) (w q.1))‖
            = ‖c q.1 * om (g q.1, h q.1) (heisO ψ S T q.2 f) (w q.1)‖ * ‖α q.2‖ := by
              simp only [norm_mul]; ring
          _ ≤ C * (‖c q.1‖ * (quotHeight S (g q.1) * quotHeight T (h q.1)) ^ A) * ‖α q.2‖ :=
              mul_le_mul_of_nonneg_right (hC _ _) (norm_nonneg _)

end GlobalTheory.KerTame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilOperatorLatticeStabiliserFixesVacuumNonsplit
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VecInvInert

variable {D : D7} {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
  {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F}

theorem idem_smul_eq (hε : IsPlaceIdem D v ε) {u : WO S T} (hu : u ∈ latO S T LS LT fun w => w = v) :
    algebraMap (AF D.host.F) (AE D) ε • u = u := by
  obtain ⟨β, rfl, h1, h0⟩ := hε
  have hβα : ∀ α : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F, (∀ w, ¬ w = v → evalV D.host.F w α = 0) → β * α = α := by
    intro α hα
    apply RestrictedProduct.ext
    intro w
    show β w * α w = α w
    by_cases hw : w = v
    · subst hw
      have : β w = 1 := h1
      rw [this, one_mul]
    · have : α w = 0 := hα w hw
      rw [this, mul_zero]
  unfold latO at hu
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
      obtain ⟨α, -, hα, a, -, s, -, t, -, rfl⟩ := hw
      funext i j
      show algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β) * _ = _
      rw [Algebra.TensorProduct.algebraMap_apply]
      simp only [Matrix.of_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      congr 1
      show ((0 * 0, β * α) : AF D.host.F) = (0, α)
      rw [mul_zero, hβα α hα]
  | zero => exact smul_zero _
  | add x y _ _ hx hy => rw [smul_add, hx, hy]
  | neg x _ hx => rw [smul_neg, hx]

theorem mem_place_iff (hε : IsPlaceIdem D v ε) (u : WO S T) :
    u ∈ (latO S T LS LT fun w => w = v) ↔
      u ∈ (latO S T LS LT fun _ => True) ∧ algebraMap (AF D.host.F) (AE D) ε • u = u := by
  constructor
  · intro hu
    exact ⟨GlobalTheory.PlaceModel.latO_le_top _ hu, idem_smul_eq hε hu⟩
  · rintro ⟨hu, he⟩
    have := GlobalTheory.PlaceModel.placeIdem_smul_mem hε hu
    rwa [he] at this

theorem act_injective (g : GA D S) (h : GA D T) : Function.Injective (actO S T g h) := by
  intro x y hxy
  unfold actO at hxy
  have hT : Formalism.L2.Theta.mt T h⁻¹ * Formalism.L2.Theta.mt T h = 1 := by
    rw [← GlobalTheory.AdelicLatMove.mt_mul, inv_mul_cancel, GlobalTheory.AdelicLatMove.mt_one]
  have hS : Formalism.L2.Theta.mt S g⁻¹ * Formalism.L2.Theta.mt S g = 1 := by
    rw [← GlobalTheory.AdelicLatMove.mt_mul, inv_mul_cancel, GlobalTheory.AdelicLatMove.mt_one]
  calc x = (Formalism.L2.Theta.mt T h⁻¹ * Formalism.L2.Theta.mt T h) * x * (Formalism.L2.Theta.mt S g⁻¹ * Formalism.L2.Theta.mt S g) := by
        rw [hT, hS, Matrix.one_mul, Matrix.mul_one]
    _ = Formalism.L2.Theta.mt T h⁻¹ * (Formalism.L2.Theta.mt T h * x * Formalism.L2.Theta.mt S g⁻¹) * Formalism.L2.Theta.mt S g := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.L2.Theta.mt T h⁻¹ * (Formalism.L2.Theta.mt T h * y * Formalism.L2.Theta.mt S g⁻¹) * Formalism.L2.Theta.mt S g := by
        rw [hxy]
    _ = (Formalism.L2.Theta.mt T h⁻¹ * Formalism.L2.Theta.mt T h) * y * (Formalism.L2.Theta.mt S g⁻¹ * Formalism.L2.Theta.mt S g) := by
        simp only [Matrix.mul_assoc]
    _ = y := by
        rw [hT, hS, Matrix.one_mul, Matrix.mul_one]

theorem om_fixes_vacuum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsSelfDualC S ΛS → IsSelfDualC T ΛT → (∃ η, IsEtaTilde D η) → ∀ v ε, NonSplitAt D v ε → UnramAt ε χS → UnramAt ε χT → ∀ g h, SuppPl ε S g → SuppPl ε T h → (∀ u, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ↔ actO S T g h u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) → ∀ f, IsThetaFunO ψ S T f → IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f → om (g, h) f = f := by
  intro D ψ S T ΛS ΛT χS χT om hW hS hT hη v ε hns hχS hχT g h hg hh hlat f hf hvac
  have hε : IsPlaceIdem D v ε := hns.1
  have key := GlobalTheory.T.weilDatum_fixes_vacuum_nonSplitPlace_unramified D ψ hW.std S T ΛS ΛT hS hT χS χT om hη hW v ε hns hχS hχT
  have hc : ∀ (c : AE D) (x : WO S T), actO S T g h (c • x) = c • actO S T g h x := by
    intro c x
    unfold actO
    rw [Matrix.mul_smul, Matrix.smul_mul]
  refine key g h hg hh ?_ f hf ?_
  · intro u
    rw [mem_place_iff hε, mem_place_iff hε]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(hlat u).1 h1, by rw [← hc, h2]⟩
    · rintro ⟨h1, h2⟩
      refine ⟨(hlat u).2 h1, ?_⟩
      apply act_injective g h
      rw [hc]
      exact h2
  · intro u hu
    obtain ⟨a, ha, h2a⟩ := GlobalTheory.FinWeilO.exists_half_of_nonSplit hns
    have hu' := (mem_place_iff hε u).1 hu
    have hau := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a ha u hu'.1
    have e2 : 2 • (a • u) = u := by
      rw [two_nsmul, ← add_smul, ← two_mul, h2a]
      exact hu'.2
    have := hvac.1 (a • u) hau
    rwa [e2] at this

end GlobalTheory.VecInvInert

end
end

