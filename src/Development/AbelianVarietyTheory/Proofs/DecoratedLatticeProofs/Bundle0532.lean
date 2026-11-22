import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0289
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0483
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0179
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0190
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastTwoStepsDoubleLiftPeriodValue
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0234
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiThetaOfVac
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0138
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0523
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0390
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0275
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0270
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0437
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteAdeleIdempotentOfFMulSelf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0347
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0342
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0412
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0514
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0492
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0525
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0262
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0524
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0034
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0471
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0356
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0399
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0477
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0106
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0223
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0232
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0223
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0406
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0453
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0527
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0414

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleThetaLiftValueInvariantMiddleGL
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TriStep.GlMid

variable {D : D7}

theorem comb_right_comm (ψ : AddChar (AF D.host.F) ℂ) {A S A' : HSp D} (L : Module.End ℂ (WO A S → ℂ))
    (K : WO A S → WO S A' → ℂ) (c : WO S A' →₀ ℂ) (u : WO A S) (v : WO S A') :
    comb ψ S A' c (fun v' => L (fun u' => K u' v') u) v = L (fun u' => comb ψ S A' c (K u') v) u := by
  have e : (fun u' => comb ψ S A' c (K u') v) =
      ∑ t ∈ c.support, (c t * ψ (symplOH S A' v t)) • (fun u' => K u' (v + t)) := by
    funext u'
    simp only [comb, heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun t _ => by ring
  rw [e, map_sum]
  simp only [comb, heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_smul]
  exact Finset.sum_congr rfl fun t _ => by ring

theorem comb_left_comm (ψ : AddChar (AF D.host.F) ℂ) {A S A' : HSp D} (L : Module.End ℂ (WO S A' → ℂ))
    (K : WO A S → WO S A' → ℂ) (c : WO A S →₀ ℂ) (u : WO A S) (v : WO S A') :
    comb ψ A S c (fun u' => L (K u') v) u = L (fun v' => comb ψ A S c (fun u' => K u' v') u) v := by
  have e : (fun v' => comb ψ A S c (fun u' => K u' v') u) =
      ∑ t ∈ c.support, (c t * ψ (symplOH A S u t)) • (fun v' => K (u + t) v') := by
    funext v'
    simp only [comb, heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun t _ => by ring
  rw [e, map_sum]
  simp only [comb, heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_smul]
  exact Finset.sum_congr rfl fun t _ => by ring

theorem comb_om_comm {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {ω : Om S T}
    (h : IsWeilDatumO ψ S T χS χT ω) (g : GA D S) (g' : GA D T) (c : WO S T →₀ ℂ)
    (hc : ∀ t ∈ c.support, actO S T g g' t = t) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    comb ψ S T c (ω (g, g') f) = ω (g, g') (comb ψ S T c f) := by
  unfold comb
  rw [map_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [map_smul, h.om_heis g g' t f hf, hc t ht]

theorem idem_mul {e : AE D} (he : IsSplitIdem D e) : (e + cA D e) * (1 - (e + cA D e)) = 0 := by
  have h1 := he.1
  have h2 := he.2.1
  have h3 : cA D e * cA D e = cA D e := by rw [← map_mul, h1]
  linear_combination -h1 - 2 * h2 - h3

theorem actO_fix_left {e : AE D} (he : IsSplitIdem D e) {S T : HSp D} {a : GA D T} (ha : SuppAt e T a) {t : WO S T}
    (ht : IsHalf (1 - (e + cA D e)) t) : actO S T 1 a t = t := by
  unfold actO
  rw [inv_one, show mt S (1 : GA D S) = 1 from rfl, Matrix.mul_one]
  ext i j
  rw [Matrix.mul_apply]
  have key : ∀ k, mt T a i k * t k j = (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) i k * t k j := fun k => by
    have ha' := ha i k
    rw [Matrix.sub_apply] at ha'
    have ht' := ht k j
    linear_combination (-(t k j)) * ha' +
      (-((e + cA D e) * (mt T a i k - (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) i k))) * ht' +
      ((mt T a i k - (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) i k) * t k j) * idem_mul he
  rw [Finset.sum_congr rfl fun k _ => key k, ← Matrix.mul_apply, Matrix.one_mul]

theorem actO_fix_right {e : AE D} (he : IsSplitIdem D e) {S T : HSp D} {a : GA D S} (ha : SuppAt e S a⁻¹) {t : WO S T}
    (ht : IsHalf (1 - (e + cA D e)) t) : actO S T a 1 t = t := by
  unfold actO
  rw [show mt T (1 : GA D T) = 1 from rfl, Matrix.one_mul]
  ext i j
  rw [Matrix.mul_apply]
  have key : ∀ k, t i k * mt S a⁻¹ k j = t i k * (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) k j := fun k => by
    have ha' := ha k j
    rw [Matrix.sub_apply] at ha'
    have ht' := ht i k
    linear_combination (-(t i k)) * ha' +
      (-((e + cA D e) * (mt S a⁻¹ k j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) k j))) * ht' +
      ((mt S a⁻¹ k j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) k j) * t i k) * idem_mul he
  rw [Finset.sum_congr rfl fun k _ => key k, ← Matrix.mul_apply, Matrix.mul_one]

end GlobalTheory.TriStep.GlMid

namespace GlobalTheory.TriStep
open GlobalTheory.TriStep.GlMid

theorem valK_glMid : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ), Q.Away c₁ → Q.Away c₂ → ∀ φ, IsContAut S.B.A φ → ∀ (Λ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] (WO S.B.A S.J.W₀ → WO S.J.W₀ S.B'.A → ℂ)), (ofSplit Q.q).IsBiModel ψ Q.F.F₀ Q.F.F₁ Q.F.F₂ Λ → ∀ (g : GL Q.n₁ Q.k) (Ξ₁ Ξ₁' : SB (Matrix Q.n₁ Q.n₀ Q.k)) (Ξ₂ Ξ₂' : SB (Matrix Q.n₂ Q.n₁ Q.k)), Ξ₁'.1 = om Q.μ₁ 1 g Ξ₁.1 → Ξ₂'.1 = om Q.μ₂ g 1 Ξ₂.1 → IsBiTheta ψ S.B.A S.J.W₀ S.B'.A (biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂))) → ∀ f ∈ GlobalTheory.TriStep.space Q, GlobalTheory.TriStep.valK S Q c₁ c₂ φ Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁' Ξ₂') f = GlobalTheory.TriStep.valK S Q c₁ c₂ φ Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂) f := by
  intro D ψ hψ σ S Q c₁ c₂ hc₁ hc₂ φ hφ Λ hΛ g Ξ₁ Ξ₁' Ξ₂ Ξ₂' h₁ h₂ hC f _
  obtain ⟨a₁, ha₁⟩ := Witness.exists_isLoc (ofSplit Q.q) Q.F.F₁ g
  have hsplit : IsSplitIdem D (ofSplit Q.q).e := (ofSplit Q.q).split
  have comp₁ : (ofSplit Q.q).IsComp S.χ₁ Q.μ₁⁻¹ := fun x a hxa => by
    have e := Q.comp₁ x a hxa
    rw [MonoidHom.inv_apply, Circle.coe_inv] at e
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, e, inv_inv]
  have comp₂ : (ofSplit Q.q).IsComp S.χ₂ Q.μ₂⁻¹ := fun x a hxa => by
    have e := Q.comp₂ x a hxa
    rw [MonoidHom.inv_apply, Circle.coe_inv] at e
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, e, inv_inv]
  have hL : ∀ (X₂ : SB (Matrix Q.n₂ Q.n₁ Q.k)) (v : WO S.J.W₀ S.B'.A),
      IsThetaFunO ψ S.B.A S.J.W₀ (fun u => Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ X₂) u v) ∧
      (fun u => Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁' X₂) u v) = S.oma (1, a₁) (fun u => Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ X₂) u v) := by
    intro X₂ v
    obtain ⟨T₁, hT₁, hT⟩ := hΛ.1 X₂ v
    have e : ∀ X₁ : SB (Matrix Q.n₁ Q.n₀ Q.k), (fun u => Λ (GlobalTheory.LocFlat.CFac.prodSB X₁ X₂) u v) = T₁ X₁ :=
      fun X₁ => funext (hT X₁ _ (fun _ => rfl))
    rw [e, e]
    refine ⟨hT₁.theta Ξ₁, ?_⟩
    symm
    refine GlobalTheory.LocOm.omLoc D Q.k (ofSplit Q.q) ψ S.B.A S.J.W₀ S.χ₁ S.χ₁ S.oma S.weila Q.μ₁⁻¹ Q.μ₁⁻¹ comp₁ comp₁ Q.n₁ Q.n₀
      Q.F.F₀ Q.F.F₁ T₁ hT₁ 1 1 a₁ g (GlobalTheory.LocOm.isLoc_one_mul_inv D Q.k (ofSplit Q.q) S.B.A Q.n₀ Q.F.F₀).1 ha₁ Ξ₁ Ξ₁' ?_
    rw [h₁]
    simp
  have hR : ∀ (X₁ : SB (Matrix Q.n₁ Q.n₀ Q.k)) (u : WO S.B.A S.J.W₀),
      IsThetaFunO ψ S.J.W₀ S.B'.A (Λ (GlobalTheory.LocFlat.CFac.prodSB X₁ Ξ₂) u) ∧
      Λ (GlobalTheory.LocFlat.CFac.prodSB X₁ Ξ₂') u = S.omb (a₁, 1) (Λ (GlobalTheory.LocFlat.CFac.prodSB X₁ Ξ₂) u) := by
    intro X₁ u
    obtain ⟨T₂, hT₂, hT⟩ := hΛ.2 X₁ u
    have e : ∀ X₂ : SB (Matrix Q.n₂ Q.n₁ Q.k), Λ (GlobalTheory.LocFlat.CFac.prodSB X₁ X₂) u = T₂ X₂ :=
      fun X₂ => funext (hT X₂ _ (fun _ => rfl))
    rw [e, e]
    refine ⟨hT₂.theta Ξ₂, ?_⟩
    symm
    refine GlobalTheory.LocOm.omLoc D Q.k (ofSplit Q.q) ψ S.J.W₀ S.B'.A S.χ₂ S.χ₂ S.omb S.weilb Q.μ₂⁻¹ Q.μ₂⁻¹ comp₂ comp₂ Q.n₂ Q.n₁
      Q.F.F₁ Q.F.F₂ T₂ hT₂ a₁ g 1 1 ha₁ (GlobalTheory.LocOm.isLoc_one_mul_inv D Q.k (ofSplit Q.q) S.B'.A Q.n₂ Q.F.F₂).1 Ξ₂ Ξ₂' ?_
    rw [h₂]
    simp
  have hA : ∀ t ∈ c₁.support, actO S.B.A S.J.W₀ 1 a₁ t = t := fun t ht =>
    actO_fix_left hsplit ha₁.1 (hc₁ t ht)
  have hB : ∀ t ∈ c₂.support, actO S.J.W₀ S.B'.A a₁ 1 t = t := fun t ht =>
    actO_fix_right hsplit ((GlobalTheory.LocOm.isLoc_one_mul_inv D Q.k (ofSplit Q.q) S.J.W₀ Q.n₁ Q.F.F₁).2.2 a₁ g ha₁).1 (hc₂ t ht)

  have hY : ∀ v', IsThetaFunO ψ S.B.A S.J.W₀ (fun u => comb ψ S.J.W₀ S.B'.A c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂) u) v') := by
    intro v'
    have e : (fun u => comb ψ S.J.W₀ S.B'.A c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂) u) v') =
        ∑ t ∈ c₂.support, (c₂ t * ψ (symplOH S.J.W₀ S.B'.A v' t)) •
          (fun u => Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂) u (v' + t)) := by
      funext u
      simp only [comb, heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun t _ => by ring
    rw [e]
    exact GlobalTheory.Core.Rk.Collect.theta_sum _ _ _ fun t => (hL Ξ₂ (v' + t)).1
  have hC' : ∀ u v, biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁' Ξ₂')) u v =
      S.omb (a₁, 1) (fun v' => S.oma (1, a₁)
        (fun u' => biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂)) u' v') u) v := by
    intro u v
    have s1 : ∀ u'', comb ψ S.J.W₀ S.B'.A c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁' Ξ₂') u'') =
        S.omb (a₁, 1) (comb ψ S.J.W₀ S.B'.A c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁' Ξ₂) u'')) := fun u'' => by
      rw [(hR Ξ₁' u'').2]
      exact comb_om_comm S.weilb a₁ 1 c₂ hB (hR Ξ₁' u'').1
    have s2 : ∀ v' u'', comb ψ S.J.W₀ S.B'.A c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁' Ξ₂) u'') v' =
        S.oma (1, a₁) (fun u => comb ψ S.J.W₀ S.B'.A c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂) u) v') u'' := fun v' u'' => by
      have e : Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁' Ξ₂) u'' =
          fun w => S.oma (1, a₁) (fun u => Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂) u w) u'' :=
        funext fun w => congrFun (hL Ξ₂ w).2 u''
      rw [e]
      exact comb_right_comm ψ (S.oma (1, a₁)) (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂)) c₂ u'' v'
    unfold biComb
    simp only [s1]
    rw [comb_left_comm ψ (S.omb (a₁, 1)) (fun u'' v' => comb ψ S.J.W₀ S.B'.A c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁' Ξ₂) u'') v') c₁ u v]
    refine congrArg (fun F => S.omb (a₁, 1) F v) (funext fun v' => ?_)
    simp only [s2 v']
    rw [comb_om_comm S.weila 1 a₁ c₁ hA (hY v')]

  obtain ⟨b1, -, -, -⟩ := GlobalTheory.SeeSaw.biAct_all D ψ S.B.A S.J.W₀ S.B'.A S.χ₁ S.χ₁ S.χ₂ S.χ₂ S.oma S.omb S.weila S.weilb _ hC
  have hD := b1 (1, a₁)
  obtain ⟨-, -, d3, -⟩ := GlobalTheory.SeeSaw.biAct_all D ψ S.B.A S.J.W₀ S.B'.A S.χ₁ S.χ₁ S.χ₂ S.χ₂ S.oma S.omb S.weila S.weilb _ hD
  have integ : ∀ (h₂ : GA D S.B'.A) (h₁ : GA D S.J.W₀) (h₀ : GA D S.B.A),
      φ h₀ * S.omb (h₁, h₂) (fun v => S.oma (h₀, h₁)
        (fun u => biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁' Ξ₂')) u v) 0) 0 =
      φ h₀ * S.omb (h₁ * a₁, h₂) (fun v => S.oma (h₀, h₁ * a₁)
        (fun u => biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂)) u v) 0) 0 := by
    intro h₂ h₁ h₀
    have e1 : (fun v => S.oma (h₀, h₁)
        (fun u => biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁' Ξ₂')) u v) 0) =
        S.omb (a₁, 1) (fun v => S.oma (h₀, h₁ * a₁)
          (fun u => biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂)) u v) 0) := by
      funext v
      simp only [hC']
      rw [← d3 (h₀, h₁) (a₁, 1) 0 v]
      refine congrArg (fun F => S.omb (a₁, 1) F v) (funext fun v' => ?_)
      change S.oma (h₀, h₁) (S.oma (1, a₁)
        (fun u' => biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂)) u' v')) 0 = _
      rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
    rw [e1, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  have hinv : ∀ h₂ : GA D S.B'.A, ∀ γ ∈ GQ S.J.W₀, ∀ h₁ : GA D S.J.W₀,
      (fun h₁ => ∫ h₀ in S.B.vA.𝓕, φ h₀ * S.omb (h₁, h₂) (fun v => S.oma (h₀, h₁)
        (fun u => biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂)) u v) 0) 0 ∂S.B.vA.μ) (γ * h₁) =
      (fun h₁ => ∫ h₀ in S.B.vA.𝓕, φ h₀ * S.omb (h₁, h₂) (fun v => S.oma (h₀, h₁)
        (fun u => biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂)) u v) 0) 0 ∂S.B.vA.μ) h₁ := by
    intro h₂ γ hγ h₁
    refine congrArg (fun F : GA D S.B.A → ℂ => ∫ h₀ in S.B.vA.𝓕, F h₀ ∂S.B.vA.μ) (funext fun h₀ => ?_)
    have e1 : ∀ v, S.oma (h₀, γ * h₁)
        (fun u => biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂)) u v) 0 =
        S.oma (h₀, h₁) (fun u => biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂)) u v) 0 := fun v => by
      have := GlobalTheory.SeeSawLastValue.om_aut_mul S.weila (one_mem _) hγ h₀ h₁ (GlobalTheory.FrComb.slice_left hC v)
      rwa [one_mul] at this
    simp only [e1]
    have := GlobalTheory.SeeSawLastValue.om_aut_mul S.weilb hγ (one_mem _) h₁ h₂ (GlobalTheory.FrComb.slice_right (b1 (h₀, h₁)) 0)
    rw [one_mul] at this
    exact congrArg (φ h₀ * ·) this
  unfold valK
  congr 1
  funext h₂
  unfold biLift
  simp only [integ h₂]
  exact GlobalTheory.ChainOnto.setIntegral_fd_mul_right D S.J.W₀ S.J.v0.μ S.J.v0.𝓕 S.J.v0.haar S.J.v0.fund
    (fun h₁ => ∫ h₀ in S.B.vA.𝓕, φ h₀ * S.omb (h₁, h₂) (fun v => S.oma (h₀, h₁)
        (fun u => biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂)) u v) 0) 0 ∂S.B.vA.μ) (hinv h₂) a₁

end GlobalTheory.TriStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCentralElementHomotheticGluedCoresStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_central_element_homothetic_gluedCores : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S A L : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (n : Type) [Fintype n] [DecidableEq n] (β : GlobalTheory.FinPl.Frame p A n) (β₀ : GlobalTheory.FinPl.Frame p S (n ⊕ Fin 1)) (M M' : Lat S) (μ : D.host.E) (T : ℕ) (q : GlobalTheory.LatPair.Unif k) (P : GlobalTheory.LatPair.Pair k n) (a₀ : GA D A), 3 ≤ Fintype.card n → IsSumFrame o ζ β β₀ → IsSelfDualC S M → IsSelfDualC S M' → β₀.IsLat M (GlobalTheory.LatPair.gluedS q 1 P.ker P.vec) → μ ≠ 0 → LineAt (vecB o ζ) μ M' p.v → star ζ ⬝ᵥ L.gram *ᵥ ζ = -(μ * star μ * (T : D.host.E)) → valuation k (p.pr (incA D (T : D.host.E))) = valuation k ((q.1 : 𝒪[k]) : k) → (∀ a ∈ grpAt A (· = p.v), Moves S (o.emb (a, 1)) M M (· = p.v) ↔ Moves S (o.emb (a₀ * a * a₀⁻¹, 1)) M' M' (· = p.v)) → ∃ (a : GA D A) (c : AE D), CenAt A p.v a ∧ NormOneAt p.v c ∧ SMoves S c (o.emb (a₀ * a, 1)) M M' p.v := by
  first | exact @GlobalTheory.Core.Mi.LatMatch.CoreHomothety.exists_central_sMoves | exact GlobalTheory.Core.Mi.LatMatch.CoreHomothety.exists_central_sMoves | (intros; apply GlobalTheory.Core.Mi.LatMatch.CoreHomothety.exists_central_sMoves <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsChartPointRightTranslateStabilizerSplitPla
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.DiaChart

theorem decoratedLattice_unitScale_functional_keeps_frames {X : Formalism.L2.Col.Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y}
    (p : PtY (X := X) (n := n) ST SG Q y) (P : ST) (c : (𝓞 X.E ⧸ P.1.asIdeal)ˣ) (P' : HeightOneSpectrum (𝓞 X.E)) :
    ptFr (p.mv (Formalism.L2.Col.DecoSet.dia1 P c p.1.1.deco)).1.1 P' = ptFr p.1.1 P' := by
  by_cases h : (∀ (P₁ : Q) (x : Formalism.L2.Col.Sp X.E n), p.1.1.1.2 P₁ x ∈ (Formalism.L2.Col.DecoSet.dia1 P c p.1.1.deco).1.at P₁.1 ↔
      x ∈ Formalism.L2.Col.stdAt X.E n P₁.1) ∧ p.1.2 ∈ y.ys (Formalism.L2.Col.DecoSet.dia1 P c p.1.1.deco).1.N
  · have e : p.mv (Formalism.L2.Col.DecoSet.dia1 P c p.1.1.deco) =
        ⟨(⟨(Formalism.L2.Col.DecoSet.dia1 P c p.1.1.deco, p.1.1.1.2), h.1⟩, p.1.2), h.2⟩ := dif_pos h
    rw [e]
    unfold ptFr
    rfl
  · have e : p.mv (Formalism.L2.Col.DecoSet.dia1 P c p.1.1.deco) = p := dif_neg h
    rw [e]

theorem finM_mul' {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) (g h : GA D V) :
    finM V hn (g * h) = finM V hn g * finM V hn h := by
  subst hn
  exact GlobalTheory.AdForm.RdLaw.finM_mul V g h

theorem ptOf_gl_dia : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m) (i : ι) (v : (I.atT l u a).vT), Formalism.L2.NTheta.IsIdemAt (p i).e v.1 →
    ∀ g : 𝓀[k]ˣ → GL (Fin ((I.rec7 l Z).sp.X j).rank) k, (∀ s, g s • Q j i = s • Q j i) →
      ∀ b (c : {c // A.chOf j c = b}), ∃ e : 𝓀[k]ˣ ≃ ((I.atT l u a).Fv v)ˣ, ∀ s,
        ∃ z : TC.GA B (B.R.N j),
          z.1 = finM _ (rankN (I.rec7 l Z) j hj) (A.h j b c * (β j i).gl (g s)) ∧
          TC.PtOf (z * A.kb j b) (extTo I.SQ (((I.atIn u a).A j).diaPt v (e s) c.1).1.1) := by
  intro B X I hOk hPins l Z u a Ch A hA k _ _ _ _ ι p β Q L hStd j hj i v hv g hg b c
  obtain ⟨c, rfl⟩ := c
  obtain ⟨-, ρ, hρ⟩ := GlobalTheory.FinPl.SplitPt.resField_equiv (I.rec7 l Z) k (p i) v.1 hv
  refine ⟨(Units.mapEquiv ρ.toMulEquiv).toEquiv, fun s => ?_⟩
  obtain ⟨δ, hδ, huni, hint, hint'⟩ := GlobalTheory.AdForm.frameGl_int I hOk hPins l Z u a k ι p β Q L hStd j hj i v hv (g s) s (hg s)
  have htriv := GlobalTheory.T.frameImage_trivial_off_levelPrime I hOk hPins l Z u a k ι p β Q L hStd j hj i v hv (g s) δ hδ
  have hrow := GlobalTheory.AdForm.lastRow_inv_frame I hOk hPins l Z u a k ι p β Q L hStd j hj i v hv ρ hρ (g s) s (hg s) δ hδ hint'
  have hR := hA.reads j hj
  let y : TC.GA B (B.R.N j) := ((A.K j hj (A.chOf j c)).y ⟨c, rfl⟩).1
  refine ⟨y * δ, ?_, ?_⟩
  · rw [Units.val_mul, hδ, finM_mul', (hA.h j hj _ ⟨c, rfl⟩).2]
    rfl
  · obtain ⟨p0, hk0, hN0⟩ := hR.k_std (A.chOf j c)
    have hkc := hk0.lat
    rw [hN0] at hkc
    refine GlobalTheory.Mem.Col2.DilPt.isPointOf_last_coordinate_dilation_one_prime_alt _ _ _ _ _ _ _ y δ (A.kb j (A.chOf j c)) (extTo I.SQ ((I.stp u a j).rep c).1.1) _
      ⟨v.1, v.2⟩ ((Units.mapEquiv ρ.toMulEquiv) s) _ (hR.pt c) hk0.uni huni hkc hint hint' htriv
      (fun r r' hr => hR.k_T (A.chOf j c) ⟨v.1, v.2⟩ r r' hr) (fun r r' hr => hrow r r' hr) ?_ ?_
    · rw [extTo_deco, extTo_deco]
      exact GlobalTheory.Mem.Col2.TwAtStd.diaPt_deco B X I u a j ⟨v.1, v.2⟩ _ c
    · funext P'
      rw [extTo_fr, extTo_fr]
      exact decoratedLattice_unitScale_functional_keeps_frames ((I.stp u a j).rep c) ⟨v.1, v.2⟩ _ P'.1

end GlobalTheory.AdForm.DiaChart

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSplitPlaceModelExtensionLineLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair cosetInd withRow)
open GlobalTheory.FinPl.ExtZero (colFun rowFun)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_splitPlaceModel_extension_lineLattice : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (S L'' : HSp D) (ζ₀ : Fin L''.rank → D.host.E), IsLineVec L'' ζ₀ → ∀ (LS : Lat S), IsSelfDualC S LS → ∀ (n : Type) [Fintype n] [DecidableEq n] (FS : GlobalTheory.LocMod.Frame k S.rank n) (FL'' : GlobalTheory.LocMod.Frame k L''.rank Unit) (TL : SB (Matrix Unit n k) →ₗ[ℂ] (WO S L'' → ℂ)), (GlobalTheory.LocMod.Place.ofSplitPt p).IsModel ψ FS FL'' TL → ∃ (g₃ : WO S L'' → ℂ) (T₃ : (WO S L'' → ℂ) →ₗ[ℂ] (WO S L'' → ℂ)), IsThetaFunO ψ S L'' g₃ ∧ IsPlaceModel ψ (symplO S L'') (heisO ψ S L'') p.e (latO S L'' (LS : Set _) ((Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ₀} : Lat L'') : Set _) (· = p.v)) 1 g₃ T₃ ∧ ∀ Φ, T₃ (GlobalTheory.LocMod.Witness.ext (GlobalTheory.LocMod.Place.ofSplitPt p) FS FL'' Φ) = TL Φ := by
  first | exact @GlobalTheory.ModelExtend.exists_placeModel_ext | exact GlobalTheory.ModelExtend.exists_placeModel_ext | (intros; apply GlobalTheory.ModelExtend.exists_placeModel_ext <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTupleAdelicDataStandardBasePointsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tupleAdelicData_standardBasePoints : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι), ∃ (Ch : ℕ → Type) (_ : ∀ i, Fintype (Ch i)) (A : TwDat I l Z u a Ch), A.Is ∧ Nonempty (Unique (Ch B.R.m)) ∧ (∀ i, Nonempty (Idx I.sel (I.tup a) (I.idx a) i) → Nonempty (Ch i)) ∧ GlobalTheory.QTw.BaseCommon A ∧ (∀ i, i < B.R.m → ∀ β, A.kb i β = TC.kStd X u (B.R.N i)) ∧ ∀ i, i ≤ B.R.m → ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), ((B.T u : ℕ) : 𝓞 B.host.F) ∉ v.asIdeal → (i < B.R.m ∨ ¬ I.UnderQ a v) → Formalism.UG.bc (Formalism.UG.prV (E := B.host.E) v) (A.kb i β) = 1 ∧ ∀ i, i < B.R.m → ∀ β, A.kb i β = TC.kStd X u (B.R.N i) := by
  first | exact @GlobalTheory.AdForm.exists_twDat_baseStd | exact GlobalTheory.AdForm.exists_twDat_baseStd | (intros; apply GlobalTheory.AdForm.exists_twDat_baseStd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTwistRationalLevelElementsSameCharacters
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

namespace GlobalTheory.AdForm.RatApprox

theorem mt_mul' {D : D7} (V : HSp D) (g h : GA D V) :
    Formalism.L2.Theta.mt V (g * h) = Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V h := by
  unfold Formalism.L2.Theta.mt; rw [map_mul]; rfl

theorem actO_actO' {D : D7} (S T : HSp D) (g g' : GA D S) (h h' : GA D T) (x : WO S T) :
    actO S T g h (actO S T g' h' x) = actO S T (g * g') (h * h') x := by
  unfold actO
  rw [_root_.mul_inv_rev, mt_mul', mt_mul']
  simp only [Matrix.mul_assoc]

theorem isHalf_actO' {D : D7} {S T : HSp D} {e : AE D} (g : GA D S) (h : GA D T) {u : WO S T} (hu : IsHalf e u) :
    IsHalf e (actO S T g h u) := by
  intro i j
  simp only [actO, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  conv_rhs => rw [← hu l k]
  ring

end GlobalTheory.AdForm.RatApprox

namespace GlobalTheory.AdForm.RatApprox

set_option maxHeartbeats 2000000 in

theorem approx : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ (k : ℕ), 0 < k → ∀ (κ : A.U i α) (κ' : A.U (i + 1) γ) x y, IsDetRoot _ κ.1 x → IsDetRoot _ κ'.1 y → ∀ (z : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E), ∃ (κ₁ : A.U i α) (κ₁' : A.U (i + 1) γ) (x₁ y₁ : (AE (I.rec7 l Z))ˣ) (t : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))), (∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.host.E, ∀ r s, adAt B.host.F P ((finM _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) κ₁.1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s)) ∧ (∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.host.E, ∀ r s, adAt B.host.F P ((finM _ (rankN (I.rec7 l Z) (i + 1) hi) κ₁'.1 : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s)) ∧ IsDetRoot _ κ₁.1 x₁ ∧ IsDetRoot _ κ₁'.1 y₁ ∧ A.chr (i + 1) x₁ = A.chr (i + 1) x ∧ A.chr (i + 1) y₁ = A.chr (i + 1) y ∧ A.chi i α κ₁ = A.chi i α κ ∧ A.chi (i + 1) γ κ₁' = A.chi (i + 1) γ κ' ∧ t ∈ stdHom _ _ ∧ IsHalf A.e t ∧ actO _ _ κ₁.1⁻¹ κ₁'.1⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r) = actO _ _ κ.1⁻¹ κ'.1⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r) + k • t := by
  intro B X I hI hP l Z u a Ch A hA i hi α γ k hk κ κ' x y hx hy z
  have hi' : i ≤ B.R.m := Nat.le_of_succ_le hi
  obtain ⟨NB, hNB⟩ := GlobalTheory.T.heckeCharacter_eq_at_det_roots_of_congruent (I.rec7 l Z) (A.chr (i + 1)) (hA.chr ⟨i, hi⟩).1
  have hee : A.e * A.e = A.e := GlobalTheory.PlaceDatum.idemSum_mul_self hA.idem
  have hez : IsHalf A.e (z.map fun r => A.e * incA (I.rec7 l Z) r) := fun r s => by
    simp only [Matrix.map_apply, ← mul_assoc, hee]
  have hM := isHalf_actO' κ.1⁻¹ κ'.1⁻¹ hez
  obtain ⟨NC, hNC⟩ := GlobalTheory.T.halfMatrix_move_deepCongruence_bound (I.rec7 l Z) _ _ (rankN (I.rec7 l Z) i hi') (rankN (I.rec7 l Z) (i + 1) hi) A.e _ hM k hk
  have hfin : ∀ j (hj : j ≤ B.R.m) (β : Ch j), GlobalTheory.Mem.Col2.AdT.ChiFin I l Z (A.K j hj β).lev := fun j hj β => by
    obtain ⟨n, hn, h⟩ := hA.fin j hj β
    exact ⟨n, hn, fun κ _ => h κ⟩
  have step : ∀ j (hj : j ≤ B.R.m) (β : Ch j) (g : A.U j β), ∃ w : A.U j β, A.chi j β w = 1 ∧
      (∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) B.host.E, ∀ r s, adAt B.host.F P ((finM _ (rankN (I.rec7 l Z) j hj) (g * w).1 : Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s)) ∧
      ∀ (P : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.E)) (r s : Fin (B.R.N j)), Valued.v (adAt (I.rec7 l Z).host.F P (finM _ (rankN (I.rec7 l Z) j hj) w.1 r s - (1 : Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) (EF (I.rec7 l Z))) r s)) ≤ WithZero.exp (-((max NB NC : ℕ) : ℤ)) := by
    intro j hj β g
    obtain ⟨g₀, hg₀⟩ := ((hA.U j hj β g.1).1 g.2).2
    obtain ⟨zz, hz1, hz2, hz3⟩ := GlobalTheory.T.exists_trivialCharLevel_elt_rational_at_twistPrimes I hI hP l Z a _ j hj _ (A.K j hj β).lev (hfin j hj β) (max NB NC) (show TC.GA B (B.R.N j) from g₀.1)
    obtain ⟨w, hw⟩ := GlobalTheory.T.chartLevel_exists_adelicLevel_trivialReal_lift I hI hP l Z u a Ch A hA j hj β zz
    refine ⟨w, ?_, fun P hPQ => ?_, fun P r s => ?_⟩
    · rw [hA.chi j hj β w zz hw, hz1]
    · obtain ⟨M, hM⟩ := hz2 P hPQ
      refine ⟨M, fun r s => ?_⟩
      rw [← hM r s, Subgroup.coe_mul, GlobalTheory.RepLattice.finM_mul', ← hg₀, ← hw]
      rfl
    · rw [← hw]
      exact hz3 P r s
  obtain ⟨w, hw1, hw2, hw3⟩ := step i hi' α κ
  obtain ⟨w', hw1', hw2', hw3'⟩ := step (i + 1) hi γ κ'
  have hwG : w.1 ∈ GfC _ := ((hA.U i hi' α w.1).1 w.2).1
  have hwG' : w'.1 ∈ GfC _ := ((hA.U (i + 1) hi γ w'.1).1 w'.2).1
  have dB : ∀ {n : ℕ} (f : Matrix (Fin n) (Fin n) (EF (I.rec7 l Z))), (∀ (P : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.E)) (r s : Fin n), Valued.v (adAt (I.rec7 l Z).host.F P (f r s - (1 : Matrix (Fin n) (Fin n) (EF (I.rec7 l Z))) r s)) ≤ WithZero.exp (-((max NB NC : ℕ) : ℤ))) → ∀ N₀ : ℕ, N₀ ≤ max NB NC → ∀ (P : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.E)) (r s : Fin n), Valued.v (adAt (I.rec7 l Z).host.F P (f r s - (1 : Matrix (Fin n) (Fin n) (EF (I.rec7 l Z))) r s)) ≤ WithZero.exp (-(N₀ : ℤ)) := by
    intro n f hf N₀ hN P r s
    exact (hf P r s).trans (WithZero.exp_le_exp.2 (neg_le_neg (Nat.cast_le.2 hN)))
  obtain ⟨x₁, hx₁, hcx⟩ := hNB _ (rankN (I.rec7 l Z) i hi') κ.1 w.1 hwG (dB _ hw3 NB (le_max_left _ _)) x hx
  obtain ⟨y₁, hy₁, hcy⟩ := hNB _ (rankN (I.rec7 l Z) (i + 1) hi) κ'.1 w'.1 hwG' (dB _ hw3' NB (le_max_left _ _)) y hy
  obtain ⟨t, ht, hth, hte⟩ := hNC w.1 w'.1 hwG hwG' (dB _ hw3 NC (le_max_right _ _)) (dB _ hw3' NC (le_max_right _ _))
  refine ⟨κ * w, κ' * w', x₁, y₁, t, hw2, hw2', hx₁, hy₁, hcx, hcy, ?_, ?_, ht, hth, ?_⟩
  · rw [map_mul, hw1, mul_one]
  · rw [map_mul, hw1', mul_one]
  · rw [← hte, actO_actO']
    simp only [Subgroup.coe_mul, _root_.mul_inv_rev]

end GlobalTheory.AdForm.RatApprox
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FamilyRowsColumnsValid
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.IsFam

theorem main : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ f : FamCh W u, f.RowOK → f.c.Is ∧ (f.ColOK → ∀ t, (f.t t).Is) := by
  intro hDS hHC D L hT Gi Gl Kc Yd cX ex W u hP f hR
  have hC := hP.bot.hyp.2.2.2.1
  have hstd : IsStdChar D (pk W).ψ (-1) := (hC.chain.ωX W.P.A3.A.μ0).std
  have hinf : IsInfFam (pk W).θ := hC.models.inf
  have spanT : ∀ n (e : D.R.m - 1 = n), GlobalTheory.Core.Mi.ItSpans ((pk W).MY n) (pk W).MX
      (Eq.rec (motive := fun n _ => PolF D D.sp.X'.rank (Yc D n).rank →ₗ[ℂ] SmT (pk W).MX →ₗ[ℂ] SmT ((pk W).MY n)) (pk W).ItX e) := by
    intro n e
    subst e
    exact GlobalTheory.T.iterates_span_last_step hDS hHC W hP
  refine ⟨⟨hstd, hinf, hR.x, (GlobalTheory.Unf.CoCptOf.coCpt_of_isAniso_or_posDef D D.sp.X').2 GlobalTheory.Hk3.StepX.gram_posDef_X,
    hR.meas.μf, hR.meas.ρJ, hR.meas.ρB, fun j hj => GlobalTheory.T.iterates_span_consecutive_spaces hDS hHC W hP j hj, fun j h => spanT _ (idx_top h)⟩, fun hCol t => ?_⟩
  exact
    { sBF := fun j ρ h => ⟨((hR.row t).sBF j ρ h).1, ((hR.row t).sBF j ρ h).2.1⟩
      sFB := fun j σ h => ⟨((hR.row t).sFB j σ h).1, ((hR.row t).sFB j σ h).2.1⟩
      pt := fun j hj P => GlobalTheory.Chain.InnerSteps.theta_pureTensorO hstd hinf _ _ _ _
        (GlobalTheory.VecTheta.isThetaFunO_stepVec ((hR.row t).vP j hj)) P
      ptT := fun j h P => GlobalTheory.Chain.InnerSteps.theta_pureTensorO hstd hinf _ _ _ _
        (GlobalTheory.VecTheta.isThetaFunO_stepVec ((hR.row t).vT j h)) P
      CC := fun j _ => ⟨_, _, le_rfl⟩
      CT := ⟨_, _, le_rfl⟩
      io := GlobalTheory.T.theta_lift_chain_scalar W u hP f hR t
      ioT := GlobalTheory.T.theta_lift_top_scalar W u hP f hR t
      cI := fun j hj => hR.meas.cIOf_ne_zero (lvP W) t j hj
      ker := hCol.ker t
      e := hCol.e t
      eT := hCol.eT t
      stabK := hCol.stabK t
      stabS := hCol.stabS t }

end GlobalTheory.Fam.IsFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastPeriodLawMovedLevelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastPeriod_law_movedLevel : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → JOf R j J → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (r : RowCh R P u g t) (a : I.ι) (k : ColCh (D := (I.rec7 l Z)) u ((I.rec7 l Z).chTw u a)) (tl : ColT I l u a B.R.m → CXP R P t → ℂ) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) w, PinChL R g k c₀ A ι w → ∀ UT ε, PinTopL R g P (t := t) k UT ε → ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad) (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → (∀ z c (y : FrP (I.rec7 l Z)) y', y'.1 = y.1 → eW z c y = z c y') → g.bT ∈ GfC _ → LevG K g.bT (levS _ R.βX (datXP R P t)) (levChi _ R.βX (datXP R P t)) → (∀ ψ f, ∃ G', ReadsG K eW j g.bT G' f.1 ∧ tl ψ f = (I.per l u a).Ptil ψ G') → ∀ n (hn : n = (I.rec7 l Z).R.m), ∀ ψ ∈ k.Ram n, ∀ (f : CXP R P t) v y β (x : GA (I.rec7 l Z) (I.rec7 l Z).sp.X'), ∀ κ ∈ UT, trc (k.eT n hn β) (f.1 v) (x * κ) * k.rd n β ψ y ((g.oT n hn).emb (x * κ, 1)) = trc (k.eT n hn β) (f.1 v) x * k.rd n β ψ y ((g.oT n hn).emb (x, 1)) := by
  first | exact @GlobalTheory.AdForm.TopInv.law_top | exact GlobalTheory.AdForm.TopInv.law_top | (intros; apply GlobalTheory.AdForm.TopInv.law_top <;> assumption)
end

