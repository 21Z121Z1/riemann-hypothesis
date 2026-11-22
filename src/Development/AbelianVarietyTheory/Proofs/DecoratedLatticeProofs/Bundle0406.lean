import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0382
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0195
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0181
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0333
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0137
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0008
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0368
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0071
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0084
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1151
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0386
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0359
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0210
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0080
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentSubMulComplementEqComplement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0391
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0387
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0388

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GlobalDoublingZetaFormSelfDualLatticeTransfer
section
noncomputable section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.GlobMove

variable {D : D7}

theorem rmul_one' {V : HSp D} (q : AutomorphicL2Unitary.Quot (GQ V)) : AutomorphicL2Unitary.rmul (GQ V) 1 q = q := by
  induction q using Quotient.inductionOn' with
  | h x => exact congrArg _ (mul_one x)

def rmulEquiv {V : HSp D} (y : GA D V) : AutomorphicL2Unitary.Quot (GQ V) ≃ᵐ AutomorphicL2Unitary.Quot (GQ V) where
  toFun := AutomorphicL2Unitary.rmul (GQ V) y
  invFun := AutomorphicL2Unitary.rmul (GQ V) y⁻¹
  left_inv q := by rw [← AutomorphicL2Unitary.rmul_mul, mul_inv_cancel, rmul_one']
  right_inv q := by rw [← AutomorphicL2Unitary.rmul_mul, inv_mul_cancel, rmul_one']
  measurable_toFun := AutomorphicL2Unitary.measurable_rmul y
  measurable_invFun := AutomorphicL2Unitary.measurable_rmul y⁻¹

theorem descend_mul_right {V : HSp D} {φ : GA D V → ℂ} (hφ : AutomorphicL2Unitary.LeftInv (GQ V) φ) (y : GA D V) :
    AutomorphicL2Unitary.descend (GQ V) (fun x => φ (x * y)) = AutomorphicL2Unitary.descend (GQ V) φ ∘ AutomorphicL2Unitary.rmul (GQ V) y := by
  funext q
  have e : AutomorphicL2Unitary.rmul (GQ V) y q = AutomorphicL2Unitary.mk (GQ V) (q.out * y) := by
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  simp only [Function.comp, e, hφ.descend_mk]
  rfl

section Quot

variable {V : HSp D} (m : Measure (GA D V)) [m.IsHaarMeasure] [m.IsMulRightInvariant]

theorem integral_descend_mul_right {φ : GA D V → ℂ} (hφ : AutomorphicL2Unitary.LeftInv (GQ V) φ) (y : GA D V) :
    ∫ q, AutomorphicL2Unitary.descend (GQ V) (fun x => φ (x * y)) q ∂autMeasure V m =
      ∫ q, AutomorphicL2Unitary.descend (GQ V) φ q ∂autMeasure V m := by
  rw [descend_mul_right hφ y]
  exact (AutomorphicL2Unitary.measurePreserving_rmul (Γ := GQ V) (μ := m) y).integral_comp (rmulEquiv y).measurableEmbedding _

theorem integrable_descend_mul_right_iff {φ : GA D V → ℂ} (hφ : AutomorphicL2Unitary.LeftInv (GQ V) φ) (y : GA D V) :
    Integrable (AutomorphicL2Unitary.descend (GQ V) (fun x => φ (x * y))) (autMeasure V m) ↔
      Integrable (AutomorphicL2Unitary.descend (GQ V) φ) (autMeasure V m) := by
  rw [descend_mul_right hφ y]
  exact (AutomorphicL2Unitary.measurePreserving_rmul (Γ := GQ V) (μ := m) y).integrable_comp_emb (rmulEquiv y).measurableEmbedding

theorem petersson_rTr {φ ψ : GA D V → ℂ} (hφ : AutomorphicL2Unitary.LeftInv (GQ V) φ) (hψ : AutomorphicL2Unitary.LeftInv (GQ V) ψ) (y : GA D V) :
    petersson V m (rTr V y φ) (rTr V y ψ) = petersson V m φ ψ := by
  show ∫ q, AutomorphicL2Unitary.descend (GQ V) (fun x => φ (x * y)) q * conj (AutomorphicL2Unitary.descend (GQ V) (fun x => ψ (x * y)) q)
      ∂autMeasure V m = ∫ q, AutomorphicL2Unitary.descend (GQ V) φ q * conj (AutomorphicL2Unitary.descend (GQ V) ψ q) ∂autMeasure V m
  rw [descend_mul_right hφ y, descend_mul_right hψ y]
  exact (AutomorphicL2Unitary.measurePreserving_rmul (Γ := GQ V) (μ := m) y).integral_comp (rmulEquiv y).measurableEmbedding
    (fun q => AutomorphicL2Unitary.descend (GQ V) φ q * conj (AutomorphicL2Unitary.descend (GQ V) ψ q))

end Quot

section Conj

variable {V : HSp D} (m : Measure (GA D V)) [m.IsHaarMeasure] [m.IsMulRightInvariant]

theorem integral_conj (F : GA D V → ℂ) (k : GA D V) : ∫ y, F (k * y * k⁻¹) ∂m = ∫ y, F y ∂m := by
  rw [integral_mul_left_eq_self (fun z => F (z * k⁻¹)) k, integral_mul_right_eq_self F k⁻¹]

theorem integrable_of_conj {F : GA D V → ℂ} (k : GA D V) (h : Integrable (fun y => F (k * y * k⁻¹)) m) :
    Integrable F m := by
  have h2 := (h.comp_mul_left k⁻¹).comp_mul_right k
  refine h2.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]

end Conj

end GlobalTheory.Core.Rk.GlobMove

namespace GlobalTheory.Core.Rk.GlobMove

variable {D : D7}

section Weil

variable {ψ : AddChar (AF D.host.F) ℂ} {A B : HSp D} {χA χB : (AE D)ˣ →* Circle} {om : WRep A B}

theorem om_mul_one (g g' : GA D A) (f : WO A B → ℂ) : om (g, 1) (om (g', 1) f) = om (g * g', 1) f := by
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

theorem thetaKO_om (g k : GA D A) (h : GA D B) (Φ : WO A B → ℂ) :
    thetaKO om g h (om (k, 1) Φ) = thetaKO om (g * k) h Φ := by
  unfold thetaKO
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

theorem leftInv_thetaKO (hW : IsWeilDatumO ψ A B χA χB om) {Φ : WO A B → ℂ} (hΦ : IsThetaFunO ψ A B Φ) (h : GA D B) :
    AutomorphicL2Unitary.LeftInv (GQ A) fun g => thetaKO om g h Φ := by
  intro γ hγ g
  show om (γ * g, h) Φ 0 = om (g, h) Φ 0
  have e : ((γ * g, h) : GA D A × GA D B) = (γ, 1) * (g, h) := by rw [Prod.mk_mul_mk, one_mul]
  rw [e, map_mul, Module.End.mul_apply]
  exact hW.om_aut γ hγ 1 (GQ B).one_mem _ (hW.om_pres _ _ hΦ)

theorem wcoef_om (hW : IsWeilDatumO ψ A B χA χB om) {ν : Measure (WO A B)} {𝓕 : Set (WO A B)}
    (hν : IsCovolOne (ratL B A) ν 𝓕) {Φ₁ Φ₂ : WO A B → ℂ} (h₁ : IsThetaFunO ψ A B Φ₁) (h₂ : IsThetaFunO ψ A B Φ₂)
    (k y : GA D A) :
    wcoef om ν 𝓕 (om (k⁻¹, 1) Φ₁) (om (k⁻¹, 1) Φ₂) y = wcoef om ν 𝓕 Φ₁ Φ₂ (k * y * k⁻¹) := by
  have e : om (y, 1) (om (k⁻¹, 1) Φ₁) = om (k⁻¹, 1) (om (k * y * k⁻¹, 1) Φ₁) := by
    rw [om_mul_one, om_mul_one]; congr 2; group
  have key := GlobalTheory.Mem.LiftPolar.scalar_eq D ψ hW.std A B ν 𝓕 hν.1 hν.2.1 (om (k⁻¹, 1))
    (fun f hf => hW.om_pres (k⁻¹, 1) f hf) (fun f hf => hW.om_unit ν 𝓕 hν.1 hν.2.1 (k⁻¹, 1) f hf)
    (om (k * y * k⁻¹, 1) Φ₁) Φ₂ (hW.om_pres _ _ h₁) h₂
  simp only [wcoef, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.ip, e]
  exact key

end Weil

section Cusp

variable {V : HSp D} (m : Measure (GA D V)) [m.IsHaarMeasure] [m.IsMulRightInvariant]

theorem rcoef_rTr {u₁ u₂ : GA D V → ℂ} (h₁ : AutomorphicL2Unitary.LeftInv (GQ V) u₁) (h₂ : AutomorphicL2Unitary.LeftInv (GQ V) u₂) (k y : GA D V) :
    rcoef m (rTr V k⁻¹ u₁) (rTr V k⁻¹ u₂) y = rcoef m u₁ u₂ (k * y * k⁻¹) := by
  unfold rcoef
  have h₃ : AutomorphicL2Unitary.LeftInv (GQ V) (rTr V (k * y * k⁻¹) u₁) := h₁.mul_right _
  rw [← petersson_rTr m h₃ h₂ k⁻¹]
  congr 1
  funext x
  simp only [rTr]
  congr 1
  group

end Cusp

end GlobalTheory.Core.Rk.GlobMove

namespace GlobalTheory.Core.Rk.GlobMove

variable {D : D7}

theorem cuspFormsArchimedeanKFinite_left_invariant {θ : InfFam D} {A : HSp D} {cA : CptF A} {u : GA D A → ℂ} (hu : u ∈ A0 θ A cA) :
    AutomorphicL2Unitary.LeftInv (GQ A) u :=
  AutomorphicL2Unitary.leftInv_of_isAutFun (Submodule.mem_inf.1 hu).1.1.toIsAutFun

theorem globalFormAt_move : ∀ (D : D7) (A : HSp D) (L L' : Lat A), IsSelfDualC A L → IsSelfDualC A L' →
    GlobalFormAt A L → GlobalFormAt A L' := by
  intro D A L L' hL hL' hG
  obtain ⟨k, hk, hh⟩ := GlobalTheory.T.doubledLatticeHeight_selfDual_lattices_eq_conj D A L L' hL hL'
  intro ψ θ B χA χB sA sB t cA a om ν 𝓕 hP hw m mH hm hmH Φ₁ Φ₂ hΦ₁ hΦ₂ u₁ hu₁ u₂ hu₂
  haveI := hm
  haveI := hmH
  haveI : m.IsMulRightInvariant := Formalism.IndefR.Eqv.unimodGA_holds A m hm
  have hW := hP.weil
  have hθ : IsInfFam θ := hP.setting.2.2.2.1
  have hki : k⁻¹ ∈ GfC A := inv_mem hk
  have fock : ∀ Φ, IsFockVec ψ θ A B sA sB Φ → IsFockVec ψ θ A B sA sB (om (k⁻¹, 1) Φ) := by
    rintro Φ ⟨hΦ, N, hN⟩
    refine ⟨hW.om_pres _ _ hΦ, N, fun l hl => ?_⟩
    refine GlobalTheory.T.weilRep_preserves_fockDegree_of_commute_cartan D ψ θ A B χA χB om sA sB hW hθ k⁻¹ (fun τ => ?_) N Φ hΦ hN l hl
    rw [GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ A hki τ, Matrix.one_mul, Matrix.mul_one]
  have lu₁ := cuspFormsArchimedeanKFinite_left_invariant hu₁
  have lu₂ := cuspFormsArchimedeanKFinite_left_invariant hu₂

  have upEq : ∀ Φ, IsThetaFunO ψ A B Φ → ∀ u : GA D A → ℂ, AutomorphicL2Unitary.LeftInv (GQ A) u →
      (∀ h, AutomorphicL2Unitary.descend (GQ A) (fun g => thetaKO om g h (om (k⁻¹, 1) Φ) * rTr A k⁻¹ u g) =
        AutomorphicL2Unitary.descend (GQ A) (fun g => (fun x => thetaKO om x h Φ * u x) (g * k⁻¹))) ∧
      ∀ h, AutomorphicL2Unitary.LeftInv (GQ A) (fun x => thetaKO om x h Φ * u x) := by
    intro Φ hΦ u hu
    refine ⟨fun h => ?_, fun h γ hγ g => ?_⟩
    · congr 1
      funext g
      rw [thetaKO_om]
      rfl
    · simp only [leftInv_thetaKO hW hΦ h γ hγ g, hu γ hγ g]
  have upConvIff : ∀ Φ, IsThetaFunO ψ A B Φ → ∀ u : GA D A → ℂ, AutomorphicL2Unitary.LeftInv (GQ A) u →
      up om m (om (k⁻¹, 1) Φ) (rTr A k⁻¹ u) = up om m Φ u ∧
      (UpConv om m mH (om (k⁻¹, 1) Φ) (rTr A k⁻¹ u) → UpConv om m mH Φ u) := by
    intro Φ hΦ u hu
    obtain ⟨e1, e2⟩ := upEq Φ hΦ u hu
    have hup : up om m (om (k⁻¹, 1) Φ) (rTr A k⁻¹ u) = up om m Φ u := by
      funext h
      simp only [up]
      rw [e1 h, integral_descend_mul_right m (e2 h) k⁻¹]
    refine ⟨hup, fun ⟨c1, c2⟩ => ⟨fun h => ?_, hup ▸ c2⟩⟩
    have := c1 h
    rw [e1 h, integrable_descend_mul_right_iff m (e2 h) k⁻¹] at this
    exact this

  have hint : ∀ s y, integrand om m ν 𝓕 L a (om (k⁻¹, 1) Φ₁) (om (k⁻¹, 1) Φ₂) (rTr A k⁻¹ u₁) (rTr A k⁻¹ u₂) s y =
      integrand om m ν 𝓕 L' a Φ₁ Φ₂ u₁ u₂ s (k * y * k⁻¹) := by
    intro s y
    simp only [integrand]
    rw [wcoef_om hW hP.covol hΦ₁.1 hΦ₂.1, rcoef_rTr m lu₁ lu₂, hh a hP.maj]
    congr 3
    group
  obtain ⟨c1, c2, c3, z, hz, hpet⟩ := hG ψ θ B χA χB sA sB t cA a om ν 𝓕 hP hw m mH hm hmH
    (om (k⁻¹, 1) Φ₁) (om (k⁻¹, 1) Φ₂) (fock Φ₁ hΦ₁) (fock Φ₂ hΦ₂)
    (rTr A k⁻¹ u₁) (GlobalTheory.T.rTr_mem_A0 D θ A cA hθ k⁻¹ hki u₁ hu₁)
    (rTr A k⁻¹ u₂) (GlobalTheory.T.rTr_mem_A0 D θ A cA hθ k⁻¹ hki u₂ hu₂)
  obtain ⟨up₁, cv₁⟩ := upConvIff Φ₁ hΦ₁.1 u₁ lu₁
  obtain ⟨up₂, cv₂⟩ := upConvIff Φ₂ hΦ₂.1 u₂ lu₂
  refine ⟨cv₁ c1, cv₂ c2, fun s hs => integrable_of_conj m k ?_, z, ?_, ?_⟩
  · have := c3 s hs
    rwa [show integrand om m ν 𝓕 L a (om (k⁻¹, 1) Φ₁) (om (k⁻¹, 1) Φ₂) (rTr A k⁻¹ u₁) (rTr A k⁻¹ u₂) s =
      fun y => integrand om m ν 𝓕 L' a Φ₁ Φ₂ u₁ u₂ s (k * y * k⁻¹) from funext (hint s)] at this
  · have e : (fun s => ∫ g, integrand om m ν 𝓕 L' a Φ₁ Φ₂ u₁ u₂ s g ∂m) =
        fun s => ∫ g, integrand om m ν 𝓕 L a (om (k⁻¹, 1) Φ₁) (om (k⁻¹, 1) Φ₂) (rTr A k⁻¹ u₁) (rTr A k⁻¹ u₂) s g ∂m := by
      funext s
      simp only [hint]
      rw [integral_conj m (integrand om m ν 𝓕 L' a Φ₁ Φ₂ u₁ u₂ s) k]
    rw [e]
    exact hz
  · rw [← up₁, ← up₂]
    exact hpet

end GlobalTheory.Core.Rk.GlobMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HalfAIdempotentComponentCocycleTrivial
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.CocycleSS
open GlobalTheory.LatVac

variable {D : D7}

theorem natCast_smul_mem_of_halfAO {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}
    {SS : Finset (HeightOneSpectrum (𝓞 E))} {M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b)} {c : ℕ} (hc : 0 < c)
    {x : Formalism.L2.Col.HomE E a b} (hx : x ∈ halfAO SS M c) : (c : E) • x ∈ M := by
  refine GlobalTheory.ThetaMove.mem_of_locP fun Q => ?_
  have h : ((c : E) ^ (-expS SS Q))⁻¹ • x ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M := (Submodule.mem_iInf _).1 hx Q
  have hc' : (c : E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  have key : ∀ k : ℕ, (c : E) = (c : E) ^ k * ((c : E) ^ (-expS SS Q))⁻¹ →
      (c : E) • x ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M := fun k hk => by
    have := nsmul_mem h (c ^ k)
    rwa [← Nat.cast_smul_eq_nsmul E, smul_smul, Nat.cast_pow, ← hk] at this
  unfold expS at key
  split_ifs at key
  · exact key 0 (by simp)
  · exact key 2 (by rw [neg_neg, zpow_one]; field_simp)
  · exact key 1 (by simp)

theorem conjP_conjP (Q : HeightOneSpectrum (𝓞 D.host.E)) : Formalism.L2.Col.conjPrime₂ (Formalism.L2.Col.conjPrime₂ Q) = Q := by
  apply HeightOneSpectrum.ext
  ext r
  rw [Formalism.L2.Col.mem_conjP, Formalism.L2.Col.mem_conjP, Formalism.L2.Col.cO_cO]

theorem conjP_not_mem {e : AE D} {SS : Finset (Formalism.L2.DIV.Pl D.host.E)} (h : IsIdemSum e SS)
    {PP : HeightOneSpectrum (𝓞 D.host.E)} (hPP : PP ∈ SS) : Formalism.L2.Col.conjPrime₂ PP ∉ SS := fun h' =>
  GlobalTheory.ChainOnto.FlagAct.not_isConjPl_of_idemSum h PP hPP _ h' fun r hr =>
    ⟨Formalism.L2.Col.cO D.host.E r, by rw [Formalism.L2.Col.mem_conjP, Formalism.L2.Col.cO_cO]; exact hr, rfl⟩

end GlobalTheory.AdForm.CocycleSS

namespace GlobalTheory.AdForm.CocycleSS
open GlobalTheory.LatVac

variable {D : D7} {S T : HSp D}

theorem smul_tmul_fin {a : AE D} (ha : infPart D a = 0) (r : D.host.E) :
    a * ((pairA D.host.F 0 1) ⊗ₜ[D.host.F] r) = a * incA D r :=
  GlobalTheory.SplitScalar.adele_ext (by rw [RingHom.map_mul, RingHom.map_mul, ha, zero_mul, zero_mul])
    (by rw [RingHom.map_mul, RingHom.map_mul]; rfl)

theorem symplOH_smul (a : AE D) (x y : WO S T) : symplOH S T (a • x) y = symplOH S T x (cA D a • y) := by
  rw [symplOH, symplOH, GlobalTheory.SplitScalar.symplO_smul]

theorem lhs_eq {e : AE D} (hinf : infPart D (cA D e) = 0) (hec : e * cA D e = 0)
    (X : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    symplOH S T (X.map fun r => e * incA D r) (GlobalTheory.VacUnique.finRat S T X - X.map fun r => e * incA D r) =
      symplOH S T (X.map (incA D)) (cA D e • X.map (incA D)) := by
  have hXt : (X.map fun r => e * incA D r : WO S T) = e • (X.map (incA D) : WO S T) := by ext i j; rfl
  have hF : cA D e • GlobalTheory.VacUnique.finRat S T X = cA D e • (X.map (incA D) : WO S T) := by
    ext i j; exact smul_tmul_fin hinf _
  rw [hXt, symplOH_smul, smul_sub, hF, smul_smul, mul_comm, hec, zero_smul, sub_zero]

theorem smul_finRat_natCast {e : AE D} (hinf : infPart D e = 0) (c : ℕ) (X : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    e • GlobalTheory.VacUnique.finRat S T ((c : D.host.E) • X) = (e * incA D (c : D.host.E)) • (X.map (incA D) : WO S T) := by
  ext i j
  show e * ((pairA D.host.F 0 1) ⊗ₜ[D.host.F] ((c : D.host.E) * X i j)) = (e * incA D (c : D.host.E)) * incA D (X i j)
  rw [smul_tmul_fin hinf, map_mul, mul_assoc]

theorem smul_map_inv {e : AE D} (hcc : cA D e * cA D e = cA D e) (c : ℕ) (X : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    cA D e • (((c : D.host.E)⁻¹ • X).map fun r => cA D e * incA D r : WO S T) =
      (cA D e * incA D ((c : D.host.E)⁻¹)) • (X.map (incA D) : WO S T) := by
  ext i j
  show cA D e * (cA D e * incA D ((c : D.host.E)⁻¹ * X i j)) = (cA D e * incA D ((c : D.host.E)⁻¹)) * incA D (X i j)
  rw [map_mul, ← mul_assoc, hcc, mul_assoc]

theorem cA_incA_natCast (c : ℕ) : cA D (incA D (c : D.host.E)) = incA D (c : D.host.E) := by
  show incA D (star (c : D.host.E)) = _
  rw [star_natCast]

theorem rhs_eq {e : AE D} (hinf : infPart D e = 0) (hcc : cA D e * cA D e = cA D e) {c : ℕ} (hc : 0 < c)
    (X : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    symplOH S T (e • GlobalTheory.VacUnique.finRat S T ((c : D.host.E) • X))
        (cA D e • (((c : D.host.E)⁻¹ • X).map fun r => cA D e * incA D r : WO S T)) =
      symplOH S T (X.map (incA D)) (cA D e • X.map (incA D)) := by
  have hcE : (c : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  have hs : cA D e * incA D (c : D.host.E) * (cA D e * incA D ((c : D.host.E)⁻¹)) = cA D e := by
    rw [mul_mul_mul_comm, hcc, ← map_mul, mul_inv_cancel₀ hcE, map_one, mul_one]
  rw [smul_finRat_natCast hinf, smul_map_inv hcc, symplOH_smul, smul_smul, RingHom.map_mul, cA_incA_natCast, hs]

theorem finRat_mem {N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hcc : D.host.ccK = ⊤) (hN : IsSelfDualC S N) {SS : Finset (HeightOneSpectrum (𝓞 D.host.E))} {c : ℕ} (hc : 0 < c)
    {x' : Formalism.L2.Col.HomE D.host.E S.rank T.rank}
    (hx : x' ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c) :
    GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' ((c : D.host.E) • x')) ∈
      latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True := by
  have e1 : GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' ((c : D.host.E) • x')) =
      finTens 1 (LinearMap.toMatrix' ((c : D.host.E) • x')) := by ext i j; rfl
  rw [e1]
  exact finTens_mem_latO (one_mem_intAf _)
    (GlobalTheory.AdForm.HalfPairing.toMatrix_mem_latRat hcc hN (natCast_smul_mem_of_halfAO hc hx))

theorem conjHalf_mem {N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hcc : D.host.ccK = ⊤) (hN : IsSelfDualC S N) {e : AE D} {SS : Finset (Formalism.L2.DIV.Pl D.host.E)} (hE : IsIdemSum e SS)
    {c : ℕ} {x' : Formalism.L2.Col.HomE D.host.E S.rank T.rank}
    (hx : x' ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c) :
    ((LinearMap.toMatrix' ((c : D.host.E)⁻¹ • x')).map fun r => cA D e * incA D r : WO S T) ∈
      latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True := by
  have hno : ∀ PP ∈ SS, Formalism.L2.Col.conjPrime₂ PP ∉ SS := fun PP hPP => conjP_not_mem hE hPP
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := hE
  have e1 : ((LinearMap.toMatrix' ((c : D.host.E)⁻¹ • x')).map fun r => cA D (∑ PP ∈ SS, es PP) * incA D r : WO S T) =
      ∑ PP ∈ SS, ((LinearMap.toMatrix' ((c : D.host.E)⁻¹ • x')).map fun r => cA D (es PP) * incA D r : WO S T) := by
    ext i j
    rw [Matrix.map_apply, Matrix.sum_apply, map_sum, Finset.sum_mul]
    rfl
  rw [e1]
  refine sum_mem fun PP hPP => GlobalTheory.AdForm.HalfPairing.conj_comp_mem hcc hN (hes PP hPP) ?_ ?_
  · refine GlobalTheory.PlaceVec.idemSum_infPart (P := {PP}) ⟨⟨es, fun Q hQ => ?_, (Finset.sum_singleton _ _).symm⟩, (hes PP hPP).1.2.1⟩
    rw [Finset.mem_singleton.1 hQ]
    exact hes PP hPP
  · have h : ((c : D.host.E) ^ (-expS SS (Formalism.L2.Col.conjPrime₂ PP)))⁻¹ • x' ∈
        Formalism.HermitianLatticesTheory.localization₂ (Formalism.L2.Col.conjPrime₂ PP).asIdeal (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') :=
      (Submodule.mem_iInf _).1 hx _
    have hexp : expS SS (Formalism.L2.Col.conjPrime₂ PP) = -1 := by
      unfold expS
      rw [if_neg (hno PP hPP), conjP_conjP, if_pos hPP]
    rw [hexp, neg_neg, zpow_one] at h
    exact h

theorem cocycle_trivial : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ (c : ℕ), 0 < c → Odd c → ∀ x' ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, ψ (symplOH S T ((LinearMap.toMatrix' x').map fun r => e * incA D r) ((GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' x')) - ((LinearMap.toMatrix' x').map fun r => e * incA D r))) = 1 := by
  intro D ψ θ S T δ sc hP e SS hE h2 N N' hN hN' c hc _hodd x' hx
  have hinf : infPart D e = 0 := GlobalTheory.PlaceDatum.infPart_idemSum hE
  have hinfc : infPart D (cA D e) = 0 := GlobalTheory.PlaceDatum.infPart_cA hinf
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self hE
  have hcc : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, hee]
  have H := GlobalTheory.HalfCocycle.char_symplOH_idem_conj D ψ θ S T δ sc hP e SS hE h2 N N' hN hN' _ (finRat_mem hP.cc hN hc hx) _
    (conjHalf_mem hP.cc hN hE hx)
  have e1 : ∀ r : D.host.E, (LinearMap.toMatrix' (r • x') : Matrix (Fin T.rank) (Fin S.rank) D.host.E) =
      r • LinearMap.toMatrix' x' := fun r => LinearEquiv.map_smul LinearMap.toMatrix' r x'
  rw [e1, e1, rhs_eq hinf hcc hc] at H
  rw [lhs_eq hinfc hE.2]
  exact H

end GlobalTheory.AdForm.CocycleSS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralFiniteAdeleOfSplitPlaceComponents
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

theorem GlobalTheory.IntPlaces.mem_of_idem_sum {R : Type} [CommRing R] {n : ℕ} (S : Set R) (hS0 : (0 : R) ∈ S)
    (E : Fin n → R) (hEE : ∀ i, E i * E i = E i) (hE : ∀ i j, i ≠ j → E i * E j = 0) (G : Fin n → R → Prop)
    (hint : ∀ i z, z ∈ S ↔ (1 - E i) * z ∈ S ∧ G i z) (hG : ∀ i j z, i ≠ j → G i z → G i ((1 - E j) * z)) :
    ∀ z, (∑ i, E i) * z = z → (∀ i, G i z) → z ∈ S := by
  have key : ∀ s : Finset (Fin n), ∀ z, (∑ i ∈ s, E i) * z = z → (∀ i ∈ s, G i z) → z ∈ S := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro z hz _
      rw [Finset.sum_empty, zero_mul] at hz
      rw [← hz]
      exact hS0
    | insert a s ha ih =>
      intro z hz hzi
      rw [Finset.sum_insert ha] at hz
      refine (hint a z).2 ⟨?_, hzi a (Finset.mem_insert_self a s)⟩
      have hET : E a * ∑ i ∈ s, E i = 0 := by
        rw [Finset.mul_sum]
        exact Finset.sum_eq_zero fun i hi => hE a i fun h => ha (h ▸ hi)
      have hw : (1 - E a) * z = (∑ i ∈ s, E i) * z := by
        calc (1 - E a) * z = (1 - E a) * ((E a + ∑ i ∈ s, E i) * z) := by rw [hz]
          _ = (∑ i ∈ s, E i) * z := by linear_combination (-z) * hEE a + (-z) * hET
      refine ih _ ?_ fun i hi => ?_
      · linear_combination (-1 : R) * hw + (-z) * hET
      · exact hG i a z (fun h => ha (h ▸ hi)) (hzi i (Finset.mem_insert_of_mem hi))
  exact fun z hz hzi => key Finset.univ z hz fun i _ => hzi i

open GlobalTheory.IdemSupport in

theorem GlobalTheory.IntPlaces.mem_intAf_of_split : ∀ (D : D7) (n : ℕ) (k : Fin n → Type) [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)] [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] (q : ∀ i, GlobalTheory.FinPl.SplitPt D (k i)) (P : Fin n → Formalism.L2.DIV.Pl D.host.E), (∀ i, Formalism.L2.NTheta.IsIdemAt (q i).e (P i)) → Function.Injective P → ∀ (π' : ∀ i, Formalism.IndefR.Datum.EAf D →+* k i), (∀ i a, π' i (Formalism.IndefR.Datum.toEAf D a) = (q i).pr a) → (∀ i (z : Formalism.IndefR.Datum.EAf D), z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ (1 - Formalism.IndefR.Datum.toEAf D (q i).e) * z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ π' i z ∈ 𝒪[k i]) → ∀ z : Formalism.IndefR.Datum.EAf D, Formalism.IndefR.Datum.toEAf D (∑ i, (q i).e) * z = z → (∀ i, π' i z ∈ 𝒪[k i]) → z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  intro D n k _ _ _ _ q P hI hP π' hπ hint z0 hz0 hzi0
  have hΦ := GlobalTheory.StdFrames.comp_toAd D
  have hd : ∀ i, IsDelta ((GlobalTheory.StdFrames.toAd D).comp (Formalism.IndefR.Datum.toEAf D)) (P i) (q i).e :=
    fun i => delta_of_isIdemAt hΦ (hI i)
  have horth : ∀ i j, i ≠ j → (q i).e * (q j).e = 0 := by
    intro i j hij
    refine hΦ.ext' (by rw [RingHom.map_mul, (hd i).1, zero_mul, RingHom.map_zero]) fun Q => ?_
    rw [ev_mul, ev_zero]
    by_cases hQ : Q = P i
    · rw [(hd j).2.2 Q (fun h => hij (hP (hQ.symm.trans h))), mul_zero]
    · rw [(hd i).2.2 Q hQ, zero_mul]
  have hidem : ∀ i, (q i).e * (q i).e = (q i).e := by
    intro i
    refine hΦ.ext' (by rw [RingHom.map_mul, (hd i).1, zero_mul]) fun Q => ?_
    rw [ev_mul]
    by_cases hQ : Q = P i
    · rw [hQ, (hd i).2.1, mul_one]
    · rw [(hd i).2.2 Q hQ, zero_mul]
  have hpr : ∀ i j, i ≠ j → π' i (Formalism.IndefR.Datum.toEAf D (q j).e) = 0 := by
    intro i j hij
    rw [hπ, ← (q i).pr_sec ((q i).pr (q j).e), (q i).sec_pr, horth i j hij, map_zero]
  refine GlobalTheory.IntPlaces.mem_of_idem_sum (Formalism.L2.Herm.intAf D.host.F D.host.E : Set _) (zero_mem _)
    (fun i => Formalism.IndefR.Datum.toEAf D (q i).e) (fun i => by rw [← RingHom.map_mul, hidem])
    (fun i j hij => by rw [← RingHom.map_mul, horth i j hij, RingHom.map_zero]) (fun i z => π' i z ∈ 𝒪[k i])
    hint (fun i j z hij hz => ?_) z0 (by rw [show (∑ i, Formalism.IndefR.Datum.toEAf D (q i).e) = Formalism.IndefR.Datum.toEAf D (∑ i, (q i).e) from
      (map_sum (Formalism.IndefR.Datum.toEAf D).toAddMonoidHom (fun i => (q i).e) Finset.univ).symm]; exact hz0) hzi0
  rw [RingHom.map_mul, RingHom.map_sub, RingHom.map_one, hpr i j hij, sub_zero, one_mul]
  exact hz
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratesSpanConsecutiveSpacesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iterates_span_consecutive_spaces : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ j, j + 1 < D.R.m → GlobalTheory.Core.Mi.ItSpans ((pk W).MY j) ((pk W).MY (j + 1)) ((pk W).ItY j) := by
  first | exact @GlobalTheory.Core.Mi.SpanY.itSpans_pk | exact GlobalTheory.Core.Mi.SpanY.itSpans_pk | (intros; apply GlobalTheory.Core.Mi.SpanY.itSpans_pk <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratesSpanLastStepStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iterates_span_last_step : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → GlobalTheory.Core.Mi.ItSpans ((pk W).MY (D.R.m - 1)) (pk W).MX (pk W).ItX := by
  first | exact @GlobalTheory.Core.Mi.SpanX.itSpans_pk | exact GlobalTheory.Core.Mi.SpanX.itSpans_pk | (intros; apply GlobalTheory.Core.Mi.SpanX.itSpans_pk <;> assumption)
end

