import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1522
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0083
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0232
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0101
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0152
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0173
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0210
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0482
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0011
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0185
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0198
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0259
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0158
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0514
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0273
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0443
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0263
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalIntegralGL
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LiftsGen
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0045
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0085
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0254
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0511
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0095
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0515
import GroundTheory.GlobalFields.TateThesis.AdelicCharDual

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfDefinite
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConstRatio

open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle

section RatPart

variable {L ι : Type} [Field L] (σ : L →+* ℂ)

def ratPart (φ : ℂ → L) (w : ℂ) (P : MvPolynomial ι ℂ) : MvPolynomial ι ℂ :=
  ∑ k ∈ P.support, σ (φ (w * P.coeff k)) • MvPolynomial.monomial k 1

variable {σ}

theorem ratPart_rat {ℓ : MvPolynomial ι ℂ →ₗ[ℂ] ℂ} {Ω : ℂ} (h : ∀ k, ∃ z : L, ℓ (MvPolynomial.monomial k 1) = Ω * σ z)
    (φ : ℂ → L) (w : ℂ) (P : MvPolynomial ι ℂ) : ∃ z : L, ℓ (ratPart σ φ w P) = Ω * σ z := by
  choose z hz using h
  refine ⟨∑ k ∈ P.support, φ (w * P.coeff k) * z k, ?_⟩
  simp only [ratPart, map_sum, map_smul, hz, map_mul, Finset.mul_sum, smul_eq_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem ratPart_eq {ℓ : MvPolynomial ι ℂ →ₗ[ℂ] ℂ} {Ω : ℂ} (h : ∀ k, ∃ z : L, ℓ (MvPolynomial.monomial k 1) = Ω * σ z)
    (φ : ℂ →+ L) (hφ : ∀ x y, φ (x * σ y) = φ x * y) (w : ℂ) (P : MvPolynomial ι ℂ) :
    ℓ (ratPart σ φ (w * Ω) P) = Ω * σ (φ (w * ℓ P)) := by
  choose z hz using h
  have e : ℓ P = ∑ k ∈ P.support, P.coeff k * (Ω * σ (z k)) := by
    conv_lhs => rw [P.as_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hz, ← smul_eq_mul, ← map_smul, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [e]
  simp only [ratPart, map_sum, map_smul, hz, Finset.mul_sum, smul_eq_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show w * (P.coeff k * (Ω * σ (z k))) = (w * Ω * P.coeff k) * σ (z k) by ring, hφ, σ.map_mul]
  ring

theorem exists_dual {x : ℂ} (hx : x ≠ 0) : ∃ φ : ℂ →+ L, (∀ a y, φ (a * σ y) = φ a * y) ∧ φ x ≠ 0 := by
  letI : Algebra L ℂ := σ.toAlgebra
  obtain ⟨φ, hφ⟩ := not_forall.1 (mt (Module.forall_dual_apply_eq_zero_iff L x).1 hx)
  refine ⟨φ.toAddMonoidHom, fun a y => ?_, hφ⟩
  have : a * σ y = y • a := by rw [Algebra.smul_def, mul_comm]; rfl
  show φ (a * σ y) = φ a * y
  rw [this, map_smul, smul_eq_mul, mul_comm]

end RatPart

variable {D : D7}

section Bottom

variable {T : Type} {A A' WW : HSp D} {X : Tri T A A' WW} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}

theorem Factor.ratIn {L : Type} [Field L] {σ : L →+* ℂ} {lam : T → ℂ} (h : Factor X ψ θ lam) (hr : X.RationalSums ψ θ σ)
    (hi' : ∀ t P g, IntegrableOn (X.ker' ψ θ t P g) X.fd' X.m')
    (hz : ∀ t P P' (a b : ℂ), (∀ g ∈ GfC WW, a * X.I ψ θ t P g - b * X.I' ψ θ t P' g = 0) →
      ∀ g, a * X.I ψ θ t P g - b * X.I' ψ θ t P' g = 0) (t₀ : T) : RatIn σ t₀ lam := by
  obtain ⟨h0, Pi, p, p', J, hs, hJ, -, hI, hI', P', hP', -⟩ := h
  obtain ⟨Ω, Ω', hΩ, hΩ', H⟩ := hr
  obtain ⟨P, hP⟩ := hs (p' P')
  have hI'' : ∀ t Q, X.I' ψ θ t Q = J t (p' Q) := fun t Q => hI' t Q (hi' t Q)
  let ℓ : T → GA D WW → (PolF D WW.rank A.rank →ₗ[ℂ] ℂ) := fun t g => lam t • (LinearMap.proj g ∘ₗ J t ∘ₗ p)
  let ℓ' : T → GA D WW → (PolF D WW.rank A'.rank →ₗ[ℂ] ℂ) := fun t g => LinearMap.proj g ∘ₗ J t ∘ₗ p'
  have hℓ : ∀ t g Q, ℓ t g Q = X.I ψ θ t Q g := fun t g Q => by rw [hI]; rfl
  have hℓ' : ∀ t g Q, ℓ' t g Q = X.I' ψ θ t Q g := fun t g Q => by rw [hI'']; rfl
  have r : ∀ t, ∀ g ∈ GfC WW, ∀ k, ∃ z : L, ℓ t g (MvPolynomial.monomial k 1) = Ω * σ z := fun t g hg k => by
    rw [hℓ]; exact ((H t g hg).1 k).2
  have r' : ∀ t, ∀ g ∈ GfC WW, ∀ k, ∃ z : L, ℓ' t g (MvPolynomial.monomial k 1) = Ω' * σ z := fun t g hg k => by
    rw [hℓ']; exact ((H t g hg).2 k).2
  have sep : ∀ t Q Q' (a b : ℂ), (∀ g ∈ GfC WW, a * ℓ t g Q - b * ℓ' t g Q' = 0) → (a * lam t) • p Q = b • p' Q' :=
    fun t Q Q' a b hh => hJ t (funext fun g => by
      have := hz t Q Q' a b (fun g hg => by rw [← hℓ, ← hℓ']; exact hh g hg) g
      rw [hI, hI''] at this
      simp only [map_smul, _root_.Pi.smul_apply, smul_eq_mul] at this ⊢
      linear_combination this)
  have nz : ∀ t Q', p' Q' ≠ 0 → ∃ g ∈ GfC WW, ℓ' t g Q' ≠ 0 := fun t Q' hQ => by
    by_contra hc
    push Not at hc
    have := sep t P Q' 0 1 fun g hg => by rw [hc g hg]; simp
    exact hQ (by simpa using this.symm)
  obtain ⟨g₀, hg₀, hn₀⟩ := nz t₀ P' hP'
  obtain ⟨φ, hφ, hφ0⟩ := exists_dual (σ := σ) hn₀
  have e0 : ∀ g, (lam t₀)⁻¹ * ℓ t₀ g P = 1 * ℓ' t₀ g P' := fun g => by
    show (lam t₀)⁻¹ * (lam t₀ * J t₀ (p P) g) = 1 * J t₀ (p' P') g
    rw [hP, inv_mul_cancel_left₀ (h0 _), one_mul]
  set Q := ratPart σ φ ((lam t₀)⁻¹ * Ω) P
  set Q' := ratPart σ φ (1 * Ω') P'
  have e1 : (Ω' * lam t₀) • p Q = Ω • p' Q' := sep t₀ Q Q' Ω' Ω fun g hg => by
    rw [ratPart_eq (r t₀ g hg) φ hφ, ratPart_eq (r' t₀ g hg) φ hφ, e0]; ring
  have hQ' : p' Q' ≠ 0 := fun hh => by
    have h1 : ℓ' t₀ g₀ Q' = 0 := by
      show J t₀ (p' Q') g₀ = 0
      rw [hh, map_zero]; rfl
    rw [ratPart_eq (r' t₀ g₀ hg₀) φ hφ, one_mul] at h1
    exact mul_ne_zero hΩ' ((map_ne_zero σ).2 hφ0) h1
  intro t
  refine ⟨h0 t, ?_⟩
  obtain ⟨g, hg, hn⟩ := nz t Q' hQ'
  obtain ⟨z, hz1⟩ := ratPart_rat (r t g hg) φ ((lam t₀)⁻¹ * Ω) P
  obtain ⟨z', hz2⟩ := ratPart_rat (r' t g hg) φ (1 * Ω') P'
  have e2 : Ω' * lam t₀ * ℓ t g Q = lam t * Ω * ℓ' t g Q' := by
    have := congrArg (fun x => J t x g) e1
    simp only [map_smul, _root_.Pi.smul_apply, smul_eq_mul] at this
    show Ω' * lam t₀ * (lam t * J t (p Q) g) = lam t * Ω * J t (p' Q') g
    linear_combination lam t * this
  have hz' : σ z' ≠ 0 := fun hh => hn (hz2.trans (by rw [hh, mul_zero]))
  have e3 : σ (z / z') = lam t / lam t₀ := by
    rw [show ℓ t g Q = _ from hz1, show ℓ' t g Q' = _ from hz2] at e2
    have := h0 t₀
    rw [map_div₀]
    field_simp
    have e4 : Ω * Ω' * (σ z * lam t₀ - lam t * σ z') = 0 := by linear_combination e2
    have := (mul_eq_zero.1 e4).resolve_left (mul_ne_zero hΩ hΩ')
    linear_combination this
  have hne : z / z' ≠ 0 := fun hh => div_ne_zero (h0 t) (h0 t₀) (by rw [← e3, hh, map_zero])
  exact ⟨Units.mk0 _ hne, e3⟩

theorem ideal_ne_bot (X : Tri T A A' WW) (S : T → Finset (Pl D.host.E)) (t : T) : X.ideal S t ≠ ⊥ :=
  Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ w.ne_bot

variable {α β : T → ((AE D)ˣ →* Circle)} {νH : T → Formalism.L2.Host.HChar D.host.E} {S : T → Finset (Pl D.host.E)}

theorem theta_f (h : X.Is ψ θ α β νH S) (t : T) : IsThetaFunO ψ (neg A) WW (X.f t) ∧ IsThetaFunO ψ A' WW (X.f' t) := by
  have hν : IsHeckeChar D (α t / β t) := (h.weil' t).hecT
  obtain ⟨f, h1, h2⟩ := GlobalTheory.T.first_standard_pair_member_has_theta_function D ψ θ A WW X.rA X.rW _ _ _ _ _ h.rigA h.rigW hν (h.idem t) (ideal_ne_bot X S t) h.isVac
  obtain ⟨f', h1', h2'⟩ := GlobalTheory.T.exists_thetaFunction_standardPairSecond D ψ θ A' WW X.rA' X.rW _ _ _ _ A.rank _ h.rigA' h.rigW hν (h.idem t) (ideal_ne_bot X S t) h.isVac'
  obtain ⟨Tm, hT⟩ := h1.1
  obtain ⟨Tm', hT'⟩ := h1'.1
  exact ⟨((h.fst t).2 Tm hT).trans (h1.2 Tm hT).symm ▸ h2, ((h.snd t).2 Tm' hT').trans (h1'.2 Tm' hT').symm ▸ h2'⟩

theorem ratIn_of_definite {L : Type} [Field L] {σ : L →+* ℂ} {lam : T → ℂ} (h : X.Is ψ θ α β νH S)
    (hA : ∀ τ, (gramAt D A τ).PosDef) (hA' : ∀ τ, (gramAt D A' τ).PosDef) (hW : ∀ τ, (gramAt D WW τ).PosDef)
    (hF : Factor X ψ θ lam) (hr : X.RationalSums ψ θ σ) (t₀ : T) : RatIn σ t₀ lam := by
  have c := fun t P => GlobalTheory.T.thetaIntegral_definiteSource_converges_continuous_invariant D ψ true A WW _ _ (X.ω t) X.m X.fd _ (h.weil t) hA h.meas.1 h.meas.2
    (GlobalTheory.Chain.InnerSteps.theta_pureTensorO (S := neg A) h.isVac.1 h.isVac.2.inf (fun τ => -X.rA.s τ) X.rA.B X.rW.s X.rW.B (theta_f h t).1 P)
  have c' := fun t P => GlobalTheory.T.thetaIntegral_definiteSource_converges_continuous_invariant D ψ false A' WW _ _ (X.ω' t) X.m' X.fd' _ (h.weil' t) hA' h.meas'.1 h.meas'.2
    (GlobalTheory.Chain.InnerSteps.theta_pureTensorO h.isVac.1 h.isVac.2.inf X.rA'.s X.rA'.B X.rW.s X.rW.B (theta_f h t).2 P)
  refine hF.ratIn hr (fun t P g => (c' t P).1 g) (fun t P P' a b => ?_) t₀
  refine GlobalTheory.T.continuous_automorphic_eq_zero_of_vanish_on_finiteAdelic D WW (fun g => a * X.I ψ θ t P g - b * X.I' ψ θ t P' g) hW
    ((continuous_const.mul (c t P).2.1).sub (continuous_const.mul (c' t P').2.1)) fun γ hγ g => ?_
  exact congrArg₂ (fun u v => a * u - b * v) ((c t P).2.2 γ hγ g) ((c' t P').2.2 γ hγ g)

theorem posDef_of_std {V : HSp D} {r : Rig V} (h : r.IsStd) (τ : D.what₂.Tau) : (gramAt D V τ).PosDef := by
  have : gramAt D V τ = 1 := by rw [gramAt, h.1]; simp
  rw [this]; exact Matrix.PosDef.one

end Bottom

variable {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {Fam : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D Fam Ks} {F : Face D Fam} {G : GridPre R}

theorem exists_expAt (χ : Formalism.L2.Host.HChar D.host.E) (w : Pl D.host.E) : ∃ n, GlobalTheory.CMVal.ExpAt χ w n := by
  classical
  have h := GlobalTheory.Mem.UnrAe.exists_levelLe χ w
  refine ⟨Nat.find h, fun m => ⟨fun hm => Nat.find_min' h hm, fun hm x hx hx' => Nat.find_spec h x hx (hx'.trans ?_)⟩⟩
  rw [WithZero.exp_le_exp]
  omega

theorem exists_meas (V : HSp D) : ∃ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), μ.IsHaarMeasure ∧ IsFundamentalDomain (GQ V) 𝓕 μ := by
  have := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V).1
  have : BorelSpace (GA D V) := ⟨rfl⟩
  have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (AF D.host.F) _
  have : IsTopologicalGroup (GA D V) :=
    inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  obtain ⟨𝓕, h⟩ := GlobalTheory.FundDomDiscrete.exists_fundDom D V Measure.haar inferInstance
  exact ⟨Measure.haar, 𝓕, inferInstance, h⟩

theorem exists_isWeil {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (hη : ∃ η, GlobalTheory.WeilParts.IsEtaTilde D η) (ε : Bool)
    (S W : HSp D) {χS χW : (AE D)ˣ →* Circle} (h1 : IsHeckeChar D χS) (h2 : IsHeckeChar D χW) (h3 : ResEta D χS S.rank)
    (h4 : ResEta D χW W.rank) : ∃ ω : WRep S W, IsWeil ψ ε S W χS χW ω := by
  obtain ⟨om, h⟩ := GlobalTheory.T.exists_weilDatum_of_splittingCharacters D ψ hψ (sgn ε S) W χS χW hη h1 h2 h3 h4
  exact ⟨om.comp ((ofSgn ε S).symm.toMonoidHom.prodMap (MonoidHom.id _)), h⟩

end GlobalTheory.ConstRatio

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlaceComponentArchLineComplexStructureStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.VacTransfer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPlaceComponent_archLine_complexStructure : ∀ (D : D7) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d),
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
    ∀ u u' : Matrix (Fin S.rank) (Fin d) (AE D),
      (∀ w, u'.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w)) =
        Complex.I • (Vs.θ w * u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w)) * (Ws.θ w)ᵀ)) →
    ∀ τ, compAt θ τ (GlobalTheory.VacTransfer.archLine cS u' 1) =
      cplxO ((frSgn ε A).cart τ) (B.cart τ) (compAt θ τ (GlobalTheory.VacTransfer.archLine cS u 1)) := by
  first | exact @GlobalTheory.CartanLinTransfer.compAt_archLine_cplxO | exact GlobalTheory.CartanLinTransfer.compAt_archLine_cplxO | (intros; apply GlobalTheory.CartanLinTransfer.compAt_archLine_cplxO <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexLevelSelfDualStabilizerEqProdLocal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)

noncomputable section

namespace GlobalTheory.ParIndex

theorem gram_herm (D : D7) (V : HSp D) : Formalism.UG.IsHerm (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram := by
  refine Matrix.ext fun i j => ?_
  show (D.sp.cm.sig : D.host.E →+* D.host.E) (V.gram j i) = V.gram i j
  exact V.herm.eq (V.frame j) (V.frame i)

theorem gram_det_ne (D : D7) (V : HSp D) : V.gram.det ≠ 0 :=
  ((GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).2 V).2

theorem hermitianSpace_standard_lattice_span_eq_top (D : D7) (V : HSp D) :
    Submodule.span D.host.E (L0c D V) = ⊤ := by
  let f := V.frame.equivFun.toLinearMap
  let L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := V.L0.map (f.restrictScalars (𝓞 D.host.E))
  have hL : (L : Set (Fin V.rank → D.host.E)) = L0c D V := by
    ext v
    constructor
    · rintro ⟨x, hx, rfl⟩
      change ∑ i, V.frame.equivFun x i • V.frame i ∈ V.L0
      rwa [V.frame.sum_equivFun]
    · intro hv
      refine ⟨V.frame.equivFun.symm v, ?_, V.frame.equivFun.apply_symm_apply v⟩
      rw [Module.Basis.equivFun_symm_apply]
      exact hv
  rw [← hL, eq_top_iff]
  intro v _
  obtain ⟨x, rfl⟩ := V.frame.equivFun.surjective v
  have hx : x ∈ Submodule.span D.host.E (V.L0 : Set V.V) := by
    rw [V.standardTuple_isLattice.span_eq_top]; trivial
  have := Submodule.mem_map_of_mem (f := f) hx
  rw [Submodule.map_span] at this
  exact this

theorem relIndex_levV_latLev : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (i : Fin D.R.m) (t : T) (P : LevelP R.Pg D.R.r ℂ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Hl : ∀ PP : ↥R.Pg, Subgroup (GL (Fin D.R.r) (kP PP.1))) (cl : ∀ PP : ↥R.Pg, Hl PP →* ℂˣ), GlobalTheory.Hk3.Core R F → P = LevelP.ofLocal Hl cl → (((GlobalTheory.AdelicScalar.levV R i t P m).relIndex (GlobalTheory.Mass.Levels.latLev (Vc D i)) : ℕ) : ℝ) = (∏ PP ∈ R.Pg.attach, (Nat.card (GL (Fin (Vc D i).rank) (kP PP.1)) : ℝ) / ((Nat.card (Hl PP) : ℝ) * (Nat.card (GL (Fin D.R.t) (kP PP.1)) : ℝ) * (Nat.card (kP PP.1) : ℝ) ^ (D.R.r * D.R.t))) * ∏ PP ∈ R.Q t, (Nat.card (GL (Fin (Vc D i).rank) (kP PP)) : ℝ) / ((Nat.card (GL (Fin D.R.r) (kP PP)) : ℝ) * (Nat.card (GL (Fin D.R.t) (kP PP)) : ℝ) * (Nat.card (kP PP) : ℝ) ^ (D.R.r * D.R.t)) := by
  classical
  intro D G _ _ Pl0 T A Ks _ _ _ R F i t P m Hl cl hC hP
  obtain ⟨c, hB⟩ := hC.lev.βV i
  rw [one_pow] at hB
  have hK := GlobalTheory.T.latticeLevel_eq_unitary_inf_frame_stabilizer D (Vc D i) (R.βV i) _ hB
  obtain ⟨hsplit, hdis⟩ := GlobalTheory.T.levelPlaces_union_twistPlaces_split_disjoint R F hC t
  have hspan : Submodule.span D.host.E ((R.ΛV i : Submodule (𝓞 D.host.E) _) : Set (Fin (Vc D i).rank → D.host.E)) = ⊤ := by
    rw [eq_top_iff, ← hermitianSpace_standard_lattice_span_eq_top D (Vc D i)]
    refine Submodule.span_mono fun x hx => ?_
    have := hB.2.2.2.1 x hx
    rwa [Nat.cast_one, one_smul] at this
  have hdual : dualSet (D.sp.cm.sig : D.host.E →+* D.host.E) (Vc D i).gram (R.ΛV i) = ((R.ΛV i : Submodule (𝓞 D.host.E) _) : Set (Fin (Vc D i).rank → D.host.E)) := by
    have e := Formalism.IndefR.Fin.Lifts.span_dualSet_eq (D.sp.cm.sig : D.host.E →+* D.host.E) (Vc D i).gram (R.ΛV i)
    have h := hB.2.1
    unfold Formalism.L2.Herm.dualL at h
    rw [h] at e
    exact e.symm
  have hn : (Vc D i).rank = D.R.r + D.R.t := by
    rw [D.sp.V_rank _ (Nat.le_add_left _ _) i.2]; rfl
  have hSt : ∀ x ∈ GlobalTheory.Mass.Levels.latLev (Vc D i), x ∈ Formalism.L2.DIV.St (R.βV i) := by
    intro x hx; rw [hK] at hx; exact hx.2
  set Ts := R.Pg ∪ R.Q t with hTs
  let φ : GlobalTheory.Mass.Levels.latLev (Vc D i) →* (∀ PP : ↥Ts, GL (Fin (Vc D i).rank) (kP PP.1)) :=
    { toFun := fun x PP => redFn (R.βV i) PP.1 x
      map_one' := by funext PP; exact redFn_one _
      map_mul' := fun x y => by funext PP; exact redFn_mul (hSt _ x.2) (hSt _ y.2) _ }
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨x, hx, hred⟩ := Formalism.IndefR.Fin.Lifts.redSurj_sd D.sp.cm Ts (gram_herm D (Vc D i))
      (isUnit_iff_ne_zero.2 (gram_det_ne D (Vc D i))) hspan hdual hB.1 hsplit y
    exact ⟨⟨x, by rw [hK]; exact hx⟩, funext hred⟩
  let Bl : ∀ PP : ↥Ts, Subgroup (GL (Fin (Vc D i).rank) (kP PP.1)) := fun PP =>
    if h : PP.1 ∈ R.Pg then parSub (r_le_V i) (Hl ⟨PP.1, h⟩) else blockTri (blk2 D.R.r)
  have hBp : ∀ (PP : ↥Ts) (h : PP.1 ∈ R.Pg), Bl PP = parSub (r_le_V i) (Hl ⟨PP.1, h⟩) := fun PP h => dif_pos h
  have hBn : ∀ (PP : ↥Ts), PP.1 ∉ R.Pg → Bl PP = blockTri (blk2 D.R.r) := fun PP h => dif_neg h
  have hcomap : (GlobalTheory.AdelicScalar.levV R i t P m).subgroupOf (GlobalTheory.Mass.Levels.latLev (Vc D i)) =
      (Subgroup.pi Set.univ Bl).comap φ := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_pi]
    have hxK : (x : GL (Fin (Vc D i).rank) (Lev.EAf D)) ∈ Formalism.L2.DIV.UA D.sp.cm (Vc D i).gram ⊓ Formalism.L2.DIV.St (R.βV i) := by
      rw [← hK]; exact x.2
    subst hP
    constructor
    · intro hx PP _
      have hx' := (mem_lev.1 hx)
      obtain ⟨-, -, hg, hq⟩ := mem_parLev.1 hx'.1
      show redFn (R.βV i) PP.1 x ∈ Bl PP
      by_cases h : PP.1 ∈ R.Pg
      · rw [hBp PP h]
        refine ⟨?_, ?_⟩
        · have := hg PP.1 h
          change redFn (R.βV i) PP.1 x ∈ blockTri (blkOf D.R.r D.R.t) at this
          rwa [blockTri_blkOf_eq hn] at this
        · exact hx'.2 ⟨PP.1, h⟩ (Set.mem_univ _)
      · rw [hBn PP h]
        have hQ : PP.1 ∈ R.Q t := by
          rcases Finset.mem_union.1 PP.2 with h' | h'
          · exact absurd h' h
          · exact h'
        exact hq PP.1 hQ
    · intro hx
      have hx1 : ∀ PP (h : PP ∈ Ts), redFn (R.βV i) PP x ∈ Bl ⟨PP, h⟩ := fun PP h => hx ⟨PP, h⟩ (Set.mem_univ _)
      refine mem_lev.2 ⟨mem_parLev.2 ⟨hxK.1, hxK.2, fun PP hPP => ?_, fun PP hPP => ?_⟩, ?_⟩
      · have := hx1 PP (Finset.mem_union_left _ hPP)
        rw [hBp ⟨PP, Finset.mem_union_left _ hPP⟩ hPP] at this
        show _ ∈ blockTri (blkOf D.R.r D.R.t)
        rw [blockTri_blkOf_eq hn]
        exact this.1
      · have := hx1 PP (Finset.mem_union_right _ hPP)
        by_cases h : PP ∈ R.Pg
        · rw [hBp ⟨PP, Finset.mem_union_right _ hPP⟩ h] at this
          exact this.1
        · rw [hBn ⟨PP, Finset.mem_union_right _ hPP⟩ h] at this
          exact this
      · intro PP _
        have := hx1 PP.1 (Finset.mem_union_left _ PP.2)
        rw [hBp ⟨PP.1, Finset.mem_union_left _ PP.2⟩ PP.2] at this
        exact this.2

  have hidx : (((GlobalTheory.AdelicScalar.levV R i t P m).relIndex (GlobalTheory.Mass.Levels.latLev (Vc D i)) : ℕ) : ℝ) =
      ∏ PP : ↥Ts, (((Bl PP).index : ℕ) : ℝ) := by
    rw [Subgroup.relIndex, hcomap, Subgroup.index_comap_of_surjective _ hφ, GlobalTheory.index_pi_univ_dep, Nat.cast_prod]
  let g : Pl D.host.E → ℝ := fun PP =>
    if h : PP ∈ R.Pg then (Nat.card (GL (Fin (Vc D i).rank) (kP PP)) : ℝ) / ((Nat.card (Hl ⟨PP, h⟩) : ℝ) *
      (Nat.card (GL (Fin D.R.t) (kP PP)) : ℝ) * (Nat.card (kP PP) : ℝ) ^ (D.R.r * D.R.t))
    else (Nat.card (GL (Fin (Vc D i).rank) (kP PP)) : ℝ) / ((Nat.card (GL (Fin D.R.r) (kP PP)) : ℝ) *
      (Nat.card (GL (Fin D.R.t) (kP PP)) : ℝ) * (Nat.card (kP PP) : ℝ) ^ (D.R.r * D.R.t))
  have hloc : ∀ PP : ↥Ts, (((Bl PP).index : ℕ) : ℝ) = g PP.1 := by
    intro PP
    haveI : PP.1.asIdeal.IsMaximal := PP.1.isMaximal
    letI : Field (kP PP.1) := Ideal.Quotient.field _
    have hc := Subgroup.card_mul_index (Bl PP)
    have hpos : (Nat.card (Bl PP) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.card_pos (α := Bl PP)).ne'
    have e1 : (((Bl PP).index : ℕ) : ℝ) = (Nat.card (GL (Fin (Vc D i).rank) (kP PP.1)) : ℝ) / (Nat.card (Bl PP) : ℝ) := by
      rw [eq_div_iff hpos, mul_comm]
      exact_mod_cast hc
    rw [e1]
    by_cases h : PP.1 ∈ R.Pg
    · have e2 : Bl PP = parSub (r_le_V i) (Hl ⟨PP.1, h⟩) := hBp PP h
      simp only [g, dif_pos h]
      rw [e2, GlobalTheory.T.card_blockUpperTriangularSubgroupOfTopBlock (kP PP.1) _ _ _ (r_le_V i) hn]
      push_cast; ring
    · have e2 : Bl PP = parSub (r_le_V i) ⊤ := by
        rw [hBn PP h]
        ext x
        simp [mem_parSub]
      simp only [g, dif_neg h]
      rw [e2, GlobalTheory.T.card_blockUpperTriangularSubgroupOfTopBlock (kP PP.1) _ _ _ (r_le_V i) hn, Subgroup.card_top]
      push_cast; ring
  rw [hidx, Finset.prod_congr rfl (fun PP _ => hloc PP), Finset.prod_coe_sort Ts g, hTs, Finset.prod_union hdis]
  congr 1
  · rw [← Finset.prod_attach R.Pg g]
    refine Finset.prod_congr rfl fun PP _ => ?_
    simp only [g, dif_pos PP.2]
  · refine Finset.prod_congr rfl fun PP hPP => ?_
    have h : PP ∉ R.Pg := Finset.disjoint_right.1 hdis hPP
    simp only [g, dif_neg h]

end GlobalTheory.ParIndex

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestChoiceDatumSurjective
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open GlobalTheory.FunObj

namespace GlobalTheory.ChoiceSurjectivity

theorem choice_phi_surj : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ∀ (ch : Choice R), ch.Is → ∀ (Φ : ch.G.Datum), ∃ a, ch.Phi a = Φ := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R large₂ F _ ch _ Φ
  obtain ⟨i⟩ := GlobalTheory.TestLat.SlopeModel.nonempty_idx (LaP ch.G)
  refine ⟨ch.e.symm ((Φ, Quotient.mk'' 1), i), ?_⟩
  simp [Choice.Phi, datumOf]

end GlobalTheory.ChoiceSurjectivity
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestLiftFormulaPrincipalLevelStatement
section
open GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowTestLiftFormula_principalLevel : StepProj → StepFlip → StepUnfold → StepJets → ConstK → SumOKK → Formula2K := by
  first | exact @GlobalTheory.RowClaim.FormulaTwo.formula2K | exact GlobalTheory.RowClaim.FormulaTwo.formula2K | (intros; apply GlobalTheory.RowClaim.FormulaTwo.formula2K <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScaledLatticeCompletionSupportedInvIdealSmulStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scaledLatticeCompletion_supported_invIdeal_smul : ∀ {D : D7} (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (I : GlobalTheory.SeeSaw.FI D) (v : GlobalTheory.FinPl.Pl D) (y : Fin S.rank → AE D), y ∈ GlobalTheory.FinPl.latMul S {a | a ∈ I} L (· = v) → (∀ i, y i ∈ idAt D (· = v)) ∧ ∀ s ∈ GlobalTheory.SeeSaw.idV I⁻¹ v, s • y ∈ latV S L (· = v) := by
  first | exact @GlobalTheory.LatMulAt.latMul_inv_smul | exact GlobalTheory.LatMulAt.latMul_inv_smul | (intros; apply GlobalTheory.LatMulAt.latMul_inv_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StandardCharSeparatesIntegralFiniteAdelesStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardChar_separates_integralFiniteAdeles : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ →
    ∀ b : FiniteAdeleRing (𝓞 F) F, ¬ (∀ v : HeightOneSpectrum (𝓞 F), b v ∈ v.adicCompletionIntegers F) →
    ∃ s : F, ψ (((0 : InfiniteAdeleRing F), b * algebraMap F (FiniteAdeleRing (𝓞 F) F) s) : AF F) ≠ 1 ∧
      ∀ w : FiniteAdeleRing (𝓞 F) F, (∀ v : HeightOneSpectrum (𝓞 F), w v ∈ v.adicCompletionIntegers F) →
        ψ (((0 : InfiniteAdeleRing F), w * algebraMap F (FiniteAdeleRing (𝓞 F) F) s) : AF F) = 1 := by
  first | exact @GlobalTheory.StdCharSep.exists_sep | exact GlobalTheory.StdCharSep.exists_sep | (intros; apply GlobalTheory.StdCharSep.exists_sep <;> assumption)
end

