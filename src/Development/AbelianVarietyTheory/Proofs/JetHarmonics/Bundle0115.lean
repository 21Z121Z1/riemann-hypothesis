import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0112
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0038
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0011
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ImagQuadraticMaximalOrderArithmeticAtSplitPrime
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0021
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UwEllipticFlow
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0108
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0110
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0113
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointsLiftToLevelCover
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsLevMoveOfFrOver
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointMoveCalculus

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntegralTypesAndDirectionsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_types_and_directions' : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y) (ϖ : T.V), Irreducible ϖ → ∀ (g : ℕ), g.Prime → ¬ IsUnit ((g : ℕ) : T.V) → (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).card = Module.finrank ℚ E → (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).Nodup → ∀ (F : Type) [Field F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → letI := io.toAlgebra; ∃ (σ : (E →+* ℂ) → 𝓞 E →+* TWO.Ov v) (e : Lt1 Dw → Fin (chD C.ch) → TWO.Ov v), (∀ τ a, (σ τ a : F) = algebraMap T.Fr F (io (embK c τ a))) ∧ (∀ ℓ i, (e ℓ i : F) = algebraMap T.V F (C.uvecT ℓ i)) ∧ (∀ ℓ i, (e ℓ i : F) = algebraMap T.Fr F (C.ch.uvec ℓ i)) ∧ (∀ (a : 𝓞 E) ℓ, (dAct F C.ch.B a).mulVec (fun i => (e ℓ i : F)) = (σ ℓ.1 a : F) • fun i => (e ℓ i : F)) ∧ (∀ τ a, (0 < v (σ τ a : F) → σ τ a ∈ Ideal.span {((g : ℕ) : TWO.Ov v)}) ∧ (¬ 0 < v (σ τ a : F) → IsUnit (σ τ a))) ∧ (∀ τ a, σ (ComplexEmbedding.conjugate τ) a = σ τ (star a)) ∧ (open Classical in ∃ lam : Lt1 Dw → Fin (chD C.ch) → TWO.Ov v, ∀ l l', ∑ s, lam l s * e l' s = if l = l' then 1 else 0) ∧ (open Classical in ∃ ε : (E →+* ℂ) → 𝓞 E, ∀ τ τ', σ τ' (ε τ) - (if τ = τ' then 1 else 0) ∈ Ideal.span {((g : ℕ) : TWO.Ov v)}) ∧ ¬ IsUnit ((g : ℕ) : TWO.Ov v) := by
  first | exact @GlobalTheory.PowGerm.exists_integral_types_and_directions | exact GlobalTheory.PowGerm.exists_integral_types_and_directions | (intros; apply GlobalTheory.PowGerm.exists_integral_types_and_directions <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FamilySetupCayleyRecursionStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.family_setup_cayley_recursion : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ) (Q : Mx k r) (E : ∀ ν, Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (R ν).smSub), Setup lam u b bv ga h q0 z π μW μN μG νq R l dg → PI.UpqRep.IsCayleyU k r (PI.BesselPeriodGGP.eps48 k r) Q → (∀ ν, n1 ν ≤ q0 → (R ν).IsE Q (E ν) ∧ Formalism.REAL.GlRel (E ν)) → ∀ (q : ℕ) ν, n1 ν + q ≤ q0 → ∀ j : ℕ, j + 2 * q ≤ 4 * (2 * r + k + 1) ^ 2 → ∀ w : (R ν).smSub, Lev (PI.BesselPeriodGGP.eps48 k r) (E ν) (fun a => lam a + ((ν : Fin (2 * r + k + 1) → ℤ) a : ℝ)) j w → ∫⁻ x, ENNReal.ofReal (lenA k r z (Matrix.of x) 0 ^ (2 * q) * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal ((((2 * r + k + 1) : ℝ) ^ 2 * (Formalism.QuantumDeterminants.Tz k r z * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2))) ^ q * ‖w‖ ^ 2) := by
  first | exact @GlobalTheory.Moment.moment_first_length | exact GlobalTheory.Moment.moment_first_length | (intros; apply GlobalTheory.Moment.moment_first_length <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormPlus
section
noncomputable section

namespace GlobalTheory.ShortMove

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct

def Marked {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} (V : HSp D) {r : ℕ} (hr : V.rank = r)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (l : Level H)
    (Λ : Submodule (𝓞 D.host.E) (Fin r → D.host.E)) (mk : Dw.La → (Fin r → D.host.E)) (h : GA D V) : Prop :=
  (Λ : Set (Fin r → D.host.E)) =
      (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast hr.symm) '' (latG V h : Set _) ∧
    ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ w ∈ latGHat V h, finVec V (mk a ∘ Fin.cast hr) - (finHom V h).1.mulVec (finVec V (io a)) = (l.M : ℕ) • w

attribute [local instance] Formalism.BasicNotions.Host.cmStar in

def FormPlus {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} (V : HSp D)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) : Prop :=
  ∀ x y, ((Dw.EF x y : ℤ) : ℚ) =
    Algebra.trace ℚ D.host.E (D.host.xi0 * V.hT (V.frame.equivFun.symm (io x)) (V.frame.equivFun.symm (io y)))

end GlobalTheory.ShortMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HeightOneOfSplit
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne

private theorem norm_zc_eq {q : ℕ} [Fact q.Prime] (a : ℤ_[q]) : ‖zc a‖ = ‖a‖ := by
  unfold zc
  exact (PadicComplex.norm_extends' (p := q) (a : ℚ_[q])).trans (PadicInt.norm_def).symm

private theorem zc_natCast_eq {q : ℕ} [Fact q.Prime] (n : ℕ) : zc (n : ℤ_[q]) = (n : ℂ_[q]) := by
  simp [zc]

theorem height_one_of_split : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (F : FormalGroup 𝓞_ℂ_[q]), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.Ok → MvPowerSeries.subst (![PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[q]) (PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u)), PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[q]) (PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u))] : Fin 2 → MvPowerSeries (Fin 2) ℂ_[q]) (MvPowerSeries.map (algebraMap 𝓞_ℂ_[q] ℂ_[q]) F.toPowerSeries) = PowerSeries.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[q]) (PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u)) → ∃ ℓ : ℂ_[q]⟦X⟧, constantCoeff ℓ = 0 ∧ PowerSeries.subst ℓ (PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u)) = X ∧ ‖coeff q (PowerSeries.subst (C (q : ℂ_[q]) * ℓ) (PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u)))‖ = 1 ∧ ∀ k < q, ‖coeff k (PowerSeries.subst (C (q : ℂ_[q]) * ℓ) (PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u)))‖ < 1 := by
  intro d q _ M F hd hd16 hs hOK hM hF
  set U : ℂ_[q]⟦X⟧ := PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u) with hUdef
  have flow := uw_elliptic_flow q M hM
  have hU0 : constantCoeff U = 0 := by
    rw [hUdef, ← coeff_zero_eq_constantCoeff_apply, coeff_map, tay, coeff_mk]
    simp [flow.2.2.2.2.1]

  obtain ⟨ℓ, hchart, hℓX⟩ := Basic.exists_chart M hM
  have hℓ0 : constantCoeff ℓ = 0 := hchart.2.1
  have hUℓ : U.subst ℓ = X := hℓX
  obtain ⟨P1, P2, P3⟩ := GlobalTheory.T.formalGroup_padicMul_integral_vanishingOrder q F U ℓ hU0 hℓ0 hUℓ hF
  refine ⟨ℓ, hℓ0, hUℓ, ?_, ?_⟩
  ·

    have hle : ‖coeff q (U.subst (C (q : ℂ_[q]) * ℓ))‖ ≤ 1 := by
      have := P1 (q : ℤ_[q])
      rw [zc_natCast_eq] at this
      exact this q
    refine le_antisymm hle (not_lt.1 fun hlt => ?_)
    have P3' := P3 hlt
    set k : ℕ := d + 3 with hk
    obtain ⟨β, N, hβ, hβ0, hβn, hN, hNle⟩ := exists_small_in_prime_pow d q M.ι hd hd16 hs k
    have ar := okArith d q M.ι hd hd16 hs
    obtain ⟨a, ha⟩ := (ar.2.1 β hβ).1
    have hanorm : ‖a‖ ≤ (q : ℝ) ^ (-(k : ℤ)) := by
      rw [← norm_zc_eq, ← ha]
      exact hβn
    have hlat : ∀ l ∈ M.L.lattice, β * l ∈ M.L.lattice := by
      intro l hl
      rw [hOK] at hl ⊢
      exact (ar.1.2.2 β l hβ hl).2.1
    have hu0 : AnalyticAt ℂ M.u 0 := (flow.2.2.2.2.2.2.2.2 0 (Or.inl ((hOK 0).2 ⟨0, 0, by simp⟩))).1
    have hhat : hat M.ι ℓ (fun z => M.u (β * z)) = U.subst (C (zc a) * ℓ) := by
      rw [(TaylorRead.hat_laws q M.ι ℓ hℓ0).2.2.2.2.2.1 M.u β hu0, ← ha]
      rfl
    have hbd : Bd 1 (hat M.ι ℓ (fun z => M.u (β * z))) := by
      rw [hhat]
      exact P1 a
    obtain ⟨n, hnN, hn1⟩ := GlobalTheory.T.exists_unit_coeff_mul_series_le_norm q M ℓ β N hchart hβ0 hlat hN hbd
    have hnlt : n < (2 * q) ^ k := by
      have hq : 0 < q ^ k := pow_pos (Fact.out : q.Prime).pos k
      have h2 : d + 3 < 2 ^ k := Nat.lt_two_pow_self
      calc n ≤ N := hnN
        _ ≤ (d + 3) * q ^ k := hNle
        _ < 2 ^ k * q ^ k := Nat.mul_lt_mul_of_pos_right h2 hq
        _ = (2 * q) ^ k := (mul_pow 2 q k).symm
    have := P3' k a hanorm n hnlt
    rw [← hhat, hn1] at this
    exact lt_irrefl _ this
  · intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · have hc : constantCoeff (C (q : ℂ_[q]) * ℓ) = 0 := by simp [hℓ0]
      rw [coeff_zero_eq_constantCoeff_apply, TaylorRead.constantCoeff_subst_of hc, hU0, norm_zero]
      exact one_pos
    · exact P2 k (Nat.not_dvd_of_pos_of_lt hkpos hk)

end GlobalTheory.MomOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.JetsOnCopiesOfCompatibleFramesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jets_on_copies_of_compatible_frames : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → JetsOnCopiesCompatibleFrames := by
  first | exact @GlobalTheory.PowJets.jets_on_copies | exact GlobalTheory.PowJets.jets_on_copies | (intros; apply GlobalTheory.PowJets.jets_on_copies <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LiesOverFramedOfSquareLevelMoves
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace OverSquare

open FrameLift OverMove

theorem rel_square {A A₂ Y Y' Y₂ Y₂' : Scheme.{0}} {L : LB A} {L₂ : LB A₂} (hL : L.IsLB) (hL₂ : L₂.IsLB)
    {φ φ' : A₂ ⟶ A} {ν : A ⟶ A} {ν₂ : A₂ ⟶ A₂} (hφ : ν₂ ≫ φ' = φ ≫ ν)
    {w₀ : LB.Iso L₂ (L.pull φ)} {w' : LB.Iso L₂ (L.pull φ')} {w : LB.Iso L (L.pull ν)} {w₂ : LB.Iso L₂ (L₂.pull ν₂)}
    (hw : ∀ (Z : Scheme.{0}) (f : Z ⟶ A₂) (z : Z) i k j l, ν (φ (f z)) ∈ L.U i → φ (f z) ∈ L.U k →
      ν₂ (f z) ∈ L₂.U j → f z ∈ L₂.U l →
      gw w (f ≫ φ) z i k * gw w₀ f z k l = gw w' (f ≫ ν₂) z i j * gw w₂ f z j l)
    {q : Y ⟶ A} {q' : Y' ⟶ A} {q₂ : Y₂ ⟶ A₂} {q₂' : Y₂' ⟶ A₂} {p : Y₂ ⟶ Y} {p' : Y₂' ⟶ Y'} {pm : Y ⟶ Y'}
    {pm₂ : Y₂ ⟶ Y₂'} {σ : Y₂' ⟶ Y₂} (hσ : σ ≫ pm₂ = 𝟙 _) (hp : p ≫ q = q₂ ≫ φ) (h₂ : pm₂ ≫ q₂' = q₂ ≫ ν₂)
    (sq : pm₂ ≫ p' = p ≫ pm) {s : LB.Sec (LOne L q)} {s' : LB.Sec (LOne L q')} {s₂ : LB.Sec (LOne L₂ q₂)}
    {s₂' : LB.Sec (LOne L₂ q₂')} (H₀ : Rel w₀ p s₂ s) (H : Rel w pm s s') (H₂ : Rel w₂ pm₂ s₂ s₂') :
    Rel w' p' s₂' s' := by
  intro Z r z i j hi hj
  obtain ⟨r₀, rfl⟩ : ∃ r₀ : Z ⟶ Y₂, r = r₀ ≫ pm₂ := ⟨r ≫ σ, by rw [Category.assoc, hσ, Category.comp_id]⟩
  obtain ⟨k, hk⟩ := exists_chart hL (φ (q₂ (r₀ z)))
  obtain ⟨l, hl⟩ := exists_chart hL₂ (q₂ (r₀ z))
  have e₂ : q₂' (pm₂ (r₀ z)) = ν₂ (q₂ (r₀ z)) := pt_eq h₂ (r₀ z)
  have e₁ : q (p (r₀ z)) = φ (q₂ (r₀ z)) := pt_eq hp (r₀ z)
  have e₀ : φ' (ν₂ (q₂ (r₀ z))) = ν (φ (q₂ (r₀ z))) := pt_eq hφ (q₂ (r₀ z))
  have hj' : ν₂ (q₂ (r₀ z)) ∈ L₂.U j := e₂ ▸ (show q₂' (pm₂ (r₀ z)) ∈ L₂.U j from hj)
  have hi' : ν (φ (q₂ (r₀ z))) ∈ L.U i := by
    have : φ' (q₂' (pm₂ (r₀ z))) ∈ L.U i := hi
    rwa [e₂, e₀] at this
  have a := H Z (r₀ ≫ p) z i k (by show ν (q (p (r₀ z))) ∈ _; rw [e₁]; exact hi')
    (by show q (p (r₀ z)) ∈ _; rw [e₁]; exact hk)
  have b := H₀ Z r₀ z k l hk hl
  have c := H₂ Z r₀ z j l hj' hl
  have e := hw Z (r₀ ≫ q₂) z i k j l hi' hk hj' hl
  rw [Category.assoc r₀ pm₂ p', sq, ← Category.assoc r₀ p pm, a, b, c, ← _root_.mul_assoc, ← _root_.mul_assoc,
    ← Units.val_mul, ← Units.val_mul, Category.assoc r₀ p q, hp, ← Category.assoc r₀ q₂ φ, e,
    Category.assoc r₀ pm₂ q₂', h₂, Category.assoc r₀ q₂ ν₂]

theorem gw_square {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {S S₂ : Scheme.{0}} {t : SAB H S} {t₂ : SAB H S₂} {r r' : S₂ ⟶ S} {ρ : S ⟶ S} {ρ₂ : S₂ ⟶ S₂}
    (hu : Function.Surjective t₂.G.hom.appTop.hom)
    (m : SABMap t₂ t r) (m' : SABMap t₂ t r') (ν : SABMap t t ρ) (ν₂ : SABMap t₂ t₂ ρ₂)
    (hr : ρ₂ ≫ r' = r ≫ ρ) (hφ : ν₂.φ ≫ m'.φ = m.φ ≫ ν.φ)
    {w₀ : LB.Iso t₂.PP.L (t.PP.L.pull m.φ)} {w' : LB.Iso t₂.PP.L (t.PP.L.pull m'.φ)}
    {w : LB.Iso t.PP.L (t.PP.L.pull ν.φ)} {w₂ : LB.Iso t₂.PP.L (t₂.PP.L.pull ν₂.φ)}
    (h₀ : OverMove.RigIso m w₀) (h' : OverMove.RigIso m' w') (h : OverMove.RigIso ν w) (h₂ : OverMove.RigIso ν₂ w₂)
    (Z : Scheme.{0}) (f : Z ⟶ t₂.G.left) (z : Z) (i k : t.PP.L.ι) (j l : t₂.PP.L.ι)
    (hi : ν.φ (m.φ (f z)) ∈ t.PP.L.U i) (hk : m.φ (f z) ∈ t.PP.L.U k) (hj : ν₂.φ (f z) ∈ t₂.PP.L.U j)
    (hl : f z ∈ t₂.PP.L.U l) :
    gw w (f ≫ m.φ) z i k * gw w₀ f z k l = gw w' (f ≫ ν₂.φ) z i j * gw w₂ f z j l := by
  obtain ⟨a, Ta⟩ := exists_comp t.PP.isLB w w₀ h.1 h₀.1 t.PP.isLB t₂.PP.isLB
  obtain ⟨b, Tb⟩ := exists_comp t₂.PP.isLB w' w₂ h'.1 h₂.1 t.PP.isLB t₂.PP.isLB
  have ga := Ta.pgen_comp t.PP.isLB h.1 h₀.1
  have ra := Ta.pmaps_comp t.PP.isLB (fun _ => m.cm.e_comm) h.2 h₀.2
  have gb := Tb.pgen_comp t₂.PP.isLB h'.1 h₂.1
  have rb := Tb.pmaps_comp t₂.PP.isLB (fun _ => ν₂.cm.e_comm) h'.2 h₂.2
  have e := gw_eq_of_pmaps (S := S₂) (S₀ := S) t.PP.isLB t₂.PP.isLB t₂.G.hom (eSec t₂.G) (Over.w η[t₂.G]) hu
    hφ.symm ga gb (h₁ := m.cm.e ≫ ν.cm.e) (h₂ := ν₂.cm.e ≫ m'.cm.e)
    (by rw [m.base, m'.base, ν.base, ν₂.base]; exact hr.symm) ra rb f z i l
  have hi' : m'.φ (ν₂.φ (f z)) ∈ t.PP.L.U i :=
    (congrArg (· ∈ t.PP.L.U i) (pt_eq hφ (f z))).mpr hi
  exact (Ta Z f z i k l hi hk hl).symm.trans (e.trans (Tb Z f z i j l hi' hj hl))

end OverSquare

open FrameLift OverMove OverSquare in

theorem frOver_of_square_of_frMove : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (ρ₂ : d.Xo₂.X ⟶ d.Xo₂.X) (ν₂ : SABMap d.Xo₂.univ.t d.Xo₂.univ.t ρ₂) (r' : d.Xo₂.X ⟶ Xo.X) (m' : SABMap d.Xo₂.univ.t Xo.univ.t r'), ρ₂ ≫ r' = d.r ≫ ρ → ν₂.φ ≫ m'.φ = d.m.φ ≫ ν.φ → ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra d.c₂.F S] (y y' : FrPt Xo c S) (y₂ y₂' : FrPt d.Xo₂ d.c₂ S), FrOver d y₂ y → FrMove ρ ν y y' → FrMove ρ₂ ν₂ y₂ y₂' → FrOver { d with r := r', m := m' } y₂' y' := by
  intro E _ _ _ H Dw l Xo c n d ρ ν ρ₂ ν₂ r' m' hr hφ S _ _ _ y y' y₂ y₂' h hy hy₂
  obtain ⟨e, hu, w₀, p, hw₀, p₁, p₂, H₀⟩ := (frOver_iff d _ _).1 h
  obtain ⟨ex, eu, pm, w, a₁, a₂, hw, H₁⟩ := MoveCalc.frMove_iff_carry.1 hy
  obtain ⟨ex₂, eu₂, pm₂, w₂, b₁, b₂, hw₂, H₂⟩ := MoveCalc.frMove_iff_carry.1 hy₂
  obtain ⟨w', g', r₁', -⟩ := m'.lin
  have e' : y₂'.x ≫ r' = y'.x := by rw [ex₂, ex, Category.assoc, hr, ← Category.assoc, e]
  obtain ⟨p', -, p₁', p₂', -⟩ := exists_pm_iso m' e'
  obtain ⟨σ, hσ⟩ := MoveCalc.exists_section ν₂ ex₂ b₁ b₂
  have sq : pm₂ ≫ p' = p ≫ pm := by
    refine pm_ext ?_ ?_
    · rw [Category.assoc, p₁', ← Category.assoc, b₂, Category.assoc, hφ, Category.assoc, a₂, ← Category.assoc p, p₁,
        Category.assoc]
    · rw [Category.assoc, p₂', b₁, Category.assoc, a₁, p₂]
  have hs : Function.Surjective d.Xo₂.univ.t.G.hom.appTop.hom := (GlobalTheory.globalFns_holds _ _
    ⟨d.Xo₂.univ.t.semi.comm, d.Xo₂.univ.t.semi.smooth, d.Xo₂.univ.proper, d.Xo₂.univ.t.semi.geomConnected⟩).2
  refine (frOver_iff { d with r := r', m := m' } y₂' y').2 ⟨e', fun τ i => ?_, w', p', ⟨g', r₁'⟩, p₁', p₂', ?_⟩
  · show y₂'.u τ i ≫ m'.φ = y'.u τ i
    rw [eu₂, eu, Category.assoc, hφ, ← Category.assoc, hu]
  · exact rel_square Xo.univ.t.PP.isLB d.Xo₂.univ.t.PP.isLB hφ
      (gw_square hs d.m m' ν ν₂ hr hφ (rigIso_of d.m hw₀.1 hw₀.2) (rigIso_of m' g' r₁') (rigIso_of ν hw.1 hw.2.1)
        (rigIso_of ν₂ hw₂.1 hw₂.2.1)) hσ p₁ b₂ sq H₀ H₁ H₂

end GlobalTheory
end
end

