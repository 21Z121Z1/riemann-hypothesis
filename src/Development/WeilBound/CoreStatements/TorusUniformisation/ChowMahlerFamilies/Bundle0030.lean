import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0010
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0258
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.KappaIntegralBound
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0074
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0077

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.LineFunctionPlaceValuation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

namespace PositivityTheory.Xgn.PlaceValuation

theorem exists_place {K : Type} [Field K] [NumberField K] (p : Nat.Primes) (κ : K →+* ℂ_[p]) :
    ∃ la : HeightOneSpectrum (𝓞 K), ∀ a : K, la.valuation K a ≤ 1 ↔ ‖κ a‖ ≤ 1 :=
  _root_.Bl.KappaIntegralBound.goal1 p κ

theorem place_unique {K : Type} [Field K] [NumberField K] {p : Nat.Primes} {κ : K →+* ℂ_[p]}
    {la la' : HeightOneSpectrum (𝓞 K)} (h : ∀ a : K, la.valuation K a ≤ 1 ↔ ‖κ a‖ ≤ 1)
    (h' : ∀ a : K, la'.valuation K a ≤ 1 ↔ ‖κ a‖ ≤ 1) : la = la' :=
  HeightOneSpectrum.eq_of_valuation_isEquiv_valuation (K := K)
    (Valuation.isEquiv_iff_val_le_one.2 fun {a} => (h a).trans (h' a).symm)

theorem log_norm_ne_zero {K : Type} [Field K] [NumberField K] {p : Nat.Primes} {κ : K →+* ℂ_[p]}
    {la : HeightOneSpectrum (𝓞 K)} (h : ∀ a : K, la.valuation K a ≤ 1 ↔ ‖κ a‖ ≤ 1) {π : K}
    (hπ : la.valuation K π = WithZero.exp (-1 : ℤ)) : Real.log ‖κ π‖ ≠ 0 := by
  have h1 : ¬ la.valuation K π⁻¹ ≤ 1 := by
    rw [map_inv₀, hπ, ← WithZero.exp_neg, ← WithZero.exp_zero, WithZero.exp_le_exp]
    norm_num
  rw [h, map_inv₀, norm_inv, not_le] at h1
  have := Real.log_pos h1
  rw [Real.log_inv] at this
  linarith

end PositivityTheory.Xgn.PlaceValuation

theorem PositivityTheory.Xgn.line_function_place_valuation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) [NumberField c.F] (Z : Formalism.L2.Pj.Comp Xo c) (τ : GlobalTheory.AllWt.Psi H) (s : Formalism.L2.Pj.Rul Xo c) (φ : FrameFn Xo c) (ρ : HeightOneSpectrum (𝓞 c.F) → ℝ), IsLineFn (Z : Set (Xo.XF c)) τ.1 φ → Reads (Z : Set (Xo.XF c)) τ.1 s φ → (∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]) (la : HeightOneSpectrum (𝓞 c.F)) (π : c.F), (∀ a : c.F, la.valuation c.F a ≤ 1 ↔ ‖κ a‖ ≤ 1) → la.valuation c.F π = WithZero.exp (-1 : ℤ) → HasFinNorm (Z : Set (Xo.XF c)) τ.1 φ p κ (ρ la * Real.log ‖κ π‖)) → ∀ la, ∀ v ∈ GlobalTheory.FlatLine.valOn Z la, v s = (ρ la : EReal) := by
  intro E _ _ _ H D l Xo c _ Z τ s φ ρ hφ hs hN la v hv
  choose pl hpl using fun (p : Nat.Primes) (κ : c.F →+* ℂ_[p]) => PositivityTheory.Xgn.PlaceValuation.exists_place p κ
  choose un hun using fun la : HeightOneSpectrum (𝓞 c.F) => la.valuation_exists_uniformizer c.F
  obtain ⟨⟨_, T, io, e, ho, y, hy, eta, -, rfl⟩, rfl⟩ := hv
  letI := io.toAlgebra
  obtain ⟨p, κ, hκ, hval⟩ := GlobalTheory.CompanionTheory.Ar.Flat.nval_flat_rule E H D l Xo c (Z : Set (Xo.XF c)) τ.1 φ s
    (fun p κ => ρ (pl p κ) * Real.log ‖κ (un (pl p κ))‖) τ.2 hφ hs
    (fun p κ => hN p κ (pl p κ) _ (hpl p κ) (hun _)) la T io e y (GlobalTheory.AllWt.ptF y.1) ho hy.1
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) (by rintro _ ⟨x, rfl⟩; exact hy.2 x)
  have hla : pl p κ = la := PositivityTheory.Xgn.PlaceValuation.place_unique (hpl p κ) hκ
  refine (hval (un la) (hun la)).trans ?_
  rw [hla, mul_div_assoc, div_self (PositivityTheory.Xgn.PlaceValuation.log_norm_ne_zero hκ (hun la)), _root_.mul_one]
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XXgzChowMahlerFibrefactor
section
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

namespace PositivityTheory.Xgn.A_xgz_chow_mahler_fibrefactor

theorem pair_eq {n : ℕ} (h : HermNorm n) (p : Fin n → ℂ) (y : EuclideanSpace ℂ (Fin n)) :
    ∑ j, ((h.mat)⁻¹ *ᵥ p) j * h.pointOf y j = ∑ j, p j * y j := by
  have h1 : ((h.mat)⁻¹ *ᵥ p) ⬝ᵥ (h.matᵀ *ᵥ fun i => y i) = p ⬝ᵥ fun i => y i := by
    rw [Matrix.mulVec_transpose, dotProduct_comm, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ h.isUnit_det, Matrix.one_mulVec, dotProduct_comm]
  exact h1

theorem pointOf_inj {n : ℕ} (h : HermNorm n) : Function.Injective h.pointOf := by
  intro y y' hy
  ext i
  have h1 := pair_eq h (Pi.single i 1) y
  have h2 := pair_eq h (Pi.single i 1) y'
  rw [hy, h2] at h1
  simpa [Pi.single_apply] using h1.symm

theorem row_zero {n e : ℕ} {S : Set (EuclideanSpace ℂ (Fin n))} {π : Fin (e + 1) → Fin n → ℂ}
    {y : EuclideanSpace ℂ (Fin n)} (hy : y ∈ fibrePts S π) : ∑ j, π 0 j * y j = 1 := by
  have h1 : linProj π y 0 = firstCoordVec (e + 1) 0 := by rw [hy.2]
  simpa [linProj, firstCoordVec] using h1

theorem row_succ {n e : ℕ} {S : Set (EuclideanSpace ℂ (Fin n))} {π : Fin (e + 1) → Fin n → ℂ}
    {y : EuclideanSpace ℂ (Fin n)} (hy : y ∈ fibrePts S π) (i : Fin e) :
    ∑ j, π i.succ j * y j = 0 := by
  have h1 : linProj π y i.succ = firstCoordVec (e + 1) i.succ := by rw [hy.2]
  simpa [linProj, firstCoordVec] using h1

end PositivityTheory.Xgn.A_xgz_chow_mahler_fibrefactor

open PositivityTheory.Xgn.A_xgz_chow_mahler_fibrefactor in
theorem PositivityTheory.Xgn.t_xgz_chow_mahler_fibrefactor : ∀ (n e δ : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
  (g : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (π : Fin (e + 1) → Fin n → ℂ) (u₀ : Fin n → ℂ),
  IsProjPrime W → IsChowForm W (e + 1) g → IsMultiHomog δ g →
  (fibrePts (coneSet h W) π).encard = δ →
  eval (consGroup u₀ (nrmGroups h e (coefRows h π))) g ≠ 0 →
    ∃ c : ℂ, c ≠ 0 ∧ ∀ u : Fin n → ℂ, eval (consGroup u (nrmGroups h e (coefRows h π))) g =
      c * ∏ᶠ y ∈ fibrePts (coneSet h W) π, ∑ j, u j * h.pointOf y j := by
  classical
  intro n e δ h W g π u₀ _ hch hmh hcard hne
  have hfin : (fibrePts (coneSet h W) π).Finite := Set.finite_of_encard_eq_coe hcard
  have hc : hfin.toFinset.card = δ := by
    have h1 := hfin.encard_eq_coe_toFinset_card
    rw [hcard] at h1
    exact_mod_cast h1.symm
  have hone : ∀ y ∈ fibrePts (coneSet h W) π,
      ∑ j, ((h.mat)⁻¹ *ᵥ π 0) j * h.pointOf y j = 1 := fun y hy => by
    rw [pair_eq, row_zero hy]
  obtain ⟨c, hc0, hcu⟩ := GlobalTheory.T.chow_form_specialization_proportional n e δ W g (nrmGroups h e (coefRows h π))
    (hfin.toFinset.image h.pointOf) u₀ hch hmh
    (by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      rw [Set.Finite.mem_toFinset] at hy
      refine ⟨fun h0 => ?_, hy.1, fun i => ?_⟩
      · have h1 := hone y hy
        rw [h0] at h1
        simp at h1
      · have h1 := pair_eq h (π i.succ) y
        rw [row_succ hy] at h1
        simp only [nrmGroups, coefRows, mul_assoc]
        rw [← Finset.mul_sum, h1, mul_zero])
    (by
      intro x hx x' hx' t ht
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hx'
      rw [Set.Finite.mem_toFinset] at hy hy'
      have h1 := hone y hy
      have h2 := hone y' hy'
      rw [ht] at h2
      simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm _ t] at h2
      rw [← Finset.mul_sum, h1, mul_one] at h2
      rw [ht, h2, one_smul])
    (by rw [Finset.card_image_of_injective _ (pointOf_inj h), hc]) hne
  refine ⟨c, hc0, fun u => ?_⟩
  rw [hcu u, Finset.prod_image (fun a _ b _ hab => pointOf_inj h hab),
    finprod_mem_eq_finite_toFinset_prod _ hfin]
end

