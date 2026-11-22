import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2212
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2243
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfAcyclic
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SubsingletonOfSheafPullback
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0025
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0001
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CechTwistNonzeroLocusMaps
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2403
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0252
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2435

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CohomologyVanishingNonzeroLocus
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false
noncomputable section
namespace GlobalTheory

theorem isZero_cechH_nonzeroLocus_of_eventually_twist : ∀ (X : Scheme.{0}) (F : X.Modules) [F.IsQuasicoherent] (L : LB X), L.IsLB → ∀ (σ : L.Sec)
    {ι : Type} [LinearOrder ι] [Fintype ι] (U : ι → X.Opens),
    (∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i)) → ∀ n : ℕ,
    (∀ᶠ c : ℕ in atTop, IsZero (cechH ℤ (twistZ F L c) ⊤ U n)) → IsZero (cechH ℤ F (nonzeroLocus σ) U n) := by
  intro X F _ L hL σ ι _ _ U hU n h
  obtain ⟨μ, ρ, h₁, h₂, h₃, h₄⟩ := GlobalTheory.T.cech_twist_nonzero_locus_maps X F L hL σ U hU
  exact GlobalTheory.T.cech_complex_direct_limit (fun c => cechCube ℤ (twistZ F L c) ⊤ U) (cechCube ℤ F (nonzeroLocus σ) U) μ ρ h₁ h₂ h₃ h₄ n h

theorem subsingleton_cohOn_nonzeroLocus_of_eventually_twist : ∀ (X : Scheme.{0}) [CompactSpace X] [X.IsSeparated] (F : X.Modules) [F.IsQuasicoherent] (L : LB X), L.IsLB → ∀ (σ : L.Sec) (i : ℕ), (∀ᶠ c : ℕ in atTop, Subsingleton (coh (twist F (lbPow L c)) i)) → Subsingleton (cohOn F (nonzeroLocus σ) i) := by
  intro X _ _ F _ L hL σ i h
  obtain ⟨κ, hκ, T, c, hT, -, hTc, hcov⟩ :=
    Twist.exists_finite_affine_chart_cover hL (W := ⊤) (isCompact_univ (X := X))
  letI : Fintype κ := Fintype.ofFinite κ
  letI : LinearOrder κ := LinearOrder.lift' (Fintype.equivFin κ) (Fintype.equivFin κ).injective
  have hsep : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (⨅ a ∈ s, T a) :=
    (cech_computes_coh_of_affine_cover.{0, 0, 0} X ℤ).1 (Or.inl inferInstance) κ T hT
  have hc : ⨆ a, T a = ⊤ := eq_top_iff.2 hcov
  have hV : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (cechOpen (nonzeroLocus σ) T s) := by
    rintro s ⟨a, ha⟩
    have hle : ⨅ b ∈ s, T b ≤ L.U (c a) := (biInf_le T ha).trans (hTc a)
    have e := Twist.basicOpen_resG_zfun (Twist.zofSec σ) (c a) hle
    rw [Twist.nonzeroLocus_zofSec hL] at e
    have e' : cechOpen (nonzeroLocus σ) T s = X.basicOpen (resG X hle (Twist.zfun (Twist.zofSec σ) (c a))) := by
      rw [e, cechOpen, inf_comm]
    rw [e']
    exact (hsep s ⟨a, ha⟩).basicOpen _
  have hVc : nonzeroLocus σ ≤ ⨆ a, T a := hc ▸ le_top
  have eV := cechHEquivCohOn ℤ hVc (cechAcyclicMod_of_isAffineOpen hV F) i
  have hZ : IsZero (cechH ℤ F (nonzeroLocus σ) T i) := by
    refine isZero_cechH_nonzeroLocus_of_eventually_twist X F L hL σ T hsep i (h.mono fun k hk => ?_)
    haveI hq : (twistZ F L k).IsQuasicoherent := Twist.isQuasicoherent_twist (Twist.isLB_lbZPow hL k)
    have e2 := cechHEquivCoh ℤ hc hsep (twistZ F L k) i
    haveI : Subsingleton (coh (twistZ F L k) i) := by rw [Twist.twistZ_natCast]; exact hk
    haveI : Subsingleton (cechH ℤ (twistZ F L k) ⊤ T i) := e2.injective.subsingleton
    exact ModuleCat.isZero_of_subsingleton _
  haveI : Subsingleton (cechH ℤ F (nonzeroLocus σ) T i) := ModuleCat.subsingleton_of_isZero hZ
  exact eV.symm.injective.subsingleton

end GlobalTheory
end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FinrankKaehlerResidueField
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LogPair
open scoped TensorProduct
theorem _root_.GlobalTheory.T.finrank_kaehler_residue_field : ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Sp k) (d : ℕ) [SmoothOfRelativeDimension d f] (U : X.Opens) (x : X) (hxU : x ∈ U), IsAffineOpen U → letI : Algebra k Γ(X, U) := (cstOn f U).toAlgebra; letI : Algebra Γ(X, U) (IsLocalRing.ResidueField (X.presheaf.stalk x)) := ((IsLocalRing.residue (X.presheaf.stalk x)).comp (X.presheaf.germ U x hxU).hom).toAlgebra; Module.finrank (IsLocalRing.ResidueField (X.presheaf.stalk x)) (IsLocalRing.ResidueField (X.presheaf.stalk x) ⊗[Γ(X, U)] Ω[Γ(X, U)⁄k]) = d := by
  first | exact @_root_.GlobalTheory.SmoothStalk.finrank_residue_kaehler | exact _root_.GlobalTheory.SmoothStalk.finrank_residue_kaehler | (intros; apply _root_.GlobalTheory.SmoothStalk.finrank_residue_kaehler <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.RootOfMonomialQuotientIntegral
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

theorem _root_.GlobalTheory.T.root_of_monomial_quotient_integral : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [IsDomain A] [Algebra (ZMod p) A] {n : ℕ} (t : Fin n → A), (MvPolynomial.aeval (R := ZMod p) t).toRingHom.Etale → ∀ (P : Ideal A) [P.IsPrime] (L : Type) [Field L] [Algebra A L] [IsFractionRing A L] (S : Finset (Fin n)) (g : L) (m : ℕ), 0 < m → (∃ a b : A, b ∉ P ∧ g ^ m / algebraMap A L (∏ j ∈ S, t j) * algebraMap A L b = algebraMap A L a) → ∃ a b : A, b ∉ P ∧ g / algebraMap A L (∏ j ∈ S, t j) * algebraMap A L b = algebraMap A L a := by
  first | exact @_root_.GlobalTheory.EtRoot.div_prod_coords_mem_of_pow | exact _root_.GlobalTheory.EtRoot.div_prod_coords_mem_of_pow | (intros; apply _root_.GlobalTheory.EtRoot.div_prod_coords_mem_of_pow <;> assumption)
end

