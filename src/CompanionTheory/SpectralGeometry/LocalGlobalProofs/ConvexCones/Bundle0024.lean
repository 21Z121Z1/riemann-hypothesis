import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.Bundle0020
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0807
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0663
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0841
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0688
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0840
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsSmoothPolyhedralFanRefinement

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsFan
section
set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem exists_fan (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) :
    ∃ φ : InvFun (𝓞 E), IsPolFan H.bar q φ ∧ NoSelfInt H.bar q φ ∧ GlobalTheory.TorRef.IsPosFn H φ := by
  have hpoly : IsPolyFan H.bar q (vorFun (𝓞 E) (Module.finrank ℤ (𝓞 E) * q)) :=
    GlobalTheory.T.voronoi_fan_is_polyhedral (𝓞 E) H.bar _ q (fun Y _ _ _ _ => GlobalTheory.T.hasPolyhedralCover_balancedForms_CMField E H Y) le_rfl
  have htw : IsTwInv H (vorFun (𝓞 E) (Module.finrank ℤ (𝓞 E) * q)) := fun σ _ n B => baseFun_twist _ _ _ σ n B
  obtain ⟨φ₁, f1, f2, f3, -⟩ := GlobalTheory.T.exists_invariant_smoothProjective_refinement_polyFan E H q _ (fun X _ _ _ _ => GlobalTheory.T.dominatesLinearFormsOnBalancedForms_cm E H X) hpoly htw
  obtain ⟨φ₂, k1, k2, -, k4, -, -⟩ := GlobalTheory.T.exists_homogeneous_positive_polFan_extension E H q φ₁ f1 f2 f3
  exact ⟨φ₂, k1, k2, k4⟩

end GlobalTheory.CompanionTheory.Ar.Fan
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsSmoothPolyhedralFanRefinementStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan
theorem _root_.GlobalTheory.T.exists_smooth_polyhedral_fan_refinement : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (q : ℕ) (ψ : InvFun O), (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Dominates bar X) → IsPolyFan bar q ψ → IsTwG w0 ψ → ∃ φ' : InvFun O, IsPolFan bar q φ' ∧ NoSelfInt bar q φ' ∧ IsTwG w0 φ' ∧ ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCone bar φ' γ → ψ.LinearOn γ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.SmoothRefinement.exists_smooth_refinement | exact GlobalTheory.CompanionTheory.Ar.Fan.SmoothRefinement.exists_smooth_refinement | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.SmoothRefinement.exists_smooth_refinement <;> assumption)
end

