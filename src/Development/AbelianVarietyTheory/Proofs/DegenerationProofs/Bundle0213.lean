import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsExtendValuation
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0190
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0204
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemRangeIffOfFinite
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0131
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSectionsPowLineBundleFromLocalBasis
import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsArcFamilyPointWithFramesOfLaws
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.Ex

theorem arcFam : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt →
    ThetaUnifAV → GlobalTheory.LN.ArcFamSt := by
  intro h₁ h₂ h₃ h₄ h₅ h₆ h₇ E _ _ _ H D l Xo c W₀ Y O' _ _ _ b ϖ a hb m hm hmu
  have pt := GlobalTheory.ArcPoint.exists_point h₁ h₂ h₃ h₄ h₅ h₆ h₇ E H D l Xo c W₀ Y O' b ϖ a hb
  have bad := GlobalTheory.Ex.Trait.hasArcData_at_trait h₁ h₂ h₃ h₄ h₅ h₆ h₇ E H D l Xo c W₀ Y O' b ϖ a hb
  have good := GlobalTheory.Ex.GoodTrait.range_subset_abLocus h₁ h₂ h₃ h₄ h₅ h₆ h₇ E H D l Xo c W₀ Y O' b ϖ a hb
  have fr₁ := GlobalTheory.T.exists_single_polarisation_generator_all_traits h₁ h₂ h₃ h₄ h₅ h₆ h₇ E H D l Xo c W₀ Y O' b ϖ a hb
  have frm := GlobalTheory.OneBasis.exists_isFrame_pow_sq h₁ h₂ h₃ h₄ h₅ h₆ h₇ E H D l Xo c W₀ Y O' b ϖ a hb
  have mono := GlobalTheory.Ex.Mono.mono h₁ h₂ h₃ h₄ h₅ h₆ h₇ E H D l Xo c W₀ Y O' b ϖ a hb
  obtain ⟨R₁, _, _, g, y₁, gi, gf, n₁, hy, hr, ht⟩ := pt
  have td : GlobalTheory.LN.TraitData Y a g y₁ := ⟨hy, fun W _ _ _ hW φ gam hg χ hχ =>
    ⟨good R₁ g y₁ gi gf n₁ ht hy W hW φ gam hg χ hχ, bad R₁ g y₁ gi gf n₁ hr hy W hW φ gam hg χ hχ⟩⟩
  obtain ⟨R₂, _, _, h, h', hi, hf, n₂, hh, hθ⟩ := fr₁ R₁ g y₁ gi gf n₁ td ht
  obtain ⟨td₂, hr₂, -⟩ := mono R₁ g y₁ gi gf n₁ R₂ h h' hf hh
  have gi₂ : Function.Injective (h.comp g) := hi.comp gi
  have gf₂ : (h.comp g).Finite := hf.comp gf
  obtain ⟨R₃, _, _, k, k', ki, kf, n₃, kk, hfm⟩ :=
    frm R₂ (h.comp g) (spMap h' ≫ y₁) gi₂ gf₂ n₂ (td₂ td) (hr₂ hr) hθ m hm hmu
  obtain ⟨td₃, -, hfr⟩ := mono R₂ (h.comp g) (spMap h' ≫ y₁) gi₂ gf₂ n₂ R₃ k k' kf kk
  obtain ⟨θ, hθ⟩ := hθ
  obtain ⟨f', hf'⟩ := hfr 1 1 _ hθ
  refine ⟨R₃, inferInstance, inferInstance, k.comp (h.comp g), spMap k' ≫ spMap h' ≫ y₁, ki.comp gi₂, kf.comp gf₂, n₃,
    td₃ (td₂ td), ⟨f' 0, ?_⟩, hfm⟩
  have e : (fun _ : Fin 1 => f' 0) = f' := funext fun i => by rw [Subsingleton.elim i 0]
  rw [e]; exact hf'
end GlobalTheory.Ex
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSectionsPowLineBundleFromLocalBasisStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sections_pow_line_bundle_from_local_basis : GlobalTheory.Published.SemistableReductionSt → ThmUSt → Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Q : ZHPre ρ M U₀), S.Over₀ M U₀ → S.IsEE M U₀ EE → Q.SecO EE → ∀ (W : M.Z.Opens) (x₀ : S.Gam) (b : Matrix S.J S.J Ω), (∀ z ∈ W, x₀ ∈ S.supI M z ∧ EE.E z = Submodule.span (M.O z) (Set.range b)) → ∃ σ : S.J → ∀ j, Γ(Q.G.left, Q.G.hom ⁻¹ᵁ W ⊓ (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => (S.N : ℤ))).U j), (∀ i, σ i ∈ secOn (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => (S.N : ℤ))) (Q.G.hom ⁻¹ᵁ W) ∧ GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w S.N ρ.s (fun l => b i l / S.th x₀) _ (σ i)) ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ M.Z), Set.range x ⊆ W → (∀ g : Sp K ⟶ Q.G.left, g ≫ Q.G.hom = x → ∃ i j, valF g _ (σ i j) ≠ 0) ∧ ∀ c : S.J → K, (∀ (g : Sp K ⟶ Q.G.left) (j : _), g ≫ Q.G.hom = x → ∑ i, c i * valF g _ (σ i j) = 0) → c = 0 := by
  first | exact @GlobalTheory.ZH.PowSec.exists_sections | exact GlobalTheory.ZH.PowSec.exists_sections | (intros; apply GlobalTheory.ZH.PowSec.exists_sections <;> assumption)
end

