import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0020
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0014
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InstBorelGL
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0008
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0005
import GroundTheory.AutomorphicForms.GL2.GJUnramifiedCosets
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0003
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SphericalZetaCosets
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
section
set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

def TotPos (F : Type) [Field F] (x : F) : Prop := ∀ σ : F →+* ℝ, 0 < σ x

def congUnits {F : Type} [Field F] [NumberField F] (𝔣 : Ideal (𝓞 F)) : Set (𝓞 F)ˣ :=
  {u | ((u : 𝓞 F) - 1 ∈ 𝔣) ∧ TotPos F ((u : 𝓞 F) : F)}

def openCone {F : Type} [Field F] {r : ℕ} (v : Fin r → F) : Set F :=
  {x | ∃ t : Fin r → ℚ, (∀ i, 0 < t i) ∧ x = ∑ i, (t i : F) * v i}

def IsConeDomain {F : Type} [Field F] [NumberField F] (𝔣 : Ideal (𝓞 F)) {ι : Type} (r : ι → ℕ) (v : ∀ c, Fin (r c) → F) : Prop :=
  (∀ c, 0 < r c) ∧ (∀ c, LinearIndependent ℚ (v c)) ∧ (∀ c i, TotPos F (v c i)) ∧
    ∀ x : F, TotPos F x → ∃! p : congUnits 𝔣 × ι, (((p.1 : (𝓞 F)ˣ) : 𝓞 F) : F) * x ∈ openCone (v p.2)

def ClassParam {F : Type} [Field F] [NumberField F] (𝔣 𝔞 𝔟 : Ideal (𝓞 F)) {J : Type} (r : J → ℕ) (y : J → 𝓞 F)
    (v : ∀ j, Fin (r j) → 𝓞 F) : Prop :=
  𝔟 ≠ ⊥ ∧ (∀ j, y j ∈ 𝔟 ∧ TotPos F (y j : F)) ∧ (∀ j i, v j i ∈ 𝔟 ∧ TotPos F (v j i : F)) ∧
    (∀ j, r j ≤ Module.finrank ℚ F) ∧
    ∃ e : (Σ j, (Fin (r j) → ℕ)) ≃ {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I 𝔞},
      ∀ p, (e p).1 * 𝔟 = Ideal.span {y p.1 + ∑ i, (p.2 i : 𝓞 F) * v p.1 i}

open Classical in

def classWeight {F : Type} [Field F] [NumberField F] (l : ℕ) (𝔠 I : Ideal (𝓞 F)) : ℚ := if I ≤ 𝔠 then (l : ℚ) - 1 else -1

def GoodWeight (l : ℕ) {r : ℕ} (w : (Fin r → ℕ) → ℚ) : Prop :=
  (∀ m i, w (m + (Pi.single i l : Fin r → ℕ)) = w m) ∧ ∀ m i, ∑ e ∈ Finset.range l, w (m + (Pi.single i e : Fin r → ℕ)) = 0

def coneTerm {ι : Type} [Fintype ι] {r : ℕ} (a : ι → Fin r → ℝ) (b : ι → ℝ) (s : ℂ) (m : Fin r → ℕ) : ℂ :=
  ∏ j, (((b j + ∑ i, a j i * (m i : ℝ) : ℝ) : ℂ) ^ (-s))

def AbelContinuation : Prop :=
  ∀ (ι : Type) [Fintype ι] (r l : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (w : (Fin r → ℕ) → ℚ),
    r ≤ Fintype.card ι → 0 < l → (∀ j i, 0 < a j i) → (∀ j, 0 < b j) → GoodWeight l w →
      ∃ T : ℂ → ℂ, Differentiable ℂ T ∧
        (∀ s : ℂ, 1 < s.re → HasSum (fun m => (w m : ℂ) * coneTerm a b s m) (T s)) ∧
        ∀ p : ℕ, (∀ m : Fin r → ℕ, ∃ q : ℚ, ∏ j, (b j + ∑ i, a j i * (m i : ℝ)) ^ p = (q : ℝ)) →
          ∃ q : ℚ, T (-(p : ℂ)) = (q : ℂ)

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.BlowupOfAgreeingIdealCartierStatement
section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blowup_of_agreeing_ideal_cartier : ∀ {X₁ X₂ : Scheme.{0}} (π : X₂ ⟶ X₁) (Z Z' : X₁.IdealSheafData) (O₁ O₂ : X₁.Opens), FinalTheorems.Blowup π Z → O₁ ⊔ O₂ = ⊤ → Z'.comap O₁.ι = Z.comap O₁.ι → (∀ x ∈ O₂, x ∉ Z'.support) → FinalTheorems.EffCartier (Z.comap O₂.ι) → FinalTheorems.Blowup π Z' := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.BlowupGlue.blowup_of_eq_on_open | exact GlobalTheory.CompanionTheory.Hypotheses₂.BlowupGlue.blowup_of_eq_on_open | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.BlowupGlue.blowup_of_eq_on_open <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.EffCartierRestrictIffCartierAtStatement
section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.effCartier_restrict_iff_cartier_at : ∀ {X : Scheme.{0}} (J : X.IdealSheafData) (O : X.Opens), FinalTheorems.EffCartier (J.comap O.ι) ↔ ∀ x ∈ O, CartAt J x := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.effCartier_comap_opens_iff | exact GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.effCartier_comap_opens_iff | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.effCartier_comap_opens_iff <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.IntegrandEqOnPiece
section
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel

namespace GlobalTheory.CompanionTheory.ZetaSph

def piece {F : Type} [Field F] (O : Subring F) (nrm : AbsoluteValue F ℝ) (q : ℕ) {c : ℕ} (e : Fin c → ℕ) :
    Set (GL (Fin c) F) :=
  {g : GL (Fin c) F | g ∈ Mint O c ∧ ∃ b : GL (Fin c) F, (b : Matrix (Fin c) (Fin c) F).BlockTriangular id ∧
    (∀ i, nrm ((b : Matrix (Fin c) (Fin c) F) i i) = (q : ℝ) ^ (-(e i : ℤ))) ∧ ∃ k ∈ GLint O c, g = b * k}

noncomputable def pieceVal {c : ℕ} (q : ℕ) (α : Fin c → ℂ) (σ : ℝ) (e : Fin c → ℕ) : ℂ :=
  ∏ i : Fin c, (α i ^ e i *
    (((q : ℝ) ^ (-(e i : ℝ) * (((c : ℝ) - 1) / 2 - ((i : ℕ) : ℝ) + σ)) : ℝ) : ℂ))

theorem zeta_spherical : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ {c : ℕ} (χ : Fin c → F → ℂ) (α : Fin c → ℂ), UnrChar nrm q χ α → ∀ (φ : GL (Fin c) F → ℂ), IsSphFn O nrm χ φ → ∀ (κ : Measure (GL (Fin c) F)), κ.IsMulLeftInvariant → κ (GLint O c : Set (GL (Fin c) F)) = 1 → ∀ σ : ℝ, (∀ i, ‖α i‖ * (q : ℝ) ^ (((c : ℝ) - 1) / 2 - σ) < 1) → IntegrableOn (fun g => φ g * ((nrm (g : Matrix (Fin c) (Fin c) F).det ^ (σ) : ℝ) : ℂ)) (Mint O c) κ ∧ ∫ g in Mint O c, φ g * ((nrm (g : Matrix (Fin c) (Fin c) F).det ^ (σ) : ℝ) : ℂ) ∂κ = ∏ i : Fin c, (1 - α i * (((q : ℝ) ^ (((c : ℝ) - 1) / 2 - σ) : ℝ) : ℂ))⁻¹ :=
  _root_.UpperTheory.Reformulated.B.SphericalZetaCosets.zeta_spherical

end GlobalTheory.CompanionTheory.ZetaSph
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.JacquetModuleFiniteLengthStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_module_finite_length : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.JacquetFiniteLength k := by
  first | exact @GlobalTheory.CompanionTheory.JacquetBridge.jacquetFiniteLength | exact GlobalTheory.CompanionTheory.JacquetBridge.jacquetFiniteLength | (intros; apply GlobalTheory.CompanionTheory.JacquetBridge.jacquetFiniteLength <;> assumption)
end

