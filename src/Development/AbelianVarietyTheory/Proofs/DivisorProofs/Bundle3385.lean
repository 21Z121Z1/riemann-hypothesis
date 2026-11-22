import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3367
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorFieldsEqOnSubopensOfEqAffine
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LogKS

theorem isField_eq_basicOpen {Z : Scheme.{0}} {V : Z.Opens} (hV : IsAffineOpen V)
    {d₁ d₂ : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)} (h₁ : IsField V d₁) (h₂ : IsField V d₂)
    (h : ∀ a, d₁ V a = d₂ V a) (s : Γ(Z, V)) (g : Γ(Z, Z.basicOpen s)) :
    d₁ (Z.basicOpen s) g = d₂ (Z.basicOpen s) g := by
  have hle : Z.basicOpen s ≤ V := Z.basicOpen_le s
  haveI := hV.isLocalization_basicOpen s
  have halg : ∀ x, algebraMap Γ(Z, V) Γ(Z, Z.basicOpen s) x = resG Z hle x := fun _ => rfl

  have hres : ∀ x : Γ(Z, V), d₁ _ (resG Z hle x) = d₂ _ (resG Z hle x) := by
    intro x
    rw [h₁.2.2 V _ hle le_rfl, h₂.2.2 V _ hle le_rfl, h]
  obtain ⟨⟨a, m⟩, hm⟩ := IsLocalization.surj (Submonoid.powers s) g
  simp only [halg] at hm
  have hu : IsUnit (resG Z hle (m : Γ(Z, V))) := by
    rw [← halg]; exact IsLocalization.map_units _ m
  have e₁ := congrArg (d₁ _) hm
  have e₂ := congrArg (d₂ _) hm
  rw [h₁.2.1 _ hle] at e₁
  rw [h₂.2.1 _ hle] at e₂
  have key : resG Z hle (m : Γ(Z, V)) * (d₁ _ g - d₂ _ g) = 0 := by
    rw [hres m] at e₁
    rw [hres a] at e₁
    linear_combination e₁ - e₂
  exact sub_eq_zero.mp ((hu.mul_right_eq_zero).mp key)

theorem isField_eq_of_affine : ∀ (Z : Scheme.{0}) (V : Z.Opens), IsAffineOpen V → ∀ (d₁ d₂ : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)), IsField V d₁ → IsField V d₂ → (∀ a, d₁ V a = d₂ V a) → ∀ O : Z.Opens, O ≤ V → ∀ f, d₁ O f = d₂ O f := by
  intro Z V hV d₁ d₂ h₁ h₂ h O hO f
  refine TopCat.Presheaf.section_ext Z.sheaf O _ _ fun x hx => ?_
  obtain ⟨r, hrO, hxr⟩ := hV.exists_basicOpen_le ⟨x, hx⟩ (hO hx)
  have e₁ := h₁.2.2 O _ hrO hO f
  have e₂ := h₂.2.2 O _ hrO hO f
  have e := isField_eq_basicOpen hV h₁ h₂ h r (resG Z hrO f)
  rw [e₁, e₂] at e
  have g₁ := TopCat.Presheaf.germ_res_apply Z.presheaf (homOfLE hrO) x hxr (d₁ O f)
  have g₂ := TopCat.Presheaf.germ_res_apply Z.presheaf (homOfLE hrO) x hxr (d₂ O f)
  exact g₁.symm.trans ((congrArg _ e).trans g₂)

end GlobalTheory.LogKS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightLatticeSpanEqTopStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_lattice_span_eq_top : GlobalTheory.CovTop.Hypotheses2 → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ la : GlobalTheory.AllWt.Weight (T.Q.Dw j), GapGe 1 la → FiniteDimensional Y.d.c₂.F (Y.V (wtOf _ la 0)) → Submodule.span Y.d.c₂.F (GlobalTheory.AllWt.latW Y.U (wtOf _ la 0) : Set (Y.V (wtOf _ la 0))) = ⊤ := by
  first | exact @GlobalTheory.SupSpanDeep.span_latW_eq_top | exact GlobalTheory.SupSpanDeep.span_latW_eq_top | (intros; apply GlobalTheory.SupSpanDeep.span_latW_eq_top <;> assumption)
end

