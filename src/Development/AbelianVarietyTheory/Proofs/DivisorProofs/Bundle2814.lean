import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2721
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2722
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2606
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0097
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2726
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.FnOfComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2681
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValRConstHom
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2665
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsMonHomOfLinearMapKernelsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_isMonHom_of_linear_map_kernels : ∀ (A A' : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (g g' : ℕ), IsAbelianScheme A → IsAbelianScheme A' → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g' A'.hom → ∀ (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)) (e' : (Fin g' → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A')) (M : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)), IsExp (𝟙 (Sp ℂ)) e → IsExp (𝟙 (Sp ℂ)) e' → (∀ z, e z = 1 → e' (M z) = 1) → ∃! f : A ⟶ A', IsMonHom f ∧ ∀ z, e' (M z) = e z ≫ f := by
  first | exact @GlobalTheory.HomAlgAny.existsUnique_isMonHom_of_map_ker | exact GlobalTheory.HomAlgAny.existsUnique_isMonHom_of_map_ker | (intros; apply GlobalTheory.HomAlgAny.existsUnique_isMonHom_of_map_ker <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePushoutTorsorSectionDifference
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem isSec_sub_root_eq {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] [IsCommMonObj A] {n : ℕ}
    {b : Fn0 A} {D : Type} [CommRing D] [Algebra R D] {x : Pt A D} {s s' : RootFn A D}
    (hs : IsSec n b x s) (hs' : IsSec n b x s') {D' : Type} [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D')
    (z z' : Pt A D') (hz : z ^ n = spOver φ ≫ x) (hz' : z' ^ n = spOver φ ≫ x) :
    s D' φ z' - s' D' φ z' = s D' φ z - s' D' φ z := by
  have hw : (z⁻¹ * z') ^ n = 1 := by rw [mul_pow, inv_pow, hz, hz', inv_mul_cancel]
  have e : z' = z * (z⁻¹ * z') := (mul_inv_cancel_left z z').symm
  rw [e, hs.2 D' φ z _ hz hw, hs'.2 D' φ z _ hz hw]
  abel

theorem isSec_sub_natural {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {n : ℕ}
    {b : Fn0 A} {D : Type} [CommRing D] [Algebra R D] {x : Pt A D} {s s' : RootFn A D}
    (hs : IsSec n b x s) (hs' : IsSec n b x s') {D' : Type} [CommRing D'] [Algebra R D']
    {D'' : Type} [CommRing D''] [Algebra R D''] (φ : D →ₐ[R] D') (ψ : D' →ₐ[R] D'')
    (z : Pt A D') (hz : z ^ n = spOver φ ≫ x) :
    s D'' (ψ.comp φ) (spOver ψ ≫ z) - s' D'' (ψ.comp φ) (spOver ψ ≫ z) = ψ (s D' φ z - s' D' φ z) := by
  rw [hs.1 D' D'' φ ψ z hz, hs'.1 D' D'' φ ψ z hz, map_sub]

theorem root_spOver {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {n : ℕ}
    {D : Type} [CommRing D] [Algebra R D] {x : Pt A D} {D' : Type} [CommRing D'] [Algebra R D']
    {D'' : Type} [CommRing D''] [Algebra R D''] (φ : D →ₐ[R] D') (ψ : D' →ₐ[R] D'')
    (z : Pt A D') (hz : z ^ n = spOver φ ≫ x) : (spOver ψ ≫ z) ^ n = spOver (ψ.comp φ) ≫ x := by
  rw [← MonObj.comp_pow, hz, ← Category.assoc, spOver_comp]

end GlobalTheory.PtExt

namespace GlobalTheory.PtExt

theorem isSec_sub_existsUnique : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (n : ℕ),
    HasRoots A n → ∀ (b : Fn0 A) (D : Type) [CommRing D] [Algebra R D] (x : Pt A D) (s s' : RootFn A D),
    IsSec n b x s → IsSec n b x s' → ∃! e : D, ∀ (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D')
      (z : Pt A D'), z ^ n = spOver φ ≫ x → s D' φ z - s' D' φ z = φ e := by
  intro R _ A _ _ n hR b D _ _ x s s' hs hs'
  obtain ⟨D₁, _, _, ψ, z₀, hψ, hz₀⟩ := hR D x
  have hdesc := GlobalTheory.ff_descent_pairs R D D₁ ψ hψ (s D₁ ψ z₀ - s' D₁ ψ z₀) (fun E _ _ α β hαβ ↦ by
    rw [← isSec_sub_natural hs hs' ψ α z₀ hz₀, ← isSec_sub_natural hs hs' ψ β z₀ hz₀]
    have h1 := root_spOver ψ α z₀ hz₀
    have h2 := root_spOver ψ β z₀ hz₀
    rw [hαβ] at h1 ⊢
    exact isSec_sub_root_eq hs hs' _ _ _ h2 h1)
  obtain ⟨e, he, heu⟩ := hdesc
  have key : ∀ (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (z : Pt A D'), z ^ n = spOver φ ≫ x →
      s D' φ z - s' D' φ z = φ e := by
    intro D' _ _ φ z hz
    obtain ⟨E', _, _, ψ', φ', hψ', hsq⟩ := GlobalTheory.exists_pushout_faithfullyFlat R D D₁ D' ψ φ hψ
    have hinj : Function.Injective ψ' := by
      letI : Algebra D' E' := (ψ' : D' →+* E').toAlgebra
      haveI : Module.FaithfullyFlat D' E' := hψ'
      exact FaithfulSMul.algebraMap_injective D' E'
    apply hinj
    have h1 := root_spOver φ ψ' z hz
    have h2 := root_spOver ψ φ' z₀ hz₀
    rw [← isSec_sub_natural hs hs' φ ψ' z hz]
    rw [hsq] at h1 ⊢
    rw [isSec_sub_root_eq hs hs' _ _ _ h2 h1, isSec_sub_natural hs hs' ψ φ' z₀ hz₀, ← he]
    exact (congrArg (fun f : D →ₐ[R] E' ↦ f e) hsq).symm
  exact ⟨e, key, fun e' he' ↦ heu e' ((he' D₁ ψ z₀ hz₀).symm)⟩

end GlobalTheory.PtExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePushoutTorsorSectionMulDifference
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SecMul

theorem comp_pow_pt {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {T T' : Over (Sp R)} (f : T' ⟶ T)
    (x : T ⟶ A) (n : ℕ) : f ≫ x ^ n = (f ≫ x) ^ n := by
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ, comp_mul, ih]

end GlobalTheory.SecMul

namespace GlobalTheory

theorem sec_mul_diff : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (n : ℕ),
    HasRoots A n → ∀ b : Fn0 A, IsTorsChar n b → ∀ (D : Type) [CommRing D] [Algebra R D] (x y : Pt A D)
    (s s' s'' : RootFn A D), IsSec n b x s → IsSec n b y s' → IsSec n b (x * y) s'' → ∃! e : D,
    ∀ (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (z w : Pt A D'), z ^ n = spOver φ ≫ x →
      w ^ n = spOver φ ≫ y → s'' D' φ (z * w) - s D' φ z - s' D' φ w = φ e := by
  intro R _ A _ _ n hR b hb D _ _ x y s s' s'' hs hs' hs''
  have hroot : ∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (φ : D →ₐ[R] E)
      (ψ : E →ₐ[R] E') (p : Pt A D) (z : Pt A E), z ^ n = spOver φ ≫ p →
      (spOver ψ ≫ z) ^ n = spOver (ψ.comp φ) ≫ p := by
    intro E _ _ E' _ _ φ ψ p z hz
    rw [← SecMul.comp_pow_pt, hz, ← Category.assoc, spOver_comp]
  have hmul : ∀ (E : Type) [CommRing E] [Algebra R E] (φ : D →ₐ[R] E) (z w : Pt A E), z ^ n = spOver φ ≫ x →
      w ^ n = spOver φ ≫ y → (z * w) ^ n = spOver φ ≫ (x * y) := by
    intro E _ _ φ z w hz hw
    rw [mul_pow, hz, hw, comp_mul]
  have hinv : ∀ (E : Type) [CommRing E] [Algebra R E] (φ : D →ₐ[R] E) (z z' w w' : Pt A E),
      z ^ n = spOver φ ≫ x → z' ^ n = spOver φ ≫ x → w ^ n = spOver φ ≫ y → w' ^ n = spOver φ ≫ y →
      s'' E φ (z' * w') - s E φ z' - s' E φ w' = s'' E φ (z * w) - s E φ z - s' E φ w := by
    intro E _ _ φ z z' w w' hz hz' hw hw'
    obtain ⟨t, rfl⟩ : ∃ t, z' = z * t := ⟨z⁻¹ * z', (mul_inv_cancel_left z z').symm⟩
    obtain ⟨u, rfl⟩ : ∃ u, w' = w * u := ⟨w⁻¹ * w', (mul_inv_cancel_left w w').symm⟩
    have ht : t ^ n = 1 := by rw [mul_pow, hz] at hz'; exact mul_eq_left.mp hz'
    have hu : u ^ n = 1 := by rw [mul_pow, hw] at hw'; exact mul_eq_left.mp hw'
    rw [_root_.mul_mul_mul_comm, hs''.2 E φ _ _ (hmul E φ z w hz hw) (by rw [mul_pow, ht, hu, _root_.one_mul]),
      hb.2 E t u ht hu, hs.2 E φ z t hz ht, hs'.2 E φ w u hw hu]
    ring
  have hnat : ∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (φ : D →ₐ[R] E)
      (ψ : E →ₐ[R] E') (z w : Pt A E), z ^ n = spOver φ ≫ x → w ^ n = spOver φ ≫ y →
      s'' E' (ψ.comp φ) (spOver ψ ≫ z * spOver ψ ≫ w) - s E' (ψ.comp φ) (spOver ψ ≫ z) -
        s' E' (ψ.comp φ) (spOver ψ ≫ w) = ψ (s'' E φ (z * w) - s E φ z - s' E φ w) := by
    intro E _ _ E' _ _ φ ψ z w hz hw
    rw [← comp_mul, hs''.1 E E' φ ψ _ (hmul E φ z w hz hw), hs.1 E E' φ ψ z hz, hs'.1 E E' φ ψ w hw,
      map_sub, map_sub]
  obtain ⟨D2, _, _, ψ, z0, w0, hf, hz0, hw0⟩ : ∃ (D2 : Type) (_ : CommRing D2) (_ : Algebra R D2)
      (ψ : D →ₐ[R] D2) (z0 w0 : Pt A D2), (ψ : D →+* D2).FaithfullyFlat ∧ z0 ^ n = spOver ψ ≫ x ∧
      w0 ^ n = spOver ψ ≫ y := by
    obtain ⟨D1, _, _, ψ1, z1, hf1, hz1⟩ := hR D x
    obtain ⟨D2, _, _, ψ2, w2, hf2, hw2⟩ := hR D1 (spOver ψ1 ≫ y)
    refine ⟨D2, inferInstance, inferInstance, ψ2.comp ψ1, spOver ψ2 ≫ z1, w2,
      ringHom_faithfullyFlat_comp hf1 hf2, hroot D1 D2 ψ1 ψ2 x z1 hz1, ?_⟩
    rw [hw2, ← Category.assoc, spOver_comp]
  have hinjψ : Function.Injective ψ := RingHom.FaithfullyFlat.injective hf
  obtain ⟨e, he, -⟩ := ff_descent_pairs R D D2 ψ hf
    (s'' D2 ψ (z0 * w0) - s D2 ψ z0 - s' D2 ψ w0) (fun E _ _ α β hαβ ↦ by
      rw [← hnat D2 E ψ α z0 w0 hz0 hw0, ← hnat D2 E ψ β z0 w0 hz0 hw0]
      have h1 := hroot D2 E ψ α x z0 hz0
      have h2 := hroot D2 E ψ α y w0 hw0
      rw [hαβ] at h1 h2 ⊢
      exact hinv E (β.comp ψ) _ _ _ _ (hroot D2 E ψ β x z0 hz0) h1 (hroot D2 E ψ β y w0 hw0) h2)
  refine ⟨e, fun E _ _ φ z w hz hw ↦ ?_, fun e' he' ↦ hinjψ ((he' D2 ψ z0 w0 hz0 hw0).symm.trans he.symm)⟩
  obtain ⟨E', _, _, ψ', φ', hf', hcomm⟩ := exists_pushout_faithfullyFlat R D D2 E ψ φ hf
  apply RingHom.FaithfullyFlat.injective hf'
  have hR2 : ψ' (φ e) = s'' E' (φ'.comp ψ) (spOver φ' ≫ z0 * spOver φ' ≫ w0) - s E' (φ'.comp ψ) (spOver φ' ≫ z0) -
      s' E' (φ'.comp ψ) (spOver φ' ≫ w0) := by
    rw [hnat D2 E' ψ φ' z0 w0 hz0 hw0, ← he]
    change (ψ'.comp φ) e = (φ'.comp ψ) e
    rw [hcomm]
  change ψ' (s'' E φ (z * w) - s E φ z - s' E φ w) = ψ' (φ e)
  rw [← hnat E E' φ ψ' z w hz hw, hR2]
  have h1 := hroot E E' φ ψ' x z hz
  have h2 := hroot E E' φ ψ' y w hw
  rw [hcomm] at h1 h2 ⊢
  exact hinv E' (φ'.comp ψ) _ _ _ _ (hroot D2 E' ψ φ' x z0 hz0) h1 (hroot D2 E' ψ φ' y w0 hw0) h2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueStalkHomPadicAlgClosureValuationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unique_stalkHom_padicAlgClosure_valuation : ∀ (X : Scheme.{0}) (x : X) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ X), y (cPt p) = x → ∃ φ : X.presheaf.stalk x →+* OO p, IsLocalHom φ ∧ spMap φ ≫ X.fromSpecStalk x = y ∧ ∀ g : X.presheaf.stalk x →+* OO p, spMap g ≫ X.fromSpecStalk x = y → g = φ := by
  first | exact @GlobalTheory.ValPt.exists_unique_stalk_hom | exact GlobalTheory.ValPt.exists_unique_stalk_hom | (intros; apply GlobalTheory.ValPt.exists_unique_stalk_hom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueUnitsGlueArtinFibreProduct
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.PinchUnits

open ReciprocityTheory.ChartRestriction.G.Out.TLinPf

theorem pushout_sec_exists {X₀ X₁ X₂ X : Scheme.{0}} {i₁ : X₀ ⟶ X₁} {i₂ : X₀ ⟶ X₂} {j₁ : X₁ ⟶ X}
    {j₂ : X₂ ⟶ X} (H : IsPushout i₁ i₂ j₁ j₂) (s₁ : Γ(X₁, ⊤)) (s₂ : Γ(X₂, ⊤))
    (h : i₁.appTop.hom s₁ = i₂.appTop.hom s₂) :
    ∃ s : Γ(X, ⊤), j₁.appTop.hom s = s₁ ∧ j₂.appTop.hom s = s₂ := by
  have w : i₁ ≫ mOf s₁ = i₂ ≫ mOf s₂ := by rw [comp_mOf, comp_mOf, h]
  refine ⟨fnOf (H.desc (mOf s₁) (mOf s₂) w), ?_, ?_⟩
  · rw [← fnOf_comp, H.inl_desc, fnOf_mOf]
  · rw [← fnOf_comp, H.inr_desc, fnOf_mOf]

theorem pushout_sec_ext {X₀ X₁ X₂ X : Scheme.{0}} {i₁ : X₀ ⟶ X₁} {i₂ : X₀ ⟶ X₂} {j₁ : X₁ ⟶ X}
    {j₂ : X₂ ⟶ X} (H : IsPushout i₁ i₂ j₁ j₂) (s s' : Γ(X, ⊤))
    (h₁ : j₁.appTop.hom s = j₁.appTop.hom s') (h₂ : j₂.appTop.hom s = j₂.appTop.hom s') : s = s' := by
  apply mOf_inj
  apply H.hom_ext
  · rw [comp_mOf, comp_mOf, h₁]
  · rw [comp_mOf, comp_mOf, h₂]

theorem resLE_appTop_topIso_inv {X Y : Scheme.{0}} (t : X ⟶ Y) {U : Y.Opens} {V : X.Opens}
    (e : V ≤ t ⁻¹ᵁ U) (g : Γ(Y, U)) :
    (t.resLE U V e).appTop.hom (U.topIso.inv.hom g) = V.topIso.inv.hom ((t.appLE U V e).hom g) := by
  rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, ← CommRingCat.comp_apply,
    Iso.inv_hom_id_assoc, CommRingCat.comp_apply]

theorem isPullback_resLE_self {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) :
    IsPullback (f.resLE U (f ⁻¹ᵁ U) le_rfl) (f ⁻¹ᵁ U).ι U.ι f := by
  rw [Scheme.Hom.resLE_eq_morphismRestrict]; exact isPullback_morphismRestrict f U

theorem main : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (Y : Over (Spec P)) (Y₁ : Over (Spec R₁)) (Y₂ : Over (Spec R₂)) (Y₀ : Over (Spec R₀)) (j₁ : Y₁.left ⟶ Y.left) (j₂ : Y₂.left ⟶ Y.left) (i₁ : Y₀.left ⟶ Y₁.left) (i₂ : Y₀.left ⟶ Y₂.left), Flat Y.hom → IsPullback j₁ Y₁.hom Y.hom (Spec.map f₁) → IsPullback j₂ Y₂.hom Y.hom (Spec.map f₂) → IsPullback i₁ Y₀.hom Y₁.hom (Spec.map g₁) → i₁ ≫ j₁ = i₂ ≫ j₂ → i₂ ≫ Y₂.hom = Y₀.hom ≫ Spec.map g₂ → (∀ (U : Y.left.Opens) (a₁ : Γ(Y₁.left, j₁ ⁻¹ᵁ U)ˣ) (a₂ : Γ(Y₂.left, j₂ ⁻¹ᵁ U)ˣ), (∀ x : Y₀.left, i₁ x ∈ j₁ ⁻¹ᵁ U → gm i₁ x (j₁ ⁻¹ᵁ U) a₁ = gm i₂ x (j₂ ⁻¹ᵁ U) a₂) → ∃ d : Γ(Y.left, U)ˣ, pullU j₁ U d = a₁ ∧ pullU j₂ U d = a₂) ∧ (∀ (U : Y.left.Opens) (d d' : Γ(Y.left, U)ˣ), pullU j₁ U d = pullU j₁ U d' → pullU j₂ U d = pullU j₂ U d' → d = d') := by
  intro P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hpb hloc hart hs₁ hs₂ Y Y₁ Y₂ Y₀ j₁ j₂ i₁ i₂ hfl h₁ h₂ h₀ hc hc₂
  have hle : ∀ U : Y.left.Opens, i₁ ⁻¹ᵁ (j₁ ⁻¹ᵁ U) ≤ i₂ ⁻¹ᵁ (j₂ ⁻¹ᵁ U) := by
    intro U x hx
    have e : (i₁ ≫ j₁) x = (i₂ ≫ j₂) x := by rw [hc]
    show j₂ (i₂ x) ∈ U
    simp only [Scheme.Hom.comp_apply] at e
    rw [← e]; exact hx
  have key : ∀ U : Y.left.Opens,
      (∀ (s₁ : Γ(Y₁.left, j₁ ⁻¹ᵁ U)) (s₂ : Γ(Y₂.left, j₂ ⁻¹ᵁ U)),
        (i₁.appLE (j₁ ⁻¹ᵁ U) (i₁ ⁻¹ᵁ (j₁ ⁻¹ᵁ U)) le_rfl).hom s₁ =
          (i₂.appLE (j₂ ⁻¹ᵁ U) (i₁ ⁻¹ᵁ (j₁ ⁻¹ᵁ U)) (hle U)).hom s₂ →
        ∃ d : Γ(Y.left, U), (j₁.app U).hom d = s₁ ∧ (j₂.app U).hom d = s₂) ∧
      (∀ d d' : Γ(Y.left, U), (j₁.app U).hom d = (j₁.app U).hom d' →
        (j₂.app U).hom d = (j₂.app U).hom d' → d = d') := by
    intro U
    let V₁ := j₁ ⁻¹ᵁ U
    let V₂ := j₂ ⁻¹ᵁ U
    let V₀ := i₁ ⁻¹ᵁ V₁
    let k₁ := j₁.resLE U V₁ le_rfl
    let k₂ := j₂.resLE U V₂ le_rfl
    let l₁ := i₁.resLE V₁ V₀ le_rfl
    let l₂ := i₂.resLE V₂ V₀ (hle U)
    have pb1 : IsPullback k₁ (V₁.ι ≫ Y₁.hom) (U.ι ≫ Y.hom) (Spec.map f₁) :=
      (isPullback_resLE_self j₁ U).paste_vert h₁
    have pb2 : IsPullback k₂ (V₂.ι ≫ Y₂.hom) (U.ι ≫ Y.hom) (Spec.map f₂) :=
      (isPullback_resLE_self j₂ U).paste_vert h₂
    have pb0 : IsPullback l₁ (V₀.ι ≫ Y₀.hom) (V₁.ι ≫ Y₁.hom) (Spec.map g₁) :=
      (isPullback_resLE_self i₁ V₁).paste_vert h₀
    have e1 : l₁ ≫ k₁ = l₂ ≫ k₂ := by
      rw [← cancel_mono U.ι]
      simp only [k₁, k₂, l₁, l₂, Category.assoc, Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι_assoc, hc]
    have e2 : l₂ ≫ (V₂.ι ≫ Y₂.hom) = (V₀.ι ≫ Y₀.hom) ≫ Spec.map g₂ := by
      simp only [l₂, Category.assoc, Scheme.Hom.resLE_comp_ι_assoc, hc₂]
    have hfl' : Flat (Over.mk (U.ι ≫ Y.hom)).hom := by
      haveI := hfl
      show Flat (U.ι ≫ Y.hom)
      infer_instance
    have H : IsPushout l₁ l₂ k₁ k₂ :=
      GlobalTheory.T.flat_over_artinFibreProduct_isPushout P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hpb hloc hart hs₁ hs₂ (Over.mk (U.ι ≫ Y.hom))
        (Over.mk (V₁.ι ≫ Y₁.hom)) (Over.mk (V₂.ι ≫ Y₂.hom)) (Over.mk (V₀.ι ≫ Y₀.hom)) k₁ k₂ l₁ l₂
        hfl' pb1 pb2 pb0 e1 e2
    have hj : ∀ d : Γ(Y.left, U), k₁.appTop.hom (U.topIso.inv.hom d) = V₁.topIso.inv.hom ((j₁.app U).hom d) ∧
        k₂.appTop.hom (U.topIso.inv.hom d) = V₂.topIso.inv.hom ((j₂.app U).hom d) := fun d =>
      ⟨(resLE_appTop_topIso_inv j₁ le_rfl d).trans (by rw [Scheme.Hom.app_eq_appLE]),
       (resLE_appTop_topIso_inv j₂ le_rfl d).trans (by rw [Scheme.Hom.app_eq_appLE])⟩
    refine ⟨fun s₁ s₂ h => ?_, fun d d' e₁ e₂ => ?_⟩
    · obtain ⟨t, ht1, ht2⟩ := pushout_sec_exists H (V₁.topIso.inv.hom s₁) (V₂.topIso.inv.hom s₂)
        (by rw [resLE_appTop_topIso_inv, resLE_appTop_topIso_inv, h])
      refine ⟨U.topIso.hom.hom t, ?_, ?_⟩
      · have := congrArg V₁.topIso.hom.hom ((hj (U.topIso.hom.hom t)).1)
        rwa [Iso.hom_inv_id_apply, ht1, Iso.inv_hom_id_apply, Iso.inv_hom_id_apply, eq_comm] at this
      · have := congrArg V₂.topIso.hom.hom ((hj (U.topIso.hom.hom t)).2)
        rwa [Iso.hom_inv_id_apply, ht2, Iso.inv_hom_id_apply, Iso.inv_hom_id_apply, eq_comm] at this
    · have := pushout_sec_ext H (U.topIso.inv.hom d) (U.topIso.inv.hom d')
        (by rw [(hj d).1, (hj d').1, e₁]) (by rw [(hj d).2, (hj d').2, e₂])
      have := congrArg U.topIso.hom.hom this
      rwa [Iso.inv_hom_id_apply, Iso.inv_hom_id_apply] at this
  refine ⟨fun U a₁ a₂ hg => ?_, fun U d d' e₁ e₂ => Units.ext ((key U).2 d.val d'.val
    (congrArg Units.val e₁) (congrArg Units.val e₂))⟩
  have heq : ∀ (b₁ : Γ(Y₁.left, j₁ ⁻¹ᵁ U)ˣ) (b₂ : Γ(Y₂.left, j₂ ⁻¹ᵁ U)ˣ),
      (∀ x : Y₀.left, i₁ x ∈ j₁ ⁻¹ᵁ U → gm i₁ x (j₁ ⁻¹ᵁ U) b₁ = gm i₂ x (j₂ ⁻¹ᵁ U) b₂) →
      (i₁.appLE (j₁ ⁻¹ᵁ U) (i₁ ⁻¹ᵁ (j₁ ⁻¹ᵁ U)) le_rfl).hom b₁.val =
        (i₂.appLE (j₂ ⁻¹ᵁ U) (i₁ ⁻¹ᵁ (j₁ ⁻¹ᵁ U)) (hle U)).hom b₂.val := by
    intro b₁ b₂ hb
    apply TopCat.Presheaf.section_ext Y₀.left.sheaf
    intro x hx
    have := congrArg Units.val (hb x hx)
    rw [gm_val i₁ x _ hx, gm_val i₂ x _ (hle U hx)] at this
    simp only [Scheme.Hom.appLE, CommRingCat.comp_apply]
    erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
    exact this
  obtain ⟨d, hd1, hd2⟩ := (key U).1 a₁.val a₂.val (heq a₁ a₂ hg)
  obtain ⟨d', hd1', hd2'⟩ := (key U).1 (a₁⁻¹).val (a₂⁻¹).val (heq a₁⁻¹ a₂⁻¹ (fun x hx => by
    rw [map_inv, map_inv, hg x hx]))
  have hdd : d * d' = 1 := (key U).2 _ _ (by rw [map_mul, map_one, hd1, hd1', Units.mul_inv])
    (by rw [map_mul, map_one, hd2, hd2', Units.mul_inv])
  exact ⟨⟨d, d', hdd, by rw [mul_comm, hdd]⟩, Units.ext hd1, Units.ext hd2⟩

end GlobalTheory.PinchUnits
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryTraitPullbackThetaSystemStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitaryTrait_pullback_thetaSystem : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (u' : Sp (ratHull S.R) ⟶ Xo.XF cf) (G : Over (Sp (ratHull S.R))) (_ : GrpObj G) (α : G.left ⟶ ρ.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left), IsGrpPullback G ρ.P.A (spMap (toRat S.R)) α → IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β → LBIso (ρ.P.L.pull α) (Xo.univ.t.PP.L.pull β) → ∀ (T : UTrait Xo cf) (yK : ratHull S.R →+* FractionRing T.V), spMap yK ≫ u' = T.y → ∃ φ : T.P.A.A.left ⟶ ρ.P.A.left, IsGrpPullback T.P.A.A ρ.P.A (spMap (yK.comp (toRat S.R))) φ ∧ LBIso T.P.A.L (ρ.P.L.pull φ) ∧ ∀ (Y : Over (Sp (FractionRing T.V))) (x x' : Y ⟶ T.P.A.A) (w w' : Y.left ⟶ G.left) (a : 𝓞 E), w ≫ α = x.left ≫ φ → w' ≫ α = x'.left ≫ φ → w' ≫ β = w ≫ β ≫ (Xo.univ.t.act.act a).left → x' = x ≫ T.P.oA.act a := by
  first | exact @GlobalTheory.UPoinc.TraitPullAct.exists_pull_act | exact GlobalTheory.UPoinc.TraitPullAct.exists_pull_act | (intros; apply GlobalTheory.UPoinc.TraitPullAct.exists_pull_act <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVeryAmpleFourthPowerPolarisedAbelianField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.FieldVA

variable {X : Scheme.{0}}

theorem nonzeroLocus_pullPow (L : LB X) (N : ℕ) (t : (lbPow L N).Sec) :
    nonzeroLocus (GlobalTheory.ZH.CrdMove.pullPow (𝟙 X) t) = nonzeroLocus t := by
  apply le_antisymm
  · refine iSup_le fun j y hy => ?_
    have hy' : y ∈ X.basicOpen ((Scheme.Hom.appLE (𝟙 X) _ _ (GlobalTheory.ZH.CrdMove.pow_chart_le L N (𝟙 X) j)).hom
        (t.f (fun _ => j 0))) := hy
    rw [Scheme.basicOpen_appLE] at hy'
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨_, hy'.2⟩
  · refine iSup_le fun j y hy => ?_
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => j PUnit.unit, ?_⟩
    have hc : y ∈ (lbPow L N).U j := X.basicOpen_le (t.f j) hy
    show y ∈ X.basicOpen ((Scheme.Hom.appLE (𝟙 X) _ _
      (GlobalTheory.ZH.CrdMove.pow_chart_le L N (𝟙 X) (fun _ => j PUnit.unit))).hom (t.f (fun _ => j PUnit.unit)))
    rw [Scheme.basicOpen_appLE]
    exact ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hc PUnit.unit, hy⟩

end GlobalTheory.Mum.FieldVA

namespace GlobalTheory.Mum

open GlobalTheory.Mum.FieldVA in

theorem veryAmpleAlong_field (hA : AmpleSt) (K : Type) [Field K] (P : PolAV (Sp K)) :
    ∃ (m : ℕ) (b : Fin (m + 1) → H0 P.L 4), VeryAmpleAlong P.A.hom (𝟙 P.A.left) P.L b := by
  obtain ⟨m, t, hcov, hs⟩ := GlobalTheory.ZH.CrdMove.immBy_lbPow hA K P 4 le_rfl
  have hb : ∀ i, nonzeroLocus (GlobalTheory.ZH.CrdMove.pullPow (𝟙 P.A.left) (t i)) = nonzeroLocus (t i) :=
    fun i => nonzeroLocus_pullPow P.L 4 (t i)
  refine ⟨m, fun i => GlobalTheory.ZH.CrdMove.pullPow (𝟙 P.A.left) (t i), ?_, fun i => ?_⟩
  · refine _root_.top_le_iff.1 fun y _ => ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1
      (show y ∈ ⨆ i ∈ Set.univ, nonzeroLocus (t i) by rw [hcov]; trivial)
    obtain ⟨_, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hi
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, show y ∈ nonzeroLocus (GlobalTheory.ZH.CrdMove.pullPow (𝟙 P.A.left) (t i)) by
      rw [hb]; exact hi⟩
  obtain ⟨haff, r, hr, hsurj⟩ := hs i (Set.mem_univ i)
  have hW : (𝟙 P.A.left) ⁻¹ᵁ nonzeroLocus (GlobalTheory.ZH.CrdMove.pullPow (𝟙 P.A.left) (t i)) = nonzeroLocus (t i) := by
    rw [← hb i]; exact le_antisymm (fun y hy => hy) (fun y hy => hy)
  have le1 := hW.le
  have le2 := hW.ge
  have hconst : ∀ a, resG P.A.left le1 (constFn P.A.hom (nonzeroLocus (t i)) a) =
      AbLaw.cst P.A.hom ((𝟙 P.A.left) ⁻¹ᵁ nonzeroLocus (GlobalTheory.ZH.CrdMove.pullPow (𝟙 P.A.left) (t i))) a := by
    intro a
    have h2 : constFn P.A.hom ((𝟙 P.A.left) ⁻¹ᵁ nonzeroLocus (GlobalTheory.ZH.CrdMove.pullPow (𝟙 P.A.left) (t i))) a =
        AbLaw.cst P.A.hom ((𝟙 P.A.left) ⁻¹ᵁ nonzeroLocus (GlobalTheory.ZH.CrdMove.pullPow (𝟙 P.A.left) (t i))) a := rfl
    refine (fn_ext fun x hx => ?_).trans h2
    rw [gs_res _ x le1 hx, gs_constFn _ _ _ _ (le1 hx), gs_constFn _ _ _ _ hx]
  refine ⟨by rw [hW]; exact haff, fun j => resG P.A.left le1 (r j), fun j c a ha hc => ?_, ?_⟩
  · have hc' : a ∈ (lbPow P.L 4).U (fun _ => c 0) := Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hc 0
    have key : ∀ s : (lbPow P.L 4).Sec, secGerm (𝟙 P.A.left) a (GlobalTheory.ZH.CrdMove.pullPow (𝟙 P.A.left) s) c =
        gs (𝟙 P.A.left) a ((lbPow P.L 4).U (fun _ => c 0)) (s.f (fun _ => c 0)) := fun s =>
      (gs_appLE (𝟙 P.A.left) _ _ _ (𝟙 P.A.left) a hc _).trans
        (congrArg (fun q => gs q a _ (s.f (fun _ => c 0))) (Category.id_comp _))
    have hm : (𝟙 P.A.left) a ∈ nonzeroLocus (t i) ⊓ (lbPow P.L 4).U (fun _ => c 0) := ⟨le1 ha, hc'⟩
    have e := congrArg (gs (𝟙 P.A.left) a _) (hr j (fun _ => c 0))
    rw [gs_res _ a _ hm, gs_mul _ a _ hm, gs_res _ a _ hm, gs_res _ a _ hm] at e
    rw [key, key, gs_res _ a le1 ha]
    exact e
  · have hρ : ∀ f, resG P.A.left le1 (resG P.A.left le2 f) = f := fun f => fn_ext fun x hx => by
      rw [gs_res _ x le1 hx, gs_res _ x le2 (le1 hx)]
    have hcl : Subring.closure (Set.range (constFn P.A.hom (nonzeroLocus (t i))) ∪ Set.range r) ≤
        (MvPolynomial.eval₂Hom (AbLaw.cst P.A.hom
          ((𝟙 P.A.left) ⁻¹ᵁ nonzeroLocus (GlobalTheory.ZH.CrdMove.pullPow (𝟙 P.A.left) (t i))))
          (fun j => resG P.A.left le1 (r j))).range.comap (resG P.A.left le1) := by
      refine Subring.closure_le.2 ?_
      rintro g (⟨a, rfl⟩ | ⟨j, rfl⟩)
      · exact Subring.mem_comap.2 (RingHom.mem_range.2 ⟨MvPolynomial.C a, by
          rw [MvPolynomial.eval₂Hom_C]; exact (hconst a).symm⟩)
      · exact Subring.mem_comap.2 (RingHom.mem_range.2 ⟨MvPolynomial.X j, by rw [MvPolynomial.eval₂Hom_X']⟩)
    intro f
    obtain ⟨p, hp⟩ := RingHom.mem_range.1 (Subring.mem_comap.1
      (hcl (hsurj ▸ Subring.mem_top (resG P.A.left le2 f))))
    exact ⟨p, hp.trans (hρ f)⟩

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightZeroSectionNonzeroAtOriginStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weightZero_section_nonzero_at_origin : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)), ∃ k₀ : ℕ, ∀ k ≥ k₀, ∃ b : D.toPre.SecB k 0, eSec D.toPre.P.A (closedPoint R) ∈ nonzeroLocus b := by
  first | exact @GlobalTheory.Mum.exists_secB_zero_nonzero_origin | exact GlobalTheory.Mum.exists_secB_zero_nonzero_origin | (intros; apply GlobalTheory.Mum.exists_secB_zero_nonzero_origin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightZeroSectionNotVanishingClosedFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weightZero_section_not_vanishing_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (D : DegData R (maximalIdeal R)) (k : ℕ), 2 ≤ k → ∀ x : D.toPre.P.A.left,
      D.toPre.P.A.hom x = closedPoint R →
      ∃ (σ : D.toPre.SecB k 0) (j : Fin 4 → D.toPre.P.L.ι), x ∈ D.toPre.P.A.left.basicOpen (σ.f j) := by
  first | exact @GlobalTheory.Mum.exists_secB_zero_mem_basicOpen | exact GlobalTheory.Mum.exists_secB_zero_mem_basicOpen | (intros; apply GlobalTheory.Mum.exists_secB_zero_mem_basicOpen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionScalarArbitraryOfMembersZeroStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expansion_scalar_arbitrary_of_members_zero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ), 1 ≤ k → ∀ (s : SecK C.P.L.L C.α k) (F : IntFam (maximalIdeal R) D.toPre k), (∀ α j, (F.f α).f j = 0) → ∀ a b : W, T.Exp a b s F → ∀ b' : W, T.Exp a b' s F := by
  first | exact @GlobalTheory.Mum.ZeroFam.exp_of_members_zero | exact GlobalTheory.Mum.ZeroFam.exp_of_members_zero | (intros; apply GlobalTheory.Mum.ZeroFam.exp_of_members_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExponentEstimateFromLanglandsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exponent_estimate_from_langlands : GlobalTheory.Published.ClozelCohomological → GlobalTheory.Published.CohomologicalCsdTempered → GlobalTheory.Published.HeckeLAdicCharacter → GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.DiscreteSpectrumGL → GlobalTheory.Published.GaloisRepOfPolarizedCuspidal → GlobalTheory.Published.BaseChangeDefiniteUnitary → GlobalTheory.Published.BhattScholzeCrystallineLattices → GlobalTheory.Published.HeckeLAdicCharacterAbove → GlobalTheory.Published.LocalLanglandsGL → GlobalTheory.BigOn.ExpSt := by
  first | exact @GlobalTheory.BigOn.expSt_of_hypotheses | exact GlobalTheory.BigOn.expSt_of_hypotheses | (intros; apply GlobalTheory.BigOn.expSt_of_hypotheses <;> assumption)
end

