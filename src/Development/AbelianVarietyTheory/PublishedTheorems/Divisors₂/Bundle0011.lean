import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0030
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbDual

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published

def CubeTheorem : Prop :=
  ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB →
    ∀ (T : Over S) (a b c : T ⟶ A),
      GlobalTheory.AbLaw.Triv (LB.LinComb L (fun k : Fin 8 ↦ (![a * b * c, a * b, a * c, b * c, a, b, c, 1] k).left) ![1, -1, -1, -1, 1, 1, 1, -1])

end GlobalTheory.Published
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsThetaMeanSquareNorm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto

noncomputable section

namespace GlobalTheory.MBModel

variable {K : Type} [Field K] [NumberField K] {P : Out.PolAV (Sp K)} {AA : Over (Sp (𝓞 K))} [GrpObj AA] [IsCommMonObj AA]
  {φ : P.A.left ⟶ AA.left} {MM : RigLB AA} {n : ℕ}

def RigIs (w : LB.Iso (MM.L.pull φ) (lbPow P.L n)) (σ : K →+* ℂ) {Q : Out.PolAV (Sp ℂ)} {ψ : Q.A.left ⟶ P.A.left}
    (wσ : LB.Iso ((lbPow P.L n).pull ψ) (lbPow Q.L n)) {g : ℕ} (u : HolUnif Q.A Q.L g) (ρ : ℂ) : Prop :=
  ∀ (k : (lbPow Q.L n).ι) (j : ((lbPow P.L n).pull ψ).ι) (p : PUnit → MM.L.ι),
    ⊤ ≤ (u.ex 0).left ⁻¹ᵁ ((lbPow Q.L n).U k ⊓ ((lbPow P.L n).pull ψ).U j) →
    ⊤ ≤ ((u.ex 0).left ≫ ψ) ⁻¹ᵁ ((lbPow P.L n).U (j PUnit.unit) ⊓ (MM.L.pull φ).U p) →
    valAt' (u.ex 0).left ((lbPow Q.L n).U k ⊓ ((lbPow P.L n).pull ψ).U j) (wσ.s (k, j)).val *
      valAt' ((u.ex 0).left ≫ ψ) ((lbPow P.L n).U (j PUnit.unit) ⊓ (MM.L.pull φ).U p) (w.s (j PUnit.unit, p)).val *
      valAt' (X := (𝟙_ (Over (Sp (𝓞 K)))).left) (spMap (σ.comp (algebraMap (𝓞 K) K))) ((MM.L.pull (eSec AA)).U p)
        (MM.rig.s p).val = ρ * u.fr (k PUnit.unit) 0 ^ n

def IsThetaMeanSquareNorm (w : LB.Iso (MM.L.pull φ) (lbPow P.L n)) {r : ℕ} (b : Fin r → (lbPow P.L n).Sec)
    (hE : HermFam K (Fin r → K)) (g : ℕ) : Prop :=
  ∀ (σ : K →+* ℂ) (Q : Out.PolAV (Sp ℂ)) (ψ : Q.A.left ⟶ P.A.left)
    (wσ : LB.Iso ((lbPow P.L n).pull ψ) (lbPow Q.L n)) (s : Fin r → (lbPow Q.L n).Sec)
    (u : HolUnif Q.A Q.L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (ρ : ℂ)
    (θ : Fin r → (Fin g → ℂ) → ℂ) (Fd : Set (Fin g → ℂ)),
    IsPolFibre σ P Q ψ → wσ.IsGen → (∀ i, SecMaps wσ (secPull (b i) ψ) (s i)) → u.IsAH Hm χ → RigIs w σ wσ u ρ →
    (∀ i, u.IsFnPow n (s i) (θ i)) → IsAddFundamentalDomain u.Λ Fd volume →
    ∀ i j, hE.form σ (Pi.single i 1) (Pi.single j 1) =
      (∫ z in Fd, starRingEnd ℂ (θ i z) * θ j z * (Real.exp (-(Real.pi * n * (hermForm Hm z z).re)) : ℝ)) /
        (((volume Fd).toReal * ‖ρ‖ ^ 2 : ℝ) : ℂ)

def IsModel (w : LB.Iso (MM.L.pull φ) (lbPow P.L n)) : Prop :=
  Smooth AA.hom ∧ IsSeparated AA.hom ∧ QuasiCompact AA.hom ∧ IsGrpPullback P.A AA (spMap (algebraMap (𝓞 K) K)) φ ∧
  (∃ (G : Over (Sp (𝓞 K))) (_ : GrpObj G) (j : G ⟶ AA) (φ₀ : P.A.left ⟶ G.left), IsSemiAbelian G ∧ IsMonHom j ∧
    IsOpenImmersion j.left ∧ φ₀ ≫ j.left = φ ∧ IsGrpPullback P.A G (spMap (algebraMap (𝓞 K) K)) φ₀) ∧
  Nonempty (CubicalStr AA MM) ∧ w.IsGen ∧
  ∃ (Z : Scheme.{0}) (ζ : Z ⟶ AA.left), IsClosedImmersion ζ ∧ IsFinite (ζ ≫ AA.hom) ∧ Flat (ζ ≫ AA.hom) ∧
    ∀ (T : Over (Sp K)) (x : T ⟶ P.A), x ^ (2 * n) = 1 ↔ ∃ y : T.left ⟶ Z, y ≫ ζ = x.left ≫ φ

end GlobalTheory.MBModel

namespace GlobalTheory.Published

open GlobalTheory.MBModel

def MoretBaillyModel : Prop := ∀ (K : Type) [Field K] [NumberField K] (F : SemiFib K) (h : HermFam K (Fin F.P₀.g → K)),
  F.IsHerm h → ∀ n : ℕ, 1 ≤ n → ∀ (K' : Type) [Field K'] [NumberField K'] [Algebra K K'],
    ∃ (K'' : Type) (_ : Field K'') (_ : NumberField K'') (_ : Algebra K' K'') (_ : Algebra K K'') (_ : IsScalarTower K K' K'')
      (P : Out.PolAV (Sp K'')) (ψ : P.A.left ⟶ F.P₀.A.left) (AA : Over (Sp (𝓞 K''))) (_ : GrpObj AA) (_ : IsCommMonObj AA)
      (φ : P.A.left ⟶ AA.left) (MM : RigLB AA) (w : LB.Iso (MM.L.pull φ) (lbPow P.L n))
      (b : Fin (n ^ F.P₀.g) → (lbPow P.L n).Sec) (E : Submodule (𝓞 K'') (Fin (n ^ F.P₀.g) → K''))
      (hE : HermFam K'' (Fin (n ^ F.P₀.g) → K'')),
      IsPolFibre (algebraMap K K'') F.P₀ P ψ ∧ IsModel w ∧
      Function.Bijective (fun c : Fin (n ^ F.P₀.g) → K'' => secComb P.A.hom c b) ∧
      (∀ c, c ∈ E ↔ ∃ t : MM.L.Sec, SecMaps w (secPull t φ) (secComb P.A.hom c b)) ∧
      IsThetaMeanSquareNorm w b hE F.P₀.g ∧ Full E ∧
      MuLe hE E (-F.falt h / 2 + (F.P₀.g : ℝ) / 4 * Real.log (n / (2 * Real.pi))) ∧
      deg hE E = (n ^ F.P₀.g : ℕ) * (-F.falt h / 2 + (F.P₀.g : ℝ) / 4 * Real.log (n / (2 * Real.pi)))

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.OfAbelianDeRham
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published.AbelianDeRhamStructure.Test

variable {R : Type} [CommRing R]

theorem isAb_sq {A : Over (Sp R)} [GrpObj A] (hA : IsAbelianScheme A) : IsAbelianScheme (A ⊗ A) := by
  have := hA.comm
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  refine ⟨inferInstance, ?_, ?_, ?_⟩
  · rw [Over.tensorObj_hom, Limits.pullback.condition]
    infer_instance
  · rw [Over.tensorObj_hom, Limits.pullback.condition]
    infer_instance
  · rw [Over.tensorObj_hom, Limits.pullback.condition]
    exact GeometricallyConnected.comp _ _

theorem pull_one {Y A : Over (Sp R)} [GrpObj A] (c : FirstDeRham (A.hom ≫ 𝟙 _)) :
    pullOver (dp0 R) (𝟙 _) (1 : Y ⟶ A) c = 0 := by
  haveI : IsIso ((𝟙_ (Over (Sp R))).hom ≫ 𝟙 _) := inferInstanceAs (IsIso (𝟙 (Sp R) ≫ 𝟙 _))
  rw [Hom.one_def, ← pullOver_pullOver, firstDeRham_base_eq_zero _ (pullOver (dp0 R) (𝟙 _) η[A] c), map_zero]

theorem pull_id {A : Over (Sp R)} (c : FirstDeRham (A.hom ≫ 𝟙 _)) :
    pullOver (dp0 R) (𝟙 _) (𝟙 A) c = c := IsMor.pullCohomologyOne_id _ _

theorem allPrim (H : AbelianDeRhamFree) {A : Over (Sp R)} [GrpObj A] {g : ℕ} (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) : AllPrim (dp0 R) (𝟙 _) A := by
  have hg2 : SmoothOfRelativeDimension (g + g) (A ⊗ A).hom := by
    have : SmoothOfRelativeDimension g (Limits.pullback.fst A.hom A.hom) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
        (IsPullback.of_hasPullback A.hom A.hom).flip hg
    rw [Over.tensorObj_hom]
    exact smoothOfRelativeDimension_comp g g _ _
  obtain ⟨f1, p1, r1, -⟩ := H R A g hA hg
  obtain ⟨f2, p2, r2, -⟩ := H R (A ⊗ A) (g + g) (isAb_sq hA) hg2
  let r : FirstDeRham ((A ⊗ A).hom ≫ 𝟙 _) →ₗ[R] FirstDeRham (A.hom ≫ 𝟙 _) × FirstDeRham (A.hom ≫ 𝟙 _) :=
    (pullOver (dp0 R) (𝟙 _) (lift (𝟙 A) 1)).prod (pullOver (dp0 R) (𝟙 _) (lift 1 (𝟙 A)))
  have hv : ∀ x, r x = (pullOver (dp0 R) (𝟙 _) (lift (𝟙 A) 1) x, pullOver (dp0 R) (𝟙 _) (lift 1 (𝟙 A)) x) :=
    fun _ ↦ rfl
  have hr : ∀ a b, r (pullOver (dp0 R) (𝟙 _) (fst A A) a + pullOver (dp0 R) (𝟙 _) (snd A A) b) = (a, b) := by
    intro a b
    rw [hv]
    simp only [map_add, pullOver_pullOver, lift_fst, lift_snd, pull_one,
      pull_id, add_zero, zero_add]
  have hs : Function.Surjective r := fun x ↦ ⟨_, hr x.1 x.2⟩
  have hb : Function.Bijective r :=
    Module.bijective_of_surjective_of_rankAtStalk_eq hs fun m _ ↦ by
      rw [Module.rankAtStalk_prod, Pi.add_apply, r1, r2]; ring
  refine eq_top_iff.2 fun c _ ↦ (mem_prim_iff _ _ A c).2 (hb.1 ?_)
  rw [hr, hv]
  simp only [pullOver_pullOver, ← Hom.mul_def, _root_.mul_one, _root_.one_mul, pull_id]

theorem free_iff : AbelianDeRhamFree ↔ AbelianDeRham.Free :=
  ⟨fun H R _ A _ g hA hg ↦ ⟨allPrim H hA hg, H R A g hA hg⟩, fun H R _ A _ g hA hg ↦ (H R A g hA hg).2⟩

theorem of_abelianDeRham (H : AbelianDeRham) : AbelianDeRhamStructure :=
  ⟨free_iff.2 H.1, H.2.1, H.2.2.1⟩

theorem elliptic (H : AbelianDeRhamStructure) (k : Type) [Field k] (W : WeierstrassCurve k) [W.IsElliptic] :
    (∀ p : PrimeSpectrum k, Module.rankAtStalk (primDR (GlobalTheory.WeierstrassCurve.ellPolAV W).A) p = 2) ∧
    (∀ p : PrimeSpectrum k, Module.rankAtStalk (PrimitiveSubmodule (GlobalTheory.WeierstrassCurve.ellPolAV W).A) p = 1) ∧
    Module.finrank k (SecondDeRham ((GlobalTheory.WeierstrassCurve.ellPolAV W).A.hom ≫ 𝟙 _)) = 1 := by
  let P := GlobalTheory.WeierstrassCurve.ellPolAV W
  have hg : SmoothOfRelativeDimension 1 P.A.hom := P.smoothDim
  refine ⟨((free_iff.1 H.1).prim P.isAb hg).2.2, (H.2.1 k P.A 1 P.isAb hg).2.2.2.2, ?_⟩
  obtain ⟨f, p, r, e, -⟩ := H.1 k P.A 1 P.isAb hg
  have h2 : Module.finrank k (FirstDeRham (P.A.hom ≫ 𝟙 _)) = 2 := by
    have := r ⊥
    rwa [Module.rankAtStalk_eq_finrank_of_free] at this
  rw [← e.finrank_eq, exteriorPower.finrank_eq, h2]
  rfl

theorem unit_baseChange (R' : Type) [CommRing R'] [Algebra R R']
    (φ : (𝟙_ (Over (Sp R'))).left ⟶ (𝟙_ (Over (Sp R))).left)
    (h : IsGrpPullback (𝟙_ (Over (Sp R'))) (𝟙_ (Over (Sp R))) (spMap (algebraMap R R')) φ) :
    (AbelianDeRham.bcMor h).IsBC ∧ PrimitiveSubmodule (𝟙_ (Over (Sp R'))) =
      Submodule.span R' ((AbelianDeRham.bcMor h).pull '' (PrimitiveSubmodule (𝟙_ (Over (Sp R))))) := by
  have : Subsingleton (primDR (𝟙_ (Over (Sp R)))) :=
    ⟨fun a b ↦ (primDR_unit a).trans (primDR_unit b).symm⟩
  have : Subsingleton (primDR (𝟙_ (Over (Sp R')))) :=
    ⟨fun a b ↦ (primDR_unit a).trans (primDR_unit b).symm⟩
  exact ⟨⟨fun a b _ ↦ Subsingleton.elim a b, fun c ↦ ⟨0, Subsingleton.elim _ _⟩⟩, Subsingleton.elim _ _⟩

end GlobalTheory.Published.AbelianDeRhamStructure.Test
end
end

