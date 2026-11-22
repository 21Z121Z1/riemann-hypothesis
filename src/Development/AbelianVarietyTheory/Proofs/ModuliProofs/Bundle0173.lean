import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0171
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.EqIdOfFixesTorsion
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivBasicOpenOfTrivFibre
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0069
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0016
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0122
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0172
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0008
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0004
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0010
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivPullCompIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0114
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0090
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0092
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0096
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0111
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0143
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0047
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0098
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0105
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0048
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0132

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.EighthPowerThetaObjectOfUniformisationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eighthPower_theta_object_of_uniformisation : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (h : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (σ : Fin 8 × Fin h ≃ Fin g) (EF : LinearMap.BilinForm ℤ (Fin 8 → (Fin h ⊕ Fin h → ℤ))), IsE8 W → IsSharpBasis W bas → (W + W.transpose) * a w = W → (W + W.transpose) * a w' = W.transpose → (∀ x y, EF x y = ∑ u, ∑ v, (W + W.transpose) u v * omegaStd (x u) (y v)) → ∀ (t : TObj g k J b (spMap em)) (τ : Matrix (Fin h) (Fin h) ℂ) (m : (Fin h ⊕ Fin h → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (Q : (Fin 8 → (Fin h ⊕ Fin h → ℤ)) →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), ((τ).IsSymm ∧ ((τ).map Complex.im).PosDef) → (∀ x y, Complex.exp (-(2 * Real.pi * Complex.I) * (omegaStd (m x) (m y) : ℂ) / k) = em (b.ζ : o) ^ omegaStd x y) → (∀ x u i, Q x (σ (u, i)) = (τ).mulVec (fun i' => (x u (.inl i') : ℂ)) i + (x u (.inr i) : ℂ)) → (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = EF x y) → (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH Hm χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q x → χ' l = (-1) ^ EF x ((fun j (x : (Fin 8 → (Fin h ⊕ Fin h → ℤ))) u => ∑ v, a j u v • x v) w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q ((fun i u => m (bas (Pi.single i 1) u)) i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q ((fun j (x : (Fin 8 → (Fin h ⊕ Fin h → ℤ))) u => ∑ v, a j u v • x v) j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) → SharpClass W a bas em t := by
  first | exact @GlobalTheory.sharpClass_of_unif | exact GlobalTheory.sharpClass_of_unif | (intros; apply GlobalTheory.sharpClass_of_unif <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClosedTriv
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

namespace GlobalTheory.SeesawGlobal

theorem isPullback_tensor {S : Scheme.{0}} (T A : Over S) :
    IsPullback (snd T A).left (fst T A).left A.hom T.hom :=
  (IsPullback.of_hasPullback T.hom A.hom).flip

theorem exists_closed_triv :
    Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (T : Over (Sp K)) (N : LB (T ⊗ P.A).left), N.IsLB → (∃ t : (N.pull (lift (𝟙 T) (1 : T ⟶ P.A)).left).Gen, t.IsGen) → ∃ (Z : Scheme.{0}) (i : Z ⟶ T.left), IsClosedImmersion i ∧ ∀ (T' : Over (Sp K)) (h : T' ⟶ T), (∃ t : (N.pull (h ▷ P.A).left).Gen, t.IsGen) ↔ ∃ u : T'.left ⟶ Z, u ≫ i = h.left := by
  intro hL _ K _ _ P T N hN h0
  have hproj : GlobalTheory.AbLaw.IsProjBy P.A.hom := by
    obtain ⟨n, -, m, s, h₁, h₂⟩ := GlobalTheory.AbLaw.polAV_veryAmpleBy hL.polBaseChange (Sp K) P K (𝟙 _) P.A.left
      (𝟙 _) P.A.hom (IsPullback.of_horiz_isIso ⟨by simp⟩)
    exact ⟨_, h₁, m, s, h₂⟩
  obtain ⟨H, j, hj, hH⟩ := GlobalTheory.T.exists_closedSubscheme_locallyTrivial_product_lineBundle hL.globalFns K T P.A P.isAb hproj N hN
  refine ⟨H.left, j.left, hj, fun T' h => ⟨?_, ?_⟩⟩
  · rintro ⟨t, ht⟩
    obtain ⟨y, hy⟩ := (hH T' h).1 fun p => ⟨⊤, trivial, GlobalTheory.TorsionFixedAut.exists_gen_pull _ t ht _⟩
    exact ⟨y.left, congrArg (·.left) hy⟩
  · rintro ⟨u, hu⟩
    have hw : u ≫ H.hom = T'.hom := by rw [← Over.w j, ← Category.assoc, hu, Over.w h]
    have hloc := (hH T' h).2 ⟨Over.homMk u hw, Over.OverMorphism.ext hu⟩
    refine GlobalTheory.exists_gen_of_local_of_section (T' ⊗ P.A).left T'.left (fst T' P.A).left
      (lift (𝟙 T') (1 : T' ⟶ P.A)).left _ (pull_isLB hN _)
      (congrArg (·.left) (lift_fst (𝟙 T') (1 : T' ⟶ P.A)))
      (GlobalTheory.BaseChangeFns.app_surjective hL.globalFns _ P.A P.isAb _ _ T'.hom _ _ (isPullback_tensor T' P.A))
      hloc ?_
    refine GlobalTheory.AbLaw.CubeOpen.triv_pull_pull _ _ (GlobalTheory.AbLaw.CubeOpen.triv_comp h.left ?_ h0)
    have e : h ≫ lift (𝟙 T) (1 : T ⟶ P.A) = lift (𝟙 T') (1 : T' ⟶ P.A) ≫ h ▷ P.A := by
      ext <;> simp
    exact congrArg (·.left) e

end GlobalTheory.SeesawGlobal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteFlatSurjectiveMulByNAbelianSchemeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_flat_surjective_mul_by_n_abelianScheme : Out.Laws → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ M : LB A.left, M.IsLB → Out.RelAmple A M → ∀ n : ℕ, 1 ≤ n → IsFinite ((𝟙 A) ^ n : A ⟶ A).left ∧ Flat ((𝟙 A) ^ n : A ⟶ A).left ∧ Surjective ((𝟙 A) ^ n : A ⟶ A).left := by
  first | exact @GlobalTheory.MulAmple.finite_flat_surjective_pow | exact GlobalTheory.MulAmple.finite_flat_surjective_pow | (intros; apply GlobalTheory.MulAmple.finite_flat_surjective_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HilbertFunctionVanishingIdealVeryAmpleSystemStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertFunction_vanishingIdeal_veryAmpleSystem : ∀ (K σ : Type) [Field K] [Finite σ] [Nonempty σ] (X : Scheme.{0}) (p : X ⟶ Sp K) (M : LB X) (th : σ → M.Sec), M.IsLB → VAmp p M th → ∃ Q : Polynomial ℚ, ∀ᶠ e : ℕ in Filter.atTop, ∃ r, SectionsHaveFiniteDimension p (lbPow M e) r ∧ (r : ℚ) = Q.eval (e : ℚ) ∧ dimDeg (idealOf p M th (𝟙 X)) e + r = Module.finrank K ↥(MvPolynomial.homogeneousSubmodule σ K e) := by
  first | exact @GlobalTheory.ZV.HilbFn.hilbertFunction_idealOf | exact GlobalTheory.ZV.HilbFn.hilbertFunction_idealOf | (intros; apply GlobalTheory.ZV.HilbFn.hilbertFunction_idealOf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsogOfSurjectiveBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

noncomputable section

namespace GlobalTheory.IsogDescent

section Grp

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {G₁ G₂ : Over S} {G₁' G₂' : Over S'}

theorem over_ext {T G : Over S} [IsReduced T.left] [IsSeparated G.hom] {a b : T ⟶ G} {W : Scheme.{0}}
    (q : W ⟶ T.left) [Surjective q] (h : q ≫ a.left = q ≫ b.left) : a = b :=
  Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated G.hom ((Over.w a).trans (Over.w b).symm) q h)

variable [GrpObj G₁] [GrpObj G₂] [GrpObj G₁'] [GrpObj G₂'] {φ₁ : G₁'.left ⟶ G₁.left} {φ₂ : G₂'.left ⟶ G₂.left}

theorem mul_comp [Surjective f] [IsSeparated G₂.hom] (h₁ : IsGrpPullback G₁' G₁ f φ₁)
    (h₂ : IsGrpPullback G₂' G₂ f φ₂) (ψ : G₁ ⟶ G₂) (ψ' : G₁' ⟶ G₂') [IsMonHom ψ']
    (hψ : ψ'.left ≫ φ₂ = φ₁ ≫ ψ.left) (T : Over S) [IsReduced T.left] (x y : T ⟶ G₁) :
    (x * y) ≫ ψ = (x ≫ ψ) * (y ≫ ψ) := by
  have H := IsPullback.of_hasPullback T.hom f
  let q := pullback.fst T.hom f
  let W : Over S' := Over.mk (pullback.snd T.hom f)
  let l : (T ⟶ G₁) → (W ⟶ G₁') := fun z => Over.homMk
    (h₁.1.lift (q ≫ z.left) (pullback.snd T.hom f) (by rw [Category.assoc, Over.w z]; exact H.w))
    (h₁.1.lift_snd _ _ _)
  have hl : ∀ z, (l z).left ≫ φ₁ = q ≫ z.left := fun z => h₁.1.lift_fst _ _ _
  let q' : Over.mk (W.hom ≫ f) ⟶ T := Over.homMk q H.w
  have hl' : ∀ z, (q' ≫ z ≫ ψ).left = (l z ≫ ψ').left ≫ φ₂ := fun z => by
    show q ≫ z.left ≫ ψ.left = ((l z).left ≫ ψ'.left) ≫ φ₂
    rw [Category.assoc, hψ, ← Category.assoc (l z).left, hl, Category.assoc]
  have e₁ := h₁.2 W (l x) (l y) (q' ≫ x) (q' ≫ y) (hl x).symm (hl y).symm
  have e₂ := h₂.2 W (l x ≫ ψ') (l y ≫ ψ') (q' ≫ x ≫ ψ) (q' ≫ y ≫ ψ) (hl' x) (hl' y)
  rw [← MonObj.comp_mul] at e₁ e₂
  rw [← MonObj.mul_comp (l x) (l y) ψ'] at e₂
  replace e₂ : _ = (l x * l y).left ≫ ψ'.left ≫ φ₂ := e₂.trans (Category.assoc _ _ _)
  rw [hψ, ← Category.assoc, ← e₁] at e₂
  refine over_ext q ?_
  refine Eq.trans ?_ e₂.symm
  exact (Category.assoc _ _ _).symm

theorem isMonHom [IsReduced S] [Surjective f] [Smooth G₁.hom] [IsSeparated G₂.hom] (h₁ : IsGrpPullback G₁' G₁ f φ₁)
    (h₂ : IsGrpPullback G₂' G₂ f φ₂) (ψ : G₁ ⟶ G₂) (ψ' : G₁' ⟶ G₂') [IsMonHom ψ']
    (hψ : ψ'.left ≫ φ₂ = φ₁ ≫ ψ.left) : IsMonHom ψ := by
  have : IsReduced (𝟙_ (Over S)).left := ‹IsReduced S›
  have : Smooth (G₁ ⊗ G₁).hom := inferInstanceAs (Smooth (pullback.fst G₁.hom G₁.hom ≫ G₁.hom))
  have : IsReduced (G₁ ⊗ G₁).left := GlobalTheory.isReduced_of_smooth_of_isReduced (G₁ ⊗ G₁).hom
  refine ⟨?_, ?_⟩
  · have h := mul_comp h₁ h₂ ψ ψ' hψ (𝟙_ _) 1 1
    rw [_root_.mul_one] at h
    have h' : (1 : 𝟙_ (Over S) ⟶ G₁) ≫ ψ = 1 := mul_eq_left.1 h.symm
    simpa [Hom.one_def] using h'
  · have h := mul_comp h₁ h₂ ψ ψ' hψ (G₁ ⊗ G₁) (fst _ _) (snd _ _)
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at h
    rw [h]; congr 1

theorem kerSet [Surjective f] [IsSeparated G₂.hom] (h₁ : IsPullback φ₁ G₁'.hom G₁.hom f)
    (h₂ : IsPullback φ₂ G₂'.hom G₂.hom f) (he : η[G₂'].left ≫ φ₂ = f ≫ η[G₂].left) (ψ : G₁ ⟶ G₂) (ψ' : G₁' ⟶ G₂')
    (hψ : ψ'.left ≫ φ₂ = φ₁ ≫ ψ.left) (K : Set G₁.left) (hK : KerSet ψ' (φ₁ ⁻¹' K)) : KerSet ψ K := by
  intro k _ _ x z
  obtain ⟨w, -⟩ := (pullback.fst x f).surjective (default : PrimeSpectrum k)
  let k' := AlgebraicClosure ((pullback x f).residueField w)
  let u : Sp k' ⟶ pullback x f :=
    Spec.map (CommRingCat.ofHom (algebraMap ((pullback x f).residueField w) k')) ≫ (pullback x f).fromSpecResidueField w
  let j : Sp k' ⟶ Sp k := u ≫ pullback.fst x f
  let x' : Sp k' ⟶ S' := u ≫ pullback.snd x f
  have hj : j ≫ x = x' ≫ f := by simp only [j, x', Category.assoc, pullback.condition]
  have : Surjective j := ⟨fun a => ⟨(default : PrimeSpectrum k'), Subsingleton.elim (α := PrimeSpectrum k) _ _⟩⟩
  let z' : Over.mk x' ⟶ G₁' := Over.homMk (h₁.lift (j ≫ z.left) x' (by rw [Category.assoc, Over.w z]; exact hj))
    (h₁.lift_snd _ _ _)
  have hz : z'.left ≫ φ₁ = j ≫ z.left := h₁.lift_fst _ _ _
  have a₁ : (z' ≫ ψ').left ≫ φ₂ = j ≫ (z ≫ ψ).left := by
    rw [Over.comp_left, Category.assoc, hψ, ← Category.assoc, hz, Category.assoc]
    rfl
  have a₂ : (1 : Over.mk x' ⟶ G₂').left ≫ φ₂ = j ≫ (1 : Over.mk x ⟶ G₂).left := by
    show (x' ≫ η[G₂'].left) ≫ φ₂ = j ≫ x ≫ η[G₂].left
    rw [Category.assoc, he, ← Category.assoc, ← hj, Category.assoc]
  have : IsReduced (Over.mk x).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of k)))
  have b₁ : z ≫ ψ = 1 ↔ z' ≫ ψ' = 1 :=
    ⟨fun h => Over.OverMorphism.ext (h₂.hom_ext (by rw [a₁, a₂, h]) ((Over.w _).trans (Over.w _).symm)),
      fun h => over_ext (T := Over.mk x) j (by rw [← a₁, ← a₂, h])⟩
  have pt : ∀ a, φ₁ (z'.left a) = z.left (j a) := fun a => congrArg (fun q => q a) hz
  rw [b₁, hK k' x' z']
  constructor
  · rintro h _ ⟨a, rfl⟩
    obtain ⟨a', rfl⟩ := j.surjective a
    rw [← pt]
    exact h ⟨a', rfl⟩
  · rintro h _ ⟨a, rfl⟩
    show φ₁ (z'.left a) ∈ K
    rw [pt]
    exact h ⟨_, rfl⟩

end Grp

section Bundle

theorem exists_gen_pow {X Y : Scheme.{0}} (L : LB X) (e : Y ⟶ X) (n : ℤ) (t : (L.pull e).Gen) (ht : t.IsGen) :
    ∃ c : (LB.LinComb L (K := PUnit) (fun _ => e) (fun _ => n)).Gen, c.IsGen := by
  refine ⟨⟨fun j => (t.s j) ^ n⟩, fun i j => ?_⟩
  refine (map_zpow _ _ _).trans ((congrArg (· ^ n) (ht i j)).trans ((mul_zpow _ _ _).trans
    (congrArg₂ (· * ·) ?_ (map_zpow _ _ _).symm)))
  simp only [LB.pull, LB.LinComb, Fintype.prod_unique, zpow_one]
  rfl

theorem lbIso_of_surjective {S S' X' : Scheme.{0}} [IsReduced S] (A : Over S) [GrpObj A] [IsCommMonObj A]
    (M : LB A.left) (hA : IsAbelianScheme A) (hM : M.IsLB) (ha : Out.RelAmple A M) {f : S' ⟶ S} [Surjective f]
    {φ : X' ⟶ A.left} {g : X' ⟶ S'} (h : IsPullback φ g A.hom f) {P Q : LB A.left} (hP : P.IsLB) (hQ : Q.IsLB)
    (hi : LBIso (P.pull φ) (Q.pull φ)) (s : (P.pull (eSec A)).Gen) (hs : s.IsGen) (t : (Q.pull (eSec A)).Gen)
    (ht : t.IsGen) : LBIso P Q := by
  refine GlobalTheory.seesaw_reduced_of_dense GlobalTheory.globalFns_holds S A M hA hM ha S A.left (𝟙 S) (𝟙 _) A.hom (LB.div Q P)
    (IsPullback.id_horiz _) (LB.isLB_div hQ hP) ?_ (eSec A) (Over.w η[A]) ?_
  · obtain ⟨w, hw⟩ := hi
    obtain ⟨c, hc⟩ := gen_chartPull (GlobalTheory.SabMapDescent.chartPullDivPull P Q φ) w hw
    refine dense_univ.mono fun p _ => ?_
    obtain ⟨p', rfl⟩ := f.surjective p
    let x' : Sp (S'.residueField p') ⟶ S' := S'.fromSpecResidueField p'
    refine ⟨S'.residueField p', inferInstance, x' ≫ f, pullback g x', pullback.fst g x' ≫ φ, pullback.snd g x',
      ⟨(default : PrimeSpectrum (S'.residueField p')), congrArg f (Scheme.fromSpecResidueField_apply p' _)⟩,
      (IsPullback.of_hasPullback g x').paste_horiz h, ?_⟩
    exact gen_chartPull (chartPullSame (LB.div Q P) (K := PUnit) _ (fun _ => φ) (fun _ => 1) (pullback.fst g x')
      fun _ => rfl) c hc
  · obtain ⟨w, hw⟩ := GlobalTheory.SabMapDescent.lbIso_of_gen_of_gen s hs t ht
    exact gen_chartPull (GlobalTheory.SabMapDescent.chartPullDivPull P Q _) w hw

end Bundle

end GlobalTheory.IsogDescent

open GlobalTheory.IsogDescent in

theorem GlobalTheory.isIsog_of_surjective_baseChange :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (p : ℕ) (S S' : Scheme.{0}) [IsReduced S] (s : S ⟶ Sp (KA l)) (s' : S' ⟶ Sp (KA l)) (f : S' ⟶ S) (o₁ o₂ : Ob D l s) (o₁' o₂' : Ob D l s') (n₁ : ObjMap o₁' o₁ f) (n₂ : ObjMap o₂' o₂ f) (ψ : o₁.t.G ⟶ o₂.t.G) (ψ' : o₁'.t.G ⟶ o₂'.t.G), Surjective f → ψ'.left ≫ n₂.toSABMap.φ = n₁.toSABMap.φ ≫ ψ.left → IsIsog o₁' o₂' p ψ' → IsFinite ψ.left → Etale ψ.left → IsIsog o₁ o₂ p ψ ∧ ∀ K, KerSet ψ' (n₁.toSABMap.φ ⁻¹' K) → KerSet ψ K := by
  intro E _ _ _ H D l p S S' _ s s' f o₁ o₂ o₁' o₂' n₁ n₂ ψ ψ' hf hψ ⟨⟨hm, _, _, hsurj, hact, hL⟩, hlev⟩ hfin het
  have := o₁.t.semi.smooth
  have := o₂.proper
  have : IsReduced o₁.t.G.left := GlobalTheory.isReduced_of_smooth_of_isReduced o₁.t.G.hom
  have : IsReduced (𝟙_ (Over S)).left := ‹IsReduced S›
  have : Surjective n₁.cm.F := MorphismProperty.of_isPullback (P := @Surjective) n₁.cart.1.flip hf
  have : Surjective n₂.cm.F := MorphismProperty.of_isPullback (P := @Surjective) n₂.cart.1.flip hf
  have hψ : ψ'.left ≫ n₂.cm.F = n₁.cm.F ≫ ψ.left := hψ
  have hmon : IsMonHom ψ := isMonHom n₁.cart n₂.cart ψ ψ' hψ
  have sec : ∀ {a : 𝟙_ (Over S) ⟶ o₁.t.G} {b : 𝟙_ (Over S) ⟶ o₂.t.G} {a' : 𝟙_ (Over S') ⟶ o₁'.t.G}
      {b' : 𝟙_ (Over S') ⟶ o₂'.t.G}, a'.left ≫ n₁.cm.F = f ≫ a.left → b'.left ≫ n₂.cm.F = f ≫ b.left →
      a' ≫ ψ' = b' → a ≫ ψ = b := fun {a b a' b'} ha hb h =>
    over_ext (T := 𝟙_ (Over S)) f (by
      rw [← hb, ← h, Over.comp_left, Over.comp_left, Category.assoc, hψ, ← Category.assoc, ← Category.assoc, ha])
  refine ⟨⟨⟨hmon, hfin, het, ?_, fun a => over_ext n₁.cm.F ?_, ?_⟩, fun p' hp a =>
    ⟨sec (n₁.eta _) (n₂.eta _) (hlev p' hp a).1, sec (n₁.etaA _) (n₂.etaA _) (hlev p' hp a).2⟩⟩, fun K hK =>
    kerSet n₁.cart.1 n₂.cart.1 (n₂.cm.e_comm.trans (by rw [n₂.base]; rfl)) ψ ψ' hψ K hK⟩
  · have : Surjective (n₁.cm.F ≫ ψ.left) := by rw [← hψ]; infer_instance
    exact Surjective.of_comp n₁.cm.F _
  · have e := congrArg (fun q => q.left) (hact a)
    simp only [Over.comp_left] at e ⊢
    rw [← Category.assoc, ← n₁.act, Category.assoc, ← hψ, ← Category.assoc, e, Category.assoc, n₂.act,
      ← Category.assoc, hψ, Category.assoc]
  · have hP : (lbPow o₁.t.PP.L (p ^ 2)).IsLB := LB.isLB_linComb o₁.t.PP.isLB _ _
    have hP' : (lbPow o₁'.t.PP.L (p ^ 2)).IsLB := LB.isLB_linComb o₁'.t.PP.isLB _ _
    have hQ := pull_isLB o₂.t.PP.isLB ψ.left
    obtain ⟨c, hc⟩ := exists_gen_pow o₁.t.PP.L _ ((p ^ 2 : ℕ) : ℤ) o₁.t.PP.rig o₁.t.PP.rigGen
    obtain ⟨c₁, hc₁⟩ := gen_chartPull (chartPullOut o₁.t.PP.L (K := PUnit) (fun _ => 𝟙 _) (fun _ => ((p ^ 2 : ℕ) : ℤ))
      (eSec o₁.t.G) (fun _ => eSec o₁.t.G) fun _ => (Category.comp_id _).symm) c hc
    obtain ⟨c₂, hc₂⟩ := gen_chartPull (chartPullOut o₂.t.PP.L (K := PUnit) (fun _ => ψ.left) (fun _ => 1)
      (eSec o₁.t.G) (fun _ => eSec o₂.t.G) fun _ => (congrArg (fun q => q.left) hmon.one_hom).symm)
      o₂.t.PP.rig o₂.t.PP.rigGen
    refine lbIso_of_surjective o₁.t.G o₁.t.PP.L (GlobalTheory.ObjDim.isAbelianScheme o₁) o₁.t.PP.isLB o₁.ample n₁.cart.1 hP hQ
      ?_ c₁ hc₁ c₂ hc₂
    obtain ⟨w₁, hw₁, -⟩ := n₁.lin
    obtain ⟨w₂, hw₂, -⟩ := n₂.lin
    have i₁ : LBIso (lbPow o₁'.t.PP.L (p ^ 2)) ((lbPow o₁.t.PP.L (p ^ 2)).pull n₁.cm.F) :=
      LBIso.chartPull (chartPullId _) (chartPullOut o₁.t.PP.L (K := PUnit) (fun _ => 𝟙 _) _ n₁.cm.F _
        fun _ => (Category.id_comp _).trans (Category.comp_id _).symm)
        (iso_linComb ((isGen_iff w₁).1 hw₁) (K := PUnit) (fun _ => 𝟙 _) (fun _ => ((p ^ 2 : ℕ) : ℤ)))
    have i₂ : LBIso (o₂'.t.PP.L.pull ψ'.left) ((o₂.t.PP.L.pull ψ.left).pull n₁.cm.F) :=
      LBIso.chartPull (chartPullId _) (chartPullOut o₂.t.PP.L (K := PUnit) (fun _ => ψ.left) _ n₁.cm.F _ fun _ => hψ)
        (iso_linComb ((isGen_iff w₂).1 hw₂) (K := PUnit) (fun _ => ψ'.left) (fun _ => 1))
    exact LBIso.trans (pull_isLB hP _) hP' (pull_isLB hQ _) i₁.symm
      (LBIso.trans hP' (pull_isLB o₂'.t.PP.isLB _) (pull_isLB hQ _) hL i₂)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfFibres
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.FibreAmple

theorem pw_pw_natCast {X : Scheme.{0}} (H : LB X) (a b : ℕ) :
    pw (pw H a) b = pw H ((a * b : ℕ) : ℤ) := by
  rw [Nat.cast_mul]
  exact congrArg (fun g => (⟨H.ι, H.U, g⟩ : LB X))
    (funext fun i => funext fun j => (zpow_mul (H.g i j) a b).symm)

theorem triv_theta_pull {S S' : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (g : S' ⟶ S)
    (H : LB A.left) (h : Triv (Theta ((Over.pullback g).obj A) (H.pull (pullback.fst A.hom g)))) :
    Triv ((Theta A H).pull (pullback.fst (G3 A).hom g)) := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨u, hu⟩ := GlobalTheory.CubeDescent.exists_gen_comp H (pullback.fst A.hom g) _ _ t ht
  let B := (Over.pullback g).obj A
  let T : Over S' := Over.mk (pullback.snd (G3 A).hom g)
  have hG := isGrpPullback_pullback A g
  let y : Fin 3 → (T ⟶ B) := fun i => Over.homMk
    (pullback.lift (pullback.fst (G3 A).hom g ≫ (x3 A i).left) (pullback.snd (G3 A).hom g)
      (by rw [Category.assoc, Over.w, pullback.condition])) (pullback.lift_snd _ _ _)
  let r : T ⟶ G3 B := lift (y 0) (lift (y 1) (y 2))
  have hr : ∀ i, r ≫ x3 B i = y i := fun i => by fin_cases i <;> simp [r, x3]
  let U : Over.mk (T.hom ≫ g) ⟶ G3 A := Over.homMk (pullback.fst (G3 A).hom g) pullback.condition
  have key : ∀ I : Finset (Fin 3), r.left ≫ (psum B (x3 B) I).left ≫ pullback.fst A.hom g =
      pullback.fst (G3 A).hom g ≫ (psum A (x3 A) I).left := fun I => by
    have e₁ : r ≫ psum B (x3 B) I = psum B y I :=
      (psum_hom (preHom r) (x3 B) I).trans (congrArg (fun z => psum B z I) (funext hr))
    have e₂ := psum_push hG y (x3 A) U (fun i => Over.OverMorphism.ext (pullback.lift_fst _ _ _)) I
    rw [← Category.assoc, ← Over.comp_left, e₁]
    exact e₂
  refine (CubeGen.triv_pull_iff H (thφ A (x3 A)) thε _).2 ?_
  have e : (fun k => pullback.fst (G3 A).hom g ≫ thφ A (x3 A) k) =
      fun k => r.left ≫ thφ B (x3 B) k ≫ pullback.fst A.hom g := funext fun k => (key k.down).symm
  unfold CubeGen.TrivAt
  rw [e]
  exact ⟨_, DVR.pullGen_isGen _ _ _ u hu r.left⟩

theorem exists_ne_zero {X : Scheme.{0}} [Nonempty X] {N : LB X} {I : Type} (s : I → LB.Sec N)
    (h : ⨆ i, Out.nonzeroLocus (s i) = ⊤) : ∃ (σ : LB.Sec N) (k : N.ι), σ.f k ≠ 0 := by
  obtain ⟨x⟩ := ‹Nonempty X›
  have hx : x ∈ ⨆ i, Out.nonzeroLocus (s i) := by rw [h]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hi
  refine ⟨s i, k, fun e => ?_⟩
  rw [e, Scheme.basicOpen_zero] at hk
  exact hk

theorem relAmple_of_fibres : Out.Laws → ∀ (O K : Type) [CommRing O] [IsDomain O] [ValuationRing O] [Ring.DimensionLEOne O] [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K] (A : Over (Sp O)) [GrpObj A], IsAbelianScheme A → ∀ M : LB A.left, M.IsLB → Out.RelAmple (Over.mk (pullback.snd A.hom (spMap (algebraMap O K)))) (M.pull (pullback.fst A.hom (spMap (algebraMap O K)))) → Out.RelAmple (Over.mk (pullback.snd A.hom (spMap (IsLocalRing.residue O)))) (M.pull (pullback.fst A.hom (spMap (IsLocalRing.residue O)))) → Out.RelAmple A M := by
  intro hL O K _ _ _ _ _ _ _ _ A _ hA M hM hK hk
  have := hA.comm
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  have hB := CubeGen.isAb_baseChange hA (spMap (algebraMap O K))
  obtain ⟨d, hd, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy K _ _ (LB.isLB_pull hM _)).1 hK
  have hH := isLB_pw hM d
  have hproj : IsProjBy ((Over.pullback (spMap (algebraMap O K))).obj A).hom :=
    ⟨_, isLB_pw (LB.isLB_pull hM _) _, n, s, hs⟩
  have cK := triv_theta_pull A _ (pw M d)
    (GlobalTheory.T.theorem_of_cube_projective_abelianScheme_affineBase hL K _ hB hproj _ (LB.isLB_pull hH (pullback.fst A.hom (spMap (algebraMap O K)))))
  have s₂ : Smooth (A ⊗ A).hom := by
    change Smooth (pullback.fst A.hom A.hom ≫ A.hom); infer_instance
  have p₂ : IsProper (A ⊗ A).hom := by
    change IsProper (pullback.fst A.hom A.hom ≫ A.hom); infer_instance
  have c₂ : GeometricallyConnected (A ⊗ A).hom := by
    change GeometricallyConnected (pullback.fst A.hom A.hom ≫ A.hom)
    exact GeometricallyConnected.comp _ _
  have s₃ : Smooth (G3 A).hom := by
    change Smooth (pullback.fst A.hom (A ⊗ A).hom ≫ A.hom); infer_instance
  have p₃ : IsProper (G3 A).hom := by
    change IsProper (pullback.fst A.hom (A ⊗ A).hom ≫ A.hom); infer_instance
  have c₃ : GeometricallyConnected (G3 A).hom := by
    change GeometricallyConnected (pullback.fst A.hom (A ⊗ A).hom ≫ A.hom)
    exact GeometricallyConnected.comp _ _
  have gi := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected
  have cube : Triv (Theta A (pw M d)) :=
    GlobalTheory.T.generator_extends_from_genericFibre_valuationRing O K _ _ (G3 A).hom _ _ (IsPullback.of_hasPullback _ _) s₃ inferInstance (gi _ _ _ s₃ c₃) _
      (LB.isLB_linComb hH _ _) cK
  have ne : Nonempty ((Over.pullback (spMap (algebraMap O K))).obj A).left :=
    ⟨(η[(Over.pullback (spMap (algebraMap O K))).obj A]).left (default : PrimeSpectrum K)⟩
  have hσ : ∃ (σ : LB.Sec ((pw M d).pull (pullback.fst A.hom (spMap (algebraMap O K))))) (k : _), σ.f k ≠ 0 := by
    have := @exists_ne_zero _ ne _ _ s hs.1
    rw [GlobalTheory.TrivLocus.pull_pw]
    exact this
  obtain ⟨σ, hσ⟩ := hσ
  obtain ⟨-, t, -, -, ht⟩ := GlobalTheory.T.exists_sec_nonzero_on_special_fibre_extending_smul O K _ _ A.hom _ _ (IsPullback.of_hasPullback _ _) hA.smooth
    inferInstance (gi _ _ _ hA.smooth hA.geomConnected) _ hH σ hσ
  have hu := GlobalTheory.T.exists_sections_generate_square_bundle O K A hA _ hH cube t ht
  rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, pw_pw_natCast] at hu
  obtain ⟨m, u, hu⟩ := hu
  have aff := GlobalTheory.T.isAffineOpen_nonzeroLocus_of_fibrewise_ample O _ A.hom M (d * 2) m u (by omega) hA.proper hM hu (fun q hq => by
    by_cases h0 : q = ⊥
    · exact ⟨K, inferInstance, algebraMap O K,
        h0 ▸ (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective O K), hK⟩
    · exact ⟨_, inferInstance, IsLocalRing.residue O,
        IsLocalRing.ker_residue.trans (IsLocalRing.eq_maximalIdeal (hq.isMaximal h0)).symm, hk⟩)
  obtain ⟨e, he, hv⟩ := GlobalTheory.AbLaw.veryAmpleBy_pw_of_affine_loci O _ A.hom _ m u (isLB_pw hM _) hu aff
  rw [pw_pw_natCast] at hv
  exact (GlobalTheory.Unif.relAmple_iff_veryAmpleBy O A M hM).2 ⟨d * 2 * e, Nat.mul_pos (by omega) he, hv⟩

end GlobalTheory.FibreAmple
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SeesawReducedBaseAbelianSchemeOfDenseFibresStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesaw_reduced_base_abelianScheme_of_dense_fibres : Out.GlobalFnsSt → ∀ (S₀ : Scheme.{0}) (B : Over S₀) [GrpObj B] (M : LB B.left), IsAbelianScheme B → M.IsLB → Out.RelAmple B M → ∀ (S X : Scheme.{0}) [IsReduced S] (t : S ⟶ S₀) (π : X ⟶ B.left) (f : X ⟶ S) (N : LB X), IsPullback π f B.hom t → N.IsLB → Dense {p : S | ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ S) (Y : Scheme.{0}) (ρ : Y ⟶ X) (h : Y ⟶ Sp K), p ∈ Set.range x ∧ IsPullback ρ h f x ∧ ∃ c : (N.pull ρ).Gen, c.IsGen} → ∀ σ : S ⟶ X, σ ≫ f = 𝟙 S → (∃ c : (N.pull σ).Gen, c.IsGen) → ∃ c : N.Gen, c.IsGen := by
  first | exact @GlobalTheory.seesaw_reduced_of_dense | exact GlobalTheory.seesaw_reduced_of_dense | (intros; apply GlobalTheory.seesaw_reduced_of_dense <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SeesawRigidifiedLineBundleDenseFibres
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem seesaw_rigidified_of_dense :
    ∀ (R : Type) [CommRing R] [IsReduced R] (A : Over (Sp R)) [GrpObj A] (M N : LB A.left) (Sg : Set (Sp R)), IsAbelianScheme A → M.IsLB → Out.RelAmple A M → N.IsLB → Dense Sg → Out.Rigidified A N → (∀ p ∈ Sg, ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ Sp R) (X : Scheme.{0}) (φ : X ⟶ A.left) (π : X ⟶ Sp K), p ∈ Set.range x ∧ IsPullback φ π A.hom x ∧ ∃ t : (N.pull φ).Gen, t.IsGen) → ∃ t : N.Gen, t.IsGen := by
  intro R _ _ A _ M N Sg hA hM hamp hN hd hr hf
  exact GlobalTheory.seesaw_reduced_of_dense GlobalTheory.globalFns_holds (Sp R) A M hA hM hamp (Sp R) A.left (𝟙 _) (𝟙 _)
    A.hom N (IsPullback.of_horiz_isIso ⟨by simp⟩) hN (hd.mono fun p hp => hf p hp) (eSec A)
    (Over.w η[A]) hr

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TangentInjectsSymmetricAntilinearCommuting
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM GlobalTheory.KS

namespace GlobalTheory.KS

theorem tangent_injects_symm_antilinear : Out.Laws → Out.Laws2 → ThetaUnifAV → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (R : Type) [CommRing R] [Algebra o R] [Algebra o ℂ] [Algebra R ℂ] [IsScalarTower o R ℂ] (t : TObj g k J b (spMap (algebraMap o R))), (∀ (x : Sp (DualNumber ℂ) ⟶ Sp R) (t' : TObj g k J b (x ≫ spMap (algebraMap o R))), x ≫ spMap (algebraMap o R) = constPt x ≫ spMap (algebraMap o R) → TMap t' t x → TMap t' t (constPt x) → x = constPt x) → ∃ (t₀ : TObj g k J b (spMap (algebraMap o ℂ))) (m : t₀.A.left ⟶ t.A.left) (u : HolUnif t₀.pol.A t₀.pol.L t₀.pol.g) (Hm : Matrix (Fin t₀.pol.g) (Fin t₀.pol.g) ℂ) (χ : u.Λ → ℂ) (κ : Derivation o R ℂ →ₗ[ℂ] Matrix (Fin t₀.pol.g) (Fin t₀.pol.g) ℂ), GoodU u Hm χ ∧ (IsGrpPullback t₀.A t.A (spMap (algebraMap R ℂ)) m ∧ LBIso t₀.L (t.L.pull m) ∧ (∀ i, (t₀.pt i).left ≫ m = (spMap (algebraMap R ℂ)) ≫ (t.pt i).left) ∧ ∀ jj, (t₀.act jj).left ≫ m = m ≫ (t.act jj).left) ∧ Function.Injective κ ∧ ∀ D, IsSymm Hm (κ D) ∧ ∀ (f : t.A ⟶ t.A) (f₀ : t₀.pol.A ⟶ t₀.pol.A) (F : (Fin t₀.pol.g → ℂ) →ₗ[ℂ] (Fin t₀.pol.g → ℂ)), f₀.left ≫ m = m ≫ f.left → (∀ z, u.ex (F z) = u.ex z ≫ f₀) → Comm (κ D) F := by
  intro h1 h2 hU o _ g k J b R _ _ _ _ _ t hun
  have hcomp : spMap (algebraMap R ℂ) ≫ spMap (algebraMap o R) = spMap (algebraMap o ℂ) := by
    rw [IsScalarTower.algebraMap_eq o R ℂ]
    exact (Spec.map_comp (CommRingCat.ofHom (algebraMap o R)) (CommRingCat.ofHom (algebraMap R ℂ))).symm
  obtain ⟨t₀, m, hm⟩ := GlobalTheory.T.exists_thetaLevelAbelianScheme_pullback o g k J b _ _ _ _ (spMap (algebraMap R ℂ)) t hcomp
  obtain ⟨u, Hm, χ, hG, -⟩ := GlobalTheory.T.exists_goodUniformisation_kodairaSpencer hU t₀.pol
  have hsm : Smooth t.A.hom := by
    haveI := t.dim
    exact SmoothOfRelativeDimension.smooth g _
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.kodairaSpencer_matrix_linear_in_derivation t₀.pol u Hm χ hG o R t.A.left t.A.hom m hsm hm.1.1
  refine ⟨t₀, m, u, Hm, χ, κ, hG, hm, ?_, fun D => ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro D hD
    obtain ⟨s, hs⟩ := hκ D
    rw [hD] at hs
    exact GlobalTheory.T.derivation_eq_zero_of_kodairaSpencer_zero h1 h2 hU o g k J b R t _ t₀ m u Hm χ hG hm hun D s hs
  · obtain ⟨s, hs⟩ := hκ D
    refine ⟨GlobalTheory.T.kodairaSpencer_class_isSymm_of_lift t₀.pol u Hm χ hG R _ t.A.left t.A.hom m hsm hm.1.1 _ _ s hs t.L t.isLB hm.2.1, ?_⟩
    intro f f₀ F hf hF
    exact GlobalTheory.T.kodairaSpencer_commutes_with_endomorphism t₀.pol u Hm χ hG R _ t.A.left t.A.hom m hsm hm.1.1 _ _ s hs f.left f₀ F (Over.w f) hf hF

end GlobalTheory.KS
end

