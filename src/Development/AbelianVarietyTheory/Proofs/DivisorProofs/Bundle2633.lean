import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0027
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2514
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2432
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomOfMulComp
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TensAct

open GlobalTheory.Mum

section Hom

variable {S : Scheme.{0}} {G H : Over S} [GrpObj G] [GrpObj H]

end Hom

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

def matAct (T : Tens D D' W) (A : Matrix (Fin r) (Fin r) ℤ) : D'.P.A ⟶ D'.P.A :=
  T.lim.lift (Fan.mk D'.P.A fun i ↦ ∏ j, T.pr j ^ A i j)

theorem matAct_pr (T : Tens D D' W) (A : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) :
    matAct T A ≫ T.pr i = ∏ j, T.pr j ^ A i j :=
  T.lim.fac (Fan.mk D'.P.A fun i ↦ ∏ j, T.pr j ^ A i j) ⟨i⟩

theorem hom_ext (T : Tens D D' W) {X : Over (Spec (CommRingCat.of R))} {a b : X ⟶ D'.P.A}
    (h : ∀ i, a ≫ T.pr i = b ≫ T.pr i) : a = b :=
  T.lim.hom_ext fun i ↦ h i.as

def latAct (T : Tens D D' W) (A : Matrix (Fin r) (Fin r) ℤ) (y : D'.X) : D'.X :=
  T.xe.symm fun i ↦ ∑ j, A i j • T.xe y j

theorem xe_latAct (T : Tens D D' W) (A : Matrix (Fin r) (Fin r) ℤ) (y : D'.X) (i : Fin r) :
    T.xe (latAct T A y) i = ∑ j, A i j • T.xe y j := by
  simp [latAct]

section Ring

theorem zpow_finsetSum {M : Type} [CommGroup M] (a : M) {K : Type} (s : Finset K) (f : K → ℤ) :
    a ^ (∑ k ∈ s, f k) = ∏ k ∈ s, a ^ f k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add, ih]

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

theorem matAct_hom (T : Tens D D' W) (A : Matrix (Fin r) (Fin r) ℤ) : IsMonHom (matAct T A) := by
  have hp := T.pr_hom
  refine GlobalTheory.MatrixAction.isMonHom_of_points _ (fun X ↦ hom_ext T fun i ↦ ?_) (fun X x y ↦ hom_ext T fun i ↦ ?_)
  · rw [Category.assoc, matAct_pr, GlobalTheory.MatrixAction.comp_finsetProd, MonObj.one_comp (T.pr i)]
    refine Finset.prod_eq_one fun l _ ↦ ?_
    rw [GrpObj.comp_zpow, MonObj.one_comp, one_zpow]
  · rw [MonObj.mul_comp _ _ (T.pr i), Category.assoc, Category.assoc, Category.assoc, matAct_pr,
      GlobalTheory.MatrixAction.comp_finsetProd, GlobalTheory.MatrixAction.comp_finsetProd, GlobalTheory.MatrixAction.comp_finsetProd,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun l _ ↦ ?_
    rw [GrpObj.comp_zpow, GrpObj.comp_zpow, GrpObj.comp_zpow, MonObj.mul_comp, mul_zpow]

theorem matAct_one (T : Tens D D' W) : matAct T 1 = 𝟙 _ := by
  refine hom_ext T fun i ↦ ?_
  rw [matAct_pr, Category.id_comp, Finset.prod_eq_single i]
  · rw [Matrix.one_apply_eq, zpow_one]
  · intro l _ hl
    rw [Matrix.one_apply_ne hl.symm, zpow_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem matAct_mul (T : Tens D D' W) (A B : Matrix (Fin r) (Fin r) ℤ) :
    matAct T (A * B) = matAct T B ≫ matAct T A := by
  refine hom_ext T fun i ↦ ?_
  rw [Category.assoc, matAct_pr, matAct_pr, GlobalTheory.MatrixAction.comp_finsetProd]
  have e1 : ∀ k, matAct T B ≫ T.pr k ^ A i k = ∏ l, T.pr l ^ (A i k * B k l) := fun k ↦ by
    rw [GrpObj.comp_zpow, matAct_pr, ← Finset.prod_zpow]
    refine Finset.prod_congr rfl fun l _ ↦ ?_
    rw [← zpow_mul, mul_comm]
  rw [Finset.prod_congr rfl fun k _ ↦ e1 k, Finset.prod_comm]
  refine Finset.prod_congr rfl fun l _ ↦ ?_
  rw [Matrix.mul_apply, zpow_finsetSum]

theorem matAct_add (T : Tens D D' W) (A B : Matrix (Fin r) (Fin r) ℤ) :
    matAct T (A + B) = matAct T A * matAct T B := by
  refine hom_ext T fun i ↦ ?_
  have := T.pr_hom i
  rw [MonObj.mul_comp, matAct_pr, matAct_pr, matAct_pr, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun l _ ↦ ?_
  rw [Matrix.add_apply, zpow_add]

def latEnd (T : Tens D D' W) : Matrix (Fin r) (Fin r) ℤ →+* Module.End ℤ D'.X where
  toFun A :=
    { toFun := latAct T A
      map_add' := fun y z ↦ T.xe.injective (funext fun i ↦ by
        simp only [xe_latAct, map_add, Pi.add_apply, smul_add, Finset.sum_add_distrib])
      map_smul' := fun n y ↦ T.xe.injective (funext fun i ↦ by
        simp only [xe_latAct, map_zsmul, Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
        exact Finset.sum_congr rfl fun j _ ↦ smul_comm _ _ _) }
  map_one' := LinearMap.ext fun y ↦ T.xe.injective (funext fun i ↦ by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, xe_latAct, Module.End.one_apply]
    rw [Finset.sum_eq_single i]
    · rw [Matrix.one_apply_eq, one_smul]
    · intro l _ hl
      rw [Matrix.one_apply_ne hl.symm, zero_smul]
    · intro h
      exact absurd (Finset.mem_univ i) h)
  map_mul' A B := LinearMap.ext fun y ↦ T.xe.injective (funext fun i ↦ by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, xe_latAct, Module.End.mul_apply, Matrix.mul_apply,
      Finset.smul_sum, Finset.sum_smul, mul_smul]
    exact Finset.sum_comm)
  map_zero' := LinearMap.ext fun y ↦ T.xe.injective (funext fun i ↦ by
    simp [xe_latAct])
  map_add' A B := LinearMap.ext fun y ↦ T.xe.injective (funext fun i ↦ by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, xe_latAct, LinearMap.add_apply, map_add, Pi.add_apply,
      Matrix.add_apply, add_smul, Finset.sum_add_distrib])

abbrev tensModule (T : Tens D D' W) {O : Type} [Ring O] (ρ : O →+* Matrix (Fin r) (Fin r) ℤ) : Module O D'.X :=
  Module.compHom D'.X ((latEnd T).comp ρ)

def ringAct (T : Tens D D' W) {O : Type} [Ring O] (ρ : O →+* Matrix (Fin r) (Fin r) ℤ) : RingAct D'.P.A O where
  act a := matAct T (ρ a)
  hom a := matAct_hom T (ρ a)
  map_one := by rw [map_one, matAct_one]
  map_mul a b := by rw [map_mul, matAct_mul]
  map_add a b := by rw [map_add, matAct_add]; rfl

def cHom (D : DegPre R) : D.X →+ Additive (𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A) :=
  AddMonoidHom.mk' (fun x ↦ Additive.ofMul (D.c x)) fun a b ↦ by rw [D.c_add]; rfl

theorem c_lin (T : Tens D D' W) (A : Matrix (Fin r) (Fin r) ℤ) (y : D'.X) :
    D'.c (latAct T A y) = D'.c y ≫ matAct T A := by
  refine hom_ext T fun i ↦ ?_
  rw [T.c_pr, Category.assoc, matAct_pr, GlobalTheory.MatrixAction.comp_finsetProd, xe_latAct]
  have e := map_sum (cHom D) (fun j ↦ A i j • T.xe y j) Finset.univ
  simp only [map_zsmul] at e
  apply Additive.ofMul.injective
  refine e.trans ?_
  rw [ofMul_prod]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [GrpObj.comp_zpow, T.c_pr, ofMul_zpow]
  rfl

end Ring

end GlobalTheory.TensAct
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNoetherianProjectiveSpaceAndPullbackProper
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem pspace_noeth_and_pullback : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (S : Scheme.{0}) (π : S ⟶ Sp R),
    IsProper π → ∀ N : ℕ, IsNoetherian (PSpace R N) ∧ IsNoetherian (pullback (PSpace.str R N) π) := by
  intro R _ _ S π hπ N
  have hP : IsProper (PSpace.str R N) := isProper_str R N
  have h1 : IsNoetherian (PSpace R N) := by
    have : IsLocallyNoetherian (PSpace R N) := LocallyOfFiniteType.isLocallyNoetherian (PSpace.str R N)
    have : CompactSpace (PSpace R N) := QuasiCompact.compactSpace_of_compactSpace (PSpace.str R N)
    exact {}
  refine ⟨h1, ?_⟩
  haveI := hπ
  have : IsProper (pullback.fst (PSpace.str R N) π) := inferInstance
  haveI := LocallyOfFiniteType.isLocallyNoetherian (pullback.fst (PSpace.str R N) π)
  haveI := QuasiCompact.compactSpace_of_compactSpace (pullback.fst (PSpace.str R N) π)
  exact {}

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenFarSet
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

def secNz {X : Scheme.{0}} {L : LB X} (s : L.Sec) : X.Opens := ⨆ i, X.basicOpen (s.f i)

def farSet {Z Y : Scheme.{0}} (β : Z ⟶ Y) {L : LB Z} (s : L.Sec) : Set Y := {v | ∀ g, β g = v → g ∈ secNz s}

def cubeTen {S : Scheme.{0}} {G T : Over S} [GrpObj G] (x a b c : T ⟶ G) : List (T ⟶ G) :=
  [x * a, x * a⁻¹, a, a⁻¹, x * b, x * c, x * (b * c)⁻¹, b, c, (b * c)⁻¹]

theorem isOpen_farSet {Z Y : Scheme.{0}} (β : Z ⟶ Y) (hβ : IsClosedMap β) {L : LB Z} (s : L.Sec) :
    IsOpen (farSet β s) := by
  have : farSet β s = (β '' (secNz s : Set Z)ᶜ)ᶜ := by
    ext v
    simp only [farSet, Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_image, not_exists, not_and]
    constructor
    · intro h g hg hgv; exact hg (h g hgv)
    · intro h g hgv; by_contra hg; exact h g hg hgv
  rw [this, isOpen_compl_iff]
  exact hβ _ (secNz s).isOpen.isClosed_compl

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionOfMonoOfSmoothOfRelativeDimensionStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpenImmersion_of_mono_of_smoothOfRelativeDimension' : ∀ (X Y Z : Scheme.{0}) (f : X ⟶ Y) (p : Y ⟶ Z) (g : ℕ), SmoothOfRelativeDimension g p → SmoothOfRelativeDimension g (f ≫ p) → Mono f → IsOpenImmersion f := by
  first | exact @GlobalTheory.isOpenImmersion_of_mono_of_smoothOfRelativeDimension | exact GlobalTheory.isOpenImmersion_of_mono_of_smoothOfRelativeDimension | (intros; apply GlobalTheory.isOpenImmersion_of_mono_of_smoothOfRelativeDimension <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairBundle
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical

noncomputable section

namespace GlobalTheory.OmitFlag

open CategoryTheory.Limits

def IsPairBundle {B G : Scheme.{0}} (γ : G ⟶ B) (E : B.Modules) (m₁ m₂ : ℕ) {S P : G.Modules} (s : S ⟶ P)
    (j : P ⟶ (Scheme.Modules.pullback γ).obj E) : Prop :=
  ∀ (T : Scheme.{0}) (g : T ⟶ B) (S' P' : T.Modules) (s' : S' ⟶ P') (j' : P' ⟶ (Scheme.Modules.pullback g).obj E),
    GlobalTheory.VB.IsSubbundle s' → GlobalTheory.VB.IsSubbundle j' → GlobalTheory.VB.IsVB S' m₁ → GlobalTheory.VB.IsVB P' m₂ →
    ∃! g' : T ⟶ G, ∃ w : g' ≫ γ = g, ∃ (eS : (Scheme.Modules.pullback g').obj S ≅ S')
      (eP : (Scheme.Modules.pullback g').obj P ≅ P'),
      eP.hom ≫ j' = (Scheme.Modules.pullback g').map j ≫ (Scheme.Modules.pullbackComp g' γ).hom.app E ≫
        (Scheme.Modules.pullbackCongr w).hom.app E ∧
      eS.hom ≫ s' = (Scheme.Modules.pullback g').map s ≫ eP.hom

def fam {B G : Scheme.{0}} (γ : G ⟶ B) {ι : Type} (E : ι → B.Modules) (a : ι) {S P : G.Modules} (s : S ⟶ P)
    (j : P ⟶ (Scheme.Modules.pullback γ).obj (E a)) : ({b // b ≠ a} ⊕ Bool) → G.Modules :=
  Sum.elim (fun b => (Scheme.Modules.pullback γ).obj (E b.1)) fun t => cond t S (cokernel j)

def rk {ι : Type} (r : ι → ℕ) (a : ι) (m₁ m₂ : ℕ) : ({b // b ≠ a} ⊕ Bool) → ℕ :=
  Sum.elim (fun b => r b.1) fun t => cond t m₁ (r a - m₂)

end GlobalTheory.OmitFlag

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPerfPairDualOfHalfDimKernelConditions
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PerfPairField

open Module

theorem eq_zero_of_mem_of_flip_ker {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (φ : V →ₗ[K] W →ₗ[K] K) (A : Submodule K V) (B : Submodule K W)
    (hdim : finrank K A + finrank K B ≤ finrank K W)
    (h : ∀ y, (∀ x ∈ A, φ x y = 0) → y ∈ B) :
    ∀ x ∈ A, φ x = 0 → x = 0 := by
  intro x hx hφx
  set T : W →ₗ[K] Module.Dual K A := (φ.domRestrict A).flip with hT
  have hker : LinearMap.ker T ≤ B := by
    intro y hy
    apply h y
    intro a ha
    have := LinearMap.congr_fun (LinearMap.mem_ker.mp hy) ⟨a, ha⟩
    simpa [hT] using this
  have hrn := LinearMap.finrank_range_add_finrank_ker T
  have hkb := Submodule.finrank_mono hker
  have hdA : finrank K (Module.Dual K A) = finrank K A := Subspace.dual_finrank_eq
  have htop : LinearMap.range T = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have := Submodule.finrank_le (LinearMap.range T)
    omega
  have hx0 : (⟨x, hx⟩ : A) = 0 := by
    rw [← Module.forall_dual_apply_eq_zero_iff K]
    intro f
    obtain ⟨y, rfl⟩ : f ∈ LinearMap.range T := htop ▸ Submodule.mem_top
    simp [hT, hφx]
  simpa using congrArg Subtype.val hx0

end GlobalTheory.PerfPairField

open Module in
theorem GlobalTheory.PerfPairField.isPerfPair_of_kernel_conditions : ∀ (k : Type) [Field k] (M N : Type 1) [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N] [FiniteDimensional k M] [FiniteDimensional k N] (F : Submodule k M) (F' : Submodule k N) (g : ℕ), Module.finrank k M = 2 * g → Module.finrank k N = 2 * g → Module.finrank k F = g → Module.finrank k F' = g → ∀ φ : Module.Dual k M →ₗ[k] Module.Dual k N →ₗ[k] k, (∀ x, (∀ y ∈ F'.dualAnnihilator, φ x y = 0) → x ∈ F.dualAnnihilator) → (∀ y, (∀ x ∈ F.dualAnnihilator, φ x y = 0) → y ∈ F'.dualAnnihilator) → φ.IsPerfPair := by
  intro k _ M N _ _ _ _ _ _ F F' g hM hN hF hF' φ h1 h2
  have eM := Subspace.finrank_add_finrank_dualAnnihilator_eq F
  have eN := Subspace.finrank_add_finrank_dualAnnihilator_eq F'
  have dM : finrank k (Module.Dual k M) = 2 * g := by rw [Subspace.dual_finrank_eq, hM]
  have dN : finrank k (Module.Dual k N) = 2 * g := by rw [Subspace.dual_finrank_eq, hN]
  apply LinearMap.IsPerfPair.of_injective
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hA : x ∈ F.dualAnnihilator := h1 x (fun y _ => by simp [hx])
    exact GlobalTheory.PerfPairField.eq_zero_of_mem_of_flip_ker φ F.dualAnnihilator F'.dualAnnihilator
      (by omega) h2 x hA hx
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have hB : y ∈ F'.dualAnnihilator := h2 y (fun x _ => by
      have := LinearMap.congr_fun hy x
      simpa using this)
    exact GlobalTheory.PerfPairField.eq_zero_of_mem_of_flip_ker φ.flip F'.dualAnnihilator F.dualAnnihilator
      (by omega) (fun x hx => h1 x (fun y hy => by simpa using hx y hy)) y hB hy
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPointwiseCoboundaryOfPullbackBaseChangeIsIso
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtExt

namespace BcIso

variable {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {X : Over (Sp R)} {X' : Over (Sp R')}
  {q : X'.left ⟶ X.left}

def ringOf {E : Type} [CommRing E] (g : Sp E ⟶ X'.left) : R' →+* E :=
  (Spec.preimage (R := CommRingCat.of R') (S := CommRingCat.of E) (g ≫ X'.hom)).hom

theorem spMap_ringOf {E : Type} [CommRing E] (g : Sp E ⟶ X'.left) : spMap (ringOf g) = g ≫ X'.hom := by
  unfold ringOf
  exact Spec.map_preimage _

theorem ringOf_eq_of_spMap {E : Type} [CommRing E] (g : Sp E ⟶ X'.left) (τ : R' →+* E)
    (h : spMap τ = g ≫ X'.hom) : ringOf g = τ := by
  have h1 : spMap (ringOf g) = spMap τ := by rw [spMap_ringOf, h]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)

def ptBack [IsIso q] {E : Type} [CommRing E] (g : Sp E ⟶ X.left) :
    @Pt R' _ X' E _ (ringOf (X' := X') (g ≫ inv q)).toAlgebra :=
  @Over.homMk _ _ _ (@SpAlg R' E _ _ (ringOf (X' := X') (g ≫ inv q)).toAlgebra) X' (g ≫ inv q)
    (spMap_ringOf (X' := X') (g ≫ inv q)).symm

theorem ringOf_comp (w : q ≫ X.hom = X'.hom ≫ spMap σ) [IsIso q] {E : Type} [CommRing E] [Algebra R E]
    (z : Pt X E) : (ringOf (X' := X') (z.left ≫ inv q)).comp σ = algebraMap R E := by
  have h1 : spMap ((ringOf (X' := X') (z.left ≫ inv q)).comp σ) = spMap (algebraMap R E) := by
    rw [spMap_comp, spMap_ringOf]
    simp only [Category.assoc, ← w, IsIso.inv_hom_id_assoc]
    exact Over.w z
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)

theorem bcPull_transport (w : q ≫ X.hom = X'.hom ≫ spMap σ) (u : Fn1 X) (E E' : Type) [CommRing E] [CommRing E']
    (A : Algebra R' E) (A' : Algebra R' E') (i : Algebra R E) (i' : Algebra R E') (h : i = algVia σ E)
    (h' : i' = algVia σ E') (φ : @AlgHom R E E' _ _ _ i i') (z : @Pt R _ X E _ i) (ψ : E →ₐ[R'] E')
    (y : Pt X' E) (hψ : ∀ e, ψ e = φ e) (hy : y.left ≫ q = z.left) :
    @u E _ i E' _ i' φ z = bcPull w u E E' ψ y := by
  subst h h'
  letI := algVia σ E
  letI := algVia σ E'
  have e1 : homVia σ ψ = φ := AlgHom.ext hψ
  have e2 : ptVia w y = z := by
    apply Over.OverMorphism.ext
    exact hy
  rw [← e1, ← e2]
  rfl

end BcIso

open BcIso

theorem isCob_of_bcPull_isIso : ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (X : Over (Sp R))
    (X' : Over (Sp R')) (q : X'.left ⟶ X.left) (w : q ≫ X.hom = X'.hom ≫ spMap σ), IsIso q → ∀ u : Fn1 X,
    IsCoc (whole X) u → (∃ k, IsCob (whole X') (bcPull w u) k) → ∃ k, IsCob (whole X) u k := by
  intro R R' _ _ σ X X' q w hq u _ hk
  obtain ⟨k', hk'⟩ := hk
  refine ⟨fun E _ _ z ↦ @k' E _ (ringOf (X' := X') (z.left ≫ inv q)).toAlgebra (ptBack z.left), ?_⟩
  intro E _ i E' _ i' φ z _
  let τ := ringOf (X' := X') (z.left ≫ inv q)
  let τ' := ringOf (X' := X') ((spOver φ ≫ z).left ≫ inv q)
  letI A : Algebra R' E := τ.toAlgebra
  letI A' : Algebra R' E' := τ'.toAlgebra
  have hτ : τ' = (φ : E →+* E').comp τ := by
    apply ringOf_eq_of_spMap
    rw [spMap_comp, spMap_ringOf]
    simp only [Over.comp_left, Category.assoc]
    rfl
  have hc : ∀ r, φ (τ r) = τ' r := fun r ↦ by rw [hτ]; rfl
  let ψ : E →ₐ[R'] E' := { (φ : E →+* E') with commutes' := hc }
  have h : i = algVia σ E := Algebra.algebra_ext _ _ fun r ↦ (congrArg (fun f ↦ f r) (ringOf_comp w z)).symm
  have h' : i' = algVia σ E' :=
    Algebra.algebra_ext _ _ fun r ↦ (congrArg (fun f ↦ f r) (ringOf_comp w (spOver φ ≫ z))).symm
  have e1 := bcPull_transport w u E E' A A' i i' h h' φ z ψ (ptBack z.left) (fun _ ↦ rfl)
    (by simp [ptBack])
  have e2 := hk' E E' ψ (ptBack z.left) (sm_whole _)
  have e3 : spOver ψ ≫ ptBack (X' := X') z.left = ptBack (spOver φ ≫ z).left :=
    Over.OverMorphism.ext (by simp [ptBack]; rfl)
  rw [e1, e2, e3]
  rfl

end GlobalTheory.PtExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackLineBundleGeneratorAdditivityDefectStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPullbackLineBundleGenerator_additivityDefect : ∀ (S : Scheme.{0}) (A A' T : Over S) [MonObj A] [MonObj A'] (q : A ⟶ A') [IsMonHom q] (M : LB (A' ⊗ T).left) (e : ∀ k, Γ((A ⊗ T).left, (pmap q T).left ⁻¹ᵁ M.U k)ˣ), IsPullGen (pmap q T).left M e → IsPullGen (pmap2 q T).left (addBundle M) (addGen q M e) := by
  first | exact @GlobalTheory.CharKer.isPullGen_addGen | exact GlobalTheory.CharKer.isPullGen_addGen | (intros; apply GlobalTheory.CharKer.isPullGen_addGen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackMorphismRestrictImageOfRestrictRestric
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory

theorem isPullback_morphismRestrict_image_of_restrict_restrict :
    ∀ (P' X S T : Scheme.{0}) (a : X ⟶ P') (W : P'.Opens) (V : W.toScheme.Opens) (q : X ⟶ S)
      (h : P' ⟶ T) (π : S ⟶ T),
      IsPullback ((a ∣_ W) ∣_ V) (((a ∣_ W) ⁻¹ᵁ V).ι ≫ (a ⁻¹ᵁ W).ι ≫ q) (V.ι ≫ W.ι ≫ h) π →
      IsPullback (a ∣_ (W.ι ''ᵁ V)) ((a ⁻¹ᵁ (W.ι ''ᵁ V)).ι ≫ q) ((W.ι ''ᵁ V).ι ≫ h) π := by
  intro P' X S T a W V q h π H
  have e1hom : ((a ⁻¹ᵁ W).ι.isoImage ((a ∣_ W) ⁻¹ᵁ V) ≪≫
      X.isoOfEq (image_morphismRestrict_preimage a W V)).hom ≫ (a ⁻¹ᵁ (W.ι ''ᵁ V)).ι =
      ((a ∣_ W) ⁻¹ᵁ V).ι ≫ (a ⁻¹ᵁ W).ι := by
    simp only [Iso.trans_hom, Category.assoc, Scheme.isoOfEq_hom_ι, Scheme.Hom.isoImage_hom_ι]
  refine IsPullback.of_iso H
    ((a ⁻¹ᵁ W).ι.isoImage ((a ∣_ W) ⁻¹ᵁ V) ≪≫ X.isoOfEq (image_morphismRestrict_preimage a W V))
    (W.ι.isoImage V) (Iso.refl S) (Iso.refl T) ?_ ?_ ?_ ?_
  · rw [← cancel_mono (W.ι ''ᵁ V).ι]
    simp only [Category.assoc, Scheme.Hom.isoImage_hom_ι, morphismRestrict_ι]
    rw [reassoc_of% e1hom, morphismRestrict_ι_assoc, morphismRestrict_ι]
  · simp only [Iso.refl_hom, Category.comp_id]
    rw [reassoc_of% e1hom]
  · simp only [Iso.refl_hom, Category.comp_id, Scheme.Hom.isoImage_hom_ι_assoc]
  · simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianOfIsGrpPullbackSquareStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSemiAbelian_of_isGrpPullback_divisor : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] (G' : Over S') [GrpObj G'] (F : G'.left ⟶ G.left), IsGrpPullback G' G f F → IsSemiAbelian G → IsSemiAbelian G' := by
  first | exact @GlobalTheory.Mum.isSemiAbelian_of_isGrpPullback_square | exact GlobalTheory.Mum.isSemiAbelian_of_isGrpPullback_square | (intros; apply GlobalTheory.Mum.isSemiAbelian_of_isGrpPullback_square <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSncAdaptedCoordinatesOfMemNhdsStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSncAdaptedCoordinates_of_mem_nhds : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ) [SmoothOfRelativeDimension n q], ∀ (B : Closeds Y) (y : Y) (U : Y.Opens) (hy : y ∈ U) (z : Fin n → Γ(Y, U)) (J : Finset (Fin n)) (w : Fin n → Y) (u : Fin n → Y.functionFieldˣ), genericPoint Y ∉ B → IsSncChart q n B y U hy z J w u → ∃ V : Y.Opens, y ∈ V ∧ ∀ y' ∈ V, ∃ (hy' : y' ∈ U) (J' : Finset (Fin n)), J' ⊆ J ∧ IsSncChart q n B y' U hy' z J' w u ∧ ∀ j ∈ J', y' ∉ Y.basicOpen (z j) := by
  first | exact @GlobalTheory.PairStep.isSncChart_spread | exact GlobalTheory.PairStep.isSncChart_spread | (intros; apply GlobalTheory.PairStep.isSncChart_spread <;> assumption)
end

