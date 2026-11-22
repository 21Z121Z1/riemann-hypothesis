import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0036
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0039
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0050
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CoordOfHasWeight
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0043
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0016
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0042
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.InvariantTowerAlgebraMapInjective
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem mem_smul_ker_of_flat_quotient {B T C : Type} [CommRing B] [AddCommGroup T] [Module B T]
    [AddCommGroup C] [Module B C] [Module.Flat B C] (φ : T →ₗ[B] C) (hφ : Function.Surjective φ)
    (q : Ideal B) (x : LinearMap.ker φ) (hx : (x : T) ∈ q • (⊤ : Submodule B T)) :
    x ∈ q • (⊤ : Submodule B (LinearMap.ker φ)) := by
  have hinj := LinearMap.lTensor_injective_of_exact_of_flat φ hφ (LinearMap.ker φ).subtype
    (Submodule.injective_subtype _) (LinearMap.exact_subtype_ker_map φ) (B ⧸ q)
  have h0 : ∀ (M : Type) [AddCommGroup M] [Module B M] (y : M),
      ((1 : B ⧸ q) ⊗ₜ[B] y = 0 ↔ y ∈ q • (⊤ : Submodule B M)) := by
    intro M _ _ y
    rw [← Submodule.Quotient.mk_eq_zero, ← TensorProduct.quotTensorEquivQuotSMul_symm_mk,
      LinearEquiv.map_eq_zero_iff]
  rw [← h0]
  apply hinj
  rw [LinearMap.lTensor_tmul, map_zero, h0]
  exact hx

theorem ideal_eq_bot_of_forall_prime_smul_mem {B T : Type} [CommRing B] [CommRing T]
    [Algebra B T] (J : Ideal T) (hJ : J.FG)
    (h : ∀ q : Ideal B, q.IsPrime → ∀ x ∈ J, ∃ s : B, s ∉ q ∧
      s • x ∈ q • (J.restrictScalars B)) : J = ⊥ := by
  by_cases hJt : Submodule.annihilator J = ⊤
  · exact Submodule.annihilator_eq_top_iff.1 hJt
  obtain ⟨n, hn, hJn⟩ := Ideal.exists_le_maximal _ hJt
  have hle : J ≤ n • J := by
    intro x hxJ
    obtain ⟨s, hs, hx⟩ := h (n.comap (algebraMap B T)) (Ideal.comap_isPrime _ _) x hxJ
    have hx' : s • x ∈ n • J := by
      refine Submodule.smul_induction_on hx ?_ ?_
      · intro r hr c hc
        rw [← algebraMap_smul T r c]
        exact Submodule.smul_mem_smul hr hc
      · intro a b ha hb
        exact Submodule.add_mem _ ha hb
    obtain ⟨t, m, hm, e⟩ := hn.exists_inv (x := algebraMap B T s) hs
    have e' : x = t • (s • x) + m • x := by
      rw [← algebraMap_smul T s x, ← mul_smul, ← add_smul, e, one_smul]
    rw [e']
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hx') (Submodule.smul_mem_smul hm hxJ)
  obtain ⟨r, hr, hrM⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul n J hJ hle
  have hrJ : r ∈ n := hJn (Submodule.mem_annihilator.2 hrM)
  exfalso
  apply hn.ne_top
  rw [Ideal.eq_top_iff_one]
  have := n.sub_mem hrJ hr
  rwa [sub_sub_cancel] at this

theorem isPushout_of_tame :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (A B R C : Type) [CommRing A] [CommRing B] [CommRing R] [CommRing C] [MulSemiringAction Γ B] [MulSemiringAction Γ C] [Algebra A B] [Algebra A R] [Algebra B C] [Algebra R C] [Algebra A C] [IsScalarTower A B C] [IsScalarTower A R C] [SMulCommClass Γ A B] [SMulCommClass Γ R C] [Algebra.IsInvariant A B Γ] [Algebra.IsInvariant R C Γ], Function.Injective (algebraMap A B) → Function.Injective (algebraMap R C) → (∀ (g : Γ) (b : B), g • algebraMap B C b = algebraMap B C (g • b)) → IsNoetherianRing R → Module.Finite A B → Module.Finite R C → Module.Flat B C → (∀ q : Ideal B, q.IsPrime → (Nat.card (q.inertia Γ) : B) ∉ q) → (∀ q : Ideal B, q.IsPrime → ∀ g ∈ q.inertia Γ, ∀ c : C, g • c - c ∈ q.map (algebraMap B C)) → Algebra.IsPushout A B R C := by
  intro Γ _ _ A B R C _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hAB hRC heq hnoeth hfAB hfRC hflat hcard hI
  classical
  haveI := Fintype.ofFinite Γ
  haveI : SMulCommClass A Γ B := SMulCommClass.symm _ _ _
  let φ : B ⊗[A] R →ₐ[B] C := Algebra.TensorProduct.lift (Algebra.ofId B C)
    (IsScalarTower.toAlgHom A R C) (fun _ _ => Commute.all _ _)
  have hφ : ∀ (b : B) (r : R), φ (b ⊗ₜ r) = algebraMap B C b * algebraMap R C r := by
    intro b r
    simp [φ, Algebra.ofId_apply]
  have hsurj : Function.Surjective φ := by
    have := span_range_algebraMap_eq_top_of_tame Γ A B R C hAB hRC heq hfRC hcard hI
    have h2 : LinearMap.range φ.toLinearMap = ⊤ := by
      rw [eq_top_iff, ← this, Submodule.span_le]
      rintro _ ⟨r, rfl⟩
      exact ⟨1 ⊗ₜ r, by simp [hφ]⟩
    exact LinearMap.range_eq_top.1 h2
  have hR : ∀ (g : Γ) (r : R), g • algebraMap R C r = algebraMap R C r := by
    intro g r
    rw [Algebra.algebraMap_eq_smul_one, smul_comm, smul_one]
  have hequi : ∀ (g : Γ) (x : B ⊗[A] R), φ (g • x) = g • φ x := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b r => rw [TensorProduct.smul_tmul', hφ, hφ, smul_mul', heq, hR]
    | add x y hx hy => rw [smul_add, map_add, map_add, smul_add, hx, hy]
  have hsl : ∀ (g : Γ) (b : B) (x : B ⊗[A] R), g • (b • x) = (g • b) • (g • x) := by
    intro g b x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c r => simp only [TensorProduct.smul_tmul', smul_eq_mul, smul_mul']
    | add x y hx hy => simp only [smul_add, hx, hy]
  have htr : ∀ x : B ⊗[A] R, ∃ r : R, ∑ g : Γ, g • x = (1 : B) ⊗ₜ[A] r := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul c r =>
      obtain ⟨a, ha⟩ := Algebra.IsInvariant.isInvariant (A := A) (G := Γ) (∑ g : Γ, g • c) (by
        intro k
        rw [Finset.smul_sum]
        simp only [← mul_smul]
        exact Equiv.sum_comp (Equiv.mulLeft k) (fun g => g • c))
      refine ⟨a • r, ?_⟩
      simp only [TensorProduct.smul_tmul']
      rw [← TensorProduct.sum_tmul, ← ha, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    | add x y hx hy =>
      obtain ⟨r, hr⟩ := hx
      obtain ⟨s, hs⟩ := hy
      exact ⟨r + s, by simp only [smul_add, Finset.sum_add_distrib, hr, hs, TensorProduct.tmul_add]⟩
  have hinv : ∀ x : B ⊗[A] R, φ x = 0 → (∀ g : Γ, g • x = x) → x = 0 := by
    intro x hx hg
    obtain ⟨b, hb⟩ := exists_finsum_smul_eq_one_of_tame Γ B hcard
    rw [finsum_eq_sum_of_fintype] at hb
    obtain ⟨r, hr⟩ := htr (b • x)
    simp only [hsl, hg] at hr
    rw [← Finset.sum_smul, hb, one_smul] at hr
    rw [hr, hφ, map_one, _root_.one_mul, map_eq_zero_iff _ hRC] at hx
    rw [hr, hx, TensorProduct.tmul_zero]
  have hinert : ∀ q : Ideal B, ∀ g ∈ q.inertia Γ, ∀ x : B ⊗[A] R,
      g • x - x ∈ q • (⊤ : Submodule B (B ⊗[A] R)) := by
    intro q g hg x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c r =>
      have : g • (c ⊗ₜ[A] r) - c ⊗ₜ[A] r = (g • c - c) • ((1 : B) ⊗ₜ[A] r) := by
        simp only [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one, TensorProduct.sub_tmul]
      rw [this]
      exact Submodule.smul_mem_smul (hg c) Submodule.mem_top
    | add x y hx hy =>
      rw [smul_add, add_sub_add_comm]
      exact Submodule.add_mem _ hx hy
  let K : Submodule B (B ⊗[A] R) := LinearMap.ker φ.toLinearMap
  have hK : ∀ x, x ∈ K ↔ φ x = 0 := fun x => Iff.rfl
  letI : SMul Γ K := ⟨fun g x => ⟨g • (x : B ⊗[A] R), by
    rw [hK, hequi, (hK _).1 x.2, smul_zero]⟩⟩
  letI : DistribMulAction Γ K :=
    Function.Injective.distribMulAction K.subtype.toAddMonoidHom K.injective_subtype
      (fun _ _ => rfl)
  haveI : IsNoetherianRing (B ⊗[A] R) := by
    haveI : IsNoetherianRing (R ⊗[A] B) := Algebra.FiniteType.isNoetherianRing R _
    exact isNoetherianRing_of_ringEquiv _ (Algebra.TensorProduct.comm A R B).toRingEquiv
  have hker : RingHom.ker φ = ⊥ := by
    refine ideal_eq_bot_of_forall_prime_smul_mem (B := B) _ (IsNoetherian.noetherian _) ?_
    intro q hq x hx
    obtain ⟨s, hs, hsx⟩ := exists_smul_mem_span_invariants_sup Γ B K
      (fun g b y => Subtype.ext (hsl g b y)) q hq (hcard q hq)
      (fun g hg y => mem_smul_ker_of_flat_quotient φ.toLinearMap hsurj q _ (hinert q g hg y))
      ⟨x, hx⟩
    refine ⟨s, hs, ?_⟩
    have hbot : Submodule.span B {y : K | ∀ g : Γ, g • y = y} = ⊥ := by
      rw [Submodule.span_eq_bot]
      intro y hy
      exact Subtype.ext (hinv y y.2 fun g => congrArg Subtype.val (hy g))
    rw [hbot, bot_sup_eq, Submodule.mem_smul_top_iff] at hsx
    exact hsx
  have hinj : Function.Injective φ := (RingHom.injective_iff_ker_eq_bot φ).2 hker
  exact ⟨IsBaseChange.of_equiv (LinearEquiv.ofBijective φ.toLinearMap ⟨hinj, hsurj⟩)
    (fun r => (hφ 1 r).trans (by simp))⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSectionCoordinateVectorOfLocallyOnRing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM

theorem stalkMap_germ_appLE {Y Z : Scheme.{0}} (f : Z ⟶ Y) (W : Y.Opens) (W' : Z.Opens) (h : W' ≤ f ⁻¹ᵁ W)
    (z : Z) (hz : z ∈ W') (s : Γ(Y, W)) :
    (f.stalkMap z).hom ((Y.presheaf.germ W (f z) (h hz)).hom s) =
      (Z.presheaf.germ W' z hz).hom ((f.appLE W W' h).hom s) := by
  have e : Y.presheaf.germ W (f z) (h hz) ≫ f.stalkMap z = f.appLE W W' h ≫ Z.presheaf.germ W' z hz := by
    erw [Scheme.Hom.germ_stalkMap]
    rw [Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
  exact congrArg (fun g => g.hom s) e

theorem sec_eq_of_openImm {Y : Scheme.{0}} (W : Y.Opens) (s t : Γ(Y, W))
    (H : ∀ p ∈ W, ∃ (Z : Scheme.{0}) (f : Z ⟶ Y) (_ : IsOpenImmersion f) (z : Z) (W' : Z.Opens)
      (h : W' ≤ f ⁻¹ᵁ W), z ∈ W' ∧ f z = p ∧ (f.appLE W W' h).hom s = (f.appLE W W' h).hom t) : s = t := by
  apply TopCat.Presheaf.section_ext Y.sheaf W s t
  intro p hp
  obtain ⟨Z, f, _, z, W', h, hz, rfl, e⟩ := H p hp
  apply (ConcreteCategory.injective_of_mono_of_preservesPullback (f.stalkMap z))
  have e1 := stalkMap_germ_appLE f W W' h z hz s
  have e2 := stalkMap_germ_appLE f W W' h z hz t
  rw [e] at e1
  exact e1.trans e2.symm

theorem sec_isUnit_of_pull {Y : Scheme.{0}} (W : Y.Opens) (s : Γ(Y, W))
    (H : ∀ p ∈ W, ∃ (Z : Scheme.{0}) (f : Z ⟶ Y) (z : Z) (W' : Z.Opens)
      (h : W' ≤ f ⁻¹ᵁ W), z ∈ W' ∧ f z = p ∧ IsUnit ((f.appLE W W' h).hom s)) : IsUnit s := by
  apply Y.toRingedSpace.isUnit_of_isUnit_germ W s
  intro p hp
  obtain ⟨Z, f, z, W', h, hz, rfl, u⟩ := H p hp
  apply isUnit_of_map_unit (f.stalkMap z).hom
  rw [stalkMap_germ_appLE f W W' h z hz]
  exact u.map _

def spConst (R : Type) [CommRing R] (W : (Sp R).Opens) : R →+* Γ(Sp R, W) :=
  (resG (Sp R) (le_top : W ≤ ⊤)).comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem appLE_spConst {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (W : (Sp R).Opens)
    (W' : (Sp R').Opens) (h : W' ≤ spMap φ ⁻¹ᵁ W) (r : R) :
    ((spMap φ).appLE W W' h).hom (spConst R W r) = spConst R' W' (φ r) := by
  have key : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (Sp R).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op ≫
      (spMap φ).appLE W W' h =
      CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (CommRingCat.of R')).inv ≫
        (Sp R').presheaf.map (homOfLE (le_top : W' ≤ ⊤)).op := by
    rw [Scheme.Hom.map_appLE, ← Category.assoc, Scheme.ΓSpecIso_inv_naturality, Category.assoc]
    rfl
  exact congrArg (fun g => g.hom r) key

private theorem mem_pull_U_iff' {X T : Scheme.{0}} (M : LB X) (y : T ⟶ X) (j : PUnit → M.ι) (p : T) :
    p ∈ (M.pull y).U j ↔ y p ∈ M.U (j PUnit.unit) := by
  unfold LB.pull LB.LinComb LB.wchart
  simp only [TopologicalSpace.Opens.mem_mk, Set.mem_iInter, Set.mem_preimage]
  exact ⟨fun h => h _, fun h _ => h⟩

private theorem appLE_appLE_lemma_2 {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (U : X.Opens) (V : Y.Opens)
    (V' : Z.Opens) (hV : V ≤ g ⁻¹ᵁ U) (hV' : V' ≤ f ⁻¹ᵁ V) (h3 : V' ≤ (f ≫ g) ⁻¹ᵁ U) (s : Γ(X, U)) :
    (f.appLE V V' hV').hom ((g.appLE U V hV).hom s) = ((f ≫ g).appLE U V' h3).hom s := by
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE]

private theorem appLE_resG_eq_resG_appLE {Y Z : Scheme.{0}} (f : Z ⟶ Y) {V1 V2 : Y.Opens} {W1 W2 : Z.Opens}
    (hV : V1 ≤ V2) (hW : W1 ≤ W2) (h1 : W1 ≤ f ⁻¹ᵁ V1) (h2 : W2 ≤ f ⁻¹ᵁ V2) (s : Γ(Y, V2)) :
    (f.appLE V1 W1 h1).hom (resG Y hV s) = resG Z hW ((f.appLE V2 W2 h2).hom s) := by
  simp only [resG]
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.Hom.map_appLE, ← RingHom.comp_apply,
    ← CommRingCat.hom_comp, Scheme.Hom.appLE_map]

private theorem pull_g_coe_eq_appLE_g {X T : Scheme.{0}} (M : LB X) (y : T ⟶ X) (j j' : PUnit → M.ι)
    (h : (M.pull y).U j ⊓ (M.pull y).U j' ≤ y ⁻¹ᵁ (M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit))) :
    (((M.pull y).g j j' : (Γ(T, (M.pull y).U j ⊓ (M.pull y).U j'))ˣ) : Γ(T, (M.pull y).U j ⊓ (M.pull y).U j')) =
      (y.appLE _ _ h).hom (M.g (j PUnit.unit) (j' PUnit.unit) : Γ(X, M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit))) := by
  unfold LB.pull LB.LinComb
  simp [pullU, res, Scheme.Hom.appLE]
  rfl

theorem secCoord_of_locally (X : Scheme.{0}) (M : LB X) (I : Type) (th : I → M.Sec) (R : Type) [CommRing R]
    (x : Sp R ⟶ X) (v : I → R) (_hM : M.IsLB) (hv : Ideal.span (Set.range v) = ⊤)
    (H : ∀ p : Sp R, ∃ (R' : Type) (_ : CommRing R') (φ : R →+* R'), IsOpenImmersion (spMap φ) ∧
      p ∈ Set.range (spMap φ) ∧ SecCoord M th (spMap φ ≫ x) (fun i => φ (v i))) :
    SecCoord M th x v := by
  have h1 : (1 : R) ∈ Ideal.span (Set.range v) := by rw [hv]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := Finsupp.mem_ideal_span_range_iff_exists_finsupp.1 h1
  have W1 : ∀ j : PUnit → M.ι, (M.pull x).U j ≤ x ⁻¹ᵁ M.U (j PUnit.unit) :=
    fun j p hp => (mem_pull_U_iff' M x j p).1 hp
  have W2 : ∀ {R' : Type} [CommRing R'] (φ : R →+* R') (j : PUnit → M.ι),
      (M.pull (spMap φ ≫ x)).U j ≤ spMap φ ⁻¹ᵁ (M.pull x).U j :=
    fun φ j z hz => (mem_pull_U_iff' M x j _).2 ((mem_pull_U_iff' M _ j z).1 hz)
  let t : ∀ j : PUnit → M.ι, Γ(Sp R, (M.pull x).U j) := fun j =>
    c.sum (fun i a => spConst R _ a * (x.appLE _ _ (W1 j)).hom ((th i).f (j PUnit.unit)))
  have pt : ∀ {R' : Type} [CommRing R'] (φ : R →+* R') (τ' : (M.pull (spMap φ ≫ x)).Gen),
      (∀ i j h, ((spMap φ ≫ x).appLE (M.U (j PUnit.unit)) ((M.pull (spMap φ ≫ x)).U j) h).hom
          ((th i).f (j PUnit.unit)) = spConst R' _ (φ (v i)) * (τ'.s j).val) →
      ∀ j, ((spMap φ).appLE _ _ (W2 φ j)).hom (t j) = (τ'.s j).val := by
    intro R' _ φ τ' hco j
    have e1 : ∀ i, ((spMap φ).appLE _ _ (W2 φ j)).hom
        (spConst R _ (c i) * (x.appLE _ _ (W1 j)).hom ((th i).f (j PUnit.unit))) =
        spConst R' _ (φ (c i) * φ (v i)) * (τ'.s j).val := by
      intro i
      rw [map_mul, appLE_spConst, appLE_appLE_lemma_2 (spMap φ) x _ _ _ (W1 j) (W2 φ j)
        (fun p hp => (mem_pull_U_iff' M _ j p).1 hp), map_mul, _root_.mul_assoc]
      exact congrArg (spConst R' _ (φ (c i)) * ·) (hco i j (fun p hp => (mem_pull_U_iff' M _ j p).1 hp))
    have e2 : ∑ i ∈ c.support, φ (c i) * φ (v i) = 1 := by
      have := congrArg φ hc
      rw [map_one, Finsupp.sum, map_sum] at this
      simpa [map_mul] using this
    show ((spMap φ).appLE _ _ (W2 φ j)).hom (∑ i ∈ c.support, _) = _
    rw [map_sum, Finset.sum_congr rfl (fun i _ => e1 i), ← Finset.sum_mul, ← map_sum, e2, map_one, _root_.one_mul]
  have hu : ∀ j, IsUnit (t j) := by
    intro j
    apply sec_isUnit_of_pull
    intro p hp
    obtain ⟨R', _, φ, _, ⟨z, rfl⟩, τ', _, hco⟩ := H p
    refine ⟨Sp R', spMap φ, z, (M.pull (spMap φ ≫ x)).U j, W2 φ j, ?_, rfl, ?_⟩
    · exact (mem_pull_U_iff' M _ j z).2 ((mem_pull_U_iff' M x j _).1 hp)
    · rw [pt φ τ' hco j]; exact (τ'.s j).isUnit
  unfold SecCoord
  refine ⟨⟨fun j => (hu j).unit⟩, ?_, ?_⟩
  · intro i j
    apply Units.ext
    show resG _ inf_le_left (t i) = ((M.pull x).g i j).val * resG _ inf_le_right (t j)
    apply sec_eq_of_openImm
    intro p hp
    obtain ⟨R', _, φ, hoi, ⟨z, rfl⟩, τ', hg, hco⟩ := H p
    have Wi : (M.pull (spMap φ ≫ x)).U i ⊓ (M.pull (spMap φ ≫ x)).U j ≤
        spMap φ ⁻¹ᵁ ((M.pull x).U i ⊓ (M.pull x).U j) := fun z hz => ⟨W2 φ i hz.1, W2 φ j hz.2⟩
    refine ⟨Sp R', spMap φ, hoi, z, _, Wi, ?_, rfl, ?_⟩
    · exact ⟨(mem_pull_U_iff' M _ i z).2 ((mem_pull_U_iff' M x i _).1 hp.1),
        (mem_pull_U_iff' M _ j z).2 ((mem_pull_U_iff' M x j _).1 hp.2)⟩
    · rw [map_mul, appLE_resG_eq_resG_appLE (spMap φ) inf_le_left inf_le_left Wi (W2 φ i),
        appLE_resG_eq_resG_appLE (spMap φ) inf_le_right inf_le_right Wi (W2 φ j), pt φ τ' hco i, pt φ τ' hco j]
      have h3 : (M.pull (spMap φ ≫ x)).U i ⊓ (M.pull (spMap φ ≫ x)).U j ≤
          (spMap φ ≫ x) ⁻¹ᵁ (M.U (i PUnit.unit) ⊓ M.U (j PUnit.unit)) :=
        fun q hq => ⟨(mem_pull_U_iff' M _ i q).1 hq.1, (mem_pull_U_iff' M _ j q).1 hq.2⟩
      rw [pull_g_coe_eq_appLE_g M x i j (fun q hq => ⟨W1 i hq.1, W1 j hq.2⟩)]
      erw [appLE_appLE_lemma_2 (spMap φ) x _ _ _ _ Wi h3, ← pull_g_coe_eq_appLE_g M (spMap φ ≫ x) i j h3]
      exact congrArg Units.val (hg i j)
  · intro i j h
    show _ = spConst R _ (v i) * t j
    apply sec_eq_of_openImm
    intro p hp
    obtain ⟨R', _, φ, hoi, ⟨z, rfl⟩, τ', _, hco⟩ := H p
    refine ⟨Sp R', spMap φ, hoi, z, _, W2 φ j, ?_, rfl, ?_⟩
    · exact (mem_pull_U_iff' M _ j z).2 ((mem_pull_U_iff' M x j _).1 hp)
    · rw [map_mul, appLE_spConst, pt φ τ' hco j, appLE_appLE_lemma_2 (spMap φ) x _ _ _ h (W2 φ j)
        (fun p hp => (mem_pull_U_iff' M _ j p).1 hp)]
      exact hco i j (fun p hp => (mem_pull_U_iff' M _ j p).1 hp)

end GlobalTheory.ZM
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LineBundleTrivialIsoDescendField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory

namespace FieldDescentGen

variable {X₀ X : Scheme.{0}}

theorem pull_le (M : LB X₀) (φ : X ⟶ X₀) (j : PUnit → M.ι) : (M.pull φ).U j ≤ φ ⁻¹ᵁ M.U (j PUnit.unit) :=
  fun _ hy => mem_pull.1 hy

def secPull (M : LB X₀) (φ : X ⟶ X₀) (s : M.Sec) : (M.pull φ).Sec where
  f j := (φ.appLE _ _ (pull_le M φ j)).hom (s.f (j PUnit.unit))
  compat i j := by
    have h : (M.pull φ).U i ⊓ (M.pull φ).U j ≤ φ ⁻¹ᵁ (M.U (i PUnit.unit) ⊓ M.U (j PUnit.unit)) :=
      fun _ hy => ⟨pull_le M φ i hy.1, pull_le M φ j hy.2⟩
    have e := congrArg (φ.appLE _ _ h).hom (s.compat (i PUnit.unit) (j PUnit.unit))
    rw [map_mul] at e
    have g : ((M.pull φ).g i j : Γ(X, (M.pull φ).U i ⊓ (M.pull φ).U j)) =
        (φ.appLE _ _ h).hom (M.g (i PUnit.unit) (j PUnit.unit)) := by
      have gu : (M.pull φ).g i j = res h (pullU φ _ (M.g (i PUnit.unit) (j PUnit.unit))) :=
        (Fintype.prod_unique fun k : PUnit => (res h (pullU φ _ (M.g (i k) (j k)))) ^ (1 : ℤ)).trans (zpow_one _)
      exact congrArg Units.val gu
    rw [g]
    simp only [← CommRingCat.comp_apply, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE] at e ⊢
    exact e

theorem exists_ratio {L : LB X} (hL : L.IsLB) (t : L.Gen) (ht : t.IsGen) (s : L.Sec) :
    ∃ u : Γ(X, ⊤), ∀ j, s.f j =
      (X.presheaf.map (homOfLE (le_top : L.U j ≤ ⊤)).op).hom u * (t.s j).val := by
  obtain ⟨u, hu⟩ := Out.TLinPf.glue L.U hL.cover (fun j => s.f j * ((t.s j)⁻¹).val) (fun i j => by
    have e : res (inf_le_right : L.U i ⊓ L.U j ≤ L.U j) (t.s j)⁻¹ =
        L.g i j * res (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) (t.s i)⁻¹ := by
      rw [map_inv, map_inv, ht i j, mul_inv, mul_inv_cancel_left]
    have e' : (X.presheaf.map (homOfLE (inf_le_right : L.U i ⊓ L.U j ≤ L.U j)).op).hom ((t.s j)⁻¹).val =
        (L.g i j).val * (X.presheaf.map (homOfLE (inf_le_left : L.U i ⊓ L.U j ≤ L.U i)).op).hom ((t.s i)⁻¹).val :=
      congrArg Units.val e
    rw [map_mul, map_mul, s.compat i j, e']
    ring)
  exact ⟨u, fun j => by rw [hu j, _root_.mul_assoc, Units.inv_mul, _root_.mul_one]⟩

theorem isUnit_of_surjective (φ : X ⟶ X₀) [Surjective φ] {U : X₀.Opens} {V : X.Opens} (h : V ≤ φ ⁻¹ᵁ U)
    (h' : φ ⁻¹ᵁ U ≤ V) (a : Γ(X₀, U)) (ha : IsUnit ((φ.appLE U V h).hom a)) : IsUnit a := by
  refine RingedSpace.isUnit_of_isUnit_germ X₀.toLocallyRingedSpace.toRingedSpace U a fun x hx => ?_
  obtain ⟨y, rfl⟩ := φ.surjective x
  have hy : y ∈ X.basicOpen ((φ.appLE U V h).hom a) := by
    rw [X.basicOpen_of_isUnit ha]; exact h' hx
  rw [Scheme.basicOpen_appLE] at hy
  exact (X₀.mem_basicOpen a _ hx).1 hy.2

def chartDiv (M N : LB X₀) (φ : X ⟶ X₀) :
    ChartPull ((LB.div N M).pull φ) (LB.div (N.pull φ) (M.pull φ)) (𝟙 X) where
  idx J := (fun _ => (J PUnit.unit).1, fun _ => (J PUnit.unit).2)
  le J y hy := ⟨mem_pull.2 (mem_pull.1 hy).1, mem_pull.2 (mem_pull.1 hy).2⟩
  g y J J' hj hj' := by
    have a := mem_pull.1 hj
    have a' := mem_pull.1 hj'
    refine (gm_pull_g (LB.div N M) φ (𝟙 X) y J J' hj hj').trans
      ((gm_div M N (𝟙 X ≫ φ) y (J PUnit.unit) (J' PUnit.unit) ⟨a, a'⟩).trans (Eq.symm ?_))
    refine (gm_div (M.pull φ) (N.pull φ) (𝟙 X) y (fun _ => (J PUnit.unit).1, fun _ => (J PUnit.unit).2)
      (fun _ => (J' PUnit.unit).1, fun _ => (J' PUnit.unit).2)
      ⟨⟨mem_pull.2 a.1, mem_pull.2 a.2⟩, mem_pull.2 a'.1, mem_pull.2 a'.2⟩).trans ?_
    exact congrArg₂ (fun u v => u * v⁻¹)
      (gm_pull_g N φ (𝟙 X) y _ _ (mem_pull.2 a.1) (mem_pull.2 a'.1))
      (gm_pull_g M φ (𝟙 X) y _ _ (mem_pull.2 a.2) (mem_pull.2 a'.2))

theorem exists_gen {K₀ K : Type} [Field K₀] [Field K] (i : K₀ →+* K) (p₀ : X₀ ⟶ Sp K₀) (p : X ⟶ Sp K)
    (φ : X ⟶ X₀) [Smooth p₀] [IsProper p₀] [GeometricallyConnected p₀] (H : IsPullback φ p p₀ (spMap i))
    (M : LB X₀) (hM : M.IsLB) (t : (M.pull φ).Gen) (ht : t.IsGen) : ∃ t : M.Gen, t.IsGen := by
  have hb : Function.Bijective p.appTop.hom := GlobalTheory.bijective_appTop_of_smooth_of_isProper_of_geometricallyConnected K X p
    (MorphismProperty.of_isPullback (P := @Smooth) H inferInstance)
    (MorphismProperty.of_isPullback (P := @IsProper) H inferInstance)
    (MorphismProperty.of_isPullback (P := @GeometricallyConnected) H inferInstance)
  have hF : IsField Γ(X, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.trans
      (RingEquiv.ofBijective p.appTop.hom hb)).symm.toMulEquiv.isField (Field.toIsField K)
  have : Surjective φ := ((GlobalTheory.FieldBaseChange.epi_and_isMonHom_iff K₀ K i).1 X₀ X p₀ p φ H).2.2.1
  have hP := pull_isLB hM φ
  let ts : (M.pull φ).Sec := ⟨fun j => (t.s j).val, fun a b => congrArg Units.val (ht a b)⟩
  obtain ⟨n, c, s, hs⟩ := GlobalTheory.SectionsDescent.main K₀ K i X₀ X p₀ p φ M hM H ts
  choose u hu using fun a => exists_ratio hP t ht (secPull M φ (s a))
  have hne : ∃ a, u a ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have := hF.nontrivial
    refine one_ne_zero (Out.TLinPf.eq_local (M.pull φ).U hP.cover 1 0 fun j => ?_)
    have h0 : (t.s j).val = 0 := by
      refine (hs j (pull_le M φ j)).trans (Finset.sum_eq_zero fun a _ => ?_)
      have e : (φ.appLE _ _ (pull_le M φ j)).hom ((s a).f (j PUnit.unit)) = _ := hu a j
      rw [e, hcon a, map_zero, zero_mul, mul_zero]
    rw [map_one, map_zero, ← (t.s j).mul_inv, h0, zero_mul]
  obtain ⟨a, ha⟩ := hne
  obtain ⟨v, hv⟩ := hF.mul_inv_cancel ha
  have hua : IsUnit (u a) := IsUnit.of_mul_eq_one v hv
  have hunit : ∀ k, IsUnit ((s a).f k) := fun k =>
    isUnit_of_surjective φ (pull_le M φ fun _ => k) (fun _ hy => mem_pull.2 hy) _ (by
      have e : (φ.appLE _ _ (pull_le M φ fun _ => k)).hom ((s a).f k) = _ := hu a fun _ => k
      rw [e]
      exact (hua.map _).mul (Units.isUnit _))
  exact ⟨⟨fun k => (hunit k).unit⟩, fun k l => Units.ext ((s a).compat k l)⟩

end FieldDescentGen

open FieldDescentGen in

theorem lb_gen_iso_descend_field : ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (X₀ X : Scheme.{0}) (p₀ : X₀ ⟶ Sp K₀) (p : X ⟶ Sp K) (φ : X ⟶ X₀), Smooth p₀ → IsProper p₀ → GeometricallyConnected p₀ → IsPullback φ p p₀ (spMap i) → (∀ M : LB X₀, M.IsLB → (∃ t : (M.pull φ).Gen, t.IsGen) → ∃ t : M.Gen, t.IsGen) ∧ ∀ M N : LB X₀, M.IsLB → N.IsLB → LBIso (M.pull φ) (N.pull φ) → LBIso M N := by
  intro K₀ K _ _ i X₀ X p₀ p φ h₁ h₂ h₃ H
  refine ⟨fun M hM ⟨t, ht⟩ => exists_gen i p₀ p φ H M hM t ht, fun M N hM hN ⟨w, hw⟩ => ?_⟩
  exact exists_gen i p₀ p φ H (LB.div N M) (LB.isLB_div hN hM) _
    (GtBaseChange.genPull_isGen (chartDiv M N φ) hw)

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SharpRelations
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM GlobalTheory.KS

noncomputable section
namespace GlobalTheory.SharpRel

section
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'}
  [GrpObj A] [GrpObj A'] {φ : A'.left ⟶ A.left}

theorem push_inj (h : IsGrpPullback A' A f φ) {T : Over S'} {x y : T ⟶ A'}
    (e : pushHom h T x = pushHom h T y) : x = y := by
  have hl : x.left ≫ φ = y.left ≫ φ := congrArg CommaMorphism.left e
  ext1
  exact h.1.hom_ext hl (by rw [Over.w x, Over.w y])

theorem push_comp (h : IsGrpPullback A' A f φ) {p : A ⟶ A} {p' : A' ⟶ A'}
    (e : p'.left ≫ φ = φ ≫ p.left) {T : Over S'} (x : T ⟶ A') :
    pushHom h T (x ≫ p') = pushHom h T x ≫ p := by
  ext1
  change (x ≫ p').left ≫ φ = (x.left ≫ φ) ≫ p.left
  rw [Over.comp_left, Category.assoc, Category.assoc, e]

end

def postHom {S : Scheme.{0}} {A C : Over S} [GrpObj A] [GrpObj C] (p : A ⟶ C) [IsMonHom p] (T : Over S) :
    (T ⟶ A) →* (T ⟶ C) :=
  MonoidHom.mk' (· ≫ p) fun x y => MonObj.mul_comp x y p

end GlobalTheory.SharpRel
end
end

