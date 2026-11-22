import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsScalarFormTraceForm
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0043
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClassicalPointEqOfReductionCoords
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0057
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0059
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0052
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBasisLatticeNear
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0056
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0051
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0049
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AdditivePointsDescendFieldExtension
section
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

namespace GlobalTheory.PointDescent

theorem exists_lift {X I G H : Type*} [AddGroup X] [Group G] [Group H] (b : I → X)
    (hb : AddSubgroup.closure (Set.range b) = ⊤) (a : X → G) (ha : ∀ y z, a (y + z) = a y * a z) (β : H →* G)
    (hβ : Function.Injective β) (x₀ : I → H) (hx : ∀ k, a (b k) = β (x₀ k)) :
    ∃ c₀ : X → H, (∀ y z, c₀ (y + z) = c₀ y * c₀ z) ∧ ∀ y, a y = β (c₀ y) := by
  have h0 : a 0 = 1 := by
    have := ha 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have key : ∀ y, ∃ x, a y = β x := fun y => by
    have hy : y ∈ AddSubgroup.closure (Set.range b) := hb ▸ AddSubgroup.mem_top y
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨k, rfl⟩ := hy
      exact ⟨_, hx k⟩
    | zero => exact ⟨1, by rw [h0, map_one]⟩
    | add y z _ _ hy hz =>
      obtain ⟨u, hu⟩ := hy
      obtain ⟨v, hv⟩ := hz
      exact ⟨u * v, by rw [ha, hu, hv, map_mul]⟩
    | neg y _ hy =>
      obtain ⟨u, hu⟩ := hy
      refine ⟨u⁻¹, ?_⟩
      rw [map_inv, ← hu, eq_inv_iff_mul_eq_one, ← ha, neg_add_cancel, h0]
  choose c₀ hc using key
  exact ⟨c₀, fun y z => hβ (by rw [map_mul, ← hc, ← hc, ← hc, ha]), hc⟩

theorem exists_descent {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} [Epi f]
    {Φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f Φ) {X I : Type*} [AddGroup X] (b : I → X)
    (hb : AddSubgroup.closure (Set.range b) = ⊤) (c : X → (𝟙_ (Over S') ⟶ G')) (hc : ∀ y z, c (y + z) = c y * c z)
    (x₀ : I → (𝟙_ (Over S) ⟶ G)) (hx : ∀ k, (c (b k)).left ≫ Φ = f ≫ (x₀ k).left) :
    ∃ c₀ : X → (𝟙_ (Over S) ⟶ G), (∀ y z, c₀ (y + z) = c₀ y * c₀ z) ∧ ∀ y, (c y).left ≫ Φ = f ≫ (c₀ y).left := by
  let ρ : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ 𝟙_ (Over S) :=
    Over.homMk f ((Category.comp_id f).trans (Category.id_comp f).symm)
  obtain ⟨c₀, h₁, h₂⟩ := exists_lift b hb (fun y => pushHom h (𝟙_ (Over S')) (c y))
    (fun y z => by rw [hc, map_mul]) (preHom (G := G) ρ)
    (fun u v huv => Over.OverMorphism.ext ((cancel_epi f).1 (congrArg (fun q => q.left) huv))) x₀
    (fun k => Over.OverMorphism.ext (hx k))
  exact ⟨c₀, h₁, fun y => congrArg (fun q => q.left) (h₂ y)⟩

theorem additive_points_descend : ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (P₀ : PolAV (Sp K₀)) (P : PolAV (Sp K)) (Φ : P.A.left ⟶ P₀.A.left), IsGrpPullback P.A P₀.A (spMap i) Φ → ∀ (X : Type) [AddCommGroup X] (I : Type) (b : I → X), AddSubgroup.closure (Set.range b) = ⊤ → ∀ c : X → (𝟙_ (Over (Sp K)) ⟶ P.A), (∀ y z, c (y + z) = padd P.A (c y) (c z)) → ∀ x₀ : I → (𝟙_ (Over (Sp K₀)) ⟶ P₀.A), (∀ k, (c (b k)).left ≫ Φ = spMap i ≫ (x₀ k).left) → ∃ c₀ : X → (𝟙_ (Over (Sp K₀)) ⟶ P₀.A), (∀ y z, c₀ (y + z) = padd P₀.A (c₀ y) (c₀ z)) ∧ ∀ y, (c y).left ≫ Φ = spMap i ≫ (c₀ y).left := by
  intro K₀ K _ _ i P₀ P Φ h X _ I b hb c hc x₀ hx
  have := FieldBaseChange.flat_spMap i
  have := FieldBaseChange.surjective_spMap i
  have : Epi (spMap i) := Flat.epi_of_flat_of_surjective _
  exact exists_descent h b hb c hc x₀ hx

end GlobalTheory.PointDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClassicalPointEqOfReductionCoordsStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
theorem _root_.GlobalTheory.T.classical_point_eq_of_reduction_coords : ∀ C : Core, C.HasTests → C.Fib → ∀ (w : C.G.toScheme) (W : C.G.toScheme.Opens) (hw : w ∈ W) (u : Fin C.g → Γ(C.G.toScheme, W)), C.Coord w W hw u → ∀ (p : ℕ) [Fact p.Prime] (a a' : Sp (OO p) ⟶ W.toScheme), C.Cl (a ≫ W.ι ≫ C.GG.hom) → a ≫ W.ι ≫ C.GG.hom = a' ≫ W.ι ≫ C.GG.hom → a (cPt p) = ⟨w, hw⟩ → rPt p ≫ a = rPt p ≫ a' → (∀ i, a.appTop.hom (W.topIso.inv.hom (u i)) = a'.appTop.hom (W.topIso.inv.hom (u i))) → a = a' := by
  first | exact @GlobalTheory.ZJ.classical_eq_of_coord | exact GlobalTheory.ZJ.classical_eq_of_coord | (intros; apply GlobalTheory.ZJ.classical_eq_of_coord <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClosedImmersionGenericUnitLocusStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closed_immersion_generic_unit_locus : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (Z H : Scheme.{0}) (i : Z ⟶ H) (q : H ⟶ Sp R), IsClosedImmersion i → LocallyOfFiniteType q → QuasiCompact q → (∀ (B : Type) [CommRing B] (x : Sp B ⟶ H) (t : Sp B ⟶ Sp K), x ≫ q = t ≫ spMap (algebraMap R K) → ∃ y : Sp B ⟶ Z, y ≫ i = x) → ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ (T : Scheme.{0}) (x : T ⟶ H) (t : T ⟶ Sp R'), x ≫ q = t ≫ spMap g → ∃ y : T ⟶ Z, y ≫ i = x := by
  first | exact @GlobalTheory.GenSpread.ClosedFac.exists_lift | exact GlobalTheory.GenSpread.ClosedFac.exists_lift | (intros; apply GlobalTheory.GenSpread.ClosedFac.exists_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClosureEqKerOfMeetsTorsionCosets
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem zmod_pow_exists_eq_nsmul_of_nsmul_eq_zero (n J : ℕ) (hn : n ≠ 0) (hJ : 2 ≤ J)
    (t : ZMod (n ^ J)) (ht : n • t = 0) : ∃ s : ZMod (n ^ J), t = n • s := by
  have : NeZero (n ^ J) := ⟨pow_ne_zero _ hn⟩
  have hv : n ^ J ∣ n * t.val := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_mul, ZMod.natCast_zmod_val, ← nsmul_eq_mul]
    exact ht
  obtain ⟨k, hk⟩ := hv
  have h1 : t.val = n * (n ^ (J - 2) * k) := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hn)
    rw [hk, show n ^ J = n * (n * n ^ (J - 2)) by
      rw [← pow_succ', ← pow_succ']; congr 1; omega]
    ring
  refine ⟨((n ^ (J - 2) * k : ℕ) : ZMod (n ^ J)), ?_⟩
  rw [nsmul_eq_mul, ← Nat.cast_mul, ← h1, ZMod.natCast_zmod_val]

theorem closure_eq_ker_of_meets_torsion_cosets :
    ∀ (I X : Type) [AddCommGroup X] [Module.Free ℤ X] (n J M : ℕ), n ≠ 0 → 2 ≤ J → M = n ^ J → ∀ (yy : (I → ZMod M) →+ X ⧸ (nsmulAddMonoidHom M : X →+ X).range), Function.Surjective yy → ∀ Z : Set (I → ZMod M), Z ⊆ yy.ker → (∀ a ∈ yy.ker, ∃ b, n • b = 0 ∧ a + b ∈ Z) → AddSubgroup.closure Z = yy.ker := by
  intro I X _ _ n J M hn hJ hM yy hyy Z hZ hcov
  subst hM
  have key : ∀ b : I → ZMod (n ^ J), n • b = 0 → b ∈ yy.ker → ∃ k ∈ yy.ker, n • k = b := by
    intro b hb hbk
    have hc : ∀ i, ∃ s, b i = n • s := fun i =>
      zmod_pow_exists_eq_nsmul_of_nsmul_eq_zero n J hn hJ (b i) (by
        simpa using congrFun hb i)
    choose c hc using hc
    have hbc : b = n • c := funext fun i => by simpa using hc i
    obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (yy c)
    have hnx : n • x ∈ (nsmulAddMonoidHom (n ^ J) : X →+ X).range := by
      rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.mk_nsmul, hx, ← map_nsmul, ← hbc]
      exact hbk
    obtain ⟨x', hx'⟩ := hnx
    have hx'' : (n ^ J) • x' = n • x := hx'
    have hxx : x = n ^ (J - 1) • x' := by
      have h2 : (n : ℤ) • x = (n : ℤ) • (n ^ (J - 1) • x') := by
        rw [natCast_zsmul, natCast_zsmul, smul_smul, ← pow_succ', show J - 1 + 1 = J by omega]
        exact hx''.symm
      exact smul_right_injective X (by exact_mod_cast hn) h2
    obtain ⟨c', hc'⟩ := hyy (QuotientAddGroup.mk x')
    refine ⟨c - n ^ (J - 1) • c', ?_, ?_⟩
    · rw [AddMonoidHom.mem_ker, map_sub, map_nsmul, hc', ← QuotientAddGroup.mk_nsmul, ← hxx, hx,
        sub_self]
    · have h0 : (n ^ J) • c' = 0 := funext fun i => by
        simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
      rw [smul_sub, smul_smul, ← pow_succ', show J - 1 + 1 = J by omega, ← hbc, h0, sub_zero]
  apply le_antisymm
  · exact (AddSubgroup.closure_le _).2 hZ
  · intro a ha
    obtain ⟨b, hb, hab⟩ := hcov a ha
    have hbk : b ∈ yy.ker := by
      have h3 : yy (a + b) = 0 := hZ hab
      rw [AddMonoidHom.mem_ker] at ha ⊢
      rwa [map_add, ha, zero_add] at h3
    obtain ⟨k, hk, hkb⟩ := key b hb hbk
    obtain ⟨b', hb', hkb'⟩ := hcov k hk
    have h4 : a = (a + b) - n • (k + b') := by
      rw [smul_add, hb', add_zero, hkb, add_sub_cancel_right]
    rw [h4]
    exact sub_mem (AddSubgroup.subset_closure hab) (nsmul_mem (AddSubgroup.subset_closure hkb') n)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClosureZmodPowEqTopOfMeetsTorsionCosetsStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closure_zmodPow_eq_top_of_meets_torsion_cosets : ∀ (κ : Type) (n J M : ℕ), 1 ≤ n → 2 ≤ J → M = n ^ J → ∀ X : Set (κ → ZMod M), (∀ a : κ → ZMod M, ∃ y : κ → ZMod M, n • y = 0 ∧ a + y ∈ X) → AddSubgroup.closure X = ⊤ := by
  first | exact @GlobalTheory.ThetaReal.closure_eq_top_of_meets_torsion_cosets | exact GlobalTheory.ThetaReal.closure_eq_top_of_meets_torsion_cosets | (intros; apply GlobalTheory.ThetaReal.closure_eq_top_of_meets_torsion_cosets <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EEContainsStableWeightZero
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH.LatticeStable

open FreeNear TestBasis

theorem quadratic_nonneg {X : Type} [AddCommGroup X] (q : QuadraticMap ℤ X ℝ)
    (hq : Filter.Tendsto q Filter.cofinite Filter.atTop) (a : X) : 0 ≤ q a := by
  obtain ⟨b, hb⟩ := hq.exists_forall_le
  have h0 : q b ≤ 0 := by simpa using hb 0
  have h2 := hb ((2 : ℤ) • b)
  rw [QuadraticMap.map_smul] at h2
  simp only [zsmul_eq_mul] at h2
  push_cast at h2
  have := hb a
  linarith

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω}

theorem operator_comm_proj (H : AddSubgroup S.Gam) {h : S.Gam} (hh : h ∈ H) (c : S.perp H →+ ZMod S.N) :
    S.ρ h * S.proj (S.perp H) c = S.proj (S.perp H) c * S.ρ h := by
  have := Fintype.ofFinite (S.perp H)
  rw [ThetaSys.proj, finsum_eq_sum_of_fintype, mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  have h1 : eStd S.g _ (t : S.Gam) h = 0 := t.2 h hh
  rw [mul_smul_comm, smul_mul_assoc, S.ρ_add _ _ (by rw [Weights.eStd_swap, h1, neg_zero, smul_zero]),
    S.ρ_add _ _ (by rw [h1, smul_zero]), add_comm]

variable {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (τ : S.Test p y₀)

theorem single_mem_testLattice [hA : ArithBase o Ω] (i : S.J) : Pi.single i (1 : PadicAlgCl p) ∈ τ.E := by
  have : IsDomain o := hA.inj.isDomain
  have := finite_char S (S.perp τ.yy.ker)
  have := Fintype.ofFinite (S.perp τ.yy.ker →+ ZMod S.N)
  obtain ⟨-, hsum⟩ := proj_orthogonal S _ τ.isoFree
  have h1 : Pi.single i (1 : PadicAlgCl p) = ∑ c : S.perp τ.yy.ker →+ ZMod S.N,
      fun j => 1 * y₀ (algebraMap o S.R (S.proj _ c j i)) := by
    funext j
    rw [Finset.sum_apply]
    simp only [_root_.one_mul]
    rw [← map_sum, ← map_sum, ← Matrix.sum_apply, hsum, Matrix.one_apply, Pi.single_apply]
    split_ifs <;> simp
  rw [h1]
  refine Submodule.sum_mem _ fun c _ => Submodule.subset_span ?_
  obtain ⟨α, hα, rfl⟩ := (test_weights o Ω S p y₀ τ).1 c
  refine ⟨α, 1, i, hα, ?_, rfl⟩
  rw [norm_one]
  exact Real.one_le_exp (div_nonneg (quadratic_nonneg τ.q τ.pos α) (Nat.cast_nonneg _))

theorem operator_mem_testLattice (hint : ∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) {h : S.Gam} (hh : h ∈ τ.yy.ker)
    {w : S.J → PadicAlgCl p} (hw : w ∈ τ.E) :
    (fun j => ∑ k, y₀ (algebraMap o S.R (S.ρ h j k)) * w k) ∈ τ.E := by
  induction hw using Submodule.span_induction with
  | mem _ h' =>
    obtain ⟨α, l, i, hα, hl, rfl⟩ := h'
    have h1 : (fun j => ∑ k, y₀ (algebraMap o S.R (S.ρ h j k)) *
        (l * y₀ (algebraMap o S.R (S.proj _ (τ.wt α) k i)))) =
        ∑ k, (⟨_, (mem_OO_iff _).2 (hint (S.ρ h k i))⟩ : OO p) •
          fun j => l * y₀ (algebraMap o S.R (S.proj _ (τ.wt α) j k)) := by
      funext j
      have h2 := congrArg (fun a => l * y₀ (algebraMap o S.R a))
        (congrFun (congrFun (operator_comm_proj _ hh (τ.wt α)) j) i)
      simp only [Matrix.mul_apply, map_sum, map_mul, Finset.mul_sum] at h2
      rw [Finset.sum_apply]
      refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) (h2.trans (Finset.sum_congr rfl fun k _ => ?_))
      · ring
      · change _ = y₀ (algebraMap o S.R (S.ρ h k i)) * (l * y₀ (algebraMap o S.R (S.proj _ (τ.wt α) j k)))
        ring
    rw [h1]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨α, l, k, hα, hl, rfl⟩)
  | zero =>
    convert Submodule.zero_mem τ.E using 1
    funext j
    simp
  | add a a' _ _ ha ha' =>
    convert Submodule.add_mem _ ha ha' using 1
    funext j
    simp [mul_add, Finset.sum_add_distrib]
  | smul s a _ ha =>
    convert Submodule.smul_mem _ s ha using 1
    funext j
    change ∑ k, _ * ((s : PadicAlgCl p) * a k) = (s : PadicAlgCl p) * ∑ k, _ * a k
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring

theorem weightZero_mem [hA : ArithBase o Ω] (hint : ∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1)
    {w : S.J → PadicAlgCl p} (hw : w ∈ τ.E) (j : S.J) :
    ∑ k, w k * y₀ (algebraMap o S.R (S.proj (S.perp τ.yy.ker) 0 j k)) ∈ OO p := by
  have : IsDomain o := hA.inj.isDomain
  have := finite_char S (S.perp τ.yy.ker)
  have := Fintype.ofFinite (S.perp τ.yy.ker →+ ZMod S.N)
  obtain ⟨hmul, -⟩ := proj_orthogonal S _ τ.isoFree
  refine sum_mul_mem_of_mem_span (OO p) _ ?_ hw
  rintro _ ⟨α, l, i, hα, hl, rfl⟩
  have h2 := congrArg (fun a => l * y₀ (algebraMap o S.R a)) (congrFun (congrFun (hmul 0 (τ.wt α)) j) i)
  simp only [Matrix.mul_apply, map_sum, map_mul, Finset.mul_sum] at h2
  rw [(Finset.sum_congr rfl fun k _ => by ring).trans h2]
  split_ifs with h0
  · have h3 := q_le_of_wt_eq τ (β := 0) hα (by rw [map_zero, h0])
    rw [map_zero] at h3
    refine mul_mem ((mem_OO_iff _).2 (hl.trans ?_)) ((mem_OO_iff _).2 (hint _))
    exact Real.exp_le_one_iff.2 (div_nonpos_of_nonpos_of_nonneg h3 (Nat.cast_nonneg _))
  · simp

variable {M : RatModel o Ω} {U₀ : M.Z.Opens}

theorem exists_opens_regular (hne : (U₀ : Set M.Z).Nonempty) {J : Type} [Finite J] (v : J → Ω) :
    ∃ U₁ : M.Z.Opens, U₁ ≤ U₀ ∧ (U₁ : Set M.Z).Nonempty ∧ ∀ j, v j ∈ M.ringOn U₁ := by
  let W : M.Z.Opens := ⟨⋂ j, {z | v j ∈ M.O z}, isOpen_iInter_of_finite fun j => M.isOpen_setOf_mem_O _⟩
  refine ⟨U₀ ⊓ W, inf_le_left, M.nonempty_inf hne ⟨genericPoint M.Z, Set.mem_iInter.2 fun j => ?_⟩,
    fun j => RatModel.mem_ringOn.2 fun z hz => Set.mem_iInter.1 hz.2 j⟩
  rw [Set.mem_setOf_eq, M.O_genericPoint]
  exact Algebra.mem_top

theorem over_mono (hO : S.Over₀ M U₀) {U₁ : M.Z.Opens} (hle : U₁ ≤ U₀) (hne : (U₁ : Set M.Z).Nonempty) :
    S.Over₀ M U₁ :=
  ⟨hO.normal, hO.proj, hO.div, hne, hO.le.trans (RatModel.ringOn_anti hle),
    fun x hx => RatModel.ringOn_anti hle (hO.th_unit x hx),
    fun T c k hT hk => RatModel.ringOn_anti hle (hO.FF_unit T c k hT hk)⟩

theorem val_mulVec {U₁ : Set M.Z} {z : M.Z} {y : Sp (OO p) ⟶ M.Z} (hc : M.Cen U₁ z y) (hat : S.At M y y₀)
    (A : Matrix S.J S.J o) {v : S.J → Ω} (hv : ∀ j, v j ∈ M.ringOn U₁) (j : S.J) :
    M.val (gPt p ≫ y) ((A.map (algebraMap o Ω)).mulVec v j) =
      ∑ k, M.val (gPt p ≫ y) (v k) * y₀ (algebraMap o S.R (A j k)) := by
  obtain ⟨ξ, hξU, hsp⟩ : ∃ ξ ∈ U₁, ∀ w, (gPt p ≫ y) w ⤳ ξ :=
    ⟨(gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p)), hc.2 ⟨_, rfl⟩,
      RatModel.specializes_of_range_eq (RatModel.range_eq_singleton _ _)⟩
  rw [← Matrix.vecMul_transpose, RatModel.val_vecMul_eq_sum (c := (A.map (algebraMap o Ω)).transpose) hsp
    (fun j => RatModel.mem_ringOn.1 (hv j) _ hξU) (fun _ _ => Subalgebra.algebraMap_mem _ _)]
  exact Finset.sum_congr rfl fun k _ => by rw [hat]; rfl

theorem norm_base_le_one {U₁ : Set M.Z} {z : M.Z} {y : Sp (OO p) ⟶ M.Z} (hc : M.Cen U₁ z y) (hat : S.At M y y₀)
    (a : o) : ‖y₀ (algebraMap o S.R a)‖ ≤ 1 := by
  rw [hat]
  exact hc.norm_val_le_one (Subalgebra.algebraMap_mem _ a)

end GlobalTheory.ZH.LatticeStable

namespace GlobalTheory.ZH

open LatticeStable in

theorem EE_contains_stable_weightZero :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.Over₀ M U₀ → ((∀ U₁ : M.Z.Opens, U₁ ≤ U₀ → (U₁ : Set M.Z).Nonempty → ∀ z : M.Z, IsClosed ({z} : Set M.Z) → (∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y) ∧ ∀ φ ∈ M.ringOn U₁, (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y → ‖M.val (gPt p ≫ y) φ‖ ≤ 1) → φ ∈ M.O z) ∧ JacobsonSpace M.Z) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ z y → ∃ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ ∧ (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) ∧ Nonempty (S.Test p y₀)) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → (∀ x, x ∈ S.supI M z ↔ ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ) ∧ S.HH M z = τ.yy.ker) → ((∀ ξ : M.Z, S.IsoFree (S.TT M ξ) ∧ S.perp (S.TT M ξ) = S.HH M ξ) ∧ (∀ ξ z : M.Z, ξ ⤳ z → S.supI M z ⊆ S.supI M ξ) ∧ (∀ ξ ∈ U₀, S.TT M ξ = ⊥) ∧ (∀ (ξ : M.Z) (W : M.Z.Opens), ξ ∈ W → ∃ x ∈ W, IsClosed ({x} : Set M.Z) ∧ ξ ⤳ x ∧ S.supI M x = S.supI M ξ)) → S.IsEE M U₀ EE → ∀ ξ : M.Z, (∀ i, Pi.single i (1 : Ω) ∈ EE.E ξ) ∧ (∀ h ∈ S.HH M ξ, ∀ v ∈ EE.E ξ, ((S.ρ h).map (algebraMap o Ω)).mulVec v ∈ EE.E ξ) ∧ (IsClosed ({ξ} : Set M.Z) → ∀ v ∈ EE.E ξ, ((S.proj (S.TT M ξ) 0).map (algebraMap o Ω)).mulVec v = v → ∀ j, v j ∈ M.O ξ) := by
  intro o Ω _ _ _ _ S M U₀ EE hO hloc htest hsup hT hEE
  have hmem : ∀ U₁ : M.Z.Opens, U₁ ≤ U₀ → (U₁ : Set M.Z).Nonempty → _ := fun U₁ hle hne =>
    mem_EE_iff_forall_test o Ω S M U₁ EE (over_mono hO hle hne)
      ⟨fun U hU => hloc.1 U (hU.trans hle), hloc.2⟩
      (fun z p _ y hc => htest z p y ⟨hc.1, hc.2.trans hle⟩)
      ⟨fun z hz => hEE.1 z (hle hz), fun z p _ y y₀ τ hc => hEE.2 z p y y₀ τ ⟨hc.1, hc.2.trans hle⟩⟩
  have h1 : ∀ z : M.Z, IsClosed ({z} : Set M.Z) → ∀ i, Pi.single i (1 : Ω) ∈ EE.E z := by
    intro z hz i
    refine (hmem U₀ le_rfl hO.ne z hz _ fun j => ?_).2 fun p _ y y₀ τ hc hat => ?_
    · rw [Pi.single_apply]
      split_ifs
      exacts [one_mem _, zero_mem _]
    · convert single_mem_testLattice τ i using 1
      funext j
      simp only [Pi.single_apply]
      split_ifs
      exacts [RatModel.val_one _, RatModel.val_zero _]
  have h2 : ∀ z : M.Z, IsClosed ({z} : Set M.Z) → ∀ h ∈ S.HH M z, ∀ v ∈ EE.E z,
      ((S.ρ h).map (algebraMap o Ω)).mulVec v ∈ EE.E z := by
    intro z hz h hh v hv
    obtain ⟨U₁, hle, hne, hreg⟩ := exists_opens_regular hO.ne v
    refine (hmem U₁ hle hne z hz _ fun j => ?_).2 fun p _ y y₀ τ hc hat => ?_
    · exact sum_mem fun k _ => mul_mem (Subalgebra.algebraMap_mem _ _) (hreg k)
    · have h3 := (hmem U₁ hle hne z hz v hreg).1 hv p y y₀ τ hc hat
      rw [(hsup z p y y₀ τ ⟨hc.1, hc.2.trans hle⟩ hat).2] at hh
      convert operator_mem_testLattice τ (norm_base_le_one hc hat) hh h3 using 1
      funext j
      rw [val_mulVec hc hat _ hreg]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  intro ξ
  obtain ⟨W, b, hξ, -, hE⟩ := EE.loc ξ
  obtain ⟨x, hxW, hx, hsp, hI⟩ := hT.2.2.2 ξ W hξ
  have hle : ∀ v ∈ EE.E x, v ∈ EE.E ξ := fun v hv => by
    rw [hE x hxW] at hv
    rw [hE ξ hξ]
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (v := fun i => b i) _).1 hv
    exact (Submodule.mem_span_range_iff_exists_fun (v := fun i => b i) _).2
      ⟨fun i => ⟨c i, RatModel.O_le_of_specializes hsp (c i).2⟩, rfl⟩
  refine ⟨fun i => hle _ (h1 x hx i), fun h hh v hv => ?_, fun hz v hv hP j => ?_⟩
  · have hh' : h ∈ S.HH M x := by rwa [ThetaSys.HH, hI]
    rw [hE ξ hξ] at hv
    induction hv using Submodule.span_induction with
    | mem w hw => exact hle _ (h2 x hx h hh' w (by rw [hE x hxW]; exact Submodule.subset_span hw))
    | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
    | add a a' _ _ ha ha' => rw [Matrix.mulVec_add]; exact add_mem ha ha'
    | smul s a _ ha => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ s ha
  · obtain ⟨U₁, hle₁, hne, hreg⟩ := exists_opens_regular hO.ne v
    refine (hloc.1 U₁ hle₁ hne ξ hz).2 _ (hreg j) fun p _ y hc => ?_
    have hc₀ : M.Cen U₀ ξ y := ⟨hc.1, hc.2.trans hle₁⟩
    obtain ⟨y₀, hat, hint, ⟨τ⟩⟩ := htest ξ p y hc₀
    have h3 := (hmem U₁ hle₁ hne ξ hz v hreg).1 hv p y y₀ τ hc hat
    rw [ThetaSys.TT, (hsup ξ p y y₀ τ hc₀ hat).2] at hP
    rw [← hP, val_mulVec hc hat _ hreg, ← mem_OO_iff]
    exact weightZero_mem τ hint h3 j

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAdmissibleAffineModelDividingTuple
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

theorem finite_over_subfield_of_le {Ω : Type} [Field Ω] {K L : Subfield Ω} (h : K ≤ L)
    (hK : Module.Finite K Ω) : Module.Finite L Ω := by
  letI : Algebra K L := (Subfield.inclusion h).toAlgebra
  haveI : IsScalarTower K L Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Module.Finite.of_restrictScalars_finite K L Ω

theorem exists_normal_proj_hasDiv_family (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω]
    (J : Type) [Fintype J] (t : J → Ω) (ht : ∃ i, t i ≠ 0)
    (hfin : Module.Finite
      (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j, x = t j / t i})) Ω)
    (B : Type) [Finite B] (JJ : B → Type) [∀ b, Finite (JJ b)] (tt : ∀ b, JJ b → Ω)
    (htt : ∀ b, ∃ k, tt b k ≠ 0) :
    ∃ M : RatModel o Ω, IsNormalScheme M.Z ∧ IsProjOver M.s ∧ M.HasDiv t ∧ ∀ b, M.HasDiv (tt b) := by
  haveI := ArithBase.ded (o := o) (Ω := Ω)
  haveI := ArithBase.char (o := o) (Ω := Ω)
  letI : Fintype B := Fintype.ofFinite B
  letI : Fintype (∀ b, JJ b) := Fintype.ofFinite _
  choose q₀ hq₀ using htt
  have hP : (∏ b, tt b (q₀ b)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun b _ => hq₀ b
  obtain ⟨i₀, hi₀⟩ := ht
  obtain ⟨M, hM, hp⟩ := GlobalTheory.ZH.exists_isNm_isProjOver o Ω (ArithBase.inj (o := o) (Ω := Ω))
    (J × ∀ b, JJ b) (fun q => t q.1 * ∏ b, tt b (q.2 b)) ⟨(i₀, q₀), mul_ne_zero hi₀ hP⟩
    (finite_over_subfield_of_le (Subfield.closure_mono (Set.union_subset_union_right _ (by
      rintro _ ⟨i, j, rfl⟩
      exact ⟨(i, q₀), (j, q₀), (mul_div_mul_right _ _ hP).symm⟩))) hfin)
  have h := GlobalTheory.ZH.isNm_normal_and_div_prod o Ω M J t
  have h2 : M.HasDiv t ∧ M.HasDiv (fun q : ∀ b, JJ b => ∏ b, tt b (q b)) := by
    refine ⟨fun z => ?_, fun z => ?_⟩
    · obtain ⟨⟨i, q⟩, hi⟩ := hM.1 z
      exact ⟨i, ((h.2.1 _ (fun q : ∀ b, JJ b => ∏ b, tt b (q b)) i q z).1 hi).1⟩
    · obtain ⟨⟨i, q⟩, hi⟩ := hM.1 z
      exact ⟨q, ((h.2.1 _ (fun q : ∀ b, JJ b => ∏ b, tt b (q b)) i q z).1 hi).2⟩
  exact ⟨M, (GlobalTheory.ZH.isNm_normal_and_div_prod o Ω M _ _).1 hM, hp, h2.1, (h.2.2 B JJ tt).1 h2.2⟩

theorem exists_admissible_affine_model_dividing_tuple : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (J₀ : Type) [Fintype J₀] (t₀ : J₀ → Ω), (∃ i, t₀ i ≠ 0) → Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j : S.Gam × J₀, x = S.th j.1 * t₀ j.2 / (S.th i.1 * t₀ i.2)})) Ω → ∃ (M : RatModel o Ω) (U₀ : M.Z.Opens), S.admitted M U₀ ∧ IsAffineOpen U₀ ∧ M.HasDiv t₀ := by
  intro o Ω _ _ _ _ S J₀ _ t₀ ht₀ hfin
  have hN : S.N ≠ 0 := by have := S.N_ge; omega
  have hr : S.r ≠ 0 := by have := S.r_pos; omega
  haveI : NeZero S.N := ⟨hN⟩
  haveI : NeZero (S.r * S.N) := ⟨mul_ne_zero hr hN⟩
  haveI : NeZero ((S.r * S.N) ^ 2) := ⟨pow_ne_zero _ (mul_ne_zero hr hN)⟩
  haveI : Finite (AddSubgroup S.Gam) := Finite.of_injective _ SetLike.coe_injective
  haveI : ∀ T : AddSubgroup S.Gam, Finite (T →+ ZMod S.N) := fun T =>
    Finite.of_injective _ DFunLike.coe_injective
  obtain ⟨x₀, hx₀⟩ := S.th_ne
  obtain ⟨i₀, hi₀⟩ := ht₀
  obtain ⟨M, hn, hp, hd, hF⟩ := exists_normal_proj_hasDiv_family o Ω (S.Gam × J₀)
    (fun q => S.th q.1 * t₀ q.2) ⟨(x₀, i₀), mul_ne_zero hx₀ hi₀⟩ hfin
    {b : Σ T : AddSubgroup S.Gam, T →+ ZMod S.N // S.FF b.1 b.2 ≠ 0}
    (fun b => S.J × (b.1.1 → ZMod ((S.r * S.N) ^ 2))) (fun b => S.FF b.1.1 b.1.2)
    (fun b => Function.ne_iff.1 b.2)
  have h := GlobalTheory.ZH.isNm_normal_and_div_prod o Ω M _ S.th
  have hth : M.HasDiv S.th := fun z => by
    obtain ⟨⟨x, i⟩, hi⟩ := hd z
    exact ⟨x, ((h.2.1 _ t₀ x i z).1 hi).1⟩
  have ht : M.HasDiv t₀ := fun z => by
    obtain ⟨⟨x, i⟩, hi⟩ := hd z
    exact ⟨i, ((h.2.1 _ t₀ x i z).1 hi).2⟩
  have hA : ((fun x : Ω => x⁻¹) '' (Set.range S.th ∪ {x : Ω | ∃ T c k, x = S.FF T c k})).Finite :=
    ((Set.finite_range _).union (GlobalTheory.thetaSys_FF_mem_finite_perp_proj o Ω S).2.1).image _
  obtain ⟨U₀, a, -, hne, haff, -, -, hR, hsub⟩ := GlobalTheory.ZH.exists_affineOpen_ringOn_eq_adjoin_inv o Ω M S.R _
    S.fg S.frac hA ⊤ ⟨genericPoint M.Z, trivial⟩
  refine ⟨M, U₀, ⟨⟨hn, hp, hth, hne, fun x hx => ?_, fun x _ => hsub ⟨_, Or.inl ⟨x, rfl⟩, rfl⟩,
    fun T c k _ _ => hsub ⟨_, Or.inr ⟨T, c, k, rfl⟩, rfl⟩⟩, fun T c _ h0 => hF ⟨⟨T, c⟩, h0⟩⟩, haff, ht⟩
  rw [hR]
  exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ hx)

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsComparisonCompAlongIdentityStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_comparison_comp_along_identity : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (I : Ideal R) (I' : Ideal V) (φ : R →+* V) (D : DegPre R) (D₁ D' : DegPre V) (A : PolAV (Sp (FractionRing R))) (A₁ A' : PolAV (Sp (FractionRing V))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of V))) [GrpObj G'] [IsCommMonObj G'] (U : PreU I D A G) (U₁ : PreU I' D₁ A₁ G') (U' : PreU I' D' A' G') (F : G'.left ⟶ G.left) (C₁ : Cmp φ U U₁ F) (C₂ : Cmp (RingHom.id V) U₁ U' (𝟙 G'.left)) (wL : LB.Iso U'.P.L.L (U.P.L.L.pull F)), IsCPMap U'.P U.P (spMap φ) F C₁.pb.1.w wL → (∀ (Z : Scheme.{0}) (r : Z ⟶ G'.left) (z : Z) (j : U.P.L.L.ι) (i : U₁.P.L.L.ι) (k : U'.P.L.L.ι), F (r z) ∈ U.P.L.L.U j → r z ∈ U₁.P.L.L.U i → r z ∈ U'.P.L.L.U k → gw wL r z j k = gw C₁.wL r z j i * gw C₂.wL r z i k) → ∃ C : Cmp φ U U' F, C.wL = wL := by
  first | exact @GlobalTheory.LN.Cmp.exists_comp_id | exact GlobalTheory.LN.Cmp.exists_comp_id | (intros; apply GlobalTheory.LN.Cmp.exists_comp_id <;> assumption)
end

