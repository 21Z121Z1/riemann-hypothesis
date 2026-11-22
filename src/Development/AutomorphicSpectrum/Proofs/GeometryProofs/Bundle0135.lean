import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0003
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0001
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0125
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0061
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0027
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0067
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0038
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0129
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0114
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0121
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPeriodAtRestrict
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSymplecticCoordinatesOfIsPeriod
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0130

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.KillsOverOfAdicCompletion
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.KillsAdic

theorem ext_of_quotients {A : Type} [CommRing A] {Y Z : Scheme.{0}} {f g : Sp A ⟶ Y} (s : Y ⟶ Z) [IsSeparated s]
    (h : f ≫ s = g ≫ s) {N : Type} (I : N → Ideal A) (hI : ∀ x : A, (∀ n, x ∈ I n) → x = 0)
    (hU : ∀ n, spMap (Ideal.Quotient.mk (I n)) ≫ f = spMap (Ideal.Quotient.mk (I n)) ≫ g) : f = g :=
  _root_.UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.main s h I hI hU

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]

theorem charVal_comp {A A' : Type} [CommRing A] [CommRing A'] {a : Sp A ⟶ S} {a' : Sp A' ⟶ S} (h : A →+* A')
    (e : spMap h ≫ a = a') (t : Over.mk a ⟶ splitTorus S X) (χ : X) :
    charVal ((Over.homMk (spMap h) e : Over.mk a' ⟶ Over.mk a) ≫ t) χ = h (charVal t χ) := by
  subst e
  exact (GlobalTheory.T.charVal_multiplicative S X A a).2.2.2.2.2 A' h t _ (by simp) χ

theorem exists_factor {M : Type} [CommMonoid M] (Y : AddSubgroup X) (f : X → M) (h0 : f 0 = 1)
    (hadd : ∀ x y, f (x + y) = f x * f y) (hY : ∀ y ∈ Y, f y = 1) :
    ∃ v : Multiplicative (X ⧸ Y) →* M, ∀ χ : X, v (Multiplicative.ofAdd (χ : X ⧸ Y)) = f χ := by
  have key : ∀ x x' : X, (x : X ⧸ Y) = x' → f x = f x' := by
    intro x x' e
    have hm : -x + x' ∈ Y := QuotientAddGroup.eq.1 e
    have : x' = x + (-x + x') := by abel
    rw [this, hadd, hY _ hm, _root_.mul_one]
  refine ⟨{ toFun := fun q => f (Quotient.out (Multiplicative.toAdd q))
            map_one' := ?_
            map_mul' := ?_ }, fun χ => ?_⟩
  · rw [← h0]
    exact key _ _ (by simp)
  · intro p q
    rw [← hadd]
    exact key _ _ (by simp)
  · exact key _ _ (by simp)

theorem comp_one_over {T T' M : Over S} [GrpObj M] (f : T' ⟶ T) : f ≫ (1 : T ⟶ M) = 1 := by
  rw [Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (f ≫ toUnit T) (toUnit T')]

theorem universal_one {G : Over S} [GrpObj G] [IsSeparated G.hom] (u : splitTorus S X ⟶ G) (Y : AddSubgroup X)
    {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (b : Sp R ⟶ S)
    (hk : ∀ n : ℕ, KillsOver u Y (spMap (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1))) ≫ b))
    (t₀ : Over.mk (spMap (algebraMap R (AddMonoidAlgebra R (X ⧸ Y))) ≫ b) ⟶ splitTorus S X)
    (ht₀ : ∀ χ : X, charVal t₀ χ = AddMonoidAlgebra.single (χ : X ⧸ Y) 1) : t₀ ≫ u = 1 := by
  let c := algebraMap R (AddMonoidAlgebra R (X ⧸ Y))
  let I : ℕ → Ideal (AddMonoidAlgebra R (X ⧸ Y)) := fun n =>
    Ideal.map c (IsLocalRing.maximalIdeal R ^ (n + 1))
  have hI : ∀ x, (∀ n, x ∈ I n) → x = 0 := fun x hx =>
    GlobalTheory.CompanionTheory.KrullGroupAlg.eq_zero_of_mem_map_pow R (X ⧸ Y) x fun n =>
      Ideal.map_mono (Ideal.pow_le_pow_right (Nat.le_succ n)) (hx n)
  refine Over.OverMorphism.ext (ext_of_quotients G.hom ?_ I hI fun n => ?_)
  · rw [Over.w, Over.w]
  · let J := IsLocalRing.maximalIdeal R ^ (n + 1)
    let gn : R ⧸ J →+* AddMonoidAlgebra R (X ⧸ Y) ⧸ I n :=
      Ideal.quotientMap (I n) c Ideal.le_comap_map
    have e : spMap (Ideal.Quotient.mk (I n)) ≫ spMap c ≫ b = spMap gn ≫ spMap (Ideal.Quotient.mk J) ≫ b := by
      rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
      rfl
    let m : Over.mk (spMap gn ≫ spMap (Ideal.Quotient.mk J) ≫ b) ⟶ Over.mk (spMap c ≫ b) :=
      Over.homMk (spMap (Ideal.Quotient.mk (I n))) e
    have hone := hk n _ gn (m ≫ t₀) (fun y hy => by
      rw [charVal_comp, ht₀, (QuotientAddGroup.eq_zero_iff y).2 hy]
      exact map_one _)
    have h4 : m ≫ (t₀ ≫ u) = m ≫ (1 : Over.mk (spMap c ≫ b) ⟶ G) := by
      exact (Category.assoc m t₀ u).symm.trans (hone.trans (comp_one_over m).symm)
    exact congrArg (fun w => w.left) h4

theorem killsOver_of_forall_pow : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsSeparated G.hom] (X : Type) [AddCommGroup X] (u : splitTorus S X ⟶ G) (Y : AddSubgroup X) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (b : Sp R ⟶ S), (∀ n : ℕ, KillsOver u Y (spMap (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1))) ≫ b)) → KillsOver u Y b := by
  intro S G _ _ X _ u Y R _ _ _ b hk A _ g t ht
  let c := algebraMap R (AddMonoidAlgebra R (X ⧸ Y))
  let w₀ : Multiplicative X →* AddMonoidAlgebra R (X ⧸ Y) :=
    (AddMonoidAlgebra.of R (X ⧸ Y)).comp (AddMonoidHom.toMultiplicative (QuotientAddGroup.mk' Y))
  obtain ⟨t₀, ht₀⟩ := (GlobalTheory.T.charVal_multiplicative S X _ (spMap c ≫ b)).2.2.2.2.1 w₀
  have ht₀' : ∀ χ : X, charVal t₀ χ = AddMonoidAlgebra.single (χ : X ⧸ Y) 1 := fun χ => ht₀ χ
  have hone := universal_one u Y b hk t₀ ht₀'
  have hpts := (GlobalTheory.T.charVal_multiplicative S X A (spMap g ≫ b))
  obtain ⟨v, hv⟩ := exists_factor Y (charVal t) (hpts.2.2.2.1 t).1 (hpts.2.2.2.1 t).2 ht
  let h : AddMonoidAlgebra R (X ⧸ Y) →+* A :=
    AddMonoidAlgebra.liftNCRingHom g v (fun _ _ => Commute.all _ _)
  have hc : h.comp c = g := by
    ext r
    simp [h, c]
  have e : spMap h ≫ spMap c ≫ b = spMap g ≫ b := by
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hc]
  let m : Over.mk (spMap g ≫ b) ⟶ Over.mk (spMap c ≫ b) := Over.homMk (spMap h) e
  have htm : t = m ≫ t₀ := hpts.1 _ _ fun χ => by
    rw [charVal_comp, ht₀']
    simp [h, AddMonoidAlgebra.liftNCRingHom_single, hv]
  rw [htm, Category.assoc, hone, comp_one_over]

end GlobalTheory.CompanionTheory.Ar.KillsAdic
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeIntersectionFrameSubspace
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.LocalFrames

theorem span_eq_of_saturated : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (V' : Submodule Ω E) (p : Cpt ξ) (g : ℕ) (b : Fin g → E) (S : Finset (Fin g)), IsCptGen ξ → Submodule.span Ω (Set.range b) = ⊤ → L p = Submodule.span (regAt ξ p) (Set.range b) → (L.inter V') p = Submodule.span (regAt ξ p) (b '' S) → V' = Submodule.span Ω (b '' S) := by
  intro X Ω _ ξ E _ _ L V' p g b S h hspan hL hI
  haveI hfr : IsFractionRing (regAt ξ p) Ω := (RegAtRing.regAt_ring X Ω ξ h p).1
  have sm : ∀ (c : regAt ξ p) {m : E}, m ∈ L p → (c : Ω) • m ∈ L p := fun c _ hm => (L p).smul_mem c hm
  have key : ∀ x : E, ∃ d : regAt ξ p, (d : Ω) ≠ 0 ∧ (d : Ω) • x ∈ L p := by
    intro x
    have hx : x ∈ Submodule.span Ω (Set.range b) := hspan ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy =>
      refine ⟨1, by simp, ?_⟩
      rw [hL]
      simpa using Submodule.subset_span hy
    | zero => exact ⟨1, by simp, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨d, hd, hdy⟩ := hy
      obtain ⟨e, he, hez⟩ := hz
      refine ⟨d * e, by rw [Subring.coe_mul]; exact mul_ne_zero hd he, ?_⟩
      have : ((d * e : regAt ξ p) : Ω) • (y + z) = (e : Ω) • ((d : Ω) • y) + (d : Ω) • ((e : Ω) • z) := by
        simp only [Subring.coe_mul, smul_add, smul_smul, mul_comm]
      rw [this]
      exact (L p).add_mem (sm e hdy) (sm d hez)
    | smul a y _ hy =>
      obtain ⟨d, hd, hdy⟩ := hy
      obtain ⟨u, v, hv, rfl⟩ := IsFractionRing.div_surjective (A := regAt ξ p) a
      have hv0 : (v : Ω) ≠ 0 := by
        have := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (K := Ω) hv
        simpa using this
      refine ⟨v * d, by rw [Subring.coe_mul]; exact mul_ne_zero hv0 hd, ?_⟩
      have : ((v * d : regAt ξ p) : Ω) • ((algebraMap (regAt ξ p) Ω u / algebraMap (regAt ξ p) Ω v) • y) =
          (u : Ω) • ((d : Ω) • y) := by
        have hu : algebraMap (regAt ξ p) Ω u = (u : Ω) := rfl
        have hv' : algebraMap (regAt ξ p) Ω v = (v : Ω) := rfl
        rw [hu, hv', smul_smul, smul_smul, Subring.coe_mul]
        congr 1
        field_simp
      rw [this]
      exact sm u hdy
  apply le_antisymm
  · intro x hx
    obtain ⟨d, hd, hdx⟩ := key x
    have h1 : (d : Ω) • x ∈ (L.inter V') p := ⟨hdx, V'.smul_mem _ hx⟩
    rw [hI] at h1
    have h2 : (d : Ω) • x ∈ Submodule.span Ω (b '' S) :=
      Submodule.span_subset_span (regAt ξ p) Ω (b '' S) h1
    exact (Submodule.smul_mem_iff _ hd).1 h2
  · rw [Submodule.span_le]
    intro y hy
    have h1 : y ∈ (L.inter V') p := by
      rw [hI]
      exact Submodule.subset_span hy
    exact h1.2

end GlobalTheory.CompanionTheory.Ar.LocalFrames
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelComplexLinearComparison
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FrameFibre

section Push

variable {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
  {φ : G'.left ⟶ G.left}

def push (hφ : IsGrpPullback G' G f φ) {T : Over S'} (x : T ⟶ G') : Over.mk (T.hom ≫ f) ⟶ G :=
  Over.homMk (x.left ≫ φ) (by
    have h1 := hφ.1.w
    have h2 := Over.w x
    simp only [Over.mk_hom, Category.assoc, Functor.id_obj, Functor.const_obj_obj, Over.mk_left]
    rw [h1, ← Category.assoc, h2])

theorem push_mul (hφ : IsGrpPullback G' G f φ) {T : Over S'} (x y : T ⟶ G') :
    push hφ (x * y) = push hφ x * push hφ y := by
  apply Over.OverMorphism.ext
  exact (hφ.2 T x y (push hφ x) (push hφ y) rfl rfl).symm

theorem push_one (hφ : IsGrpPullback G' G f φ) (T : Over S') :
    push hφ (1 : T ⟶ G') = 1 := by
  have h := push_mul hφ (1 : T ⟶ G') 1
  rw [_root_.mul_one] at h
  exact left_eq_mul.mp h

end Push

theorem spec_fst_dualMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom B B B).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (dualMap f)) =
      Spec.map (CommRingCat.ofHom f) ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom A A A).toRingHom) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
  simp [dualMap]

theorem spec_alg_dualMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    Spec.map (CommRingCat.ofHom (dualMap f)) ≫ Spec.map (CommRingCat.ofHom (algebraMap A (DualNumber A))) =
      Spec.map (CommRingCat.ofHom (algebraMap B (DualNumber B))) ≫ Spec.map (CommRingCat.ofHom f) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
  ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem spec_epsMul_dualMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (c : A) :
    Spec.map (CommRingCat.ofHom (epsMul (f c))) ≫ Spec.map (CommRingCat.ofHom (dualMap f)) =
      Spec.map (CommRingCat.ofHom (dualMap f)) ≫ Spec.map (CommRingCat.ofHom (epsMul c)) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
  ext <;> simp [dualMap, epsMul, mul_comm]

theorem exists_linear_of_pullback {X : Scheme.{0}} {R : Type} [CommRing R] {G' : Over (Sp R)} [GrpObj G']
    {G : Over X} [GrpObj G] {h : Sp R ⟶ X} {φ : G'.left ⟶ G.left} (hφ : IsGrpPullback G' G h φ) {g : ℕ}
    (M : LieModel G' (𝟙 (Sp R)) (Fin g → R)) (ψ : R →+* ℂ) {Vz : Type} [AddCommGroup Vz] [Module ℂ Vz]
    (MR : LieModel G (spMap ψ ≫ h) Vz) :
    ∃ Θ : (Fin g → ℂ) →ₗ[ℂ] Vz, ∀ x : Fin g → R,
      (MR.pt (Θ (fun e => ψ (x e)))).left = spMap (dualMap ψ) ≫ (M.pt x).left ≫ φ := by
  let c : epsAt (spMap ψ ≫ h) ⟶ Over.mk ((epsAt (𝟙 (Sp R))).hom ≫ h) :=
    Over.homMk (spMap (dualMap ψ)) (by
      have key := spec_alg_dualMap ψ
      simp only [Over.mk_hom, Category.comp_id]
      rw [← Category.assoc, key, Category.assoc])
  let w : (Fin g → R) → (epsAt (spMap ψ ≫ h) ⟶ G) := fun x => c ≫ push hφ (M.pt x)
  have wl : ∀ x, (w x).left = spMap (dualMap ψ) ≫ (M.pt x).left ≫ φ := fun _ => rfl
  have wt : ∀ x, IsTanAt G (spMap ψ ≫ h) (w x) := by
    intro x
    let c0 : Over.mk (spMap ψ ≫ h) ⟶ Over.mk ((Over.mk (𝟙 (Sp R))).hom ≫ h) :=
      Over.homMk (spMap ψ) (by simp)
    have h0 : c0 ≫ push hφ (1 : Over.mk (𝟙 (Sp R)) ⟶ G') = 1 := by
      rw [push_one]; exact MonObj.comp_one c0
    have h1 : spMap ψ ≫ (1 : Over.mk (𝟙 (Sp R)) ⟶ G').left ≫ φ = (1 : Over.mk (spMap ψ ≫ h) ⟶ G).left :=
      congrArg CommaMorphism.left h0
    have h2 := M.tan x
    unfold IsTanAt at h2 ⊢
    rw [wl, ← h1, ← h2, ← Category.assoc, spec_fst_dualMap ψ]
    simp only [Category.assoc]
  choose j hj using fun x => MR.onto (w x) (wt x)
  have jadd : ∀ x y, j (x + y) = j x + j y := by
    intro x y
    apply MR.inj
    rw [MR.add, hj, hj, hj]
    simp only [w, M.add, push_mul, MonObj.comp_mul]
  have jsmul : ∀ (a : R) x, j (a • x) = ψ a • j x := by
    intro a x
    apply MR.inj
    apply Over.OverMorphism.ext
    rw [MR.smul, hj, hj, wl, wl, M.smul, ← Category.assoc (Spec.map _) (spMap (dualMap ψ)),
      spec_epsMul_dualMap]
    simp only [Category.assoc]
  let J : (Fin g → R) →+ Vz := AddMonoidHom.mk' j jadd
  refine ⟨∑ i, (LinearMap.proj i : (Fin g → ℂ) →ₗ[ℂ] ℂ).smulRight (j (Pi.single i 1)), fun x => ?_⟩
  have hΘ : (∑ i, (LinearMap.proj i : (Fin g → ℂ) →ₗ[ℂ] ℂ).smulRight (j (Pi.single i 1)))
      (fun e => ψ (x e)) = j x := by
    have hx : x = ∑ i, x i • (Pi.single i 1 : Fin g → R) := by
      conv_lhs => rw [← Finset.univ_sum_single x]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Pi.single_smul, smul_eq_mul, _root_.mul_one]
    have hJ : J x = ∑ i, J (x i • (Pi.single i 1 : Fin g → R)) := by
      conv_lhs => rw [hx]
      exact map_sum J _ _
    have hJ' : j x = ∑ i, ψ (x i) • j (Pi.single i 1) := by
      refine hJ.trans (Finset.sum_congr rfl fun i _ => jsmul _ _)
    rw [hJ']
    simp [LinearMap.sum_apply]
  rw [hΘ, hj, wl]

theorem exists_linear_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (t' : SAB H (Sp R)) (h : Sp R ⟶ X) (m : SABMap t' t h) (g : ℕ) (M : LieModel t'.G (𝟙 (Sp R)) (Fin g → R)) (ψ : R →+* ℂ) (Vz : Type) [AddCommGroup Vz] [Module ℂ Vz] (MR : LieModel t.G (spMap ψ ≫ h) Vz), ∃ Θ : (Fin g → ℂ) →ₗ[ℂ] Vz, ∀ x : Fin g → R, (MR.pt (Θ (fun e => ψ (x e)))).left = spMap (dualMap ψ) ≫ (M.pt x).left ≫ m.φ := by
  intro E _ _ _ H X t R _ t' h m g M ψ Vz _ _ MR
  exact exists_linear_of_pullback m.cart M ψ MR

end GlobalTheory.CompanionTheory.Ar.FrameFibre
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineGeneratorGeometric
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ConstRatio

theorem ratio_mem {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {x : Cpt ξ}
    {W : Type} [AddCommGroup W] [Module Ω W] {e : W} {s t : Ω} (he : e ≠ 0) (hs : s ≠ 0)
    (hst : Submodule.span (regAt ξ x) {s • e} = Submodule.span (regAt ξ x) {t • e}) : t / s ∈ regAt ξ x := by
  have : t • e ∈ Submodule.span (regAt ξ x) {s • e} := hst ▸ Submodule.mem_span_singleton_self _
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp this
  have hr' : ((r : Ω) * s) • e = t • e := by rw [mul_smul]; exact hr
  have := smul_left_injective Ω he hr'
  rw [← this, mul_div_cancel_right₀ _ hs]; exact r.2

theorem exists_smul_eq {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {x : Cpt ξ}
    {W : Type} [AddCommGroup W] [Module Ω W] {a a' : W} {α α' : Ω} (hα' : α' ≠ 0)
    (h : Submodule.span (regAt ξ x) {α • a} = Submodule.span (regAt ξ x) {α' • a'}) : ∃ f : Ω, a' = f • a := by
  have : α' • a' ∈ Submodule.span (regAt ξ x) {α • a} := h ▸ Submodule.mem_span_singleton_self _
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp this
  have hr' : ((r : Ω) * α) • a = α' • a' := by rw [mul_smul]; exact hr
  refine ⟨α'⁻¹ * ((r : Ω) * α), ?_⟩
  rw [mul_smul, hr', smul_smul, inv_mul_cancel₀ hα', one_smul]

theorem unit_of_coeff {X : Scheme.{0}} {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {A B : Lat ξ V} {p q : ℕ} {a : ⋀[Ω]^p V} {b : ⋀[Ω]^q V} {s t : Ω}
    {x : Cpt ξ} (ha : a ≠ 0) (hb : b ≠ 0) (hs : s ≠ 0) (ht : t ≠ 0) (h : IsCoeffAt A B p q a b x 1)
    (h' : IsCoeffAt A B p q (s • a) (t • b) x 1) : unitAt ξ x (s / t) := by
  obtain ⟨α, β, hα, -, hA, hB, e⟩ := h
  obtain ⟨α', β', hα', -, hA', hB', e'⟩ := h'
  rw [_root_.one_mul] at e e'
  subst e e'
  rw [smul_smul] at hA' hB'
  have k1 := ratio_mem ha hα (hA.symm.trans hA')
  have k2 := ratio_mem ha (mul_ne_zero hα' hs) (hA'.symm.trans hA)
  have k3 := ratio_mem hb hα (hB.symm.trans hB')
  have k4 := ratio_mem hb (mul_ne_zero hα' ht) (hB'.symm.trans hB)
  refine ⟨div_ne_zero hs ht, ?_, ?_⟩
  · have := mul_mem k1 k4
    convert this using 1; field_simp
  · have := mul_mem k2 k3
    convert this using 1; field_simp

theorem exists_factors {X : Scheme.{0}} {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {A B : Lat ξ V} {p q : ℕ} {a a' : ⋀[Ω]^p V} {b b' : ⋀[Ω]^q V}
    {T : Set (Cpt ξ)} (hT : T.Nonempty) (h : IsLineGenOn A B p q a b T) (h' : IsLineGenOn A B p q a' b' T) :
    ∃ s t : Ω, s ≠ 0 ∧ t ≠ 0 ∧ a' = s • a ∧ b' = t • b ∧ ∀ x ∈ T, unitAt ξ x (s / t) := by
  obtain ⟨ha, hb, h⟩ := h
  obtain ⟨ha', hb', h'⟩ := h'
  obtain ⟨x₀, hx₀⟩ := hT
  obtain ⟨s, hs⟩ : ∃ s : Ω, a' = s • a := by
    obtain ⟨α, β, -, -, hA, -, -⟩ := h x₀ hx₀
    obtain ⟨α', β', hα', -, hA', -, -⟩ := h' x₀ hx₀
    exact exists_smul_eq hα' (hA.symm.trans hA')
  obtain ⟨t, ht⟩ : ∃ t : Ω, b' = t • b := by
    obtain ⟨α, β, -, -, -, hB, -⟩ := h x₀ hx₀
    obtain ⟨α', β', -, hβ', -, hB', -⟩ := h' x₀ hx₀
    exact exists_smul_eq hβ' (hB.symm.trans hB')
  have hs0 : s ≠ 0 := by rintro rfl; exact ha' (by rw [hs, zero_smul])
  have ht0 : t ≠ 0 := by rintro rfl; exact hb' (by rw [ht, zero_smul])
  refine ⟨s, t, hs0, ht0, hs, ht, fun x hx => ?_⟩
  have := h' x hx
  rw [hs, ht] at this
  exact unit_of_coeff ha hb hs0 ht0 (h x hx) this

theorem isProper_of_proj {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R} (h : IsProjOver f) :
    IsProper f := by
  obtain ⟨m, i, hi, rfl⟩ := h
  have := isProper_str R m
  infer_instance

theorem const_ratio : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (a a' : ⋀[Z.Ω]^D.p Z.V) (b b' : ⋀[Z.Ω]^D.q Z.V), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → Z.IsGeom → IsLineGenOn (Z.eig τ) (Z.eig (ComplexEmbedding.conjugate τ)) D.p D.q a b Z.genFib → IsLineGenOn (Z.eig τ) (Z.eig (ComplexEmbedding.conjugate τ)) D.p D.q a' b' Z.genFib → ∃ (x : c.F) (s t : Z.Ω), x ≠ 0 ∧ t ≠ 0 ∧ s = Z.inc x * t ∧ a' = s • a ∧ b' = t • b := by
  intro E _ _ _ H D l Xo c O _ β Y U Z τ a a' b b' ⟨hβ, hN, hfrac⟩ hG h h'
  haveI : IsDomain O := hβ.isDomain β
  letI : Algebra O Z.Ω := (Z.inc.comp β).toAlgebra
  have halg : ∀ o : O, algebraMap O Z.Ω o = Z.inc (β o) := fun _ => rfl
  have hover : (Z.ξ₀ ≫ Y.j) ≫ Y.s = Spec.map (CommRingCat.ofHom (algebraMap O Z.Ω)) := by
    have e : (Z.ξ₀ ≫ Y.j) ≫ Y.s = spMap Z.inc ≫ spMap β := by
      rw [Model.j, Category.assoc, Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over,
        ← Category.assoc, Z.over_inc]
    rw [e, spMap, spMap, ← Spec.map_comp]
    rfl
  have hinj : Function.Injective (algebraMap O Z.Ω) := Z.inc.injective.comp hβ
  have hcc : ConstClosed O Z.Ω := by
    rintro w ⟨f, hf0, hf⟩
    obtain ⟨x, rfl⟩ := hG w ⟨f.map β, (Polynomial.map_ne_zero_iff hβ).2 hf0, by
      rw [Polynomial.eval₂_map]; exact hf⟩
    obtain ⟨u, v, hv, e⟩ := hfrac x
    refine ⟨u, v, fun h0 => hv (by rw [h0, map_zero]), ?_⟩
    rw [halg, halg, ← map_mul, e]
  have hsub : genFibre O (Z.ξ₀ ≫ Y.j) ⊆ Z.genFib := by
    intro p hp
    have hbot : (Y.s p.1).asIdeal = ⊥ := by
      refine (Submodule.eq_bot_iff _).2 fun o ho => ?_
      by_contra h0
      exact ((ConstReg.regular_const _ _ _ O Y.s hover p o).2 Z.gen).1 (hp o h0) ho
    obtain ⟨w⟩ : Nonempty (Sp c.F) := inferInstance
    have e : Y.s p.1 = spMap β w := by
      refine PrimeSpectrum.ext ?_
      rw [hbot]
      refine ((Submodule.eq_bot_iff _).2 fun o ho => ?_).symm
      have h1 : β o ∈ w.asIdeal := ho
      by_contra h0
      have h2 : β o ≠ 0 := fun e0 => h0 (hβ (by rw [e0, map_zero]))
      exact w.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 (isUnit_iff_ne_zero.2 h2))
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback _ _ e
    exact ⟨z, hz⟩
  have hne : Z.genFib.Nonempty := ⟨⟨genPt (Z.ξ₀ ≫ Y.j), specializes_rfl⟩, ⟨Y.jQ (genPt Z.ξ₀), rfl⟩⟩
  obtain ⟨s, t, hs, ht, rfl, rfl, hu⟩ := exists_factors hne h h'
  haveI : IsProper Y.s := isProper_of_proj Y.proj
  let L : Lat (Z.ξ₀ ≫ Y.j) Z.Ω := fun p => Submodule.span (regAt (Z.ξ₀ ≫ Y.j) p) {1}
  obtain ⟨x', y', hy', e⟩ := (GlobalTheory.T.line_lattice_generic_sections Y.X Z.Ω (Z.ξ₀ ≫ Y.j) O Y.s hover hinj Z.gen hcc L 1
    (fun p _ => ⟨one_ne_zero, rfl⟩) (s / t)).1 (fun p hp =>
      Submodule.mem_span_singleton.2 ⟨⟨s / t, (hu p (hsub hp)).2.1⟩, by
        show (s / t) * 1 = _
        rw [_root_.mul_one]⟩)
  have hy : β y' ≠ 0 := fun h0 => hy' (hβ (by rw [h0, map_zero]))
  rw [_root_.mul_one, halg, halg] at e
  have hx' : β x' ≠ 0 := by
    intro h0
    rw [h0, map_zero] at e
    exact (mul_ne_zero (div_ne_zero hs ht) (by simpa using hy)) e
  refine ⟨β x' / β y', s, t, div_ne_zero hx' hy, ht, ?_, rfl, rfl⟩
  have hyΩ : Z.inc (β y') ≠ 0 := by simpa using hy
  rw [map_div₀, ← e]
  field_simp

end GlobalTheory.CompanionTheory.Ar.Flat.ConstRatio
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogResolutionPotentialPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_resolution_potential_pullback : ∀ (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (κ : K₀ → K) (v : (Σ k, J₀ k) → Σ k, J k) (P₀ Jd₀ : Ideal (MRing J₀)) (P Jd : Ideal (MRing J)) (D : ℕ) (R₀ : AnLogRes P₀ Jd₀ D) (R : AnLogRes P Jd D) (X : Type) [TopologicalSpace X] (B : FinHolAtlas D X) (Θ : LocPot X) (A₀ : HermLine J₀) (T : HermLine J) (π : R₀.X → X) (hπ : HoloMap R₀.A B π) (h : R.X → R₀.X) (hv : IsBlockMap κ v) (hc : Continuous (π ∘ h)), HoloMap R.A R₀.A h → (∀ x, SameOrbit (R₀.lift (h x) (h x)) (fun p => R.lift x x (v p))) → SamePot R₀.A Set.univ (potOf R₀ A₀) (Θ.pullback π hπ.1) → IsFlatOn R T → SamePot R.A Set.univ (potOf R ((pullHerm hv A₀).tensor T)) (Θ.pullback (π ∘ h) hc) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Chg.Twist.samePot_twist | exact GlobalTheory.CompanionTheory.Ar.Chg.Twist.samePot_twist | (intros; apply GlobalTheory.CompanionTheory.Ar.Chg.Twist.samePot_twist <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PairLatticeSumComapStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_lattice_sum_comap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (a b : CMType H ⊕ CMType H), a ≠ b → (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype).IsVB (labelRk D a + labelRk D b) ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgeSum.isVB_sup | exact GlobalTheory.CompanionTheory.Ar.HodgeSum.isVB_sup | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgeSum.isVB_sup <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodLatticeRankTwoG
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat.PeriodRank

theorem finrank_la_eq_two_mul :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ)
      (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)), IsPeriod D ty P →
      Module.finrank ℤ D.La = 2 * g :=
  fun _ _ _ _ _ _ _ _ _ hP => (GlobalTheory.FibreExp.free_finite_finrank_of_isPeriod hP).2.2

end GlobalTheory.CompanionTheory.Ar.Flat.PeriodRank
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SameOrbitOfProportionalCoordsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.same_orbit_of_proportional_coords : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (k₀ : K), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → EmbedsGeneric ξ (fun i : J k₀ => y ⟨k₀, i⟩) → ∀ w ∈ mcPts (mCoordIdeal y), ∀ w' ∈ mcPts (mCoordIdeal y), ∀ u : ℂ, (∀ i : J k₀, w ⟨k₀, i⟩ = u * w' ⟨k₀, i⟩) → SameOrbit w w' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.OrbitBlock.sameOrbit_of_block | exact GlobalTheory.CompanionTheory.Ar.OrbitBlock.sameOrbit_of_block | (intros; apply GlobalTheory.CompanionTheory.Ar.OrbitBlock.sameOrbit_of_block <;> assumption)
end

