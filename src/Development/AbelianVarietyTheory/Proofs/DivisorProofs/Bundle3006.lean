import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2920
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOneBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2843
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2811
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2956
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1097
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2925
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GenericIsoExtendsSemiAbelianDvrInducingFormal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2838
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCAndCoordCorrespond
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsLocalRingQuotientPow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0092
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0089
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0165
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveAlgebraMapIntegralClosureOfBirational
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2308
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2921
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2818
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Definitions.Degenerations.NotFrobGUnitRat
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2413
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2922
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2813

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalEndomorphismPullsTorusCoordinateNormalisedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalEndomorphism_pulls_torusCoordinate_normalisedGenerator : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ b, FormalEnd U.toUnifPre a h' b → ∀ (α : D.toPre.X) (u : LB.Gen (IotaLB D.toPre a α (h' α))), IsIota u → ∀ (e : ℕ) (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J), Good D.toPre.P.L z J → val ((U.gt e).t α) (x ≫ (b e).left) z J = val ((U.gt e).t (h' α)) x z J * val u (x ≫ (U.gt e).pG.left) z J := by
  first | exact @GlobalTheory.TwFam.coord_of_formalEnd | exact GlobalTheory.TwFam.coord_of_formalEnd | (intros; apply GlobalTheory.TwFam.coord_of_formalEnd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalPointsAbelianPartsMultiply
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

open GlobalTheory.Poinc.Tors

noncomputable section

namespace GlobalTheory.Poinc.Sep.FormalMul

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {G : Over (Sp R)} {D : DegData R I}
  {A : PolAV (Sp (FractionRing R))} [GrpObj G] [IsCommMonObj G]

theorem map_b_eq {U : UnifPre I D A G} {T : Over (Sp R)} {x : T ⟶ G} {g : GtPt D.toPre T}
    (hg : GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.FormalEq U x g) (e : ℕ) :
    (Over.pullback (thick R I e)).map g.b = (Over.pullback (thick R I e)).map x ≫ (U.gt e).q :=
  (GlobalTheory.FormalExt.map_eq_iff I e g.b _).2 ((hg e).1.trans (Category.assoc _ _ _).symm)

theorem b_mul : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G), ∀ (h h' : (𝟙_ (Over (Sp V))) ⟶ G) (g g' g'' : GtPt D.toPre (𝟙_ (Over (Sp V)))), GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.FormalEq U.toUnifPre h g → GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.FormalEq U.toUnifPre h' g' → GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.FormalEq U.toUnifPre (h * h') g'' → g''.b = g.b * g'.b := by
  intro V _ _ _ hV D A G _ _ _ U h h' g g' g'' hg hg' hg''
  have := hV.1
  have := hV.2.2.1
  have := D.toPre.P.isAb.proper
  have h1 : Smooth (𝟙_ (Over (Spec (CommRingCat.of V)))).hom := inferInstanceAs (Smooth (𝟙 _))
  have h1' : GeometricallyConnected (𝟙_ (Over (Spec (CommRingCat.of V)))).hom :=
    inferInstanceAs (GeometricallyConnected (𝟙 _))
  refine GlobalTheory.FormalExt.hom_ext_thick (maximalIdeal V) (IsAdicComplete.le_jacobson_bot _) _ fun e => ?_
  have := (U.gt e).q_hom
  rw [Functor.map_mul, map_b_eq hg, map_b_eq hg', map_b_eq hg'', Functor.map_mul, MonObj.mul_comp]

end GlobalTheory.Poinc.Sep.FormalMul
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalSumTwistCubeIdentityStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalSum_twist_cube_identity : ∀ {R : Type} [CommRing R] [IsDomain R] (D₂ D : DegPre R) {T Y₀ : Over (Spec (CommRingCat.of R))} (q : T ⟶ Y₀) (y : Y₀ ⟶ D.P.A) (p₂ : T ⟶ D₂.P.A) (β : D₂.P.A ⟶ D.P.A) [IsMonHom β], p₂ ≫ β = q ≫ y → ∀ (b : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A) (χ₂ : D₂.X) (χ : D.X), FormEq (Sum.elim (Sum.elim (fun p : Fin 4 × Fin 3 => D₂.Oφ p₂ χ₂ p.1 ≫ GlobalTheory.MumCmp.twφ D₂ D β b p.2) (fun k : thK => (lift (q ≫ y) (lift (toUnit T ≫ D₂.c χ₂ ≫ β) (toUnit T ≫ b))).left ≫ thφ D.P.A (x3 D.P.A) k)) (D.Oφ (q ≫ y) χ)) (Sum.elim (Sum.elim (fun p : Fin 4 × Fin 3 => Oinvε p.1 * GlobalTheory.MumCmp.twε p.2) thε) (fun k => - Oinvε k)) (fun k => q.left ≫ GlobalTheory.CoordCompare.diffφ y (D₂.c χ₂ ≫ β) (D.c χ) k) ![1, -1, 1, -1] := by
  first | exact @GlobalTheory.MumCmp.formEq_twist_cube | exact GlobalTheory.MumCmp.formEq_twist_cube | (intros; apply GlobalTheory.MumCmp.formEq_twist_cube <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyUnramifiedOfDualConstField
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory GlobalTheory.ZH
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

open TensorProduct

namespace GlobalTheory.TangentCrit

theorem formallyUnramified_of_dual_const_field {K A B : Type} [Field K] [IsAlgClosed K]
    [CommRing A] [CommRing B] [Algebra K A] [Algebra K B] [Algebra A B] [IsScalarTower K A B]
    [Algebra.FiniteType K B] [Algebra.FiniteType A B]
    (H : ∀ φ : B →+* DualNumber K, (∀ c, φ (algebraMap K B c) = algebraMap K (DualNumber K) c) →
      (∀ a, (φ (algebraMap A B a)).snd = 0) → ∀ b, (φ b).snd = 0) :
    Algebra.FormallyUnramified A B := by
  refine ⟨?_⟩
  by_contra hne
  rw [← Module.support_eq_empty_iff (R := B), ← ne_eq, ← Set.nonempty_iff_ne_empty] at hne
  obtain ⟨p, hp⟩ := hne
  obtain ⟨m, hm, hpm⟩ := p.asIdeal.exists_le_maximal p.isPrime.ne_top
  let P : PrimeSpectrum B := ⟨m, hm.isPrime⟩
  have hP : P ∈ Module.support B Ω[B⁄A] := by
    rw [Module.support_eq_zeroLocus] at hp ⊢
    exact fun x hx => hpm (hp hx)
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct] at hP
  have hsurj : Function.Surjective (algebraMap B m.ResidueField) := by
    intro y
    obtain ⟨x, rfl⟩ := m.bijective_algebraMap_quotient_residueField.surjective y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨b, rfl⟩
  haveI : Algebra.FiniteType K m.ResidueField :=
    Algebra.FiniteType.of_surjective (IsScalarTower.toAlgHom K B m.ResidueField) hsurj
  haveI : Module.Finite K m.ResidueField := finite_of_finite_type_of_isJacobsonRing K _
  let ev : m.ResidueField →ₐ[K] K := IsAlgClosed.lift
  letI : Algebra m.ResidueField K := ev.toRingHom.toAlgebra
  letI : Algebra B K := (ev.toRingHom.comp (algebraMap B m.ResidueField)).toAlgebra
  haveI : IsScalarTower B m.ResidueField K := .of_algebraMap_eq fun _ => rfl
  letI : Algebra A K := ((algebraMap B K).comp (algebraMap A B)).toAlgebra
  haveI : IsScalarTower A B K := .of_algebraMap_eq fun _ => rfl
  have key : Function.Injective ((0 : Ω[B⁄A] →ₗ[B] PUnit.{1}).lTensor m.ResidueField) :=
    lTensor_injective_of_extend (k := K) _ fun χ => by
      refine ⟨0, ?_⟩
      let D : Derivation A B K := χ.compDer (KaehlerDifferential.D A B)
      have hlin : ∀ c, derToDual D (algebraMap K B c) = algebraMap K (DualNumber K) c := by
        intro c
        ext
        · rw [fst_derToDual]
          change ev (algebraMap B m.ResidueField (algebraMap K B c)) = _
          rw [← IsScalarTower.algebraMap_apply, ev.commutes]
          rfl
        · rw [snd_derToDual, IsScalarTower.algebraMap_apply K A B, D.map_algebraMap]
          rfl
      have := H (derToDual D) hlin (fun a => (snd_derToDual D _).trans (D.map_algebraMap a))
      refine Derivation.liftKaehlerDifferential_unique _ _ (Derivation.ext fun b => ?_)
      have := this b
      rw [snd_derToDual] at this
      simpa [D] using this.symm
  obtain ⟨z, hz⟩ := exists_ne (0 : m.ResidueField ⊗[B] Ω[B⁄A])
  exact hz (key (by simp))

end GlobalTheory.TangentCrit

namespace GlobalTheory.TangentCrit

end GlobalTheory.TangentCrit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierTermSystemIndexZeroCoefficientApprox
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep.UnitZero

theorem qW_nsmul {s : ℕ} (W : Matrix (Fin s) (Fin s) ℤ) {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X)
    (N : ℕ) (ν : Fin s → X) : qW W β (fun u => N • ν u) = (N : ℤ) ^ 2 * qW W β ν := by
  simp only [qW, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  rw [← Nat.cast_smul_eq_nsmul ℤ N (ν u), ← Nat.cast_smul_eq_nsmul ℤ N (ν v), LinearMap.map_smul₂, LinearMap.map_smul,
    smul_eq_mul, smul_eq_mul]
  ring

theorem mono_nsmul {s m : ℕ} (W : Matrix (Fin s) (Fin s) ℤ) {X : Type} [AddCommGroup X] {V : Type} [CommRing V]
    (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (ν : Fin s → X) (hν : ∀ k, 0 ≤ qW W (δ k) ν) (N : ℕ) :
    mono W t δ (fun u => N • ν u) = mono W t δ ν ^ (N ^ 2) := by
  simp only [mono]
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← pow_mul, qW_nsmul]
  congr 1
  have : (N : ℤ) ^ 2 * qW W (δ k) ν = (((qW W (δ k) ν).toNat * N ^ 2 : ℕ) : ℤ) := by
    push_cast
    rw [Int.toNat_of_nonneg (hν k)]
    ring
  rw [this, Int.toNat_natCast]

theorem mem_of_forall_mem_pow_sup {V : Type} [CommRing V] [IsLocalRing V] [IsNoetherianRing V] (I : Ideal V) (x : V)
    (h : ∀ j : ℕ, x ∈ maximalIdeal V ^ j ⊔ I) : x ∈ I := by
  have hK := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (R := V) (M := V ⧸ I) (maximalIdeal V)
    (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have hx : Ideal.Quotient.mk I x ∈ ⨅ i : ℕ, maximalIdeal V ^ i • (⊤ : Submodule V (V ⧸ I)) := by
    rw [Submodule.mem_iInf]
    intro j
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (h j)
    have : Ideal.Quotient.mk I (a + b) = a • Ideal.Quotient.mk I 1 := by
      rw [map_add, Ideal.Quotient.eq_zero_iff_mem.2 hb, add_zero, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, map_one,
        _root_.mul_one]
    rw [this]
    exact Submodule.smul_mem_smul ha Submodule.mem_top
  rw [hK] at hx
  exact (Submodule.mem_bot _).1 hx

theorem pow_mem_of_radical {V : Type} [CommRing V] (J : Ideal V) {m : ℕ} (t : Fin m → V) {Ix : Type}
    (a : Ix → Fin m → ℕ) (Z : Set Ix) (hrad : ∀ ν ∈ Z, (∏ k, t k ^ a ν k) ∈ J.radical) (e : ℕ) :
    ∃ n, ∀ ν ∈ Z, ∀ M, n ≤ M → (∏ k, t k ^ a ν k) ^ M ∈ J ^ e := by
  classical
  let P : (Fin m → Bool) → V := fun p => ∏ k, t k ^ (if p k then 1 else 0)
  let pat : Ix → Fin m → Bool := fun ν k => decide (0 < a ν k)
  have hdvd : ∀ ν, P (pat ν) ∣ ∏ k, t k ^ a ν k := fun ν =>
    Finset.prod_dvd_prod_of_dvd _ _ fun k _ => pow_dvd_pow _ (by
      by_cases h : 0 < a ν k <;> simp [pat, h] <;> omega)
  have hP : ∀ p, ∃ n, (∃ ν ∈ Z, pat ν = p) → P p ^ n ∈ J := by
    intro p
    by_cases hp : ∃ ν ∈ Z, pat ν = p
    · obtain ⟨ν, hν, rfl⟩ := hp
      have hK : (∏ k, t k ^ a ν k) ∣ P (pat ν) ^ (∑ k, a ν k) := by
        simp only [P]
        rw [← Finset.prod_pow]
        refine Finset.prod_dvd_prod_of_dvd _ _ fun k _ => ?_
        rw [← pow_mul]
        refine pow_dvd_pow _ ?_
        by_cases h : 0 < a ν k
        · simp only [pat, h, decide_true, if_true, Nat.one_mul]
          exact Finset.single_le_sum (f := a ν) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
        · simp only [pat, h, decide_false]
          simp only [Bool.false_eq_true, if_false, Nat.zero_mul]
          omega
      obtain ⟨c, hc⟩ := hK
      have h1 : P (pat ν) ^ (∑ k, a ν k) ∈ J.radical := by
        rw [hc]; exact Ideal.mul_mem_right _ _ (hrad ν hν)
      obtain ⟨n, hn⟩ := Ideal.mem_radical_of_pow_mem h1
      exact ⟨n, fun _ => hn⟩
    · exact ⟨0, fun h => (hp h).elim⟩
  choose nP hnP using hP
  refine ⟨(Finset.univ.sup nP) * e, fun ν hν M hM => ?_⟩
  have hle : nP (pat ν) * e ≤ M :=
    le_trans (Nat.mul_le_mul_right _ (Finset.le_sup (f := nP) (Finset.mem_univ _))) hM
  have h1 : P (pat ν) ^ (nP (pat ν) * e) ∈ J ^ e := by
    rw [pow_mul]; exact Ideal.pow_mem_pow (hnP _ ⟨ν, hν, rfl⟩) e
  have h2 : P (pat ν) ^ (nP (pat ν) * e) ∣ (∏ k, t k ^ a ν k) ^ M :=
    (pow_dvd_pow _ hle).trans (pow_dvd_pow_of_dvd (hdvd ν) M)
  obtain ⟨c, hc⟩ := h2
  rw [hc]; exact Ideal.mul_mem_right _ _ h1

end GlobalTheory.Poinc.Sep.UnitZero

namespace GlobalTheory.Poinc.Sep.UnitZero

theorem mem_orbit_zero {O : Type} [CommRing O] {X₀ X : Type} [AddCommGroup X₀] [Module O X₀] [AddCommGroup X]
    [Module O X] {N₁ N : ℕ} {k : X₀ →ₗ[ℤ] X} {Ix : Type} {mu : Ix → X} (h : mu ∈ orbit O N₁ N k (0 : Ix → X₀)) :
    ∀ i, ∃ w, mu i = N • w := by
  obtain ⟨gam, -, -, -, hmu⟩ := h
  intro i
  obtain ⟨w, hw⟩ := hmu i
  exact ⟨w, by simpa using hw⟩

theorem zero_mem_orbit {O : Type} [CommRing O] {X₀ X : Type} [AddCommGroup X₀] [Module O X₀] [AddCommGroup X]
    [Module O X] {N₁ N : ℕ} {k : X₀ →ₗ[ℤ] X} {Ix : Type} : (0 : Ix → X) ∈ orbit O N₁ N k (0 : Ix → X₀) :=
  ⟨LinearMap.id, fun c x => ⟨0, by simp⟩, by simp, fun x => ⟨0, by simp⟩, fun i => ⟨0, by simp⟩⟩

end GlobalTheory.Poinc.Sep.UnitZero

namespace GlobalTheory.Poinc.Sep

theorem coeffZero_approx : ∀ (O : Type) [CommRing O] (bar : O → O) (q s : ℕ) (W : Matrix (Fin s) (Fin s) ℤ) (A : Type) [CommRing A] [IsLocalRing A] (Φ : VPre bar q W A) (N₁ : ℕ), 3 ≤ N₁ → Φ.Exact N₁ → Φ.abelian₂ → Φ.Four N₁ → (∀ y y', Φ.m y ≠ 1 → Φ.m y' ≠ 1 → y = y') → ∀ (c₀ : Φ.Q) (e : ℕ), ∃ a : A, ∀ y, Φ.ev y a - Φ.u y 0 c₀ ∈ (maximalIdeal A ^ e).map (Φ.ev y) := by
  intro O _ bar q s W A _ _ Φ N₁ h3 hEx hLam hFour huniq c₀ e
  classical
  rcases isEmpty_or_nonempty Φ.Y with hY | ⟨⟨y₀⟩⟩
  · exact ⟨0, fun y => (IsEmpty.false y).elim⟩
  obtain ⟨cW, hcW, hqW⟩ := QWDom.qW_ge s W Φ.posW
  obtain ⟨C, hC⟩ := hLam
  have hnn : ∀ y (k : Fin (Φ.m y)) (ν : Fin s → Φ.X y), 0 ≤ qW W (Φ.δ y k) ν := fun y k ν =>
    GlobalTheory.Poinc.qW_nonneg Φ.posW (Φ.bal y k).1 (Φ.nonneg y k) ν
  have hspec : ∃ n : ℕ, ∀ y, Φ.m y ≠ 1 → ∀ ν : Fin s → Φ.X y, ν ≠ 0 → ∀ M, n ≤ M →
      mono W (Φ.t y) (Φ.δ y) ν ^ M ∈ (maximalIdeal A ^ e).map (Φ.ev y) := by
    by_cases h : ∃ y₁, Φ.m y₁ ≠ 1
    · obtain ⟨y₁, hy₁⟩ := h
      obtain ⟨n, hn⟩ := UnitZero.pow_mem_of_radical ((maximalIdeal A).map (Φ.ev y₁)) (Φ.t y₁)
        (fun ν k => (qW W (Φ.δ y₁ k) ν).toNat) {ν | ν ≠ 0}
        (fun ν hν => GlobalTheory.T.fourierMonomial_mem_radical_extended_maximalIdeal O bar q s W A Φ N₁ h3 hEx y₁ ν hν) e
      refine ⟨n, fun y hy => ?_⟩
      obtain rfl := huniq y y₁ hy hy₁
      intro ν hν M hM
      rw [Ideal.map_pow]
      exact hn ν hν M hM
    · exact ⟨0, fun y hy => (h ⟨y, hy⟩).elim⟩
  obtain ⟨n, hn⟩ := hspec
  obtain ⟨N, hN₀, -, k, -, -, hF⟩ := hFour y₀ (n + ⌈((e * C : ℕ) : ℝ) / cW⌉₊ + 1)
  obtain ⟨f, hf⟩ := hF 1 0 (fun _ => c₀) e
  refine ⟨f, fun y => ?_⟩
  have hN2 : N ≤ N ^ 2 := Nat.le_self_pow two_ne_zero N
  have hNc : ((e * C : ℕ) : ℝ) ≤ (N : ℝ) ^ 2 * cW := by
    have h1 : ((e * C : ℕ) : ℝ) / cW ≤ (N : ℝ) ^ 2 := by
      refine (Nat.le_ceil _).trans ?_
      exact_mod_cast (show ⌈((e * C : ℕ) : ℝ) / cW⌉₊ ≤ N ^ 2 by omega)
    rwa [div_le_iff₀ hcW] at h1
  have hmono : ∀ ν : Fin s → Φ.X y, ν ≠ 0 →
      mono W (Φ.t y) (Φ.δ y) (fun v => N • ν v) ∈ (maximalIdeal A ^ e).map (Φ.ev y) := by
    intro ν hν
    by_cases hm : Φ.m y = 1
    · obtain ⟨v, hv⟩ := Function.ne_iff.1 hν
      obtain ⟨i, hi⟩ := Φ.pos y (ν v) hv
      obtain ⟨h, hh, hdiv⟩ := hC y hm i (ν v) hv
      have hexp : e * (C * (Φ.δ y i (ν v) (ν v)).toNat) ≤ (qW W (Φ.δ y i) (fun u => N • ν u)).toNat := by
        have hq := hqW (Φ.X y) (Φ.δ y i) (Φ.bal y i).1 (Φ.nonneg y i) ν
        have hsum : Φ.δ y i (ν v) (ν v) ≤ ∑ u, Φ.δ y i (ν u) (ν u) :=
          Finset.single_le_sum (f := fun u => Φ.δ y i (ν u) (ν u)) (fun u _ => Φ.nonneg y i _) (Finset.mem_univ v)
        have hsumR : ((Φ.δ y i (ν v) (ν v) : ℤ) : ℝ) ≤ ((∑ u, Φ.δ y i (ν u) (ν u) : ℤ) : ℝ) := by exact_mod_cast hsum
        have hD0 : (0 : ℝ) ≤ ((Φ.δ y i (ν v) (ν v) : ℤ) : ℝ) := by exact_mod_cast hi.le
        have hR : ((e * C : ℕ) : ℝ) * ((Φ.δ y i (ν v) (ν v) : ℤ) : ℝ) ≤ (N : ℝ) ^ 2 * (qW W (Φ.δ y i) ν : ℝ) := by
          calc ((e * C : ℕ) : ℝ) * ((Φ.δ y i (ν v) (ν v) : ℤ) : ℝ)
              ≤ (N : ℝ) ^ 2 * cW * ((Φ.δ y i (ν v) (ν v) : ℤ) : ℝ) := mul_le_mul_of_nonneg_right hNc hD0
            _ = (N : ℝ) ^ 2 * (cW * ((Φ.δ y i (ν v) (ν v) : ℤ) : ℝ)) := by ring
            _ ≤ (N : ℝ) ^ 2 * (cW * ((∑ u, Φ.δ y i (ν u) (ν u) : ℤ) : ℝ)) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsumR hcW.le) (by positivity)
            _ ≤ (N : ℝ) ^ 2 * (qW W (Φ.δ y i) ν : ℝ) := mul_le_mul_of_nonneg_left hq (by positivity)
        have hZ : ((e * C : ℕ) : ℤ) * Φ.δ y i (ν v) (ν v) ≤ (N : ℤ) ^ 2 * qW W (Φ.δ y i) ν := by exact_mod_cast hR
        have hpos : 0 ≤ (N : ℤ) ^ 2 * qW W (Φ.δ y i) ν := mul_nonneg (by positivity) (hnn y i ν)
        rw [UnitZero.qW_nsmul, ← Nat.cast_le (α := ℤ), Int.toNat_of_nonneg hpos]
        push_cast
        rw [Int.toNat_of_nonneg hi.le]
        push_cast at hZ
        linarith
      have h1 : Φ.ev y (h ^ e) ∈ (maximalIdeal A ^ e).map (Φ.ev y) := Ideal.mem_map_of_mem _ (Ideal.pow_mem_pow hh e)
      have h2 : Φ.ev y (h ^ e) ∣ mono W (Φ.t y) (Φ.δ y) (fun u => N • ν u) := by
        rw [map_pow]
        refine (pow_dvd_pow_of_dvd hdiv e).trans ?_
        rw [← pow_mul]
        refine (pow_dvd_pow _ ((Nat.mul_comm _ _).le.trans hexp)).trans ?_
        unfold mono
        exact Finset.dvd_prod_of_mem (fun k => Φ.t y k ^ (qW W (Φ.δ y k) (fun u => N • ν u)).toNat) (Finset.mem_univ i)
      obtain ⟨c, hc⟩ := h2
      rw [hc]; exact Ideal.mul_mem_right _ _ h1
    · rw [UnitZero.mono_nsmul W (Φ.t y) (Φ.δ y) ν (fun k => hnn y k ν) N]
      exact hn y hm ν hν _ (le_trans (by omega) hN2)
  have hterm : ∀ mu ∈ orbit O N₁ N (k y) (0 : Fin 1 × Fin s → Φ.X y₀), mu ≠ 0 →
      (∏ i : Fin 1, Φ.u y (fun v => mu (i, v)) c₀ * mono W (Φ.t y) (Φ.δ y) (fun v => mu (i, v))) ∈
        (maximalIdeal A ^ e).map (Φ.ev y) := by
    intro mu hmu hmu0
    choose w hw using UnitZero.mem_orbit_zero hmu
    have hν : (fun v => w (0, v)) ≠ 0 := by
      intro h0
      apply hmu0
      funext ⟨i, v⟩
      have hi0 : i = 0 := Subsingleton.elim _ _
      subst hi0
      rw [hw, Pi.zero_apply]
      have := congrFun h0 v
      simp only [Pi.zero_apply] at this
      rw [this, smul_zero]
    rw [Fin.prod_univ_one]
    have : (fun v => mu (0, v)) = fun v => N • w (0, v) := funext fun v => hw _
    rw [this]
    exact Ideal.mul_mem_left _ _ (hmono _ hν)
  have hmem : ∀ j : ℕ, Φ.ev y f - Φ.u y 0 c₀ ∈ maximalIdeal (Φ.V y) ^ j ⊔ (maximalIdeal A ^ e).map (Φ.ev y) := by
    intro j
    obtain ⟨S, hS, htail, hap⟩ := hf y (j + 1)
    have h0 : (0 : Fin 1 × Fin s → Φ.X y) ∈ S := by
      by_contra h0
      have := htail 0 UnitZero.zero_mem_orbit h0
      simp only [lin, qW, Pi.zero_apply, map_zero, LinearMap.zero_apply, mul_zero, Finset.sum_const_zero] at this
      omega
    rw [← Finset.add_sum_erase S _ h0] at hap
    have hz : (∏ i : Fin 1, Φ.u y (fun v => (0 : Fin 1 × Fin s → Φ.X y) (i, v)) c₀ *
        mono W (Φ.t y) (Φ.δ y) (fun v => (0 : Fin 1 × Fin s → Φ.X y) (i, v))) = Φ.u y 0 c₀ := by
      rw [Fin.prod_univ_one]
      show Φ.u y 0 c₀ * mono W (Φ.t y) (Φ.δ y) 0 = Φ.u y 0 c₀
      simp [mono, qW]
    rw [hz] at hap
    have hle : maximalIdeal (Φ.V y) ^ (j + 1) ⊔ (maximalIdeal A ^ e).map (Φ.ev y) ≤
        maximalIdeal (Φ.V y) ^ j ⊔ (maximalIdeal A ^ e).map (Φ.ev y) :=
      sup_le_sup_right (Ideal.pow_le_pow_right (Nat.le_succ j)) _
    have key := Submodule.add_mem _ (hle hap)
      (Ideal.mem_sup_right (Ideal.sum_mem _ fun mu hmu => hterm mu (hS (Finset.mem_of_mem_erase hmu))
        (Finset.ne_of_mem_erase hmu)))
    convert key using 1
    ring
  haveI : IsNoetherianRing (Φ.V y) := (Φ.cn y).1
  exact UnitZero.mem_of_forall_mem_pow_sup _ _ hmem

end GlobalTheory.Poinc.Sep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoefficientsDescendFiniteFreeAffineOpenStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_coefficients_descend_finiteFree_affineOpen : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ₁ : R →+* R₁) (d : ℕ) (b : Fin d → R₁), (∀ r : R₁, ∃! c : Fin d → R, r = ∑ l, ρ₁ (c l) * b l) → ∀ (X : Scheme.{0}) (f : X ⟶ Sp R) (L : LB X), L.IsLB → ∀ (W O : X.Opens), O ≤ W → IsAffineOpen O → ∀ (τ : ∀ k : L.ι, Γ((pullback f (spMap ρ₁)), (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W ⊓ (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ L.U k)ˣ), FrameAlong L (pullback.fst f (spMap ρ₁)) ((pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W) τ → ∃ s : Fin d → ∀ k : L.ι, Γ(X, O ⊓ L.U k), (∀ l, IsSecOver L O (s l)) ∧ ∀ (z : (pullback f (spMap ρ₁) : Scheme.{0})) (k : L.ι), (pullback.fst f (spMap ρ₁)) z ∈ O → (pullback.fst f (spMap ρ₁)) z ∈ L.U k → gs (𝟙 (pullback f (spMap ρ₁))) z ((pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W ⊓ (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ L.U k) (τ k).val = ∑ l, gs (pullback.snd f (spMap ρ₁)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (b l)) * gs (pullback.fst f (spMap ρ₁)) z (O ⊓ L.U k) (s l k) := by
  first | exact @GlobalTheory.FrameCoeff.frame_coeff | exact GlobalTheory.FrameCoeff.frame_coeff | (intros; apply GlobalTheory.FrameCoeff.frame_coeff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameDegreeCmLogPeriodStatement
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_degree_cm_log_period : CMDiffSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), GlobalTheory.IsKroneckerChar χ → ∀ (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → FrameDeg U x (GlobalTheory.CM.logOm E χ).re := by
  first | exact @GlobalTheory.FlatCore.frameDeg_of_cmDiff | exact GlobalTheory.FlatCore.frameDeg_of_cmDiff | (intros; apply GlobalTheory.FlatCore.frameDeg_of_cmDiff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobOverPtOver
section
open CategoryTheory GlobalTheory.AV GlobalTheory.AV.AbVar

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry Limits MonObj GlobalTheory.Published.AbVarRed GlobalTheory.SS.FrobModel
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.AV.FrobEx

theorem frobOver_ptOver (K : Type) [Field K] [Fintype K] :
    frobOver (ptOver K (AlgebraicClosure K)) =
      specAut (FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)) := by
  apply Over.OverMorphism.ext
  change absFrob (ptOver K (AlgebraicClosure K)) = Spec.map (CommRingCat.ofHom
    ((FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K) : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
      AlgebraicClosure K →+* AlgebraicClosure K))
  haveI : IsAffine (ptOver K (AlgebraicClosure K)).left := inferInstanceAs (IsAffine (Spec _))
  apply ext_of_isAffine
  rw [← cancel_epi (Scheme.ΓSpecIso (.of (AlgebraicClosure K))).inv]
  rw [← Scheme.ΓSpecIso_inv_naturality]
  ext c
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
  have e : ((FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K) :
      AlgebraicClosure K →+* AlgebraicClosure K) c) = c ^ Fintype.card K :=
    FiniteField.frobeniusAlgEquivOfAlgebraic_apply K (AlgebraicClosure K) c
  exact ((congrArg (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure K))).inv.hom e).trans (map_pow _ c _)).symm

theorem isFrob_frobOver (K : Type) [Field K] [Fintype K] (A : AbVar K) :
    letI : IsMonHom (frobOver A.X) := (frobG_frobOver A.X).1
    IsFrob (A := A) (Hom.mk (frobOver A.X)) := by
  letI : IsMonHom (frobOver A.X) := (frobG_frobOver A.X).1
  intro x
  rw [mk_hom, ← frobOver_comm, frobOver_ptOver]
  rfl

end GlobalTheory.AV.FrobEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusCanonicalLiftPrimitiveHodgeStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_primitiveSubmodule_of_isCan_of_rigToExt_eq_zero : ∀ (p : ℕ) [Fact p.Prime]  (R : Type) [CommRing R] (N : ℕ), (p : R) ^ N = 0 → ∀ (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (G : PDivGroup p R) (t : G.TorsionTower A) (c : primDR A) (x : G.RigExt), IsCan t c x → G.rigToExt x = 0 → c ∈ PrimitiveSubmodule A := by
  first | exact @GlobalTheory.PtExt.mem_F1prim_of_rigToExt_eq_zero_of_pow_eq_zero | exact GlobalTheory.PtExt.mem_F1prim_of_rigToExt_eq_zero_of_pow_eq_zero | (intros; apply GlobalTheory.PtExt.mem_F1prim_of_rigToExt_eq_zero_of_pow_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusKernelPrimitiveDeRhamHodgeStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.AbDual
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_kernel_primitive_de_rham_hodge : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (A : Over (Sp k)) [GrpObj A], IsAbelianScheme A → ∀ c : primDR A, frobDR p k hk A c = 0 → c ∈ PrimitiveSubmodule A := by
  first | exact @GlobalTheory.frobDR_eq_zero_mem_F1prim | exact GlobalTheory.frobDR_eq_zero_mem_F1prim | (intros; apply GlobalTheory.frobDR_eq_zero_mem_F1prim <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisActionRootsOfUnityStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_action_roots_of_unity : ∀ (g : ℂ ≃+* ℂ) (k : ℕ), 0 < k → ∃ a : ℤ, IsCoprime a (k : ℤ) ∧
    ∀ n : ℤ, g (Complex.exp (2 * Real.pi * Complex.I * n / k)) = Complex.exp (2 * Real.pi * Complex.I * (a * n) / k) := by
  first | exact @GlobalTheory.cyclotomic_character_of_ringEquiv | exact GlobalTheory.cyclotomic_character_of_ringEquiv | (intros; apply GlobalTheory.cyclotomic_character_of_ringEquiv <;> assumption)
end

