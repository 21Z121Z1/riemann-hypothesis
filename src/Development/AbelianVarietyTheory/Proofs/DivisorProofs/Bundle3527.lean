import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2461
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2527
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2713
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2884
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2689
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3490
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3505
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3485
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3473
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0160
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2496
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaCoordinatesExistUniqueSeparatePoints
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0052
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineHomZarhinProductToEighthPower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3488
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1191
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1267
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3240
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0191
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3501
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3193
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3322
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3331
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3343
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3323
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3506
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3443
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2514
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0618
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3025
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusMemOfSepAtBTate
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeFiltrationsOrthogonalLineBundlePairingProdu
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt.HodgeOrth

theorem fv_sum {R : Type} [CommRing R] {X : Over (Sp R)} {J : Type} (s : Finset J) (c : J → R)
    (α : J → Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))) (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D']
    [Algebra R D'] (φ : D →ₐ[R] D') (x : Pt X D) :
    fv (∑ i ∈ s, c i • α i) D D' φ x = ∑ i ∈ s, fv (α i) D D' φ x * algebraMap R D' (c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; rfl
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, (GlobalTheory.T.crystallineCocycleOnTrivialThickenings_additive_linear R X).1, ← ih, mul_comm,
      ← (GlobalTheory.T.crystallineCocycleOnTrivialThickenings_additive_linear R X).2.1]
    rfl

theorem commAlgFunctorCocyclesTwo_finsetSum_apply {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {J : Type}
    (s : Finset J) (w : J → Z2 F) (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T'') :
    (∑ i ∈ s, w i).1 T T' T'' φ ψ = ∑ i ∈ s, (w i).1 T T' T'' φ ψ := by
  simp only [Submodule.coe_sum, Finset.sum_apply]

theorem sum_cup_eq_mk {R : Type} [CommRing R] {A B : Over (Sp R)} {N : ℕ}
    (m₁ : IsMor (dp0 R) (A.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (fst A B).left)
    (m₂ : IsMor (dp0 R) (B.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (snd A B).left)
    (α : Fin N → Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))) (β : Fin N → Z1 (O (dp0 R) (B.hom ≫ 𝟙 _))) :
    (∑ k, cup _ (pullOver (dp0 R) (𝟙 _) (fst A B) (CatCoh.H1.mk _ (α k)))
      (pullOver (dp0 R) (𝟙 _) (snd A B) (CatCoh.H1.mk _ (β k)))) =
      CatCoh.H2.mk _ (∑ k, cupZ _ (m₁.coef.pullbackOneCocycle (α k)) (m₂.coef.pullbackOneCocycle (β k))) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [← cup_mk]
  rfl

theorem exists_isCupCob {R : Type} [CommRing R] {A B : Over (Sp R)} {N : ℕ} (P : LB (A ⊗ B).left)
    (α : Fin N → Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))) (β : Fin N → Z1 (O (dp0 R) (B.hom ≫ 𝟙 _)))
    (hc : IsChern (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) P
      (∑ k, cup _ (pullOver (dp0 R) (𝟙 _) (fst A B) (CatCoh.H1.mk _ (α k)))
        (pullOver (dp0 R) (𝟙 _) (snd A B) (CatCoh.H1.mk _ (β k))))) :
    ∃ n, IsCupCob P.U (fun i ↦ fv (α i)) (fun i ↦ fv (β i)) n := by
  have m₁ : IsMor (dp0 R) (A.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (fst A B).left :=
    IsMor.of_over _ (by rw [← Category.assoc, Over.w])
  have m₂ : IsMor (dp0 R) (B.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (snd A B).left :=
    IsMor.of_over _ (by rw [← Category.assoc, Over.w])
  rw [sum_cup_eq_mk m₁ m₂] at hc
  obtain ⟨n, hn⟩ := GlobalTheory.T.exists_pointwiseCochain_coboundary_eq_chernCocycle' R (A ⊗ B) P _ hc
  refine ⟨n, fun E _ _ E' _ _ E'' _ _ φ ψ z hz ↦ ?_⟩
  rw [hn E E' E'' φ ψ z hz, commAlgFunctorCocyclesTwo_finsetSum_apply]
  exact Finset.sum_congr rfl fun k _ ↦ GlobalTheory.T.cup_pullback_cocycles_pointValue R A B m₁ m₂ _ _ E E' E'' φ ψ z

theorem sum_mem_F1prim {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {N : ℕ} (a : Fin N → primDR A)
    (α : Fin N → Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))) (hα : ∀ i, CatCoh.H1.mk _ (α i) = (a i).1) (c : Fin N → R)
    (k : Fn0 A)
    (hk : IsCob (whole A) (fun D _ _ D' _ _ φ x ↦ ∑ i, fv (α i) D D' φ x * algebraMap R D' (c i)) k) :
    ∑ i, c i • a i ∈ PrimitiveSubmodule A := by
  have hF : CatCoh.H1.mk _ (∑ i, c i • α i) ∈ F1 (A.hom ≫ 𝟙 _) := by
    refine (mem_hodgeFiltration_iff_pointwiseCoboundary R A _).2 ⟨k, fun D _ _ D' _ _ ψ z hz ↦ ?_⟩
    rw [fv_sum]
    exact hk D D' ψ z hz
  rw [map_sum] at hF
  simp only [map_smul, hα] at hF
  rw [PrimitiveSubmodule, Submodule.mem_comap, map_sum]
  exact hF

theorem fil_orthogonal : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ P : LB (A ⊗ B).left, P.IsLB → ∀ φ : HdR A →ₗ[R] HdR B →ₗ[R] R, AbDual.IsCorrForm (dp0 R) (𝟙 _) A B P φ → ∀ x ∈ Fil A, ∀ y ∈ Fil B, φ x y = 0 := by
  intro H R _ A B _ _ g _ hB _ gB P hP φ hP' x hx y hy
  obtain ⟨N, a, b, hc, hφ⟩ := hP'
  choose α hα using fun k ↦ CatCoh.H1.mk_surjective _ (a k).1
  choose β hβ using fun k ↦ CatCoh.H1.mk_surjective _ (b k).1
  obtain ⟨n, hcup⟩ := exists_isCupCob P α β (by simp only [hα, hβ]; exact hc)
  have hβ' : ∀ i, CatCoh.H1.mk _ (β i) ∈ primDR B := fun i ↦ by rw [hβ]; exact (b i).2
  obtain ⟨k, hk⟩ := GlobalTheory.T.exists_coboundary_of_mem_hodgeFiltration H R A B g hB gB _ P.U hP.cover (Fin N) _ β hβ' n
    (fun i ↦ (fv_isCoc_and_ev_eq R A (α i)).1) hcup y hy
  have eb : ∀ i, (⟨_, hβ' i⟩ : primDR B) = b i := fun i ↦ Subtype.ext (hβ i)
  have h0 := (Submodule.mem_dualAnnihilator _).1 hx _ (sum_mem_F1prim a α hα _ k hk)
  rw [hφ, ← h0, map_sum]
  exact Finset.sum_congr rfl fun k _ ↦ by rw [map_smul, smul_eq_mul, mul_comm, eb]

end GlobalTheory.PtExt.HodgeOrth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealAlongMonomialFamilyEqSpanMonomialStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idealAlong_monomialFamily_eq_span_monomial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ (φ : InvFun (𝓞 E)), IsPolFan H.bar (min Dw.p Dw.q) φ → ∀ (d : ℕ) (J : C.Z.IdealSheafData), (∀ x ∈ J.support, x ∉ Set.range C.i) → UValOn Xo c C.i φ J d → ∀ (S : Scheme.{0}) (π : S ⟶ pullback C.z (spMap C.b)), IsNormBl π (J.comap (pullback.fst C.z (spMap C.b))) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Cm : GlobalTheory.UChart.MonoFam Xo c φ V), GlobalTheory.Mum.Base V → ∀ ξ : Sp V ⟶ S, Cm.y ≫ C.iF = jK V ≫ ξ ≫ π → ∃ b : Fin Cm.m → ℕ, (∀ k, (b k : ℝ) = d * φ.evalZ ((l.M' : ℤ) • Cm.δ k)) ∧ idlAlong J (ξ ≫ π ≫ pullback.fst C.z (spMap C.b)) = Ideal.span {∏ k, Cm.s k ^ b k} := by
  first | exact @GlobalTheory.UGZero.idlAlong_eq_span_monomial | exact GlobalTheory.UGZero.idlAlong_eq_span_monomial | (intros; apply GlobalTheory.UGZero.idlAlong_eq_span_monomial <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveModOfSurjectiveModOppositeStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injective_mod_of_surjective_mod_opposite : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (y : D.La →ₗ[𝓞 E] X) (n : ℕ), 0 < n → ∀ Z Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' →
    Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X → (∀ x, ∃ b ∈ Z', ∃ e, y b = x + n • e) →
    ∀ b ∈ Z', (∃ e, y b = n • e) → ∃ e ∈ Z', b = n • e := by
  first | exact @GlobalTheory.LowFilt.inj_mod_of_surj_mod | exact GlobalTheory.LowFilt.inj_mod_of_surj_mod | (intros; apply GlobalTheory.LowFilt.inj_mod_of_surj_mod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFrameIdentityOfGenericPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.FieldBaseChange GlobalTheory.UT
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Sep.Frames GlobalTheory.UT.CoefBasic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralFrame_identity_of_genericPoint : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (N : ℕ) (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A), b ^ N = 1 → ∀ (t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, b.left] (DegPre.lineε 1))), t.IsGen → ∀ (κ : LB.Gen (kapLB D (𝟙 D.P.A ^ N) (N ^ 2) 1)), Normd κ → (∀ z J, Good D.P.L z J → val t (toUnit (TF (R := V) (FractionRing V))).left z J ^ (N ^ 2) * val κ ((toUnit (TF (R := V) (FractionRing V))).left ≫ b.left) z J = 1) → ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp V) (z : Z) J, Good D.P.L z J → val t r z J ^ (N ^ 2) * val κ (r ≫ b.left) z J = 1 := by
  first | exact @GlobalTheory.Poinc.Sep.FrameInt.kap_of_generic | exact GlobalTheory.Poinc.Sep.FrameInt.kap_of_generic | (intros; apply GlobalTheory.Poinc.Sep.FrameInt.kap_of_generic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOfGrpPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAbelianScheme_of_grpPullback' : ∀ {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G'] (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → IsAbelianScheme G → IsAbelianScheme G' := by
  first | exact @GlobalTheory.GrpPullAb.isAbelianScheme_of_grpPullback | exact GlobalTheory.GrpPullAb.isAbelianScheme_of_grpPullback | (intros; apply GlobalTheory.GrpPullAb.isAbelianScheme_of_grpPullback <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineHomZarhinProductToEighthPowerStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAffineHom_zarhinProduct_to_eighthPower : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 0 < d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → IsAffineHom (GlobalTheory.ZarhinFam.zphi c.A B mu).left := by
  first | (exact @GlobalTheory.ZarhinFam.isAffineHom_zphi) | (exact GlobalTheory.ZarhinFam.isAffineHom_zphi) | (intros; apply GlobalTheory.ZarhinFam.isAffineHom_zphi  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGoodSectionGroupFamilyAmpleMultiples
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp.GoodH

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem mem_H_of_eq (P : Pair p) {a a' b b' : ℤ} {f : X.functionField} (ha : a = a') (hb : b = b')
    (h : f ∈ P.H a b) : f ∈ P.H a' b' := by
  subst ha hb; exact h

theorem nu_nonneg (P : Pair p) (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField) : 0 ≤ P.nu a b σ y f := by
  rw [Pair.nu]; positivity

theorem mono_mem {D : ℕ} (P : Pair p) (e : ℕ) (x : Fin (D + 1) → X.functionField) (hx : ∀ l, x l ∈ P.H e 0)
    (a b : ℤ) (g : X.functionField) (hg : g ∈ P.H a b) (α : Fin (D + 1) → ℕ) (S : Finset (Fin (D + 1))) :
    (∏ l ∈ S, x l ^ α l) * g ∈ P.H ((e : ℤ) * ((∑ l ∈ S, α l : ℕ) : ℤ) + a) b ∧
      ∀ (σ : k →+* ℂ) (y : CxPts p σ), P.nu ((e : ℤ) * ((∑ l ∈ S, α l : ℕ) : ℤ) + a) b σ y ((∏ l ∈ S, x l ^ α l) * g) =
        (∏ l ∈ S, P.nu e 0 σ y (x l) ^ α l) * P.nu a b σ y g := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty, one_mul, Nat.cast_zero, mul_zero, zero_add]
    exact ⟨hg, fun _ _ => trivial⟩
  | @insert j S hj ih =>
    obtain ⟨hp1, hp2⟩ := GlobalTheory.VolBr.NuPow.pow_mem_H_and_nu_pow k X p P (e : ℤ) 0 (x j) (hx j) (α j)
    obtain ⟨hm1, hm2⟩ := GlobalTheory.VolBr.NuMul.mul_mem_H_and_nu_mul k X p P _ _ _ _ _ _ hp1 ih.1
    have ea : ((α j : ℕ) : ℤ) * (e : ℤ) + ((e : ℤ) * ((∑ l ∈ S, α l : ℕ) : ℤ) + a) =
        (e : ℤ) * ((∑ l ∈ insert j S, α l : ℕ) : ℤ) + a := by
      rw [Finset.sum_insert hj]; push_cast; ring
    have eb : ((α j : ℕ) : ℤ) * 0 + b = b := by ring
    rw [ea, eb] at hm1 hm2
    have ep : (∏ l ∈ insert j S, x l ^ α l) * g = x j ^ α j * ((∏ l ∈ S, x l ^ α l) * g) := by
      rw [Finset.prod_insert hj, mul_assoc]
    rw [ep]
    refine ⟨hm1, fun σ y => ?_⟩
    rw [hm2, hp2, ih.2, Finset.prod_insert hj, mul_assoc]

end GlobalTheory.HSAmp.GoodH

namespace GlobalTheory.HSAmp.GoodH

theorem goodFam_H : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → GoodFam P D (gdeg P.L D / D.factorial) fun m => P.H m 1 := by
  intro hAr k _ X _ p D hX P hL
  obtain ⟨e, x, hx⟩ := GlobalTheory.T.exists_basepointFreeSectionTuple_ample_arith k X p D hX P hL
  have he : 0 < e := hx.pos

  have hup : ∀ s : ℕ, ∃ c : ℕ, ∀ q : ℕ, (P.H ((e * q + s : ℕ) : ℤ) 1).FG ∧
      Module.finrank ℤ (P.H ((e * q + s : ℕ) : ℤ) 1) ≤
        Module.finrank (ratF x) X.functionField * (q + c + D).choose D := by
    intro s
    obtain ⟨c, C, -, h⟩ := GlobalTheory.T.arithHilbertSamuel_upperBound_count_rank_ample k X p D hX P hL e x hx (s : ℤ) 1
    refine ⟨c, fun q => ?_⟩
    have e1 : ((e * q + s : ℕ) : ℤ) = (e : ℤ) * (q : ℤ) + (s : ℤ) := by push_cast; ring
    rw [e1]
    exact ⟨(h q).1, (h q).2.1⟩

  have hlow : ∀ s : ℕ, ∃ c : ℕ, ∀ q : ℕ, Module.finrank (ratF x) X.functionField * (q + D).choose D ≤
      Module.finrank ℤ (P.H ((e * (q + c) + s : ℕ) : ℤ) 1) := by
    intro s
    obtain ⟨c, C, -, h⟩ := GlobalTheory.T.arithHilbertSamuel_lowerBound_count_rank_ample k X p D hX P hL e x hx (s : ℤ) 1
    obtain ⟨c', hc'⟩ := hup s
    refine ⟨c, fun q => ?_⟩
    obtain ⟨v, hv, hli⟩ := (h q).1
    have e1 : ((e * (q + c) + s : ℕ) : ℤ) = (e : ℤ) * ((q + c : ℕ) : ℤ) + (s : ℤ) := by push_cast; ring
    have hfg := (hc' (q + c)).1
    rw [e1] at hfg ⊢
    haveI : Module.Finite ℤ (P.H ((e : ℤ) * ((q + c : ℕ) : ℤ) + (s : ℤ)) 1) :=
      Module.Finite.iff_addGroup_fg.2 ((AddGroup.fg_iff_addSubgroup_fg _).2 hfg)
    let w : Fin (Module.finrank (ratF x) X.functionField * (q + D).choose D) →
        P.H ((e : ℤ) * ((q + c : ℕ) : ℤ) + (s : ℤ)) 1 := fun i => ⟨v i, hv i⟩
    have hw : LinearIndependent ℤ w :=
      LinearIndependent.of_comp (P.H ((e : ℤ) * ((q + c : ℕ) : ℤ) + (s : ℤ)) 1).subtype.toIntLinearMap hli
    simpa using hw.fintype_card_le_finrank
  have hrank := GlobalTheory.T.tendsto_div_pow_of_choose_bounds D e (Module.finrank (ratF x) X.functionField)
    (fun m => Module.finrank ℤ (P.H (m : ℤ) 1)) he (fun s _ => by
      obtain ⟨c, hc⟩ := hlow s
      obtain ⟨c', hc'⟩ := hup s
      exact ⟨c, c', fun q => ⟨hc q, (hc' q).2⟩⟩)
  have hdeg := GlobalTheory.T.finrank_functionField_quotientSubfield_eq_degree hAr k X p D hX P hL e x hx
  have hg : (Module.finrank (ratF x) X.functionField : ℝ) / ((e : ℝ) ^ D * D.factorial) = gdeg P.L D / D.factorial := by
    have : (e : ℝ) ^ D ≠ 0 := pow_ne_zero _ (by exact_mod_cast he.ne')
    rw [hdeg]
    exact mul_div_mul_left _ _ this

  have hkey : ∀ s : ℕ, ∃ C : ℝ, 1 ≤ C ∧ ∀ q : ℕ, 1 ≤ e * q + s →
      P.H ((e * q + s : ℕ) : ℤ) 1 ≤
        AddSubgroup.closure (ballIn P (P.H ((e * q + s : ℕ) : ℤ) 1) ((e * q + s : ℕ) : ℤ) 1 (C ^ (e * q + s))) := by
    intro s
    classical
    obtain ⟨c, w, Cr, -, hrep⟩ := GlobalTheory.T.sections_eq_sum_aeval_boundedIntCoeff_ample k X p D hX P hL e x hx (s : ℤ) 1
    let Λ : ℕ → AddSubgroup X.functionField := fun q => P.H ((e : ℤ) * (q : ℤ) + (s : ℤ)) 1
    have hmul : ∀ q l, ∀ f ∈ Λ q, x l * f ∈ Λ (q + 1) := by
      intro q l f hf
      have h := (GlobalTheory.VolBr.NuMul.mul_mem_H_and_nu_mul k X p P _ _ _ _ _ _ (hx.mem l) hf).1
      show x l * f ∈ P.H _ 1
      exact mem_H_of_eq P (by push_cast; ring) (by ring) h
    have hrepr : ∀ q, ∀ f ∈ Λ q, ∃ T : Fin (Module.finrank (ratF x) X.functionField) → MvPolynomial (Fin (D + 1)) ℤ,
        (∀ i, (T i).IsHomogeneous (q + c)) ∧ f = ∑ i, MvPolynomial.aeval x (T i) * w i := by
      intro q f hf
      obtain ⟨T, h1, h2, -⟩ := hrep q f hf
      exact ⟨T, h1, h2⟩
    obtain ⟨G, hG, hcl⟩ := GlobalTheory.T.exists_finite_homogeneous_generators_graded_subgroup X.functionField D c x _ w Λ hmul hrepr
    have hb : ∀ (a b : ℤ) (f : X.functionField), f ∈ P.H a b → ∃ C : ℝ, 0 ≤ C ∧ ∀ σ y, P.nu a b σ y f ≤ C := by
      intro a b f hf
      obtain ⟨C, hC⟩ := ((GlobalTheory.T.continuous_hermSectionValue_mul_conj_and_norm_bounded k X p D hX P a b).2 f hf).2
      exact ⟨|C|, abs_nonneg _, fun σ y => (hC σ y).trans (le_abs_self _)⟩
    choose Cx hCx0 hCx using fun l => hb _ _ _ (hx.mem l)
    have hbG : ∀ g : ℕ × X.functionField, ∃ C : ℝ, 0 ≤ C ∧
        (g ∈ G → ∀ σ y, P.nu ((e : ℤ) * (g.1 : ℤ) + s) 1 σ y g.2 ≤ C) := by
      intro g
      by_cases hg : g ∈ G
      · obtain ⟨C, hC0, hC⟩ := hb _ _ _ (hG g hg)
        exact ⟨C, hC0, fun _ => hC⟩
      · exact ⟨0, le_rfl, fun h => absurd h hg⟩
    choose Cg hCg0 hCg using hbG
    have hC1 : 1 ≤ 1 + ∑ l, Cx l := le_add_of_nonneg_right (Finset.sum_nonneg fun l _ => hCx0 l)
    have hC2 : 1 ≤ 1 + ∑ g ∈ G, Cg g := le_add_of_nonneg_right (Finset.sum_nonneg fun g _ => hCg0 g)
    have hxl : ∀ l σ y, P.nu e 0 σ y (x l) ≤ 1 + ∑ l, Cx l := fun l σ y => (hCx l σ y).trans (by
      have := Finset.single_le_sum (fun j _ => hCx0 j) (Finset.mem_univ l); linarith)
    have hgl : ∀ g ∈ G, ∀ σ y, P.nu ((e : ℤ) * (g.1 : ℤ) + s) 1 σ y g.2 ≤ 1 + ∑ g ∈ G, Cg g :=
      fun g hg σ y => (hCg g hg σ y).trans (by
        have := Finset.single_le_sum (fun j _ => hCg0 j) hg; linarith)
    refine ⟨(1 + ∑ l, Cx l) * (1 + ∑ g ∈ G, Cg g), one_le_mul_of_one_le_of_one_le hC1 hC2, fun q hq => ?_⟩
    have e1 : ((e * q + s : ℕ) : ℤ) = (e : ℤ) * (q : ℤ) + (s : ℤ) := by push_cast; ring
    rw [e1]
    refine (hcl q).trans (AddSubgroup.closure_mono ?_)
    rintro f ⟨g, hg, α, hα, rfl⟩
    obtain ⟨h1, h2⟩ := mono_mem P e x hx.mem ((e : ℤ) * (g.1 : ℤ) + s) 1 g.2 (hG g hg) α Finset.univ
    have ea : (e : ℤ) * ((∑ l, α l : ℕ) : ℤ) + ((e : ℤ) * (g.1 : ℤ) + s) = (e : ℤ) * (q : ℤ) + (s : ℤ) := by
      rw [← hα]; push_cast; ring
    rw [ea] at h1 h2
    refine ⟨h1, fun σ y => ?_⟩
    rw [h2]
    have hnu0 : ∀ l, 0 ≤ P.nu e 0 σ y (x l) := fun l => nu_nonneg P _ _ σ y _
    have hqe : q ≤ e * q := Nat.le_mul_of_pos_left q he
    have hsum : ∑ l, α l ≤ e * q + s := by omega
    calc (∏ l, P.nu e 0 σ y (x l) ^ α l) * P.nu ((e : ℤ) * (g.1 : ℤ) + s) 1 σ y g.2
        ≤ (∏ l, (1 + ∑ l, Cx l) ^ α l) * (1 + ∑ g ∈ G, Cg g) :=
          mul_le_mul (Finset.prod_le_prod (fun l _ => pow_nonneg (hnu0 l) _)
            fun l _ => pow_le_pow_left₀ (hnu0 l) (hxl l σ y) _) (hgl g hg σ y) (nu_nonneg P _ _ σ y _)
            (Finset.prod_nonneg fun _ _ => pow_nonneg (by linarith) _)
      _ = (1 + ∑ l, Cx l) ^ (∑ l, α l) * (1 + ∑ g ∈ G, Cg g) := by rw [Finset.prod_pow_eq_pow_sum]
      _ ≤ (1 + ∑ l, Cx l) ^ (e * q + s) * (1 + ∑ g ∈ G, Cg g) ^ (e * q + s) :=
          mul_le_mul (pow_le_pow_right₀ hC1 hsum) (le_self_pow₀ hC2 (by omega)) (by linarith)
            (pow_nonneg (by linarith) _)
      _ = ((1 + ∑ l, Cx l) * (1 + ∑ g ∈ G, Cg g)) ^ (e * q + s) := (mul_pow _ _ _).symm
  choose Cs hCs1 hCs using hkey
  refine ⟨fun m => le_rfl, fun m => ?_, ⟨∑ s ∈ Finset.range e, Cs s, ?_, fun m hm => ?_⟩, ?_⟩
  · obtain ⟨c, hc⟩ := hup (m % e)
    have h := (hc (m / e)).1
    rw [Nat.div_add_mod] at h
    exact h
  · exact (hCs1 0).trans (Finset.single_le_sum (fun j _ => zero_le_one.trans (hCs1 j)) (Finset.mem_range.2 he))
  · have hs := Nat.mod_lt m he
    have h := hCs (m % e) (m / e) (by rw [Nat.div_add_mod]; exact hm)
    rw [Nat.div_add_mod] at h
    have hle : Cs (m % e) ≤ ∑ s ∈ Finset.range e, Cs s :=
      Finset.single_le_sum (fun j _ => zero_le_one.trans (hCs1 j)) (Finset.mem_range.2 hs)
    refine h.trans (AddSubgroup.closure_mono ?_)
    rintro f ⟨hf, hf'⟩
    exact ⟨hf, fun σ y => (hf' σ y).trans (pow_le_pow_left₀ (zero_le_one.trans (hCs1 _)) hle _)⟩
  · rw [← hg]
    exact hrank

end GlobalTheory.HSAmp.GoodH
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenSymplecticLevelLocusStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_symplecticLevel_locus : ∀ (h M : ℕ) (S' : Scheme.{0}) [IsLocallyNoetherian S'] (t : S' ⟶ Sp (cycAway M)) (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S') ⟶ G)), IsAbelianScheme G → P.IsLB → (∃ s : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, s.IsGen) → (∃ s : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, s.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → 3 ≤ M → Odd M → (∀ a b, lev (a + b) = lev a * lev b) → (∀ a, lev a ^ M = 1) → ∃ U : S'.Opens, (∀ V : S'.Opens, V ≤ U → IsSympLev (P.pull (Pdiv.PullbackComparison.pφ₂ V.ι G)) h M (zetaAway M) (V.ι ≫ t) (fun a => GlobalTheory.SiegelPull.secPull (Pdiv.PullbackComparison.isGrpPullback V.ι G) (lev a))) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S') (c' : SiegPre h M (zetaAway M) (g ≫ t)) (φ : c'.A.left ⟶ G.left) (φ₂ : (G2 c'.A).left ⟶ (G2 G).left), IsGrpPullback c'.A G g φ → IsSquare φ φ₂ → LBIso c'.P (P.pull φ₂) → (∀ a, (c'.lev a).left ≫ φ = g ≫ (lev a).left) → Set.range g.base ⊆ (U : Set S') := by
  first | (exact @GlobalTheory.SympLevLocus.exists_open_sympLev) | (exact GlobalTheory.SympLevLocus.exists_open_sympLev) | (intros; apply GlobalTheory.SympLevLocus.exists_open_sympLev  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperRelAmpleKTrivOfTrivialisationsGenerateStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProper_relAmple_kTriv_of_trivialisations_generate : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (f : R), (∀ y, PsiUnitOn P.D.toPre y (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R))) → ∀ tO : SAB H (Sp (Localization.Away f)), SABMap tO t (spMap (algebraMap R (Localization.Away f))) → IsProper tO.G.hom ∧ Out.RelAmple tO.G tO.PP.L ∧ Out.KTriv tO.G tO.PP.L := by
  first | exact @GlobalTheory.UCanon.Principal.isProper_relAmple_kTriv_of_psiUnitOn | exact GlobalTheory.UCanon.Principal.isProper_relAmple_kTriv_of_psiUnitOn | (intros; apply GlobalTheory.UCanon.Principal.isProper_relAmple_kTriv_of_psiUnitOn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsionFrameSqOfTorsionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTorsionFrame_sq_of_torsion : ∀ (S : Scheme.{0}) (P : PolAV S) (rig : LB.Gen (P.L.pull (eSec P.A))) (n : ℕ) (T : Over S) (x : T ⟶ P.A) (τ : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => 1))), IsTorsFrame P rig n x τ → IsTorsFrame P rig (n ^ 2) x τ := by
  first | exact @GlobalTheory.USep.isTorsFrame_sq | exact GlobalTheory.USep.isTorsFrame_sq | (intros; apply GlobalTheory.USep.isTorsFrame_sq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitCoefficientOfThetaSquareIntegralTorsionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Sep.Frames GlobalTheory.UT.CoefBasic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_coefficient_of_thetaSquare_integralTorsion : ∀ (N₁ : ℕ), 2 ≤ N₁ → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ →
    (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁)
    (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))),
    (∀ (R' : Type) [CommRing R'] (f : V₁ →+* R') θ',
      IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' →
      GlobalTheory.Poinc.ThetaOne.OneBasisAt D f θ') →
    ∀ (C : Type) (b : C → (𝟙_ (Over (Sp V₁)) ⟶ D.P.A)),
    (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp V₁) (p : Over.mk x ⟶ D.P.A), p ^ N₁ = 1 →
      ∃ c, p = toUnit _ ≫ b c) →
    ∃ c₁ : C, ∀ (G : V₁) (U : ∀ (Z : Scheme.{0}) (_ : Z ⟶ Sp V₁) (z : Z) (_ : (Z ⟶ D.P.A.left) → D.P.L.ι),
        (Z.presheaf.stalk z)ˣ),
      (∀ (Z : Scheme.{0}) (r : Z ⟶ Sp V₁) (z : Z) J, Good D.P.L z J →
        gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V₁)).inv.hom G) =
          sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (r ≫ (b c₁).left) z J ^ 2 *
            (U Z r z J).val) → IsUnit G := by
  first | exact @GlobalTheory.Poinc.Sep.CoefInt.isUnit_of_theta_sq | exact GlobalTheory.Poinc.Sep.CoefInt.isUnit_of_theta_sq | (intros; apply GlobalTheory.Poinc.Sep.CoefInt.isUnit_of_theta_sq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitTauScaledGeneratorTorusMonomialStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnitTau_scaledGenerator_torusMonomial : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
    (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (C : MonoFam Xo c φ R) (N : ℕ) (s : Fin C.m ⊕ Fin N → R)
    (ε : Module.Basis (Fin C.m ⊕ Fin N) ℤ (balForms H.bar C.P.D.toPre.X)) (τ₀ : Gens C.P.D.toPre),
    (∀ i, s (.inl i) = C.s i) → (∀ i, (ε (.inl i) : LinearMap.BilinForm ℤ _) = C.δ i) →
    TauIn C.P.D.toPre τ₀ (fun k => s (finSumFinEquiv.symm k))
      (fun k => (l.M' : ℤ) • (ε (finSumFinEquiv.symm k) : LinearMap.BilinForm ℤ C.P.D.toPre.X)) →
    ∀ (u : Fin N → Rˣ), (∀ k, (u k : R) = s (.inr k)) → ∀ a b,
      GlobalTheory.RigChart.IsUnitTau C.P.D.toPre C.s (fun i => (l.M' : ℤ) • C.δ i) a b
        (ReciprocityTheory.ChartRestriction.G.DVR.scaleGen
          (unitOn (∏ k, u k ^ ((l.M' : ℤ) * (ε (.inr k) : LinearMap.BilinForm ℤ C.P.D.toPre.X) a b))) (τ₀ a b)) := by
  first | exact @GlobalTheory.UCanon.ScaleTorus.isUnitTau_scaleGen | exact GlobalTheory.UCanon.ScaleTorus.isUnitTau_scaleGen | (intros; apply GlobalTheory.UCanon.ScaleTorus.isUnitTau_scaleGen <;> assumption)
end

