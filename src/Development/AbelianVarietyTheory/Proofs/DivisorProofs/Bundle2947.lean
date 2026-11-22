import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2845
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2753
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataBaseChangeSymmetric
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2813
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1540
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2739
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2757
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2825
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2868
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2835
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2844
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareApproxValuesAtPointOfElements
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2846
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsTauZeroNonzeroAll
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2114
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KronHolPsiStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CuspStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0038
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0037
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0026
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1528
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0946
import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0084
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0089
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2847
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodRelationPullbackMonomialConstantsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.PrimCocycle
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_relation_pullback_monomial_constants : ∀ (n : ℕ) (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (r : ℕ) (e₀ : (Fin r → ℤ) ≃+ D.X) {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (V₁ : Type) [CommRing V₁] [IsDomain V₁] (f₁ : V →+* V₁) (κ₁ : W →+* V₁) (e : (Fin T.r → ℤ) ≃+ (Fin r → ℤ)) (B' : Over (Sp V₁)) [GrpObj B'] (β₂ : (G2 B').left ⟶ (G2 D.P.A).left) (β₂' : (G2 B').left ⟶ (G2 T.B).left) (x : (Fin T.r → ℤ) → (𝟙_ (Over (Sp V₁)) ⟶ B')) (w₁ : LB.Iso ((abelian₂ D.P.A D.P.L).pull β₂) ((abelian₂ T.B T.M.L).pull β₂')) (q : (Fin T.r → ℤ) → (Fin T.r → ℤ) → (FractionRing V₁)ˣ), Function.Injective f₁ → PeriodRel D T f₁ κ₁ w₁ (e.trans e₀) x n q → ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] (f₂ : V₁ →+* V₂) (fK : FractionRing V₁ →+* FractionRing V₂) {I : Type} [Fintype I] (s : I → V₂) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)), (∀ a, fK (algebraMap V₁ _ a) = algebraMap V₂ _ (f₂ a)) → (∀ a b, fK (q a b : FractionRing V₁) = ∏ k, algebraMap V₂ _ (s k) ^ ((n : ℤ) * ε k a b)) → ∀ (D' : DegPre V₂) (hD : IsPullDeg (f₂.comp f₁) D D') (Φ : D'.P.A.left ⟶ B'.left) (gΦ : IsGrpPullback D'.P.A B' (spMap f₂) Φ), (∀ a, (D'.c a).left ≫ Φ = spMap f₂ ≫ (x (hD.xe.trans (e₀.symm.trans e.symm) a)).left) → ∀ (w : LB.Iso (abelian₂ D'.P.A D'.P.L) ((abelian₂ T.B T.M.L).pull (GlobalTheory.HalfBC.sqOf gΦ ≫ β₂'))), (∀ (Z : Scheme.{0}) (p : Z ⟶ (G2 D'.P.A).left) (z : Z) (J : (Z ⟶ T.B.left) → T.M.L.ι) (J₁ : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D'.P.A.left) → D'.P.L.ι), Good T.M.L z J → Good D.P.L z J₁ → Good D'.P.L z J' → lamVal w p z J J' = isoVal w₁ (p ≫ GlobalTheory.HalfBC.sqOf gΦ) z J J₁ * ∏ I, gw hD.w (p ≫ lamφ D'.P.A I) z (J₁ ((p ≫ lamφ D'.P.A I) ≫ GlobalTheory.PsiEvenPull.proj hD)) (J' (p ≫ lamφ D'.P.A I)) ^ lamε I) → ∀ a b : D'.X, ∃ k : (FractionRing V₂)ˣ, (k : FractionRing V₂) = ∏ i, algebraMap V₂ (FractionRing V₂) (s i) ^ ((n : ℤ) * ε i (hD.xe.trans (e₀.symm.trans e.symm) a) (hD.xe.trans (e₀.symm.trans e.symm) b)) ∧ ∀ z J J', Good T.M.L z J → Good D'.P.L z J' → val (D'.tau a b) (𝟙 _) z J' = gm (𝟙 (TK V₂).left) z ⊤ (unitOn k) * (lamVal w (lift (toUnit (TK V₂) ≫ D'.c a) (toUnit (TK V₂) ≫ D'.c b)).left z J J' * val (T.τ₀ ((n : ℤ) • hD.xe.trans (e₀.symm.trans e.symm) a) ((n : ℤ) • hD.xe.trans (e₀.symm.trans e.symm) b)) ((TK V₂).hom ≫ spMap (f₂.comp κ₁)) z J) := by
  first | exact @GlobalTheory.PeriodPull.periods_pull | exact GlobalTheory.PeriodPull.periods_pull | (intros; apply GlobalTheory.PeriodPull.periods_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodsOfGoodReductionModel
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

set_option autoImplicit false
noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PeriodDet

theorem multilinear_ext_of {K M N : Type} [CommSemiring K] [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N]
    {J : Type} [Fintype J] [DecidableEq J] (S : Set M)
    (hS : ∀ l₁ l₂ : M →ₗ[K] N, (∀ x ∈ S, l₁ x = l₂ x) → l₁ = l₂)
    (f g : MultilinearMap K (fun _ : J ↦ M) N) (h : ∀ v, (∀ i, v i ∈ S) → f v = g v) : f = g := by
  have key : ∀ s : Finset J, ∀ v : J → M, (∀ i ∉ s, v i ∈ S) → f v = g v := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro v hv; exact h v (fun i ↦ hv i (by simp))
    | insert i s hi ih =>
      intro v hv
      have hl := hS (f.toLinearMap v i) (g.toLinearMap v i) (fun x hx ↦ by
        simp only [MultilinearMap.toLinearMap_apply]
        apply ih
        intro j hj
        by_cases hji : j = i
        · subst hji; simpa using hx
        · rw [Function.update_of_ne hji]; exact hv j (by simp [hji, hj]))
      have h2 := LinearMap.congr_fun hl (v i)
      simpa [MultilinearMap.toLinearMap_apply, Function.update_eq_self] using h2
  ext v
  exact key Finset.univ v (by simp)

open GlobalTheory.RealMult.Obj in

theorem exists_detGen_isDet : GlobalTheory.Published.AbelianDeRham → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ)
    (L : Set E) (𝔠 : FracId (FR E)) (R : Subring ℂ) [IsDiscreteValuationRing R]
    (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ L 0 X)
    (p : X.A.left ⟶ X₀.A.left), X.IsPullBy X₀ (spMap R.subtype) p →
    ∀ (e : I → (X₀.Lie →ₗ[R] R)) (a : I → ℂ), (∀ i, GlobalTheory.LatModel.IsPeriodGen X₀ U p i (e i) (a i)) →
    ∀ (δ₀ : X₀.DetGen) (u₀ : R), u₀ ≠ 0 →
      (Matrix.detRowAlternating.compLinearMap (LinearMap.pi fun k ↦ e (U.e k)) : X₀.DetOmega) = u₀ • δ₀.1 →
    ∃ δ : X.DetGen, Obj.DetCorr R.subtype p δ₀.1 δ.1 ∧ U.IsDet δ.1 ((∏ i, a i) / (u₀ : ℂ)) := by
  intro _hAb E _ _ _ I _ φ L 𝔠 R _ X₀ X U p hp e a ha δ₀ u₀ hu₀ heq
  classical
  letI : Algebra R ℂ := R.subtype.toAlgebra
  obtain ⟨δ, hδ, -⟩ := Obj.IsPullBy.existsUnique_detGen R.subtype hp δ₀
  obtain ⟨eL, heL, -⟩ := Obj.exists_lieEquiv (R := R) (R' := ℂ) (φ := p) hp
  obtain ⟨h1, h2⟩ := UnifTangent.tangent_bijection U.u X.dim
  have hb : ∀ k : Fin (Module.finrank ℚ (FR E)), ∃ t : X.Lie, U.u.IsDiff (Pi.single k 1) t.hom := fun k ↦ by
    obtain ⟨t, ⟨ht, hd⟩, -⟩ := h2 (Pi.single k 1)
    exact ⟨Serre.Lie.mk X.rm t ht, hd⟩
  choose b hb using hb
  let T : (Fin (Module.finrank ℚ (FR E)) → ℂ) →ₗ[ℂ] X.Lie := Fintype.linearCombination ℂ b
  have hT : ∀ w, U.u.IsDiff w (T w).hom := fun w ↦ by
    have hc : IsLieComb w (fun k ↦ (b k).hom) (T w).hom := by
      rw [Serre.Lie.isLieComb_iff]
      simp [T, Fintype.linearCombination_apply]
    have := UnifDifferential.isDiff_of_isLieComb X.A (X.diag U.c) _ _ U.u (fun k ↦ Pi.single k 1) (fun k ↦ (b k).hom) w
      (T w).hom (fun k ↦ (b k).isTangent) hb hc
    convert this using 1
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  have hTu : ∀ (w : Fin (Module.finrank ℚ (FR E)) → ℂ) (v : X.Lie), U.u.IsDiff w v.hom → v = T w := fun w v hw ↦
    Serre.Lie.ext ((h2 w).unique ⟨v.isTangent, hw⟩ ⟨(T w).isTangent, hT w⟩)
  have hTinj : Function.Injective T := fun w w' h ↦
    (h1 (T w).hom (T w).isTangent).unique (hT w) (h ▸ hT w')
  have hTsurj : Function.Surjective T := fun v ↦ by
    obtain ⟨w, hw, -⟩ := h1 v.hom v.isTangent
    exact ⟨w, (hTu w v hw).symm⟩
  let Te := LinearEquiv.ofBijective T ⟨hTinj, hTsurj⟩
  have hS : ∀ l₁ l₂ : X.Lie →ₗ[ℂ] ℂ, (∀ x ∈ Set.range (fun y : X₀.Lie ↦ eL (1 ⊗ₜ y)), l₁ x = l₂ x) → l₁ = l₂ := by
    intro l₁ l₂ h
    have hc : l₁ ∘ₗ eL.toLinearMap = l₂ ∘ₗ eL.toLinearMap := by
      apply TensorProduct.AlgebraTensorModule.ext
      intro x y
      have hx : x ⊗ₜ[R] y = x • ((1 : ℂ) ⊗ₜ[R] y) := by rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, hx, map_smul]
      rw [h _ ⟨y, rfl⟩]
    refine LinearMap.ext fun x ↦ ?_
    simpa using LinearMap.congr_fun hc (eL.symm x)
  let eh : I → X.Lie →ₗ[ℂ] ℂ := fun i ↦
    (LinearMap.liftBaseChange ℂ ((Algebra.linearMap R ℂ) ∘ₗ e i)) ∘ₗ eL.symm.toLinearMap
  have heh : ∀ i y, eh i (eL (1 ⊗ₜ y)) = ((e i y : R) : ℂ) := by
    intro i y
    simp [eh, LinearMap.liftBaseChange_tmul]
    rfl

  have hper : ∀ i, eh i = (a i • LinearMap.proj (U.e.symm i)) ∘ₗ Te.symm.toLinearMap := by
    intro i
    apply hS
    rintro _ ⟨y, rfl⟩
    have hW : U.u.IsDiff (Te.symm (eL (1 ⊗ₜ y))) (eL (1 ⊗ₜ y)).hom := by
      have h3 := hT (Te.symm (eL (1 ⊗ₜ y)))
      have h4 : T (Te.symm (eL (1 ⊗ₜ y))) = eL (1 ⊗ₜ y) := Te.apply_symm_apply _
      rwa [h4] at h3
    rw [heh]
    have h5 := ha i y (eL (1 ⊗ₜ y)) _ ((heL _ _).2 rfl) hW
    rw [h5]
    simp
  let D : X.DetOmega := Matrix.detRowAlternating.compLinearMap (LinearMap.pi fun k ↦ eh (U.e k))
  have hD : ((u₀ : ℂ) • δ.1 : X.DetOmega) = D := by
    apply AlternatingMap.coe_multilinearMap_injective
    apply PeriodDet.multilinear_ext_of _ hS
    intro v hv
    choose y hy using hv
    obtain rfl : v = fun j ↦ eL (1 ⊗ₜ y j) := funext fun j ↦ (hy j).symm
    have hc := hδ y (fun j ↦ eL (1 ⊗ₜ y j)) (fun j ↦ (heL _ _).2 rfl)
    have hq : (Matrix.detRowAlternating.compLinearMap (LinearMap.pi fun k ↦ e (U.e k)) : X₀.DetOmega) y =
        (u₀ • δ₀.1) y := DFunLike.congr_fun heq y
    have hD1 : D (fun j ↦ eL (1 ⊗ₜ y j)) =
        R.subtype ((Matrix.detRowAlternating.compLinearMap (LinearMap.pi fun k ↦ e (U.e k)) : X₀.DetOmega) y) := by
      change Matrix.det (fun j ↦ (LinearMap.pi fun k ↦ eh (U.e k)) (eL (1 ⊗ₜ y j))) =
        R.subtype (Matrix.det (fun j ↦ (LinearMap.pi fun k ↦ e (U.e k)) (y j)))
      refine Eq.trans ?_ (RingHom.map_det R.subtype _).symm
      congr 1
      ext j k
      exact heh _ _
    simp only [AlternatingMap.coe_multilinearMap, AlternatingMap.smul_apply, smul_eq_mul]
    rw [hc, hD1, hq]
    simp
  refine ⟨δ, hδ, fun v W hW ↦ ?_⟩
  have hv : ∀ j, Te.symm (v j) = W j := fun j ↦ by
    rw [hTu (W j) (v j) (hW j)]
    exact Te.symm_apply_apply (W j)
  have hu : (u₀ : ℂ) ≠ 0 := fun h ↦ hu₀ (Subtype.ext h)
  have hDv : D v = (∏ i, a i) * W.det := by
    change Matrix.det (fun j ↦ (LinearMap.pi fun k ↦ eh (U.e k)) (v j)) = _
    have hM : (fun j ↦ (LinearMap.pi fun k ↦ eh (U.e k)) (v j)) = Matrix.of fun j k ↦ a (U.e k) * W j k := by
      funext j k
      rw [Matrix.of_apply, LinearMap.pi_apply, hper]
      simp [hv]
    rw [hM, Matrix.det_mul_row, Equiv.prod_comp U.e a]
  have h6 := DFunLike.congr_fun hD v
  rw [AlternatingMap.smul_apply, hDv, smul_eq_mul] at h6
  field_simp
  linear_combination h6

end GlobalTheory.PeriodDet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodsSumDegenerationDataFstCubeIso
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

namespace GlobalTheory.MumProd.SumTau

theorem prod_subsets_two {M : Type} [CommMonoid M] (F : ULift.{0} (Finset (Fin 2)) → M) :
    ∏ I, F I = F ⟨∅⟩ * F ⟨{0}⟩ * F ⟨{1}⟩ * F ⟨{0, 1}⟩ := by
  have h : (Finset.univ : Finset (ULift.{0} (Finset (Fin 2)))) = {⟨∅⟩, ⟨{0}⟩, ⟨{1}⟩, ⟨{0, 1}⟩} := by decide
  rw [h, Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton, _root_.mul_assoc, _root_.mul_assoc]

def unitAt {X X₁ X₂ Z : Scheme.{0}} {L : LB X} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : X ⟶ X₁} {f₂ : X ⟶ X₂}
    (w : LB.Iso L (extLB L₁ L₂ f₁ f₂)) (z : Z) (J : (Z ⟶ X) → L.ι) (J₁ : (Z ⟶ X₁) → L₁.ι)
    (J₂ : (Z ⟶ X₂) → L₂.ι) (f : Z ⟶ X) : (Z.presheaf.stalk z)ˣ :=
  gm f z _ (w.s (extIdx (f₁ := f₁) (f₂ := f₂) (J₁ (f ≫ f₁)) (J₂ (f ≫ f₂)), J f))

theorem unitAt_of {X X₁ X₂ Z : Scheme.{0}} {L : LB X} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : X ⟶ X₁} {f₂ : X ⟶ X₂}
    (w : LB.Iso L (extLB L₁ L₂ f₁ f₂)) (z : Z) (J : (Z ⟶ X) → L.ι) (J₁ : (Z ⟶ X₁) → L₁.ι)
    (J₂ : (Z ⟶ X₂) → L₂.ι) (f g : Z ⟶ X) (j : L.ι) (j₁ : L₁.ι) (j₂ : L₂.ι) (hg : g = f) (h : J f = j)
    (h₁ : J₁ (f ≫ f₁) = j₁) (h₂ : J₂ (f ≫ f₂) = j₂) :
    gm g z _ (w.s (extIdx (f₁ := f₁) (f₂ := f₂) j₁ j₂, j)) = unitAt w z J J₁ J₂ f := by
  subst hg h h₁ h₂
  rfl

theorem mapsAt_unitAt {Y X X₁ X₂ Z : Scheme.{0}} {L : LB X} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : X ⟶ X₁} {f₂ : X ⟶ X₂}
    {w : LB.Iso L (extLB L₁ L₂ f₁ f₂)} {p : Y ⟶ X} {n : ℤ}
    {a : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => p) (fun _ => n))}
    {b₁ : LB.Gen (LB.LinComb L₁ (K := PUnit) (fun _ => p ≫ f₁) (fun _ => n))}
    {b₂ : LB.Gen (LB.LinComb L₂ (K := PUnit) (fun _ => p ≫ f₂) (fun _ => n))} (h : MapsAt₂ w p n a b₁ b₂)
    (r : Z ⟶ Y) {z : Z} {J : (Z ⟶ X) → L.ι} {J₁ : (Z ⟶ X₁) → L₁.ι} {J₂ : (Z ⟶ X₂) → L₂.ι}
    (hJ : Good L z J) (hJ₁ : Good L₁ z J₁) (hJ₂ : Good L₂ z J₂) :
    val b₁ r z J₁ * val b₂ r z J₂ = unitAt w z J J₁ J₂ (r ≫ p) ^ n * val a r z J :=
  (GlobalTheory.MumProd.mapsAt₂_val _ _ _ _ _ _ _ _ _ _ w p n a b₁ b₂ h r z J J₁ J₂ hJ hJ₁ hJ₂).trans
    (congrArg (· ^ n * val a r z J) (unitAt_of w z J J₁ J₂ _ _ _ _ _ rfl rfl
      (by rw [Category.assoc]) (by rw [Category.assoc])))

theorem val_tau {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} (D : DegData R I) (a b : D.toPre.X)
    {z : (TK R).left} {J : ((TK R).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι} (hJ : Good D.toPre.P.L z J) :
    val ((pol D).tau a b) (𝟙 _) z J = val (D.toPre.psi (a + b)) (𝟙 _) z J * (val (D.toPre.psi a) (𝟙 _) z J)⁻¹ *
      (val (D.toPre.psi b) (𝟙 _) z J)⁻¹ * (val D.toPre.rigK (𝟙 _) z J)⁻¹ := by
  refine ((GlobalTheory.PolDeg.Wit.exists_tau D.toPre a b).choose_spec.2 _ (𝟙 _) z J hJ).trans ?_
  unfold DegPre.tau
  rw [val_mul hJ, val_mul hJ, val_mul hJ, val_inv, val_inv, val_inv]

section Psum

variable {S : Scheme.{0}} (G : Over S) [GrpObj G] {T : Over S} (x : Fin 2 → (T ⟶ G))

theorem psum_empty : psum G x ∅ = toUnit T ≫ η[G] := rfl

theorem psum_zero : psum G x {0} = x 0 := by
  show lift (x 0) (toUnit T ≫ η[G]) ≫ μ[G] = x 0
  exact lift_comp_one_right _ _

theorem psum_one : psum G x {1} = x 1 := by
  show lift (x 1) (toUnit T ≫ η[G]) ≫ μ[G] = x 1
  exact lift_comp_one_right _ _

theorem psum_pair : psum G x {0, 1} = padd G (x 0) (x 1) := by
  show padd G (x 0) (lift (x 1) (toUnit T ≫ η[G]) ≫ μ[G]) = _
  rw [lift_comp_one_right]

theorem comp_padd' {T' : Over S} (g : T' ⟶ T) (a b : T ⟶ G) : g ≫ padd G a b = padd G (g ≫ a) (g ≫ b) := by
  unfold padd
  rw [comp_lift_assoc]

end Psum

end GlobalTheory.MumProd.SumTau

namespace GlobalTheory.MumProd

open SumTau in

theorem tau_sum_fst : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D₁ D₂ : DegData R I) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X), IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ → ∀ (i₁ : D₁.toPre.P.A ⟶ D.toPre.P.A) (j₁ : D₁.toPre.X →+ D.toPre.X), i₁ ≫ p₁ = 𝟙 _ → i₁ ≫ p₂ = toUnit _ ≫ η[D₂.toPre.P.A] → (∀ y, q₁ (j₁ y) = y) → (∀ y, q₂ (j₁ y) = 0) → ∀ (wM : LB.Iso D.toPre.P.L (extLB D₁.toPre.P.L D₂.toPre.P.L p₁.left p₂.left)), wM.IsGen → (∃ b₁ b₂, MapsAt₂ wM (eSec D.toPre.P.A) 1 D.toPre.rig b₁ b₂ ∧ LB.Gen.Corr D₁.toPre.P.L _ _ _ _ b₁ D₁.toPre.rig ∧ LB.Gen.Corr D₂.toPre.P.L _ _ _ _ b₂ D₂.toPre.rig) → (∀ x, ∃ b₁ b₂, MapsAt₂ wM (D.toPre.xK x) (-1) (D.toPre.psi x) b₁ b₂ ∧ LB.Gen.Corr D₁.toPre.P.L _ _ _ _ b₁ (D₁.toPre.psi (q₁ x)) ∧ LB.Gen.Corr D₂.toPre.P.L _ _ _ _ b₂ (D₂.toPre.psi (q₂ x))) → ∀ (w : LB.Iso (cubeLB D.toPre.P.A ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] D.toPre.P.L) (cubeLB D₁.toPre.P.A ![fst D₁.toPre.P.A D.toPre.P.A, snd D₁.toPre.P.A D.toPre.P.A ≫ p₁] D₁.toPre.P.L)), (∀ (Z : Scheme.{0}) (f : Z ⟶ (D₁.toPre.P.A ⊗ D.toPre.P.A).left) (z : Z) (jC : ULift.{0} (Finset (Fin 2)) → D₁.toPre.P.L.ι) (jA : ULift.{0} (Finset (Fin 2)) → D.toPre.P.L.ι) (β : ULift.{0} (Finset (Fin 2)) → D₂.toPre.P.L.ι), f z ∈ (cubeLB D₁.toPre.P.A ![fst D₁.toPre.P.A D.toPre.P.A, snd D₁.toPre.P.A D.toPre.P.A ≫ p₁] D₁.toPre.P.L).U jC → f z ∈ (cubeLB D.toPre.P.A ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] D.toPre.P.L).U jA → (∀ I, (f ≫ (psum D.toPre.P.A ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] I.down).left ≫ p₂.left) z ∈ D₂.toPre.P.L.U (β I)) → (∀ I, β I = β ⟨insert 0 I.down⟩) → gm f z _ (w.s (jC, jA)) = ∏ I, gm (f ≫ (psum D.toPre.P.A ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] I.down).left) z _ (wM.s (extIdx (f₁ := p₁.left) (f₂ := p₂.left) (jC I) (β I), jA I)) ^ ((-1 : ℤ) ^ (2 - I.down.card))) → ∀ (y : D₁.toPre.X) (y' : D.toPre.X) (z : (TK R).left) (J₁ : ((TK R).left ⟶ D₁.toPre.P.A.left) → D₁.toPre.P.L.ι) (J₂ : ((TK R).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Good D₁.toPre.P.L z J₁ → Good D.toPre.P.L z J₂ → val ((pol D).tau (j₁ y) y') (𝟙 _) z J₂ = adjVal w (lift (toUnit (TK R) ≫ D₁.toPre.c y) (toUnit (TK R) ≫ D.toPre.c y')).left z J₁ J₂ * val ((pol D₁).tau y (q₁ y')) (𝟙 _) z J₁ := by
  intro R _ _ I D D₁ D₂ p₁ p₂ q₁ q₂ hS i₁ j₁ hi₁ hi₂ hj₁ hj₂ wM _ hrig hpsi w hw y y' z J₁ J₂ hJ₁ hJ₂
  obtain ⟨J₃, hJ₃⟩ := GlobalTheory.ChartCmp.CarryCalc.exists_good' D₂.toPre.P.isLB z
  have ψ : ∀ x, val (D₁.toPre.psi (q₁ x)) (𝟙 _) z J₁ * val (D₂.toPre.psi (q₂ x)) (𝟙 _) z J₃ =
      (unitAt wM z J₂ J₁ J₃ (D.toPre.xK x))⁻¹ * val (D.toPre.psi x) (𝟙 _) z J₂ := by
    intro x
    obtain ⟨b₁, b₂, hm, c₁, c₂⟩ := hpsi x
    have e := mapsAt_unitAt hm (𝟙 _) hJ₂ hJ₁ hJ₃
    rw [val_corr hJ₁ c₁, val_corr hJ₃ c₂, Category.id_comp, zpow_neg_one] at e
    exact e
  have ρ : val D₁.toPre.rigK (𝟙 _) z J₁ * val D₂.toPre.rigK (𝟙 _) z J₃ =
      unitAt wM z J₂ J₁ J₃ (toUnit (TK R) ≫ η[D.toPre.P.A]).left * val D.toPre.rigK (𝟙 _) z J₂ := by
    obtain ⟨b₁, b₂, hm, c₁, c₂⟩ := hrig
    have e := mapsAt_unitAt hm (toUnit (TK R)).left hJ₂ hJ₁ hJ₃
    rw [val_corr hJ₁ c₁, val_corr hJ₃ c₂, zpow_one] at e
    unfold DegPre.rigK
    rw [val_pull hJ₁, val_pull hJ₃, val_pull hJ₂, Category.id_comp]
    exact e
  have z₂ := GlobalTheory.MumFam.val_psi_zero_mul_rigK R D₂.toPre D₂.tau_bimult z J₃ hJ₃
  have hc := GlobalTheory.MumProd.c_inc_fst R D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ hS i₁ j₁ hi₁ hi₂ hj₁ hj₂ y
  have h1 := GlobalTheory.MumProd.PsumMap.psum_comp_hom _ D.toPre.P.A D₁.toPre.P.A _ 2 p₁
    ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A]
    ![fst D₁.toPre.P.A D.toPre.P.A, snd D₁.toPre.P.A D.toPre.P.A ≫ p₁] hS.hom₁
    (by intro i; fin_cases i <;> simp [hi₁])
  have h2 := GlobalTheory.MumProd.PsumCancel.psum_insert_zero_comp _ D.toPre.P.A D₂.toPre.P.A _ p₂
    ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] hS.hom₂
    (by
      show (fst D₁.toPre.P.A D.toPre.P.A ≫ i₁) ≫ p₂ = _
      rw [Category.assoc, hi₂, ← Category.assoc, comp_toUnit])
  have K : adjVal w (lift (toUnit (TK R) ≫ D₁.toPre.c y) (toUnit (TK R) ≫ D.toPre.c y')).left z J₁ J₂ =
      unitAt wM z J₂ J₁ J₃ (toUnit (TK R) ≫ η[D.toPre.P.A]).left * (unitAt wM z J₂ J₁ J₃ (D.toPre.xK (j₁ y)))⁻¹ *
        (unitAt wM z J₂ J₁ J₃ (D.toPre.xK y'))⁻¹ * unitAt wM z J₂ J₁ J₃ (D.toPre.xK (j₁ y + y')) := by
    have s₀ : lift (toUnit (TK R) ≫ D₁.toPre.c y) (toUnit (TK R) ≫ D.toPre.c y') ≫
        fst D₁.toPre.P.A D.toPre.P.A ≫ i₁ = toUnit (TK R) ≫ D.toPre.c (j₁ y) := by
      rw [lift_fst_assoc, hc, Category.assoc]
    have s₁ : lift (toUnit (TK R) ≫ D₁.toPre.c y) (toUnit (TK R) ≫ D.toPre.c y') ≫
        snd D₁.toPre.P.A D.toPre.P.A = toUnit (TK R) ≫ D.toPre.c y' := lift_snd _ _
    generalize lift (toUnit (TK R) ≫ D₁.toPre.c y) (toUnit (TK R) ≫ D.toPre.c y') = P at s₀ s₁ ⊢
    have mC := Good.mem hJ₁ (fun I : ULift.{0} (Finset (Fin 2)) => (psum D₁.toPre.P.A
      ![fst D₁.toPre.P.A D.toPre.P.A, snd D₁.toPre.P.A D.toPre.P.A ≫ p₁] I.down).left) P.left
    have mA := Good.mem hJ₂ (fun I : ULift.{0} (Finset (Fin 2)) => (psum D.toPre.P.A
      ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] I.down).left) P.left
    have e := hw _ P.left z _ _ (fun I => J₃ (P.left ≫ (psum D.toPre.P.A
      ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] I.down).left ≫ p₂.left)) mC mA
      (fun I => hJ₃ _) (fun I => by
        show J₃ _ = J₃ _
        rw [← Over.comp_left, ← Over.comp_left, h2 I.down]
        rfl)
    refine e.trans ?_
    have e' : ∀ I : ULift.{0} (Finset (Fin 2)), gm (P.left ≫ (psum D.toPre.P.A
        ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] I.down).left) z _
        (wM.s (extIdx (f₁ := p₁.left) (f₂ := p₂.left) (J₁ (P.left ≫ (psum D₁.toPre.P.A
          ![fst D₁.toPre.P.A D.toPre.P.A, snd D₁.toPre.P.A D.toPre.P.A ≫ p₁] I.down).left))
          (J₃ (P.left ≫ (psum D.toPre.P.A
            ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] I.down).left ≫ p₂.left)),
          J₂ (P.left ≫ (psum D.toPre.P.A
            ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] I.down).left))) =
        unitAt wM z J₂ J₁ J₃ (P ≫ psum D.toPre.P.A
          ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] I.down).left := fun I =>
      unitAt_of wM z J₂ J₁ J₃ _ _ _ _ _ rfl rfl
        (by rw [← h1 I.down, Over.comp_left, Over.comp_left, Category.assoc])
        (by rw [Over.comp_left, Category.assoc])
    refine (Finset.prod_congr rfl fun I _ => congrArg (· ^ ((-1 : ℤ) ^ (2 - I.down.card))) (e' I)).trans ?_
    rw [prod_subsets_two]
    have t₀ : P ≫ psum D.toPre.P.A ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] ∅ =
        toUnit (TK R) ≫ η[D.toPre.P.A] := by
      rw [psum_empty, ← Category.assoc, comp_toUnit]
    have t₁ : P ≫ psum D.toPre.P.A ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] {0} =
        toUnit (TK R) ≫ D.toPre.c (j₁ y) := by
      rw [psum_zero]; exact s₀
    have t₂ : P ≫ psum D.toPre.P.A ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] {1} =
        toUnit (TK R) ≫ D.toPre.c y' := by
      rw [SumTau.psum_one]; exact s₁
    have t₃ : P ≫ psum D.toPre.P.A ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] {0, 1} =
        toUnit (TK R) ≫ D.toPre.c (j₁ y + y') := by
      rw [psum_pair, D.toPre.c_add, comp_padd', comp_padd']
      exact congrArg₂ (padd D.toPre.P.A) s₀ s₁
    have c₀ : ((-1 : ℤ) ^ (2 - (∅ : Finset (Fin 2)).card)) = 1 := by decide
    have c₁ : ((-1 : ℤ) ^ (2 - ({0} : Finset (Fin 2)).card)) = -1 := by decide
    have c₂ : ((-1 : ℤ) ^ (2 - ({1} : Finset (Fin 2)).card)) = -1 := by decide
    have c₃ : ((-1 : ℤ) ^ (2 - ({0, 1} : Finset (Fin 2)).card)) = 1 := by decide
    simp only []
    rw [t₀, t₁, t₂, t₃, c₀, c₁, c₂, c₃, zpow_one, zpow_one, zpow_neg_one, zpow_neg_one]
  have ψa := ψ (j₁ y)
  have ψb := ψ y'
  have ψab := ψ (j₁ y + y')
  rw [hj₁, hj₂] at ψa
  rw [map_add, map_add, hj₁, hj₂, zero_add] at ψab
  rw [K, val_tau D _ _ hJ₂, val_tau D₁ _ _ hJ₁, ← inv_mul_eq_iff_eq_mul.2 ψa, ← inv_mul_eq_iff_eq_mul.2 ψb,
    ← inv_mul_eq_iff_eq_mul.2 ψab, ← inv_mul_eq_iff_eq_mul.2 ρ, eq_inv_of_mul_eq_one_left z₂]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.MumProd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceRingModelPullbackStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.place_ring_model_pullback : GlobalTheory.Published.AbelianDeRham →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ →
    ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (𝔠 : FracId (FR E)) (R : Subring ℂ), IsPlaceRing E l lam R →
    ∀ (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (L : Set E) (U : Unif φ L 0 X) (p : X.A.left ⟶ X₀.A.left),
      X.IsPullBy X₀ (spMap R.subtype) p → ∀ i : I, ∃ (e : X₀.Lie →ₗ[R] R) (a : ℂ), a ≠ 0 ∧ IsPeriodGen X₀ U p i e a ∧
        ∀ (e' : X₀.Lie →ₗ[R] R) (a' : ℂ), IsPeriodGen X₀ U p i e' a' → ∃ t : R, e' = t • e := by
  first | exact @GlobalTheory.LatModel.EigenForm.exists_periodGen | exact GlobalTheory.LatModel.EigenForm.exists_periodGen | (intros; apply GlobalTheory.LatModel.EigenForm.exists_periodGen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareApproxValuesAtPointOfElementsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poincareApprox_values_at_point_of_elements : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (q : ℕ) (φ : InvFun O), IsPolFan bar q φ → NoSelfInt bar q φ → ∀ d₀ d : ℕ, 1 ≤ d₀ → 1 ≤ d → HasSupports bar q φ d₀ → ∀ (s : ℕ) (W : Matrix (Fin (s + 1)) (Fin (s + 1)) ℤ), PosW W → ∀ N₁ : ℕ, 3 ≤ N₁ → ∀ (A : Type) [CommRing A] [IsLocalRing A] (Φ : VSys bar q W N₁ A) (y : Φ.Y) (ga : Fin (Φ.m y) → LinearMap.BilinForm ℤ (Φ.X y)) (M : ℕ), 1 ≤ M → IsCone bar φ ga → (∀ k, Φ.δ y k = (M : ℤ) • ga k) → ∀ (K : Type) [Field K] (ev : Φ.V y →+* K) (k₀ : Subfield K), Elements Φ y φ d ga ev k₀ → Values Φ y ev k₀ := by
  first | exact @GlobalTheory.Poinc.Sep.values_of_elements | exact GlobalTheory.Poinc.Sep.values_of_elements | (intros; apply GlobalTheory.Poinc.Sep.values_of_elements <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareL2InequalityFundamentalSetStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
open ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poincare_l2_inequality_fundamental_set : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (x x0 : Frame X.Ψ r) (FF : Set (ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X))) (F : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X) → ℂ) (P0 : Frame X.Ψ r → ℂ), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0 → ReciprocityTheory.ChartRestriction.G.AR.Up.IsFundSet X x0 FF → (∀ γ ∈ X.Γ, ∀ z z' : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ∀ b ∈ Bor X.Ψ r, lact γ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) = rmul (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z') b → γ = 1) → DifferentiableOn ℂ F (ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x) → ReciprocityTheory.ChartRestriction.G.AR.Up.IsBEq X la P0 → (∀ z ∈ ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x, P0 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) = F z) → ∫⁻ z in FF, ENNReal.ofReal (X.pnorm la (ReciprocityTheory.ChartRestriction.G.AR.Up.poin X la P0) (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) ^ 2) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x0) ≤ ENNReal.ofReal (Real.exp (C * ((X.Ψ.card : ℝ) * r) ^ 8)) * ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 / ReciprocityTheory.ChartRestriction.G.AR.Up.kaF X x (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) z) * ReciprocityTheory.ChartRestriction.G.AR.Up.IW.Wpsi X la (fun _ => 0) (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x) := by
  first | exact @GlobalTheory.PoincareL2.poincare_l2_inequality | exact GlobalTheory.PoincareL2.poincare_l2_inequality | (intros; apply GlobalTheory.PoincareL2.poincare_l2_inequality <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointsMapHolomorphic
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

set_option autoImplicit false

namespace GlobalTheory.LineForm

theorem isHolo_ptsOver_map : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsRegVar p D) (σ : k →+* ℂ),
    ∀ (Y : Scheme.{0}) (p' : Y ⟶ Sp k) (D' : ℕ) (hY : IsRegVar p' D') (π : Y ⟶ X) (w : π ≫ p = p'),
    (hX.atlas σ).IsHolo (hY.atlas σ) (GlobalTheory.Points.PtsOver.map π w _) := by
  intro k _ X _ p D hX σ Y p' D' hY π w
  exact ⟨CxPts.continuous_of_comp (f := π) (fun z => rfl),
    fun j i => AlgChart.holo_map (f := π) (fun z => rfl) j i⟩

end GlobalTheory.LineForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolAVPointDefinedOverOfCoordsProportionalStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polAV_point_defined_over_of_coords_proportional : ∀ (K : Type) [Field K] [IsAlgClosed K] (k₀ : Subfield K), IsAlgClosed k₀ → ∀ (P₀ : PolAV (Sp k₀)) (m : ℕ), Odd m → 3 ≤ m → (m : K) ≠ 0 → ∀ (z : Over.mk (spMap k₀.subtype) ⟶ P₀.A) (v : {y : Over.mk (spMap k₀.subtype) ⟶ P₀.A // y ^ m ^ 2 = 1} → K) (l : K) (r : {y : Over.mk (spMap k₀.subtype) ⟶ P₀.A // y ^ m ^ 2 = 1} → K), GlobalTheory.Ex.IsCoordPt P₀ m (fun i => i.1) z (fun i => GlobalTheory.Ex.fnOf (v i)) → (∀ i, r i ∈ k₀) → (∀ i, v i = l * r i) → GlobalTheory.Poinc.Sep.DefOver k₀ z.left := by
  first | exact @GlobalTheory.Poinc.Sep.defOver_of_coord_proportional | exact GlobalTheory.Poinc.Sep.defOver_of_coord_proportional | (intros; apply GlobalTheory.Poinc.Sep.defOver_of_coord_proportional <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolFibOfPoint
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.FibExist

theorem polFib_of_point : ∀ (X : Scheme.{0}) (P : PolAV X) (R : Type) [CommRing R] (x : Sp R ⟶ X),
    PolFib P.A P.L P.g x := by
  intro X P R _ x
  obtain ⟨P', g, hg, hgg, mul, t, ht⟩ := GlobalTheory.polBaseChange_holds X (Sp R) x P
  obtain ⟨t', ht', -⟩ := GenericSectionBasis.exists_inv_iso t ht
  refine ⟨P', g, hgg, ⟨hg, fun T a b a₀ b₀ ha hb => ?_⟩, ⟨t', ht'⟩⟩
  have ea : a₀ = toBase hg.w a := Over.OverMorphism.ext ha
  have eb : b₀ = toBase hg.w b := Over.OverMorphism.ext hb
  subst ea eb
  rw [← mul]
  rfl

end GlobalTheory.UMin.FibExist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveFamiliesThetaSymmetricMinMemberCompareStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_families_thetaSymmetric_min_member_compare : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsIntegrallyClosed V] [Field K] (io : FractionRing V →+* K) (N N' k : ℕ) (J : Type) (c : Fin N → K) (c' : Fin N' → K) (a : K) (e : Fin N → FractionRing V) (th : J → FractionRing V), a ≠ 0 → 1 ≤ k → Prim (io.comp (algebraMap V (FractionRing V))) (fun b => c b / a) → Prim (io.comp (algebraMap V (FractionRing V))) (fun b => c' b / a) → (∀ j, io (e j) = symTup c j) → (∀ x, ∃ b, c' x ^ k = io (th b) ^ k) → (∀ b, ∃ x, c' x ^ k = io (th b) ^ k) → ∀ j₀, e j₀ ≠ 0 → (∀ j, e j / e j₀ ∈ Set.range (algebraMap V (FractionRing V))) → (∀ b, th b ^ N.factorial / e j₀ ∈ Set.range (algebraMap V (FractionRing V))) ∧ ∃ b, th b ≠ 0 ∧ e j₀ / th b ^ N.factorial ∈ Set.range (algebraMap V (FractionRing V)) := by
  first | exact @GlobalTheory.UMin.prim_symTup_cmp | exact GlobalTheory.UMin.prim_symTup_cmp | (intros; apply GlobalTheory.UMin.prim_symTup_cmp <;> assumption)
end

