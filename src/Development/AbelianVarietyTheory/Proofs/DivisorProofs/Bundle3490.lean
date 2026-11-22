import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3472
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3473
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2880
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2434
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0518
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1990
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3478
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1702
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3297
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3398
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3407
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3481
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3377
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3466
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2461
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2332
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2336
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.IsQProjOverOfIsProjOver
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2875
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3468
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2979
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3474

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedPointNotMemAbelianLocusTautologicalBoundarStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closedPoint_notMem_abelianLocus_tautologicalBoundaryChart : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)) (k : Type) [Field k] (m e : ℕ) (C : MonoFam Xo c φ (ChartRing k m e)), IsTaut C → 1 ≤ C.m → closedPoint (ChartRing k m e) ∉ abLocus C.t.G := by
  first | exact @GlobalTheory.UChart.closedPoint_not_mem_abLocus_of_isTaut | exact GlobalTheory.UChart.closedPoint_not_mem_abLocus_of_isTaut | (intros; apply GlobalTheory.UChart.closedPoint_not_mem_abLocus_of_isTaut <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedPointOfValuesInSmallAlgClosed
section
open IsLocalRing NumberField

namespace GlobalTheory.PointAlg

theorem trdeg_le_of_hom_algClosure (X Y Z : Type) [Field X] [Field Y] [Field Z] [Algebra ℚ X] [Algebra ℚ Y]
    (f : X →+* AlgebraicClosure Z) (e : Y →+* Z) (he : Function.Surjective e) :
    Algebra.trdeg ℚ X ≤ Algebra.trdeg ℚ Y := by
  letI : Algebra ℚ Z := (e.comp (algebraMap ℚ Y)).toAlgebra
  have h1 : Algebra.trdeg ℚ X ≤ Algebra.trdeg ℚ (AlgebraicClosure Z) :=
    trdeg_le_of_injective f.toRatAlgHom f.injective
  have h2 : Algebra.trdeg ℚ Z ≤ Algebra.trdeg ℚ Y :=
    trdeg_le_of_surjective e.toRatAlgHom he
  have h3 := trdeg_add_eq ℚ Z (A := AlgebraicClosure Z)
  rw [trdeg_eq_zero (R := Z) (A := AlgebraicClosure Z), add_zero] at h3
  exact h1.trans (h3.ge.trans h2)

theorem closed_point_of_values (F A R K : Type) [Field F] [NumberField F] [CommRing A] [IsDomain A] [CommRing R]
    [IsLocalRing R] [Field K] (b : F →+* A) (hb : b.EssFiniteType) (ψ : A →+* R) (hψ : GlobalTheory.TChart.IsComplAt ψ)
    (ev : R →+* K) (k₀ : Subfield K) (hk : Nonempty (k₀ →+* AlgebraicClosure (ResidueField R)))
    (hev : ∀ a, ev (ψ a) ∈ k₀) : (∀ r ∈ maximalIdeal R, ev r = 0) ∧ ∀ r, ev r ∈ k₀ := by
  obtain ⟨j⟩ := hk
  obtain ⟨-, -, -, hmap, hres⟩ := hψ
  set q : Ideal A := (maximalIdeal R).comap ψ with hq
  haveI hqp : q.IsPrime := Ideal.comap_isPrime ψ _
  let L := Localization.AtPrime q
  have hu : ∀ y : q.primeCompl, IsUnit (ψ y) := fun y => by
    by_contra h
    exact y.2 ((mem_maximalIdeal _).mpr h)
  let Φ : L →+* R := IsLocalization.lift (M := q.primeCompl) hu
  have hΦ : ∀ a, Φ (algebraMap A L a) = ψ a := fun a => IsLocalization.lift_eq hu a
  have hne : ∀ a, IsUnit (ψ a) → ev (ψ a) ≠ 0 := fun a h => (h.map ev).ne_zero
  have hΦk : ∀ x, ev (Φ x) ∈ k₀ := by
    intro x
    obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj q.primeCompl x
    have h2 := congrArg (fun t => ev (Φ t)) h
    simp only [map_mul, hΦ] at h2
    rw [eq_div_of_mul_eq (hne _ (hu s)) h2]
    exact k₀.div_mem (hev _) (hev _)
  haveI : IsLocalHom Φ := by
    refine ⟨fun x hx => ?_⟩
    obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj q.primeCompl x
    have h2 := congrArg Φ h
    simp only [map_mul, hΦ] at h2
    have ha : IsUnit (ψ a) := h2 ▸ hx.mul (hu s)
    have ha' : a ∈ q.primeCompl := fun h => (mem_maximalIdeal _).mp h ha
    have := IsLocalization.map_units L ⟨a, ha'⟩
    simp only at h
    exact isUnit_of_mul_isUnit_left (h ▸ this)
  have hsurj : Function.Surjective (ResidueField.map Φ) := by
    intro z
    obtain ⟨r, rfl⟩ := residue_surjective z
    obtain ⟨a, s, hs, h⟩ := hres r
    rw [← residue_eq_zero_iff, map_sub, map_mul, sub_eq_zero] at h
    refine ⟨residue L (algebraMap A L a) / residue L (algebraMap A L s), ?_⟩
    rw [map_div₀, ResidueField.map_residue, ResidueField.map_residue, hΦ, hΦ, ← h]
    exact mul_div_cancel_right₀ _ (hs.map (residue R)).ne_zero
  let g : L →+* AlgebraicClosure (ResidueField R) := j.comp ((ev.comp Φ).codRestrict k₀ hΦk)
  haveI hP : (RingHom.ker g).IsPrime := RingHom.ker_isPrime g
  have hE : ((algebraMap A L).comp (b.comp (algebraMap ℚ F))).EssFiniteType := by
    refine RingHom.EssFiniteType.comp (RingHom.EssFiniteType.comp ?_ hb) ?_
    · exact RingHom.essFiniteType_algebraMap.mpr inferInstance
    · exact RingHom.essFiniteType_algebraMap.mpr (Algebra.EssFiniteType.of_isLocalization L q.primeCompl)
  letI : Algebra ℚ L := ((algebraMap A L).comp (b.comp (algebraMap ℚ F))).toAlgebra
  have hmax : RingHom.ker g = maximalIdeal L :=
    GlobalTheory.eq_maximalIdeal_of_trdeg_le ℚ L hE _ hP
      (trdeg_le_of_hom_algClosure _ _ _
        (IsFractionRing.lift (K := FractionRing (L ⧸ RingHom.ker g)) (RingHom.kerLift_injective g))
        (ResidueField.map Φ) hsurj)
  have h0 : ∀ r ∈ maximalIdeal R, ev r = 0 := by
    have : maximalIdeal R ≤ RingHom.ker ev := by
      rw [← hmap, Ideal.map_le_iff_le_comap]
      intro a ha
      have h1 : algebraMap A L a ∈ RingHom.ker g := by
        rw [hmax]
        exact (IsLocalization.AtPrime.to_map_mem_maximal_iff L q a).mpr ha
      rw [RingHom.mem_ker] at h1
      have h2 := congrArg Subtype.val (j.injective (h1.trans (map_zero j).symm))
      change ev (Φ (algebraMap A L a)) = 0 at h2
      rw [hΦ] at h2
      exact h2
    exact fun r hr => this hr
  refine ⟨h0, fun r => ?_⟩
  obtain ⟨a, s, hs, h⟩ := hres r
  have h2 := h0 _ h
  rw [map_sub, map_mul, sub_eq_zero] at h2
  rw [eq_div_of_mul_eq (hne _ hs) h2]
  exact k₀.div_mem (hev _) (hev _)

end GlobalTheory.PointAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologousNegTorsorCocycleOfOrthogonalStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cohomologous_neg_torsor_cocycle_of_orthogonal : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ P : LB (A ⊗ B).left, P.IsLB → ∀ φ : HdR A →ₗ[R] HdR B →ₗ[R] R, AbDual.IsCorrForm (dp0 R) (𝟙 _) A B P φ → (∀ x ∈ Fil A, ∀ y ∈ Fil B, φ x y = 0) → ∀ (h' : HdR B) (v : epsR R ⟶ B), IsLieImage h' v → ∀ c : primDR A, (∀ h ∈ Fil A, φ h h' = h c) → ∀ f : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _)), CatCoh.H1.mk _ f = c.1 → ∀ (j : ∀ (D : Type) [CommRing D] [Algebra R D], Pt A D → P.ι), IsChoice P j → Cohom (chartsA P) (fv f) (tanCoc P j v).neg := by
  first | exact @GlobalTheory.PtExt.cohom_fv_neg_tanCoc_of_orthogonal | exact GlobalTheory.PtExt.cohom_fv_neg_tanCoc_of_orthogonal | (intros; apply GlobalTheory.PtExt.cohom_fv_neg_tanCoc_of_orthogonal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComesFromTautBaseOfRescaledPullbackMonomial
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon GlobalTheory.PolDeg GlobalTheory.TInj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TInj

theorem from_rescale_pull : ∀ {o W : Type} [CommRing o] [CommRing W] [IsDomain W] [IsLocalRing W] (T : TautBase o W) (n : ℕ) (D₀ : DegPre W), D₀.PsiEven → D₀.TauBimult → (∀ y, PsiUnitOn D₀ y Set.univ) → ∀ (ib : D₀.X ≃+ (Fin T.r → ℤ)) (β : D₀.P.A.left ⟶ T.B.left) (ββ : (G2 D₀.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D₀.P.A D₀.P.L) ((abelian₂ T.B T.M.L).pull ββ)), From T (RingHom.id W) (fun _ : Empty => (1 : W)) (fun _ => 0) n D₀ ib β ββ w → ∀ (V : Type) [CommRing V] [IsDomain V] (iw : W →+* V), Function.Injective iw → ∀ (Q : DegPre V) (g : Q.X → (FractionRing V)ˣ) (hD : IsPullDeg iw D₀ (rescale Q g)) {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (e : Q.X ≃+ (Fin T.r → ℤ)), (∀ y : Q.X, e y = ib (hD.xe y)) → (∀ a a' : Q.X, (((g (a + a'))⁻¹ * g a * g a' : (FractionRing V)ˣ) : FractionRing V) = ∏ i, algebraMap V (FractionRing V) (s i) ^ ((n : ℤ) * ε i (e a) (e a'))) → ∃ (β' : Q.P.A.left ⟶ T.B.left) (ββ' : (G2 Q.P.A).left ⟶ (G2 T.B).left) (w' : LB.Iso (abelian₂ Q.P.A Q.P.L) ((abelian₂ T.B T.M.L).pull ββ')), From T iw s ε n Q e β' ββ' w' := by
  intro o W _ _ _ _ T n D₀ hev hbi hun ib β ββ w hF V _ _ iw hiw Q g hD I _ s ε e he hg
  have hin : ∀ χ, D₀.PsiIn χ ⊤ := fun χ j U hU hle h => by
    obtain ⟨r, -, hr⟩ := hun χ j U hU (Set.subset_univ _) hle h
    exact ⟨r, by rw [Ideal.map_top]; trivial, hr⟩
  let D₁ : DegData W ⊤ :=
    { toPre := D₀
      psi_even := hev
      tau_bimult := hbi
      psi_pos := fun χ _ => hin χ
      psi_tendsto := fun m => by
        rw [Ideal.top_pow]
        exact Set.finite_empty.subset fun χ hχ => hχ (hin χ) }
  obtain ⟨ββ', w', pb, sq, gen, hc, hτ⟩ :=
    from_pull T (fun _ : Empty => 0) n W V ⊤ D₁ (RingHom.id W) (fun _ => 1) ib β ββ w iw (rescale Q g) hD hiw hF
  rw [RingHom.comp_id] at pb hc hτ
  refine ⟨_, ββ', w', pb, sq, gen, fun a => ?_, fun a b => ?_⟩
  · rw [he a]; exact hc a
  · obtain ⟨k, hk, hv⟩ := hτ a b
    have hk1 : k = 1 := Units.ext (by rw [hk]; simp)
    refine ⟨_, hg a b, fun z J J' hJ hJ' => ?_⟩
    have H := hv z J J' hJ hJ'
    have E := rescale_tau_val Q g a b hJ'
    have H' := E.symm.trans H
    rw [hk1] at H'
    rw [he a, he b]
    have aux : ∀ {G : Type} [CommGroup G] (x y u t p : G), x * y⁻¹ * u⁻¹ * t = 1 * p → t = x⁻¹ * y * u * p := by
      intro G _ x y u t p h
      rw [_root_.one_mul] at h
      rw [← h, ← _root_.mul_assoc]
      have h1 : x⁻¹ * y * u * (x * y⁻¹ * u⁻¹) = (x⁻¹ * x) * (y * y⁻¹) * (u * u⁻¹) := by ac_rfl
      rw [h1]
      simp
    simp only [unitOn, map_mul, map_inv, map_one] at H' ⊢
    exact aux _ _ _ _ _ H'

end GlobalTheory.TInj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutesOfCommutesDualNumberAgreeClosed
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.EpsRigid

theorem fst_ker_le_nilradical (k : Type) [Field k] :
    RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom ≤ nilradical (DualNumber k) := by
  intro x hx
  have h0 : TrivSqZeroExt.fst x = 0 := hx
  have hx' : x = TrivSqZeroExt.inr (TrivSqZeroExt.snd x) := by
    ext
    · simp [h0]
    · simp
  rw [mem_nilradical]
  refine ⟨2, ?_⟩
  rw [pow_two, hx', TrivSqZeroExt.inr_mul_inr]

theorem quot_mk_eq (k : Type) [Field k] :
    ∃ e : k →+* DualNumber k ⧸ RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom,
      Ideal.Quotient.mk (RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom) = e.comp (TrivSqZeroExt.fstHom k k k).toRingHom := by
  have hs : Function.Surjective (TrivSqZeroExt.fstHom k k k).toRingHom := fun a => ⟨TrivSqZeroExt.inl a, by simp⟩
  refine ⟨(RingHom.quotientKerEquivOfSurjective hs).symm.toRingHom, ?_⟩
  refine RingHom.ext fun x => ?_
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  rw [RingEquiv.eq_symm_apply]
  rfl

theorem comm_of_comm :
    ∀ (k : Type) [Field k] {S : Scheme.{0}} (G' : Over (Sp (DualNumber k))) [GrpObj G'], IsAbelianScheme G' → ∀ (G : Over S) [GrpObj G] (g₂ : Sp (DualNumber k) ⟶ S) (φ₁ φ₂ : G'.left ⟶ G.left), IsGrpPullback G' G g₂ φ₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ G'.left) (y : Z ⟶ Sp k), x ≫ G'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ φ₁ = x ≫ φ₂) → ∀ (u : G' ⟶ G') [IsMonHom u] (v : G ⟶ G) [IsMonHom v], u.left ≫ φ₁ = φ₁ ≫ v.left → u.left ≫ φ₂ = φ₂ ≫ v.left := by
  intro k _ S G' _ hG G _ g₂ φ₁ φ₂ h₂ h0 u _ v _ hu
  have hsq : (φ₂ ≫ v.left) ≫ G.hom = G'.hom ≫ g₂ := by
    rw [Category.assoc, Over.w v, h₂.1.w]
  let w : G' ⟶ G' := Over.homMk (h₂.1.lift (φ₂ ≫ v.left) G'.hom hsq) (h₂.1.lift_snd _ _ _)
  have hw : w.left ≫ φ₂ = φ₂ ≫ v.left := h₂.1.lift_fst _ _ _
  suffices huw : u = w by rw [huw, hw]
  obtain ⟨e, he⟩ := quot_mk_eq k
  have hsp : spMap (Ideal.Quotient.mk (RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom)) =
      spMap e ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom := by
    rw [he, spMap, spMap, spMap, ← Spec.map_comp]
    rfl
  refine GlobalTheory.NilRigidity.eq_of_eq_on_quotient _ (fst_ker_le_nilradical k) G' G' hG u w ?_ ?_
  · have hj : ∀ x : pullback G'.hom (spMap (Ideal.Quotient.mk (RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom))) ⟶ G'.left,
        x ≫ G'.hom = pullback.fst G'.hom (spMap (Ideal.Quotient.mk (RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom))) ≫ G'.hom →
        x ≫ φ₁ = x ≫ φ₂ := by
      intro x hx
      refine h0 _ x (pullback.snd _ _ ≫ spMap e) ?_
      rw [hx, pullback.condition, Category.assoc, hsp]
    apply h₂.1.hom_ext
    · have a1 := hj (pullback.fst _ _ ≫ u.left) (by rw [Category.assoc, Over.w u])
      have a2 := hj (pullback.fst _ _) rfl
      simp only [Category.assoc] at a1 a2 ⊢
      rw [hw, ← a1, hu, ← Category.assoc, a2, Category.assoc]
    · rw [Category.assoc, Category.assoc, Over.w u, Over.w w]
  · rw [IsMonHom.one_hom]
    apply Over.OverMorphism.ext
    rw [Over.comp_left]
    apply h₂.1.hom_ext
    · rw [Category.assoc, hw, ← Category.assoc, ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.IsGrpPullback.one_left h₂,
        Category.assoc, ← Over.comp_left, IsMonHom.one_hom]
    · rw [Category.assoc, Over.w w]

end GlobalTheory.EpsRigid
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutesWithOfIsSquareConstOfTriple
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct

namespace GlobalTheory.FunObj

open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem commutesWith_of_isSquareConst_of_triple (hWC : GlobalTheory.SquareSt.WeilConvergence)
    (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree) (hP : GlobalTheory.Published.CuspDecayBound)
    {μ₀ : T} (hL : L.Is μ₀) {W : G.Weil} {B : Frames G} {ρ : RealMatch W} {t : T} {i j : Fin D.R.m}
    (hT : SquareTriple W t i j) {c : ℂ} (hc : IsSquareConst W B ρ t i j c) : CommutesWith W B ρ t i j c := by
  intro M hM Θ Θ' hΘ F hF hFc hFl hA hB
  funext g₁
  obtain ⟨hBa, hBe⟩ := GlobalTheory.T.thetaLift_eq_integral_routeKernel_fubini hWC hK hP hL W B ρ t i j hT M hM Θ Θ' hΘ F hF hFc hFl hA g₁
  obtain ⟨z, hz, hSa, hSe⟩ := GlobalTheory.T.exists_theta_translates_convergent_lift_degree hWC hK hP hL W B ρ t i j hT M hM Θ Θ' hΘ F hF hFc hFl hB g₁
  refine mul_left_cancel₀ hz ?_
  rw [Pi.smul_apply, smul_eq_mul, hBe, mul_left_comm, hSe, ← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hBa, hSa] with g hb hs
  have h := hc M hM Θ Θ' hΘ z g g₁ ⟨hb, hs⟩
  linear_combination F g * h

theorem commutesWith_of_isSquareConst (hWC : GlobalTheory.SquareSt.WeilConvergence) (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree)
    (hP : GlobalTheory.Published.CuspDecayBound) {μ₀ : T} (hL : L.Is μ₀) {W : G.Weil} {B : Frames G} {ρ : RealMatch W} {t : T}
    {i j : Fin D.R.m} (hS : SquareStanding G t) {c : ℂ} (hc : IsSquareConst W B ρ t i j c) : CommutesWith W B ρ t i j c :=
  commutesWith_of_isSquareConst_of_triple hWC hK hP hL (squareTriple_of_standing hL W t i j hS) hc

end GlobalTheory.FunObj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutingHeatOperatorsActOnValues
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat

theorem ringOp_map_of_intertwine {A B : Type} [CommRing A] [CommRing B] (iK : A →+* B) {n : ℕ} (d : A → A) (dd : Fin n → A → A)
    (d' : B → B) (dd' : Fin n → B → B) (hd : ∀ w, d' (iK w) = iK (d w)) (hdd : ∀ a w, dd' a (iK w) = iK (dd a w))
    (Θ : Matrix (Fin n) (Fin n) A) (u : Fin n → A) (p p' : A) (k : ℕ) (f : A) :
    iK (ringOp d dd Θ u p p' k f) = ringOp d' dd' (iK.mapMatrix Θ) (fun a => iK (u a)) (iK p) (iK p') k (iK f) := by
  simp only [ringOp, map_sub, map_add, map_mul, map_sum, map_pow, map_natCast, map_ofNat, hd, hdd,
    RingHom.mapMatrix_apply, Matrix.map_apply]

theorem ringOp_mul_of_const {K : Type} [CommRing K] {n : ℕ} (d : K → K) (δ : Fin n → K → K)
    (Θ : Matrix (Fin n) (Fin n) K) (u : Fin n → K) (p p' : K) (k : ℕ) (c s : K)
    (hd : d (c * s) = c * d s + s * d c) (h1 : ∀ a y, δ a (c * y) = c * δ a y) :
    ringOp d δ Θ u p p' k (c * s) = c * ringOp d δ Θ u p p' k s + 2 * (k : K) * d c * s := by
  simp only [ringOp, h1, hd, mul_left_comm _ c, ← Finset.mul_sum]
  try ring

theorem exists_derivation_fractionRing_ext (Ω : Type) [CommRing Ω] [IsDomain Ω] (d : Derivation ℤ Ω Ω) :
    ∃ dL : Derivation ℤ (FractionRing Ω) (FractionRing Ω),
      ∀ w, dL (algebraMap Ω (FractionRing Ω) w) = algebraMap Ω (FractionRing Ω) (d w) := by
  obtain ⟨δ', hder, hδ'⟩ := Formalism.L2.Pj.GenericSectionMinimum.IsDer.ofLoc (nonZeroDivisors Ω) (B := FractionRing Ω)
    (fun w => algebraMap Ω (FractionRing Ω) (d w)) (fun a b => by simp)
    (fun a b => by simp [Derivation.leibniz, smul_eq_mul])
  have hsm : ∀ (z : ℤ) (a : FractionRing Ω), δ' (z • a) = z • δ' a := by
    intro z a
    induction z using Int.induction_on with
    | zero => simp [hder.der_zero]
    | succ i ih => simp only [add_smul, one_smul, hder.add, ih]
    | pred i ih => simp only [sub_smul, one_smul, hder.der_sub, ih]
  have hint : ∀ m : ℤ, δ' (m : FractionRing Ω) = 0 := fun m => by
    have := hsm m 1
    rw [zsmul_eq_mul, _root_.mul_one, hder.der_one] at this
    simpa using this
  have hlb : ∀ a b : FractionRing Ω, δ' (a * b) = a • δ' b + b • δ' a := fun a b => by
    rw [hder.mul, smul_eq_mul, smul_eq_mul]
  let dL : Derivation ℤ (FractionRing Ω) (FractionRing Ω) := { toFun := δ', map_add' := hder.add, map_smul' := fun m y => by rw [RingHom.id_apply, Algebra.smul_def, eq_intCast, zsmul_eq_mul, hder.mul, hint m, MulZeroClass.mul_zero, add_zero], map_one_eq_zero' := hder.der_one, leibniz' := hlb }
  exact ⟨dL, hδ'⟩

theorem heat_acts_on_values : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n : ℕ) (vH : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (vH a) (dd a)) → ∀ (v' : Fin n → TanM (𝟙 (Sp R)) t.G), (∀ a, GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (tv (vH a))) (tv (v' a))) → ∀ (D : Derivation ℤ R R) (h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D), IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → ∀ (i0 : h.J) (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x : Sp Ω ⟶ Y.H.left) (x' : Sp Ω ⟶ t.G.left) (δ : Fin n → Derivation ℤ Ω Ω), IsAdicComplete ((maximalIdeal R).map φ) Ω → ∀ (hx : x ≫ Y.H.hom = spMap φ) (hx' : x' ≫ t.G.hom = spMap φ), (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x ⁻¹ᵁ O → valR x O (dd a O f) = δ a (valR x O f)) → GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ (Over.mk (spMap φ)) (Over.homMk x hx)) (Over.homMk x' hx') → ∀ (dΩ : Derivation ℤ Ω Ω), ⊤ ≤ x ⁻¹ᵁ h.W i0 → (∀ O f, O ≤ h.W i0 → ⊤ ≤ x ⁻¹ᵁ O → valR x O (h.d i0 O f) = dΩ (valR x O f)) → ∀ (g : GlobalTheory.RayEv.Transport.Frame t.PP.L (x' ≫ 𝟙 t.G.left)), g.IsGen → ∀ (δL : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)), (∀ a ω, δL a ((algebraMap Ω (FractionRing Ω)) ω) = (algebraMap Ω (FractionRing Ω)) (δ a ω)) → ∃ (dt : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (u' : Fin n → (FractionRing Ω)) (p p' : (FractionRing Ω)), (∀ r, dt ((algebraMap Ω (FractionRing Ω)) (φ r)) = (algebraMap Ω (FractionRing Ω)) (φ (D r))) ∧ ∀ (k : ℕ), 1 ≤ k → ∀ s : (FractionRing Ω), (∃ (r : R) (σ : SecM (𝟙 t.G.left) t.PP.L k) (ω : Ω), r ≠ 0 ∧ IsValue (𝟙 _) t.PP.L x' g k σ ω ∧ (algebraMap Ω (FractionRing Ω)) ω = (algebraMap Ω (FractionRing Ω)) (φ r) * (s)) → (∃ (r : R) (σ : SecM (𝟙 t.G.left) t.PP.L k) (ω : Ω), r ≠ 0 ∧ IsValue (𝟙 _) t.PP.L x' g k σ ω ∧ (algebraMap Ω (FractionRing Ω)) ω = (algebraMap Ω (FractionRing Ω)) (φ r) * (ringOp ⇑dt (fun a => ⇑(δL a)) (((algebraMap Ω (FractionRing Ω)).comp φ).mapMatrix h.Θ) u' p p' k s)) := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt gam hmono htt hab
  intro Y n vH dd hinv v' hpt D h hbasic hdef i0 Ω _ _ _ φ x x' δ hcompl hx hx' hδφ hδ hpx dΩ hW hdΩ g hg δL hδL
  letI := H.starRing
  have hDφ := (GlobalTheory.T.heatOperator_value_at_point_eq_ringOperator R Y.H _ _ P.D.toPre.P.L n dd ⇑D h i0 Ω φ x hx δ hδ dΩ hW hdΩ).1
  obtain ⟨e, p0, p0', hcore⟩ := GlobalTheory.T.heat_operator_values_of_sections_complete_local_ring E H R t P m tt gam hmono htt hab Y n vH dd hinv v' hpt D h hbasic hdef i0 Ω φ x x' δ
    hcompl hx hx' hδφ hδ hpx dΩ hW hdΩ g hg
  obtain ⟨dL, hdL⟩ := exists_derivation_fractionRing_ext Ω dΩ
  set iK := algebraMap Ω (FractionRing Ω) with hiK
  have hiKinj : Function.Injective iK := IsFractionRing.injective Ω (FractionRing Ω)
  have h2R : IsUnit (2 : R) := by
    have := (isUnit_iff_ne_zero.2 (two_ne_zero : (2 : ℚ) ≠ 0)).map (algebraMap ℚ R)
    rwa [map_ofNat] at this
  have h2K : (2 : FractionRing Ω) ≠ 0 := by
    have := (h2R.map (iK.comp φ)).ne_zero
    rwa [map_ofNat] at this
  have hsymm : ((iK.comp φ).mapMatrix h.Θ)ᵀ = (iK.comp φ).mapMatrix h.Θ := by
    show (h.Θ.map _)ᵀ = h.Θ.map _
    rw [← Matrix.transpose_map, h.symm]
  have hce : iK ((e⁻¹ : Ωˣ) : Ω) ≠ 0 := fun h0 => (e⁻¹).ne_zero (hiKinj (h0.trans (map_zero iK).symm))
  obtain ⟨d', u'', q, q', hd'c, hconj⟩ := GlobalTheory.T.heatOperatorOnRing_conj_pow_fractionField Ω n dL δL ((iK.comp φ).mapMatrix h.Θ) hsymm h2K
    (fun a => iK (φ (h.u a))) (iK p0) (iK p0') _ hce
  refine ⟨d', u'', q, q', fun r => ?_, ?_⟩
  · rw [hd'c _ (fun a => by rw [hδL, hδφ, map_zero]), hdL, hDφ]
  intro k hk s ⟨r₁, σ, ω, hr₁, hv, hs⟩
  obtain ⟨r₂, σ₂, ω₂, hr₂, hv₂, hω₂⟩ := hcore k hk σ ω hv
  have key : iK ω₂ = iK (φ r₂) * ringOp ⇑d' (fun a => ⇑(δL a)) ((iK.comp φ).mapMatrix h.Θ) u'' q q' k (iK ω) := by
    rw [hω₂, map_mul, map_mul, map_pow, ringOp_map_of_intertwine iK _ _ _ _ hdL hδL, map_mul, map_pow]
    have e1 : iK.mapMatrix (φ.mapMatrix h.Θ) = (iK.comp φ).mapMatrix h.Θ := by
      ext a b; simp
    rw [e1, hconj, ← _root_.mul_assoc (iK (e : Ω) ^ k), ← mul_pow, ← map_mul, Units.mul_inv, map_one, one_pow, _root_.one_mul]
  by_cases hc1 : φ r₁ = 0
  · exact ⟨r₁, σ, ω, hr₁, hv, by rw [hs, hc1]; simp⟩
  · have hδc : ∀ a, δL a (iK (φ r₁)) = 0 := fun a => by rw [hδL, hδφ, map_zero]
    have hdc : d' (iK (φ r₁)) = iK (φ (D r₁)) := by rw [hd'c _ hδc, hdL, hDφ]
    have hs' : iK ω = iK (φ r₁) * s := hs
    have hRO := ringOp_mul_of_const ⇑d' (fun a => ⇑(δL a)) ((iK.comp φ).mapMatrix h.Θ) u'' q q' k (iK (φ r₁)) s
      (by rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]) (fun a y => by
        rw [Derivation.leibniz, hδc, smul_zero, add_zero, smul_eq_mul])
    rw [← hs', hdc] at hRO
    obtain ⟨σ₃, hv₃⟩ := GlobalTheory.T.sectionValueInFrame_linearCombination R t.G t.PP.L Ω φ x' hx' g k σ₂ σ ω₂ ω r₁ (-(2 * (k : R)) * D r₁ * r₂) hv₂ hv
    refine ⟨r₁ * r₁ * r₂, σ₃, _, mul_ne_zero (mul_ne_zero hr₁ hr₁) hr₂, hv₃, ?_⟩
    simp only [RingHom.comp_apply, map_add, map_mul, map_neg, map_natCast, map_ofNat]
    rw [key, hRO, hs']
    ring

end GlobalTheory.Heat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectionClosedFibreOfPulledBackIsoStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.connection_closedFibre_of_pulledBack_iso : ∀ (k : Type) [Field k] (R : Type) [CommRing R] (P : PolAV (Sp R)) (ρ : R →+* DualNumber k) (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.A.left), IsGrpPullback B' P.A (spMap ρ) π₁ → IsGrpPullback B' P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → ∀ (A₀ : Over (Sp k)) [GrpObj A₀] (m₀ : A₀.left ⟶ P.A.left), IsGrpPullback A₀ P.A (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)) m₀ → ∀ pr : B'.left ⟶ A₀.left, pr ≫ m₀ = π₂ → pr ≫ A₀.hom = B'.hom ≫ spMap (algebraMap k (DualNumber k)) → ∀ {J : Type} (V : J → P.A.left.Opens) (jj : J → P.L.ι), ⨆ i, V i = ⊤ → (∀ i, V i ≤ P.L.U (jj i)) → ∀ d : ∀ W : P.A.left.Opens, Γ(P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W), GlobalTheory.KS.LocDerK A₀.hom P.A.hom m₀ (fun r => (ρ r).snd) ⊤ d → (∀ (W : P.A.left.Opens) (f : Γ(P.A.left, W)), pbT π₁ f (π₂ ⁻¹ᵁ W) = pbT π₂ f (π₂ ⁻¹ᵁ W) + constFn B'.hom (π₂ ⁻¹ᵁ W) DualNumber.eps * pbT pr (d W f) (π₂ ⁻¹ᵁ W)) → ∀ w : LB.Iso (P.L.pull π₁) (P.L.pull π₂), w.IsGen → ∃ q : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i), GlobalTheory.HeatConn.IsConnK P.A P.L A₀ m₀ (fun r => (ρ r).snd) V jj d q := by
  first | exact @GlobalTheory.PotIso.conn_of_iso | exact GlobalTheory.PotIso.conn_of_iso | (intros; apply GlobalTheory.PotIso.conn_of_iso <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescSt5
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc GlobalTheory.SiegJoin

namespace GlobalTheory.SiegDescent

theorem descSt5 : GlobalTheory.SiegJoin.DescSt5 := by
  intro g _ φ n hn _ F Z z i d S π j _ BD hB hC
  obtain ⟨J, -, -, -, ⟨hN, -⟩, hP, hD, -⟩ := hB
  have hn0 : n ≠ 0 := by omega
  haveI : IsDedekindDomain (cycAway n) := (arBase_cycAway n hn0).1
  haveI : IsProper (π ≫ z) := GlobalTheory.SchemeWords.isProper_of_isProjOver hP
  haveI : IsNoetherianRing (CommRingCat.of (cycAway n)) := inferInstanceAs (IsNoetherianRing (cycAway n))
  haveI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian (π ≫ z)
  haveI : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace (π ≫ z)
  haveI : AlgebraicGeometry.IsNoetherian S := {}
  have hj : IsDominant j := ⟨hD⟩
  have hd : SmoothOfRelativeDimension g F.univ.A.hom :=
    GlobalTheory.SiegSharpCover.smoothDim F.univ (by omega) (cycBase hn0).ζ.isUnit (isUnit_natCast hn0)
  obtain ⟨G, _, e, hG, he, hπ⟩ := GlobalTheory.T.semiAbelian_descent_from_complete_regular_charts F.X S ((GlobalTheory.isNormalScheme_iff_pred S).1 hN) j hj F.univ.A F.univ.ab F.univ.diag (pull_isLB F.univ.isLB _)
    F.princ.1 fun x => ⟨(exists_chart (hC x)).choose⟩
  obtain ⟨h₁, h₂⟩ := GlobalTheory.T.descended_group_abelianLocus_and_relDim F.X S j hj F.univ.A G e g F.univ.ab hd hG he fun x => by
    obtain ⟨C, hab⟩ := exists_chart (hC x)
    obtain ⟨p, hp, -⟩ := hπ x C
    exact ⟨C.R, inferInstance, inferInstance, C.ξ, C.G, inferInstance, p, C.centre, hp, hab⟩
  exact ⟨G, inferInstance, e, hG, h₂, he, h₁⟩

end GlobalTheory.SiegDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberUnitTranslateEqIdFieldPointsStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualNumber_unit_translate_eq_id_field_points : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (S : Type) [CommRing S] (x0 : Sp S ⟶ X) (P : tEpsG x0 ⟶ t.G), spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ P.left = (1 : Over.mk x0 ⟶ t.G).left → ∀ y : (tEpsG x0 ⊗ t.G).left, ∃ (K : Type) (_ : Field K) (z : Sp K ⟶ (tEpsG x0 ⊗ t.G).left), y ∈ Set.range z.base ∧ z ≫ (lift (fst (tEpsG x0) t.G ≫ P) (snd (tEpsG x0) t.G) ≫ μ[t.G]).left = z ≫ (snd (tEpsG x0) t.G).left := by
  first | exact @GlobalTheory.InfTranslPts.transl_points | exact GlobalTheory.InfTranslPts.transl_points | (intros; apply GlobalTheory.InfTranslPts.transl_points <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoboundaryOfMemHodgeFiltrationStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coboundary_of_mem_hodgeFiltration : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → ∀ (K : Type) (W : K → (A ⊗ B).left.Opens), ⨆ i, W i = ⊤ → ∀ (J : Type) [Fintype J] (a : J → Fn1 A) (β : J → Z1 (O (dp0 R) (B.hom ≫ 𝟙 _))) (hβ : ∀ i, CatCoh.H1.mk _ (β i) ∈ primDR B) (n : Fn1 (A ⊗ B)), (∀ i, IsCoc (whole A) (a i)) → IsCupCob W a (fun i ↦ fv (β i)) n → ∀ y ∈ Fil B, ∃ k : Fn0 A, IsCob (whole A) (fun D _ _ D' _ _ φ x ↦ ∑ i, a i D D' φ x * algebraMap R D' (y ⟨_, hβ i⟩)) k := by
  first | exact @GlobalTheory.PtExt.OrthPt.exists_isCob_of_mem_fil | exact GlobalTheory.PtExt.OrthPt.exists_isCob_of_mem_fil | (intros; apply GlobalTheory.PtExt.OrthPt.exists_isCob_of_mem_fil <;> assumption)
end

