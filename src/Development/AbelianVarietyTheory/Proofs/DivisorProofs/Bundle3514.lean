import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3417
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0085
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3485
import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreIsoCarriesSharpPointsToConjugates
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0160
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2496
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaCoordinatesExistUniqueSeparatePoints
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0052
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3442
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3474
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3487
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3462

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsRatAwayIff
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TorsAway

theorem torsRat_away_iff : ∀ (R : Type) [CommRing R] [IsDomain R] (f : R) [IsDomain (Localization.Away f)] (G : Over (Sp R))
    [GrpObj G] (G' : Over (Sp (Localization.Away f))) [GrpObj G'] (π : G'.left ⟶ G.left),
    IsGrpPullback G' G (spMap (algebraMap R (Localization.Away f))) π → ∀ n : ℕ,
      GlobalTheory.TChart.TorsRat G n ↔ GlobalTheory.TChart.TorsRat G' n := by
  intro R _ _ f _ G _ G' _ π hπ n
  have hf : f ≠ 0 := by
    rintro rfl
    have : Subsingleton (Localization.Away (0 : R)) :=
      IsLocalization.subsingleton (M := Submonoid.powers (0 : R)) ⟨1, pow_one _⟩
    exact not_subsingleton (Localization.Away (0 : R)) this
  have hle : Submonoid.powers f ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors hf
  have hinj : Function.Injective (algebraMap R (Localization.Away f)) := IsLocalization.injective _ hle
  constructor
  · exact GlobalTheory.TChart.AbLevel.torsRat_of_isGrpPullback _ hinj hπ
  · intro h K _ _ κ x hx
    letI : Algebra (Localization.Away f) (FractionRing R) :=
      IsLocalization.localizationAlgebraOfSubmonoidLe (Localization.Away f) (FractionRing R) _ _ hle
    haveI : IsScalarTower R (Localization.Away f) (FractionRing R) :=
      IsLocalization.localization_isScalarTower_of_submonoid_le (Localization.Away f) (FractionRing R) _ _ hle
    haveI : IsFractionRing (Localization.Away f) (FractionRing R) :=
      IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers f) (Localization.Away f)
        (FractionRing R)
    let e := FractionRing.algEquiv (Localization.Away f) (FractionRing R)
    let j : FractionRing (Localization.Away f) →+* FractionRing R := e.toAlgHom.toRingHom
    have hj : ∀ r : R, j (algebraMap _ (FractionRing (Localization.Away f)) (algebraMap R (Localization.Away f) r)) =
        algebraMap R (FractionRing R) r := by
      intro r
      exact (e.commutes _).trans (IsScalarTower.algebraMap_apply R (Localization.Away f) (FractionRing R) r).symm
    have hsq : spMap j ≫ jK (Localization.Away f) ≫ spMap (algebraMap R (Localization.Away f)) = jK R := by
      show spMap j ≫ spMap (algebraMap _ (FractionRing (Localization.Away f))) ≫ spMap (algebraMap R (Localization.Away f)) =
        spMap (algebraMap R (FractionRing R))
      rw [← ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, ← ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp]
      exact congrArg spMap (RingHom.ext hj)
    let T : Over (Sp (Localization.Away f)) := Over.mk (spMap (κ.comp j) ≫ jK (Localization.Away f))
    have hT : T.hom ≫ spMap (algebraMap R (Localization.Away f)) = spMap κ ≫ jK R := by
      show (spMap (κ.comp j) ≫ jK (Localization.Away f)) ≫ spMap (algebraMap R (Localization.Away f)) = _
      rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, Category.assoc, Category.assoc, hsq]
    let e0 : Over.mk (T.hom ≫ spMap (algebraMap R (Localization.Away f))) ⟶ Over.mk (spMap κ ≫ jK R) :=
      Over.homMk (𝟙 _) ((Category.id_comp _).trans hT.symm)
    let x' := (GlobalTheory.ObjPull.pushEquiv hπ T).symm (e0 ≫ x)
    have hx' : x' ^ n = 1 := by
      simp only [x']
      rw [← map_pow, ← MonObj.comp_pow, hx, MonObj.comp_one, map_one]
    obtain ⟨y, hy⟩ := h K (κ.comp j) x' hx'
    have hyw : y.left ≫ G'.hom = jK (Localization.Away f) := Over.w y
    refine ⟨Over.homMk (spMap j ≫ y.left ≫ π) ?_, ?_⟩
    · show (spMap j ≫ y.left ≫ π) ≫ G.hom = jK R
      rw [Category.assoc, Category.assoc, hπ.1.w, ← Category.assoc y.left, hyw]
      exact hsq
    · show x.left = spMap κ ≫ spMap j ≫ y.left ≫ π
      have h1 : x'.left ≫ π = x.left :=
        (GlobalTheory.ObjPull.pushEquiv_symm_left hπ T (e0 ≫ x)).trans (Category.id_comp _)
      rw [← h1, hy, ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp]
      simp only [Category.assoc]

end GlobalTheory.TorsAway
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionCoordinatesScalarMulSubfieldValued
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
open GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.USep.Coords

open GlobalTheory GlobalTheory.UT.SymFrame GlobalTheory.ThetaCoord GlobalTheory.CommPairing GlobalTheory.GlobalLift GlobalTheory.VVRank GlobalTheory.CoordSep GlobalTheory.UT.CoefBasic
open GlobalTheory.TorusExt GlobalTheory.Poinc.Sep GlobalTheory.Poinc.Sep.ConjPt

variable {V : Type} [CommRing V] [IsDomain V] {D : DegPre V}

theorem psi_pow {N : ℕ} {b : 𝟙_ (Over (Sp V)) ⟶ D.P.A} (hb : b ^ N = 1) (Ψ : LB.Gen (psiLB D.P N b)) (hΨ : Ψ.IsGen)
    {κ : LB.Gen (kapLB D (𝟙 D.P.A ^ N) (N ^ 2) 1)} (hκ : Normd κ)
    (h₁ : ∀ (T : Over (Sp V)) (z : T.left) (J), Good D.P.L z J →
      val Ψ (1 : T ⟶ D.P.A).left z J ^ N * val κ (toUnit T ≫ b).left z J = 1)
    {T : Over (Sp V)} (x : T ⟶ D.P.A) (z : T.left) (J) (hJ : Good D.P.L z J) :
    val Ψ x.left z J ^ N * val κ ((toUnit T ≫ b) * x).left z J = val κ x.left z J := by
  have key := ((((grep_gen (Y := D.P.A) Ψ hΨ (𝟙 _)).pow N).mul (grep_kap κ hκ.1 ((toUnit D.P.A ≫ b) * 𝟙 D.P.A))).mul
    (grep_kap κ hκ.1 (𝟙 D.P.A)).inv).triv GlobalTheory.abelianSchemeLaws_all.1.globalFns (fun U _ h => by
      rw [Fin.prod_univ_two, mul_pow (toUnit D.P.A ≫ b), ← MonObj.comp_pow, hb, MonObj.comp_one, _root_.one_mul]
      show (h (𝟙 _ ≫ 𝟙 _) ^ (N : ℤ) * h (𝟙 _ ≫ ((toUnit D.P.A ≫ b) * 𝟙 D.P.A).left) ^ (-(N : ℤ))) ^ N * _ * _ = _
      rw [Category.id_comp, Category.id_comp, Over.id_left]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one, ← natCast_zsmul]
      module)
    (fun y J hJ => by
      beta_reduce
      rw [Category.comp_id, Category.comp_id, normd_one hκ hJ, MonObj.comp_mul, Category.comp_id, _root_.mul_one,
        ← Category.assoc, comp_toUnit, h₁ _ y J hJ, inv_one, _root_.mul_one]) T x z J hJ
  beta_reduce at key
  rw [Category.comp_id, Category.comp_id, MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit,
    mul_inv_eq_one] at key
  exact key

theorem lift_pow {m : ℕ} {T : Over (Sp V)} {y : T ⟶ D.P.A} (hy : y ^ m ^ 2 = 1)
    (θ : ThetaGrp D.P.A D.P.L ((m : ℤ) ^ 2) T) (hθ : SymLift D.P.A D.P.L ((m : ℤ) ^ 2) (m ^ 2) y θ)
    (α : LB.Gen (LB.LinComb D.P.L (K := Fin 2) ![(snd T D.P.A).left, (snd T D.P.A ^ m).left] ![(m : ℤ) ^ 2, -1]))
    (hα : α.IsGen) {κ : LB.Gen (kapLB D (𝟙 D.P.A ^ (m ^ 2)) ((m ^ 2) ^ 2) 1)} (hκ : κ.IsGen)
    (x : T ⟶ D.P.A) (z : T.left) (J) (hJ : Good D.P.L z J) :
    ((tval θ (lift (𝟙 T) x).left z J * val α (lift (𝟙 T) (y * x)).left z J) ^ (m ^ 2) ^ 2 *
      val κ (y ^ m * x ^ m).left z J) ^ m ^ 2 =
      (val α (lift (𝟙 T) x).left z J ^ (m ^ 2) ^ 2 * val κ (x ^ m).left z J) ^ m ^ 2 := by
  obtain rfl := hθ.pt_eq
  have hL := D.P.isLB
  have G := ((((grep_gen (Y := T ⊗ D.P.A) θ.φ θ.isGen (𝟙 _)).mul
    (grep_gen α hα (translT D.P.A θ.pt).left)).pow ((m ^ 2) ^ 2)).mul
      (grep_kap κ hκ ((fst T D.P.A ≫ θ.pt) ^ m * snd T D.P.A ^ m))).mul
    (((grep_gen α hα (𝟙 _)).pow ((m ^ 2) ^ 2)).mul (grep_kap κ hκ (snd T D.P.A ^ m))).inv
  obtain ⟨K, _, φ, ε, s, hs, h₁, h₂⟩ := G
  obtain ⟨a, ha⟩ := SymLiftOdd.exists_const hL (fst T D.P.A).left (lift (𝟙 T) (1 : T ⟶ D.P.A)).left
    (by rw [← Over.comp_left, lift_fst]; rfl) (SymLiftOdd.surj_fst GlobalTheory.abelianSchemeLaws_all.1.globalFns D.P.isAb T)
    (fun U _ h => (h₁ U h).trans (by
      have e₁ : (translT D.P.A θ.pt).left ≫ (snd T D.P.A).left = ((fst T D.P.A ≫ θ.pt) * snd T D.P.A).left := by
        rw [← Over.comp_left, translT, lift_snd]; rfl
      have e₂ : (translT D.P.A θ.pt).left ≫ (snd T D.P.A ^ m).left =
          ((fst T D.P.A ≫ θ.pt) ^ m * snd T D.P.A ^ m).left := by
        rw [← Over.comp_left, MonObj.comp_pow, translT, lift_snd, ← mul_pow]; rfl
      have e₃ : ((fst T D.P.A ≫ θ.pt) ^ m * snd T D.P.A ^ m) ^ m ^ 2 = (snd T D.P.A ^ m) ^ m ^ 2 := by
        rw [mul_pow, ← pow_mul, mul_comm m, pow_mul, ← MonObj.comp_pow, hy, MonObj.comp_one, one_pow, _root_.one_mul]
      beta_reduce
      rw [Fin.prod_univ_two, Fin.prod_univ_two, Fin.prod_univ_two, e₃]
      show (h (𝟙 _ ≫ (snd T D.P.A).left) ^ ((m : ℤ) ^ 2) *
          h (𝟙 _ ≫ ((fst T D.P.A ≫ θ.pt) * snd T D.P.A).left) ^ (-((m : ℤ) ^ 2)) *
        (h ((translT D.P.A θ.pt).left ≫ (snd T D.P.A).left) ^ ((m : ℤ) ^ 2) *
          h ((translT D.P.A θ.pt).left ≫ (snd T D.P.A ^ m).left) ^ (-1 : ℤ))) ^ _ * _ *
        ((h (𝟙 _ ≫ (snd T D.P.A).left) ^ ((m : ℤ) ^ 2) * h (𝟙 _ ≫ (snd T D.P.A ^ m).left) ^ (-1 : ℤ)) ^ _ * _)⁻¹ = _
      rw [e₁, e₂, Category.id_comp, Category.id_comp, Category.id_comp]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one, ← natCast_zsmul]
      push_cast
      module)) hs
  let f : (T ⟶ D.P.A) → (T.left.presheaf.stalk z)ˣ := fun x =>
    val α (lift (𝟙 T) x).left z J ^ (m ^ 2) ^ 2 * val κ (x ^ m).left z J
  have key : ∀ x : T ⟶ D.P.A, tval θ (lift (𝟙 T) x).left z J ^ (m ^ 2) ^ 2 * f (θ.pt * x) =
      gm (𝟙 T.left) z ⊤ a * f x := fun x => by
    have e := (h₂ T (lift (𝟙 T) x) z J hJ).symm.trans (ha _ _ z J hJ)
    beta_reduce at e
    rw [lift_fst_left, Category.comp_id, lift_translT, Category.id_comp,
      MonObj.comp_mul, MonObj.comp_pow, MonObj.comp_pow, lift_snd, ← Category.assoc, lift_fst, Category.id_comp,
      mul_inv_eq_iff_eq_mul, mul_pow, _root_.mul_assoc] at e
    simp only [f]
    rw [mul_pow θ.pt]
    exact e
  have hp : ∏ j ∈ Finset.range (m ^ 2), tval θ (lift (𝟙 T) (θ.pt ^ j * x)).left z J = 1 := by
    have c := val_corr hJ hθ.pow_eq (lift (𝟙 T) x).left
    rw [ThetaPullback.val_powGen θ _ _ hJ, val_one] at c
    rw [← c, Finset.prod_range]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [lift_translT, Category.id_comp]
    rfl
  have tel : ∀ n : ℕ, (∏ j ∈ Finset.range n, tval θ (lift (𝟙 T) (θ.pt ^ j * x)).left z J) ^ (m ^ 2) ^ 2 *
      f (θ.pt ^ n * x) = gm (𝟙 T.left) z ⊤ a ^ n * f x := fun n => by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.prod_range_succ, mul_pow, _root_.mul_assoc, pow_succ' θ.pt, _root_.mul_assoc θ.pt, key,
        mul_left_comm, ih, pow_succ', _root_.mul_assoc]
  have ha1 := tel (m ^ 2)
  rw [hp, hy, one_pow, _root_.one_mul, _root_.one_mul, eq_comm, mul_eq_right] at ha1
  have k := congrArg (· ^ m ^ 2) (key x)
  simp only [f] at k
  rw [mul_pow (gm _ _ _ _), ha1, _root_.one_mul, mul_pow θ.pt, ← _root_.mul_assoc, ← mul_pow] at k
  exact k

theorem exists_scalar {K R : Type} [Field K] [CommRing R] (φ : K →+* R) (hφ : Function.Injective φ) (k₀ : Subfield K)
    [IsAlgClosed k₀] {M : ℕ} (hM : 1 ≤ M) {I : Type} (v : I → K) (Λ : R)
    (h : ∀ i, ∃ r ∈ k₀, φ (v i) ^ M = Λ * φ r) :
    ∃ (l : K) (r : I → K), (∀ i, r i ∈ k₀) ∧ ∀ i, v i = l * r i := by
  by_cases h0 : ∀ i, v i = 0
  · exact ⟨0, fun _ => 0, fun _ => k₀.zero_mem, fun i => by rw [h0, zero_mul]⟩
  obtain ⟨i₀, hi₀⟩ := not_forall.1 h0
  obtain ⟨r₀, m₀, e₀⟩ := h i₀
  have hr₀ : r₀ ≠ 0 := by
    rintro rfl
    rw [map_zero, mul_zero, ← map_pow, map_eq_zero_iff φ hφ] at e₀
    exact pow_ne_zero M hi₀ e₀
  refine ⟨v i₀, fun i => v i / v i₀, fun i => ?_, fun i => (mul_div_cancel₀ _ hi₀).symm⟩
  obtain ⟨r, m₁, e₁⟩ := h i
  have e : v i ^ M * r₀ = r * v i₀ ^ M := hφ (by
    rw [map_mul, map_mul, map_pow, map_pow, e₀, e₁]; ring)
  refine Frames.mem_of_pow_mem k₀ hM (x := v i / v i₀) ?_
  rw [div_pow, (div_eq_div_iff (pow_ne_zero M hi₀) hr₀).2 e]
  exact k₀.div_mem m₁ m₀

theorem coords_scalar [IsLocalRing V] [IsNoetherianRing V] [IsIntegrallyClosed V] (D : DegPre V) {m : ℕ} (hm : 1 ≤ m)
    {X C : Type} [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V) (mo : X → V) (a : D.X)
    (hmo : mo (e.symm (m • a)) ≠ 0) (c₀ : C) (hu : IsUnit (u (e.symm (m • a)) c₀))
    (hT : IsThetaTerms D (m ^ 2) e (fun mu c => u mu c * mo mu))
    {K : Type} [Field K] [IsAlgClosed K] (ev : V →+* K) (k₀ : Subfield K) [IsAlgClosed k₀]
    (hr : ∀ c, ∃ r ∈ k₀, ev (u (e.symm (m • a)) c) = r * ev (u (e.symm (m • a)) c₀))
    {I : Type} (y : I → (Over.mk (spMap ev) ⟶ D.P.A)) (hy : ∀ i, y i ^ m ^ 2 = 1) (v : I → K)
    (H : GlobalTheory.Ex.IsCoordPt D.P m y (toUnit _ ≫ D.c a) (fun i => GlobalTheory.Ex.fnOf (v i))) :
    ∃ (l : K) (r : I → K), (∀ i, r i ∈ k₀) ∧ ∀ i, v i = l * r i := by
  have hL := D.P.isLB
  have hN : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ hm
  set mu := e.symm (m • a) with hmu
  have hc : ∀ n : ℕ, D.c (n • a) = D.c a ^ n := fun n => by
    induction n with
    | zero =>
      have h := D.c_add 0 0
      rw [add_zero] at h
      rw [zero_smul, pow_zero]
      exact mul_eq_left.1 h.symm
    | succ n ih => rw [succ_nsmul, D.c_add, ih, pow_succ]; rfl
  have hχ : D.c (e mu) = D.c a ^ m := by rw [hmu, e.apply_symm_apply, hc]
  obtain ⟨th, g, b, w, h₁, h₂, h₃, h₄, h₅, -⟩ := hT
  have hb : ∀ c, b c ^ m ^ 2 = 1 := fun c => (Frames.torsion_of_nsmul (g c) (b c) (h₁ c) (h₂ c)).2
  obtain ⟨θ, hθ⟩ := exists_genAll D.P
  choose Ψ hΨ nΨ vΨ using fun c => exists_psi hN (g c) (b c) (h₁ c) (h₂ c) (w c) (h₄ c)
  obtain ⟨ρ, A, cross, hA⟩ := exists_vals hθ (m ^ 2) (e mu) (th.s (e mu)) g b h₁ w Ψ hΨ (fun c => vΨ c (e mu)) _ (h₅ mu)
  obtain ⟨κ, hκ⟩ := exists_kap (D := D) GlobalTheory.abelianSchemeLaws_all.1.mulPull (m ^ 2)
  have hv : ∀ c, ∃ r ∈ k₀, ev ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom (A c)) =
      r * ev ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom (A c₀)) := fun c => by
    obtain ⟨r, r₁, r₂⟩ := hr c
    have x := cross c c₀
    rw [mul_pow, mul_pow, mul_right_comm, mul_right_comm (u mu c₀ ^ m ^ 2)] at x
    have x' := congrArg ev (mul_right_cancel₀ (pow_ne_zero _ hmo) x)
    rw [map_mul, map_mul, map_pow, map_pow, r₂] at x'
    refine ⟨r ^ m ^ 2, k₀.pow_mem r₁ _, mul_left_cancel₀ (pow_ne_zero (m ^ 2) (hu.map ev).ne_zero) (x'.symm.trans ?_)⟩
    ring
  obtain ⟨-, -, t, s₁, α, τ, U, s₂, -, hα, -, hs₁, hU, hs₂, hval⟩ := H
  obtain ⟨k, hk⟩ := hθ K (spMap ev) t
  let T : Over (Sp V) := Over.mk (spMap ev)
  obtain ⟨p⟩ : Nonempty T.left := inferInstanceAs (Nonempty (PrimeSpectrum K))
  obtain ⟨J, hJ⟩ := exists_good' hL p
  have alg : ∀ {R : Type} [CommRing R] (N : ℕ) (v k t A A₀ r : R) (τ P α Ψ ρ κ κ' : Rˣ), v * τ.val = P.val * (k * t) →
      A = t ^ N * (Ψ * ρ ^ N).val → A = r * A₀ → Ψ ^ N * κ' = κ → (P ^ N ^ 2 * κ') ^ N = (α ^ N ^ 2 * κ) ^ N →
      v ^ N ^ 3 = (((α * τ⁻¹ * ρ⁻¹).val * k) ^ N ^ 3 * A₀ ^ N ^ 2) * r ^ N ^ 2 := by
    intro R _ N v k t A A₀ r τ P α Ψ ρ κ κ' a₁ a₂ a₃ a₄ a₅
    have a₆ : (P * τ⁻¹) ^ N ^ 3 = (α * τ⁻¹ * ρ⁻¹) ^ N ^ 3 * (Ψ * ρ ^ N) ^ N ^ 2 := by
      subst a₄
      have a := congrArg Additive.ofMul a₅
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_pow, ← natCast_zsmul] at a ⊢
      push_cast at a ⊢
      linear_combination (norm := module) a
    have a₇ : v = (P * τ⁻¹).val * (k * t) := by
      rw [Units.val_mul, mul_right_comm, ← a₁, Units.mul_inv_cancel_right]
    rw [_root_.mul_assoc, ← mul_pow A₀, mul_comm A₀, ← a₃, a₂, a₇, mul_pow, ← Units.val_pow_eq_pow_val, a₆,
      Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
    ring
  refine exists_scalar (GlobalTheory.RatioVal.germConst K p) (RingHom.injective _) k₀ (M := (m ^ 2) ^ 3) (Nat.one_le_pow _ _ hN) v
    (@id (T.left.presheaf.stalk p) (((val α (lift (𝟙 T) (toUnit T ≫ D.c a)).left p J * (val τ (𝟙 T.left) p J)⁻¹ *
      (val ρ T.hom p J)⁻¹).val * gs (𝟙 T.left) p ⊤ k) ^ (m ^ 2) ^ 3 * (@id (T.left.presheaf.stalk p) <| GlobalTheory.RatioVal.germConst K p
        (ev ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom (A c₀)))) ^ (m ^ 2) ^ 2)) fun i => ?_
  obtain ⟨c, hc'⟩ := h₃ K (spMap ev) (y i ^ m) (by rw [← pow_mul, mul_comm m, pow_mul, hy, one_pow])
  obtain ⟨r, r₁, r₂⟩ := hv c
  refine ⟨r ^ (m ^ 2) ^ 2, k₀.pow_mem r₁ _, ?_⟩
  have ez : (toUnit T ≫ D.c a) ^ m = toUnit T ≫ D.c (e mu) := by rw [hχ, MonObj.comp_pow]
  have e₁ := sv_value (hval i) hJ
  rw [sv_act (hU i).pt_eq (hs₂ i) _ hJ, sv_mulPull hs₁ _ hJ, hk _ _ p J hJ, lift_fst_left, ← Over.comp_left, lift_snd,
    Category.id_comp, mul_pow, ez, hc', ← _root_.mul_assoc, ← Units.val_mul] at e₁
  have e₂ := (GlobalTheory.RatioVal.gs_specMap ev p _).symm.trans (hA c T p J hJ)
  have e₃ := psi_pow (hb c) (Ψ c) (hΨ c) hκ (nΨ c κ hκ) (toUnit T ≫ D.c (e mu)) p J hJ
  have e₄ := lift_pow (hy i) (U i) (hU i) α hα hκ.1 (toUnit T ≫ D.c a) p J hJ
  rw [ez, hc'] at e₄
  rw [map_pow]
  exact alg _ _ _ _ _ _ _ _ _ _ _ _ _ _ ((congrArg (· * _) (GlobalTheory.RatioVal.gs_id_const p (v i)).symm).trans e₁.symm) e₂
    ((congrArg _ r₂).trans (map_mul _ _ _)) e₃ e₄

end GlobalTheory.USep.Coords

open NumberField ReciprocityTheory.AnForm.R GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef GlobalTheory GlobalTheory.USep

theorem GlobalTheory.USep.coords_scalar_mul_rational : ∀ (g n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁), D.P.g = g → ∀ (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D ((n ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → ∀ (I : Type) (y : I → (Over.mk (spMap ev) ⟶ D.P.A)), (∀ i, y i ^ (n ^ j) ^ 2 = 1) → ∀ (a : D.X) (z : Over.mk (spMap ev) ⟶ D.P.A), z.left = spMap ev ≫ (D.c a).left → ∃ (v : I → K) (l : K) (r : I → K), GlobalTheory.Ex.IsCoordPt D.P (n ^ j) y z (fun i => GlobalTheory.Ex.fnOf (v i)) ∧ (∀ i, r i ∈ k₀) ∧ ∀ i, v i = l * r i := by
  intro g n hn hodd
  refine ⟨0, fun j _ V₁ _ _ _ hV hunit D _ X C _ e u mo hu hT K _ _ ev k₀ hk₀ hr I y hy a z hz => ?_⟩
  haveI : IsNoetherianRing V₁ := hV.1
  haveI : IsIntegrallyClosed V₁ := hV.2.1
  have hm : 1 ≤ n ^ j := Nat.one_le_pow _ _ hn.pos
  have hK : ((n ^ j : ℕ) : K) ≠ 0 := by
    have := ((hunit (n ^ j) (by omega)).map ev).ne_zero
    rwa [map_natCast] at this
  obtain rfl : z = toUnit _ ≫ D.c a := Over.OverMorphism.ext hz
  obtain ⟨v, hv⟩ := (GlobalTheory.CoordSep.coord_exists_unique_separate GlobalTheory.abelianSchemeLaws_all.1 K (Sp V₁) D.P (spMap ev)
    (n ^ j) hodd.pow hK I y hy).1 (toUnit _ ≫ D.c a)
  obtain ⟨hmo, c₀, hc₀⟩ := hu (e.symm ((n ^ j) • a))
  obtain ⟨l, r, h₁, h₂⟩ := Coords.coords_scalar D hm e u mo a hmo c₀ hc₀ hT ev k₀ (fun c => hr _ c c₀ hc₀) y hy v hv
  exact ⟨v, l, r, hv, h₁, h₂⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFrameMulIntegralFrameEqRootMulRig
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.FieldBaseChange GlobalTheory.UT

namespace GlobalTheory.USep.FrameRoot

theorem exists_normd {V : Type} [CommRing V] [IsDomain V] (D : DegPre V) (ρ : LB.Gen (D.P.L.pull (eSec D.P.A)))
    (hρ : ρ.IsGen) (n : ℕ)
    (α : LB.Gen (LB.LinComb D.P.L (K := Fin 2) ![𝟙 D.P.A.left, (mulA D.P.A n).left] ![(n : ℤ) ^ 2, -1]))
    (hα : α.IsGen) (hn : IsNormMul D.P.A D.P.L ρ n α) :
    ∃ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ n) (n ^ 2) 1), Normd κ ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ D.P.A.left) (z : Z) (J), Good D.P.L z J →
        val κ r z J = val α r z J * val ρ (r ≫ D.P.A.hom) z J * (val ρ (r ≫ D.P.A.hom) z J ^ (n ^ 2))⁻¹ := by
  have hL := D.P.isLB
  let p := LB.pullGen D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => 1) ρ D.P.A.hom
  have hp : p.IsGen := DVR.pullGen_isGen _ _ _ _ hρ _
  let u := LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ α p) (LB.invGen D.P.L _ _ (GeneratorPullback.powGen D.P.L _ _ p (n ^ 2)))
  have hu : u.IsGen := DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ hα hp)
    (DVR.invGen_isGen _ _ _ _ (DVR.SectionScalarValuation.powGen_isGen' _ _ _ _ hp _))
  have h1 : (1 : D.P.A ⟶ D.P.A).left = D.P.A.hom ≫ eSec D.P.A := rfl
  obtain ⟨κ, hκ, hv⟩ := exists_gen hL
    (φ' := (![𝟙 _, (𝟙 D.P.A ^ n).left, (1 : D.P.A ⟶ D.P.A).left] : Fin 3 → (D.P.A.left ⟶ D.P.A.left)))
    (ε' := ![((n ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ), ((1 : ℕ) : ℤ) - ((n ^ 2 : ℕ) : ℤ)]) (by
      intro U _ h
      rw [h1]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, Fintype.prod_sum_type, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module) u hu
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ D.P.A.left) (z : Z) (J), Good D.P.L z J →
      val κ r z J = val α r z J * val ρ (r ≫ D.P.A.hom) z J * (val ρ (r ≫ D.P.A.hom) z J ^ (n ^ 2))⁻¹ :=
    fun Z r z J hJ => by
      have a : val p r z J = val ρ (r ≫ D.P.A.hom) z J := val_pull hJ _ _ _
      refine (hv Z r z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
        ((val_mul hJ _ _ _).trans (congrArg _ a)) ((val_inv _ _).trans (congrArg (·⁻¹) ?_))))
      exact (GlobalTheory.RatioVal.val_powGen _ _ _ _ _).trans (congrArg (· ^ (n ^ 2)) a)
  refine ⟨κ, ⟨hκ, corr_of_val hL fun y J hJ => ?_⟩, key⟩
  have a₃ : val (rigPow D.P.A D.P.L ρ ((n : ℤ) ^ 2)) (𝟙 _) y J = val ρ (𝟙 _) y J ^ ((n : ℤ) ^ 2) := map_zpow _ _ _
  have e₁ : (𝟙 _ ≫ eSec D.P.A) ≫ D.P.A.hom = 𝟙 _ := by
    rw [Category.id_comp]; exact Over.w η[D.P.A]
  have b := (val_pull hJ α (eSec D.P.A) (𝟙 _)).symm.trans ((val_corr hJ hn (𝟙 _)).trans ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) a₃ (val_inv ρ (𝟙 _)))))
  refine (val_pull hJ κ _ _).trans ((key _ _ y J hJ).trans (Eq.trans ?_ (val_one _).symm))
  rw [b]
  refine (congrArg (fun q => val ρ (𝟙 _) y J ^ ((n : ℤ) ^ 2) * (val ρ (𝟙 _) y J)⁻¹ * val ρ q y J *
    (val ρ q y J ^ (n ^ 2))⁻¹) e₁).trans ?_
  rw [← Nat.cast_pow, zpow_natCast, inv_mul_cancel_right, mul_inv_cancel]

theorem val_rigT {S : Scheme.{0}} (P : PolAV S) (rig : LB.Gen (P.L.pull (eSec P.A))) (T : Over S) (k : ℤ) {Z : Scheme.{0}}
    (r : Z ⟶ T.left) {z : Z} {J : (Z ⟶ P.A.left) → P.L.ι} (hJ : Good P.L z J) :
    val (rigT P.A P.L rig T k) r z J = val rig (r ≫ T.hom) z J ^ k := by
  rw [val_of rig (r ≫ T.hom) z J (fun _ => J (r ≫ T.hom ≫ eSec P.A))
    (fun _ => by rw [Category.assoc])]
  have hm := hJ.mem (fun _ : Fin 1 => T.hom ≫ eSec P.A) r
  refine (map_zpow _ _ _).trans (congrArg (· ^ k) ?_)
  exact (gm_res r z _ hm _).trans (gm_pull r T.hom z
    (LB.wchart P.L (fun _ : PUnit => eSec P.A) (fun _ => J (r ≫ T.hom ≫ eSec P.A)))
    (Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hm 0) _)

theorem exists_root {V : Type} [CommRing V] [IsDomain V] (D : DegPre V) (T : Over (Sp V))
    (ρ : LB.Gen (D.P.L.pull (eSec D.P.A))) (hρ : ρ.IsGen) (n : ℕ) (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A)
    (τ : LB.Gen (LB.LinComb D.P.L (Y := T.left) (K := Fin 1) (fun _ => (toUnit T ≫ b).left) (fun _ => 1)))
    (hτ : IsTorsFrame D.P ρ n (toUnit T ≫ b) τ)
    (t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, b.left] (DegPre.lineε 1))) (ht : t.IsGen)
    (H : ∀ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ n) (n ^ 2) 1), Normd κ → ∀ (z : T.left) J, Good D.P.L z J →
      val t T.hom z J ^ (n ^ 2) * val κ (T.hom ≫ b.left) z J = 1) :
    ∃ c : Γ(T.left, ⊤)ˣ, c ^ (n ^ 2) = 1 ∧ ∀ (z : T.left) J, Good D.P.L z J →
      val τ (𝟙 _) z J * val t T.hom z J = gm (𝟙 T.left) z ⊤ c * val ρ T.hom z J := by
  have hL := D.P.isLB
  obtain ⟨-, hτg, α, hα, hn, hc⟩ := hτ
  obtain ⟨κ, hκ, hv⟩ := exists_normd D ρ hρ n α hα hn
  have hx : (toUnit T ≫ b).left = T.hom ≫ b.left := rfl
  let p := LB.pullGen D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => 1) ρ T.hom
  have hp : p.IsGen := DVR.pullGen_isGen _ _ _ _ hρ _
  let q := LB.pullGen D.P.L _ _ t T.hom
  have hq : q.IsGen := DVR.pullGen_isGen _ _ _ _ ht _
  obtain ⟨u, hu, hw⟩ := exists_gen hL (φ' := fun _ : PUnit => T.hom ≫ eSec D.P.A) (ε' := fun _ => 1) (by
      intro U _ h
      rw [hx]
      simp [Fin.prod_univ_succ, Fintype.prod_sum_type, DegPre.lineε, eSec, mul_comm, mul_left_comm])
    (LB.mulGen D.P.L _ _ _ _ τ q) (DVR.mulGen_isGen _ _ _ _ _ _ _ hτg hq)
  obtain ⟨c, hcv⟩ := GlobalTheory.CoordSep.exists_ratio_base hL (𝟙 T.left) (𝟙 T.left) (Category.comp_id _)
    (fun a => ⟨a, rfl⟩) hu hp
  have key : ∀ (z : T.left) J, Good D.P.L z J →
      val τ (𝟙 _) z J * val t T.hom z J = gm (𝟙 T.left) z ⊤ c * val ρ T.hom z J := fun z J hJ => by
    have a : val p (𝟙 _) z J = val ρ T.hom z J := (val_pull hJ _ _ _).trans (by rw [Category.id_comp])
    have a' : val q (𝟙 _) z J = val t T.hom z J := (val_pull hJ _ _ _).trans (by rw [Category.id_comp])
    have e := hcv _ (𝟙 _) z J hJ
    rw [hw _ _ z J hJ, val_mul hJ, a, a', Category.id_comp, mul_comm (val ρ T.hom z J)] at e
    exact e
  refine ⟨c, unit_ext fun z _ => ?_, key⟩
  choose J hJ using fun χ : T.left ⟶ D.P.A.left => exists_chart hL (χ z)
  replace hJ : Good D.P.L z J := hJ
  have e₁ : (T.hom ≫ b.left) ≫ D.P.A.hom = T.hom := Over.w (toUnit T ≫ b)
  have h₁ := H κ hκ z J hJ
  rw [hv _ _ z J hJ, e₁] at h₁
  have a₃ : val (powFrame D.P.A D.P.L _ τ ((n : ℤ) ^ 2)) (𝟙 _) z J = val τ (𝟙 _) z J ^ ((n : ℤ) ^ 2) := map_zpow _ _ _
  have h₂ := a₃.symm.trans ((val_corr hJ hc (𝟙 _)).trans ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) (val_pull hJ α _ _) (val_rigT D.P ρ T 1 _ hJ))))
  replace h₂ : val τ (𝟙 _) z J ^ (n ^ 2) = val α (T.hom ≫ b.left) z J * val ρ T.hom z J := by
    rw [← zpow_natCast, Nat.cast_pow, h₂, zpow_one, Category.id_comp, Category.id_comp, hx]
  have h₃ := congrArg (· ^ (n ^ 2)) (key z J hJ)
  simp only [mul_pow] at h₃
  rw [map_pow, map_one]
  have aux : ∀ {U : Type} [CommGroup U] (a s g r r' w : U), s * (w * r' * r⁻¹) = 1 → a = w * r' → a * s = g * r →
      g = 1 := by
    rintro U _ a s g r r' w h rfl h'
    rw [← h, ← _root_.mul_assoc, mul_comm s, h', mul_inv_cancel_right]
  exact aux _ _ _ _ _ _ h₁ h₂ h₃

theorem frame_mul_eq_root : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] (D : DegPre V₁) (K : Type) [Field K] (ev : V₁ →+* K) (ρ₀ : LB.Gen (D.P.L.pull (eSec D.P.A))), ρ₀.IsGen → ∀ (n : ℕ), 1 ≤ n → ∀ (b : 𝟙_ (Over (Sp V₁)) ⟶ D.P.A) (τ : LB.Gen (LB.LinComb D.P.L (Y := (Over.mk (spMap ev)).left) (K := Fin 1) (fun _ => (toUnit (Over.mk (spMap ev)) ≫ b).left) (fun _ => 1))), IsTorsFrame D.P ρ₀ n (toUnit (Over.mk (spMap ev)) ≫ b) τ → ∀ (t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, b.left] (DegPre.lineε 1))), t.IsGen → (∀ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ n) (n ^ 2) 1), Normd κ → ∀ (z : (Over.mk (spMap ev)).left) J, Good D.P.L z J → val t (Over.mk (spMap ev)).hom z J ^ (n ^ 2) * val κ ((Over.mk (spMap ev)).hom ≫ b.left) z J = 1) → ∃ ζ : K, ζ ^ (n ^ 2) = 1 ∧ ∀ (z : (Over.mk (spMap ev)).left) J, Good D.P.L z J → (val τ (𝟙 _) z J).val * (val t (Over.mk (spMap ev)).hom z J).val = gs (𝟙 (Over.mk (spMap ev)).left) z ⊤ (GlobalTheory.Ex.fnOf ζ) * (val ρ₀ (Over.mk (spMap ev)).hom z J).val := by
  intro V₁ _ _ D K _ ev ρ₀ hρ n _ b τ hτ t ht H
  obtain ⟨c, hc, hv⟩ := exists_root D (Over.mk (spMap ev)) ρ₀ hρ n b τ hτ t ht H
  let e : Γ((Over.mk (spMap ev)).left, ⊤) ≃+* K := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv
  have he : ∀ a : K, GlobalTheory.Ex.fnOf a = e.symm a := fun _ => rfl
  refine ⟨e c.val, ?_, fun z J hJ => ?_⟩
  · rw [← map_pow, ← Units.val_pow_eq_pow_val, hc, Units.val_one, map_one]
  · rw [he, e.symm_apply_apply, gs_unit _ _ ⊤ trivial, ← Units.val_mul, ← Units.val_mul]
    exact congrArg Units.val (hv z J hJ)

end GlobalTheory.USep.FrameRoot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitPullbackSemiAbelianModelIdentification
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.HodgeFrameGen
open GlobalTheory.QCoh (pullbackSections)

theorem GlobalTheory.HodgeFrameGen.traitPullback_identification : ∀ {S' : Scheme.{0}} {G : Over S'} [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
    ∀ {R : Type} [CommRing R] [IsDomain R] {G₁ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ →
    ∀ {y : Sp (FractionRing R) ⟶ S'} {α : pullback G₁.hom (jK R) ⟶ G.left},
    IsGrpPullback ((Over.pullback (jK R)).obj G₁) G y α →
    ∀ {W : Type} [CommRing W] [IsDomain W] [IsNoetherianRing W] [IsIntegrallyClosed W] (φ : R →+* W)
    (gam : FractionRing R →+* FractionRing W), (∀ r, gam (algebraMap R _ r) = algebraMap W _ (φ r)) →
    ∀ (χ' : Sp W ⟶ S'), spMap gam ≫ y = jK W ≫ χ' →
    ∃ (ρ' : ((Over.pullback (spMap gam)).obj ((Over.pullback (jK R)).obj G₁)).left ⟶
        ((Over.pullback (spMap φ)).obj G₁).left) (ψ' : ((Over.pullback (spMap φ)).obj G₁).left ⟶ G.left),
      IsGrpPullback ((Over.pullback (spMap gam)).obj ((Over.pullback (jK R)).obj G₁))
        ((Over.pullback (spMap φ)).obj G₁) (jK W) ρ' ∧
      IsGrpPullback ((Over.pullback (spMap φ)).obj G₁) G χ' ψ' ∧
      ρ' ≫ ψ' = pullback.fst _ _ ≫ α ∧
      ρ' ≫ pullback.fst G₁.hom (spMap φ) = pullback.fst _ _ ≫ pullback.fst G₁.hom (jK R) := by
  intro S' G _ _ hG R _ _ G₁ _ _ hG₁ y α hα W _ _ _ _ φ gam hgam χ' hχ
  have hsq : spMap gam ≫ jK R = jK W ≫ spMap φ := by
    simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r
    exact hgam r
  let A := (Over.pullback (spMap gam)).obj ((Over.pullback (jK R)).obj G₁)
  let G₁W := (Over.pullback (spMap φ)).obj G₁
  have hA : IsGrpPullback A ((Over.pullback (jK R)).obj G₁) (spMap gam) (pullback.fst _ _) :=
    isGrpPullback_pullback _ _
  have hAG₁ : IsGrpPullback A G₁ (jK W ≫ spMap φ)
      ((pullback.fst _ _ ≫ pullback.fst G₁.hom (jK R))) :=
    (hA.comp (isGrpPullback_pullback G₁ (jK R))).congr hsq rfl
  have hw : (pullback.fst _ _ ≫ pullback.fst G₁.hom (jK R)) ≫ G₁.hom = (A.hom ≫ jK W) ≫ spMap φ := by
    rw [hAG₁.1.w]; simp [Category.assoc]
  let ρ' : A.left ⟶ G₁W.left := pullback.lift (pullback.fst _ _ ≫ pullback.fst G₁.hom (jK R)) (A.hom ≫ jK W) hw
  have hρfst : ρ' ≫ pullback.fst G₁.hom (spMap φ) = pullback.fst _ _ ≫ pullback.fst G₁.hom (jK R) :=
    pullback.lift_fst _ _ _
  have hρ : IsGrpPullback A G₁W (jK W) ρ' :=
    (isGrpPullback_pullback G₁ (spMap φ)).cancel (hAG₁.congr rfl hρfst.symm) (pullback.lift_snd _ _ _)
  have hG₁W : IsSemiAbelian G₁W := IsSemiAbelian.pullback (spMap φ) G₁ hG₁
  obtain ⟨ψ', hψ, hc⟩ := GlobalTheory.SemiAbDesc.exists_grpPullback_map W y ((Over.pullback (jK R)).obj G₁) G α hG hα
    G₁W hG₁W χ' (spMap gam) hχ A ρ' (pullback.fst _ _) hρ hA
  exact ⟨ρ', ψ', hρ, hψ, hc, hρfst⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinBundleIsomorphism
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhin_bundle_isomorphism : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → LBIso c.P ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (GlobalTheory.ZarhinFam.incZ c.A B ⊗ₘ GlobalTheory.ZarhinFam.incZ c.A B).left) := by
  first | (exact @GlobalTheory.ZarhinFam.zarhinBundle_pullback_inclusion) | (exact GlobalTheory.ZarhinFam.zarhinBundle_pullback_inclusion) | (intros; apply GlobalTheory.ZarhinFam.zarhinBundle_pullback_inclusion  <;> assumption)
end

