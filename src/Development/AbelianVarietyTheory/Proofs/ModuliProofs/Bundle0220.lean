import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0214
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0216
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0074
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0203
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0145
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0188
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0153
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0190
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0191
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0136
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0134
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0084
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0159
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaCosetNonvanishingOfHasTh
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0062
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0101
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0064
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0085
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0020
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0025
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0105
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0218
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0217
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionDescentFiniteEtaleCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaObjectNearGoodPrime
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

noncomputable section
namespace GlobalTheory.ZM.NearBuild

section
variable {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)}
  {Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ} {κ : ℕ} {R : Type} [CommRing R] {β : o →+* R} {v : Ix g (N' ^ 2) → R}

theorem nearC_of_den_loc (h2 : Out.Laws2) {q₀ : Ideal R} (h : Den b Mat κ β v q₀) {f : R} (hf : f ∉ q₀)
    (H : ∀ q₁, Den b Mat κ ((loc f).comp β) (fun a => loc f (v a)) q₁ →
      NearC b Mat κ ((loc f).comp β) (fun a => loc f (v a)) q₁) : NearC b Mat κ β v q₀ := by
  obtain ⟨q₁, hq₁, rfl⟩ := h.loc hf
  exact GlobalTheory.ZM.NearBuild.nearC_of_loc h2 o g N' J b Mat κ R β v f q₁ (isPrime_of_mem hq₁.2) (H q₁ hq₁)

theorem span_map {R' I : Type} [CommRing R'] (ρ : R →+* R') {w : I → R} (h : Ideal.span (Set.range w) = ⊤) :
    Ideal.span (Set.range fun a => ρ (w a)) = ⊤ := by
  have := congrArg (Ideal.map ρ) h
  rwa [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at this

theorem span_of_unit {R' I : Type} [CommRing R'] {w : I → R'} (a : I) (h : IsUnit (w a)) :
    Ideal.span (Set.range w) = ⊤ :=
  Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨a, rfl⟩) h

theorem isUnit_loc {f a : R} (h : a ∣ f) : IsUnit (loc f a) :=
  isUnit_of_dvd_unit (map_dvd _ h) (IsLocalization.Away.algebraMap_isUnit f)
end

section
variable (h1 : Out.Laws) (h2 : Out.Laws2) {g : ℕ} {J : Type} {Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ}
  {κ n j : ℕ} (hn : n.Prime) (hodd : Odd n) (hj : 2 ≤ j) {o : Type} [CommRing o] {b : TBase o ((n ^ j) ^ 2)}
include h1 h2 hn hodd hj

theorem nearC_of_grpFam {R : Type} [CommRing R] [IsNoetherianRing R] [IsReduced R] {β : o →+* R}
    {v : Ix g ((n ^ j) ^ 2) → R} {A : Over (Sp R)} [GrpObj A] {M : LB A.left} {act : J → (A ⟶ A)}
    {Q : Fin (2 * g) → (Out.baseOver (Sp R) ⟶ A)} {q₀ : Ideal R} (h : Den b Mat κ β v q₀)
    (hv : Ideal.span (Set.range v) = ⊤) (hA : GrpFam b Mat κ β v (n ^ 2) A M act Q) : NearC b Mat κ β v q₀ := by
  obtain ⟨L, hL⟩ := GlobalTheory.ZM.NearBuild.exists_polFam_of_grpFam h1 h2 o g _ J b Mat κ R β v (n ^ 2) A M act Q (pow_ne_zero _ hn.ne_zero) hodd.pow
    (pow_dvd_pow n hj) h.1 hA
  obtain ⟨f, hf, hK⟩ := GlobalTheory.ZM.NearBuild.kTriv_near_good_prime o g _ J b Mat κ R β v A L act Q q₀ h.2 hL
  obtain ⟨act', Q', hL'⟩ := GlobalTheory.ZM.NearBuild.polFam_baseChange o g _ J b Mat κ R β v A L act Q _ (loc f) hL
  exact nearC_of_den_loc h2 h hf fun q₁ hq₁ =>
    GlobalTheory.ZM.NearBuild.nearC_of_polFam_of_kTriv h1 h2 g n j J hn hodd hj o b Mat κ _ _ _ _ _ act' Q' q₁ hq₁ (span_map _ hv) hL' hK

theorem nearC_of_smooth [Finite J]
    (hadd : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R) (Z : Over (Sp R)) (M : LB Z.left) (th : Ix g ((n ^ j) ^ 2) → M.Sec) (sc : Ix g ((n ^ j) ^ 2) → (Out.baseOver (Sp R) ⟶ Z)) (q₀ : Ideal R), Den b Mat κ β v q₀ → Fam b Mat κ β v (n ^ 2) M th sc → Smooth Z.hom → ∃ f : R, f ∉ q₀ ∧ ∀ (R' : Type) [CommRing R'] (ρ : R →+* R'), IsUnit (ρ f) → ∀ (Z' : Over (Sp R')) (π : Z'.left ⟶ Z.left), IsPullback π Z'.hom Z.hom (spMap ρ) → ∃ mu : Z' ⊗ Z' ⟶ Z', AddOk b Mat κ β v (n ^ 2) M th sc ρ π mu)
    (hend : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R) (Z : Over (Sp R)) (M : LB Z.left) (th : Ix g ((n ^ j) ^ 2) → M.Sec) (sc : Ix g ((n ^ j) ^ 2) → (Out.baseOver (Sp R) ⟶ Z)) (q₀ : Ideal R) (i : Option J), Den b Mat κ β v q₀ → Fam b Mat κ β v (n ^ 2) M th sc → Smooth Z.hom → ∃ f : R, f ∉ q₀ ∧ ∀ (R' : Type) [CommRing R'] (ρ : R →+* R'), IsUnit (ρ f) → ∀ (Z' : Over (Sp R')) (π : Z'.left ⟶ Z.left), IsPullback π Z'.hom Z.hom (spMap ρ) → ∃ F : Z' ⟶ Z', EndOk b Mat κ β v (n ^ 2) M th sc ρ π i F)
    {R : Type} [CommRing R] [IsNoetherianRing R] [IsReduced R] {β : o →+* R}
    {v : Ix g ((n ^ j) ^ 2) → R} {Z : Over (Sp R)} {M : LB Z.left} {th : Ix g ((n ^ j) ^ 2) → M.Sec}
    {sc : Ix g ((n ^ j) ^ 2) → (Out.baseOver (Sp R) ⟶ Z)} {q₀ : Ideal R} (h : Den b Mat κ β v q₀)
    (hv : Ideal.span (Set.range v) = ⊤) (hZ : Fam b Mat κ β v (n ^ 2) M th sc)
    (hs : SmoothOfRelativeDimension g Z.hom) : NearC b Mat κ β v q₀ := by
  classical
  have := Fintype.ofFinite J
  haveI : NeZero ((n ^ j) ^ 2) := ⟨pow_ne_zero _ (pow_ne_zero _ hn.ne_zero)⟩
  have hs' : Smooth Z.hom := SmoothOfRelativeDimension.smooth g _
  have hq := isPrime_of_mem h.2
  obtain ⟨f₁, hf₁, hmu⟩ := hadd R β v Z M th sc q₀ h hZ hs'
  choose f₂ hf₂ hF using fun i => hend R β v Z M th sc q₀ i h hZ hs'
  obtain ⟨f₃, hf₃, hc⟩ : ∃ f, f ∉ q₀ ∧ GeometricallyConnected (pullback.snd Z.hom (spMap (loc f))) := by
    obtain ⟨K, _, _, x, s, t, rfl, ht⟩ := mem_objPrimes.1 h.2
    obtain ⟨φ, hφ⟩ := hZ.2.2 K x s t ht
    obtain ⟨I, p, hI, -⟩ := hZ.1
    refine GlobalTheory.ConnSpread.exists_geometricallyConnected_away_of_fibre R _ Z.hom K x (GlobalTheory.ZM.projRep_projective_ample R _ I Z M th hI).1 hs' ?_
    have := t.ab.geomConnected
    refine MorphismProperty.of_isPullback (P := @GeometricallyConnected)
      (IsPullback.of_horiz_isIso (fst := hφ.1.isoPullback.inv) (g := 𝟙 _) ⟨?_⟩) this
    rw [hφ.1.isoPullback_inv_snd, Category.comp_id]
  let f := f₁ * f₃ * ∏ i, f₂ i
  have hf : f ∉ q₀ := fun hh => by
    rcases hq.mem_or_mem hh with hh | hh
    · exact (hq.mem_or_mem hh).elim hf₁ hf₃
    · obtain ⟨i, -, hi⟩ := Ideal.IsPrime.prod_mem_iff.1 hh
      exact hf₂ i hi
  let Z' : Over (Sp (Localization.Away f)) := Over.mk (pullback.snd Z.hom (spMap (loc f)))
  have hpb : IsPullback (pullback.fst Z.hom (spMap (loc f))) Z'.hom Z.hom (spMap (loc f)) :=
    IsPullback.of_hasPullback _ _
  obtain ⟨mu, hmu⟩ := hmu _ (loc f) (isUnit_loc ((dvd_mul_right f₁ f₃).mul_right _)) Z' _ hpb
  choose F hF using fun i => hF i _ (loc f)
    (isUnit_loc ((Finset.dvd_prod_of_mem f₂ (Finset.mem_univ i)).mul_left _)) Z' _ hpb
  obtain ⟨th', sc', hZ', hfib⟩ := GlobalTheory.ZM.NearBuild.fam_baseChange o g _ J b Mat κ R β v _ Z M th sc _ (loc f) Z' _ hpb hZ
  have hs₁ : SmoothOfRelativeDimension g Z'.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hpb hs
  have hc₁ : GeometricallyConnected Z'.hom := by
    have hu : IsUnit (loc f f₃) := isUnit_loc ((dvd_mul_left f₃ f₁).mul_right _)
    have e : spMap (loc f) = spMap (IsLocalization.Away.lift f₃ hu : Localization.Away f₃ →+* _) ≫ spMap (loc f₃) := by
      rw [← spMap_comp, IsLocalization.Away.lift_comp]
    have hpb' : IsPullback (pullback.fst Z.hom (spMap (loc f))) Z'.hom Z.hom
        (spMap (IsLocalization.Away.lift f₃ hu : Localization.Away f₃ →+* _) ≫ spMap (loc f₃)) := by
      rw [← e]; exact hpb
    have hp₃ := IsPullback.of_hasPullback Z.hom (spMap (loc f₃))
    have := IsPullback.of_right (h₁₁ := hp₃.lift _ _ (hpb'.w.trans (Category.assoc _ _ _).symm))
      (by rw [IsPullback.lift_fst]; exact hpb') (hp₃.lift_snd _ _ _) hp₃
    exact MorphismProperty.of_isPullback (P := @GeometricallyConnected) this hc
  refine nearC_of_den_loc h2 h hf fun q₁ hq₁ => ?_
  obtain ⟨_, hG⟩ := GlobalTheory.ZM.NearBuild.grpFam_of_dense_fibres h1 h2 o g _ J b Mat κ _ _ _ _ Z' _ th' sc' mu F (pow_ne_zero _ hn.ne_zero) hq₁.1 hZ' hs₁ hc₁
    (fun K _ _ x s t φ ht hφ => hmu K x s t φ ((good_comp _ _ _).1 ht) (hfib K x s t φ hφ) hφ.1.w)
    (fun i K _ _ x s t φ ht hφ => hF i K x s t φ ((good_comp _ _ _).1 ht) (hfib K x s t φ hφ) hφ.1.w)
  exact nearC_of_grpFam h1 h2 hn hodd hj hq₁ (span_map _ hv) hG

omit h1 hodd hj in

theorem nearC_of_fam
    (H : ∀ {R : Type} [CommRing R] [IsNoetherianRing R] [IsReduced R] {β : o →+* R}
      {v : Ix g ((n ^ j) ^ 2) → R} {Z : Over (Sp R)} {M : LB Z.left} {th : Ix g ((n ^ j) ^ 2) → M.Sec}
      {sc : Ix g ((n ^ j) ^ 2) → (Out.baseOver (Sp R) ⟶ Z)} {q₀ : Ideal R}, Den b Mat κ β v q₀ →
      Ideal.span (Set.range v) = ⊤ → Fam b Mat κ β v (n ^ 2) M th sc → SmoothOfRelativeDimension g Z.hom →
      NearC b Mat κ β v q₀)
    {R : Type} [CommRing R] [IsNoetherianRing R] [IsReduced R] {β : o →+* R}
    {v : Ix g ((n ^ j) ^ 2) → R} {Z : Over (Sp R)} {M : LB Z.left} {th : Ix g ((n ^ j) ^ 2) → M.Sec}
    {sc : Ix g ((n ^ j) ^ 2) → (Out.baseOver (Sp R) ⟶ Z)} {q₀ : Ideal R} (h : Den b Mat κ β v q₀)
    (hv : Ideal.span (Set.range v) = ⊤) (hZ : Fam b Mat κ β v (n ^ 2) M th sc) : NearC b Mat κ β v q₀ := by
  haveI : NeZero ((n ^ j) ^ 2) := ⟨pow_ne_zero _ (pow_ne_zero _ hn.ne_zero)⟩
  obtain ⟨f, hf, hs⟩ : ∃ f, f ∉ q₀ ∧ SmoothOfRelativeDimension g (pullback.snd Z.hom (spMap (loc f))) := by
    obtain ⟨K, _, _, x, s, t, rfl, ht⟩ := mem_objPrimes.1 h.2
    obtain ⟨φ, hφ⟩ := hZ.2.2 K x s t ht
    obtain ⟨I, p, hI, -⟩ := hZ.1
    refine GlobalTheory.ProperFlatNearFibre.exists_away_smoothOfRelativeDimension R _ Z.hom g K x (GlobalTheory.ZM.projRep_projective_ample R _ I Z M th hI).2.1 hZ.2.1 ?_
    refine (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
      (IsPullback.of_horiz_isIso (fst := hφ.1.isoPullback.inv) (g := 𝟙 _) ⟨?_⟩) t.dim
    rw [hφ.1.isoPullback_inv_snd, Category.comp_id]
  obtain ⟨th', sc', hZ', -⟩ := GlobalTheory.ZM.NearBuild.fam_baseChange o g _ J b Mat κ R β v _ Z M th sc _ (loc f)
    (Over.mk (pullback.snd Z.hom (spMap (loc f)))) _ (IsPullback.of_hasPullback _ _) hZ
  exact nearC_of_den_loc h2 h hf fun q₁ hq₁ => H hq₁ (span_map _ hv) hZ' hs

omit h1 hodd hj in

theorem nearC_of_unimodular
    (H : ∀ {R : Type} [CommRing R] [IsNoetherianRing R] [IsReduced R] {β : o →+* R}
      {v : Ix g ((n ^ j) ^ 2) → R} {Z : Over (Sp R)} {M : LB Z.left} {th : Ix g ((n ^ j) ^ 2) → M.Sec}
      {sc : Ix g ((n ^ j) ^ 2) → (Out.baseOver (Sp R) ⟶ Z)} {q₀ : Ideal R}, Den b Mat κ β v q₀ →
      Ideal.span (Set.range v) = ⊤ → Fam b Mat κ β v (n ^ 2) M th sc → NearC b Mat κ β v q₀)
    {R : Type} [CommRing R] [IsNoetherianRing R] [IsReduced R] {β : o →+* R}
    {v : Ix g ((n ^ j) ^ 2) → R} {p : Ix g ((n ^ j) ^ 2) → Ix g ((n ^ j) ^ 2) → R} {Hh : Type} [Finite Hh]
    {hh : Hh → Ix g ((n ^ j) ^ 2)} {Q : Polynomial ℚ} {d : ℕ} {q₀ : Ideal R} (h : Den b Mat κ β v q₀)
    (hv : Ideal.span (Set.range v) = ⊤) (hp : ∀ c, Ideal.span (Set.range (p c)) = ⊤)
    (hD : FibData b Mat κ β v (n ^ 2) p hh Q d) : NearC b Mat κ β v q₀ := by
  haveI : NeZero ((n ^ j) ^ 2) := ⟨pow_ne_zero _ (pow_ne_zero _ hn.ne_zero)⟩
  obtain ⟨f, hf, Z, M, th, hrep, hfl, hfib⟩ := GlobalTheory.ZM.NearCut.exists_away_flat_projRep R _ Hh (fun c => p (hh c)) Q d _ h.1 (fun q hq => by
    obtain ⟨K, _, _, x, s, t, rfl, ht⟩ := mem_objPrimes.1 hq
    obtain ⟨σ, I, -, -, -, hc, -⟩ := hD K x s t ht
    exact ⟨K, inferInstance, x, I, rfl, hc⟩) q₀ h.2
  refine nearC_of_den_loc h2 h hf fun q₁ hq₁ => ?_
  obtain ⟨sc, hZ⟩ := GlobalTheory.ZM.FamOf.exists_sections_fam o g _ J b Mat κ _ _ _ _ _ Hh hh Q d Z M th hq₁.1 (hD.comp (loc f))
    (fun c => span_map _ (hp c)) hrep hfl hfib
  exact H hq₁ (span_map _ hv) hZ
end

theorem exists_tObj_near : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R), DenseP (objPrimes b Mat κ β v) → ∀ q₀ ∈ objPrimes b Mat κ β v, ∃ (f : R) (t : TObj g ((n ^ j) ^ 2) J b (spMap ((algebraMap R (Localization.Away f)).comp β))), f ∉ q₀ ∧ t.HasTh (𝟙 _) (fun a => (algebraMap R (Localization.Away f)) (v a)) ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x : (Localization.Away f) →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap ((algebraMap R (Localization.Away f)).comp β))), t'.Shape Mat κ → t'.HasTh (𝟙 _) (fun a => x ((algebraMap R (Localization.Away f)) (v a))) → TMap t' t (spMap x) := by
  classical
  intro h1 h2 g J _ Mat κ n hn hodd
  obtain ⟨j₁, H₁⟩ := GlobalTheory.T.exists_goodThetaObjectEmbeddingData h1 h2 g J Mat κ n hn hodd
  obtain ⟨j₂, H₂⟩ := GlobalTheory.T.exists_addition_morphism_thetaFamily_near_goodPrime h1 h2 g J Mat κ n hn hodd
  obtain ⟨j₃, H₃⟩ := GlobalTheory.T.exists_endomorphisms_extend_near_good_prime h1 h2 g J Mat κ n hn hodd
  refine ⟨j₁ + j₂ + j₃ + 2, fun j hj o _ b R _ _ _ β v hd q₀ hq₀ => ?_⟩
  haveI : NeZero ((n ^ j) ^ 2) := ⟨pow_ne_zero _ (pow_ne_zero _ hn.ne_zero)⟩
  suffices H : NearC b Mat κ β v q₀ by
    obtain ⟨f, hf, t, ht, H⟩ := H
    exact ⟨f, t, hf, ht, fun K _ _ x t' k₁ k₂ => H K x _ t' ⟨rfl, k₁, k₂⟩⟩
  obtain ⟨p, Hh, _, hh, Q, d, hD⟩ := H₁ j (by omega) o b R β v
  have hq := isPrime_of_mem hq₀
  obtain ⟨⟨a₀, ha₀⟩, hp⟩ : (∃ a, v a ∉ q₀) ∧ ∀ c, ∃ a, p c a ∉ q₀ := by
    obtain ⟨K, _, _, x, s, t, rfl, ht⟩ := mem_objPrimes.1 hq₀
    constructor
    · obtain ⟨c, hc⟩ := GlobalTheory.coset_of_hasTh h1 h2 o g _ J b _ s t n K _ _ ⊥ hn.two_le (dvd_pow_self n (by omega)) ht.2.2
        Ideal.isPrime_bot 0
      exact ⟨_, hc⟩
    · intro c
      obtain ⟨σ, I, -, hrep, -, -, hc⟩ := hD K x s t ht
      have := (hrep.2.1 K (RingHom.id K) _ _ (by
        rw [← Over.comp_left, lift_fst]
        exact (Spec.map_id _).symm) (hc c)).1
      by_contra hne
      push Not at hne
      refine (Ideal.isPrime_bot (α := K)).ne_top (eq_top_iff.2 (this ▸ Ideal.span_le.2 ?_))
      rintro _ ⟨a, rfl⟩
      exact hne a
  choose a ha using hp
  have hf : v a₀ * ∏ c, p c (a c) ∉ q₀ := fun hh => by
    rcases hq.mem_or_mem hh with hh | hh
    · exact ha₀ hh
    · obtain ⟨c, -, hc⟩ := Ideal.IsPrime.prod_mem_iff.1 hh
      exact ha c hc
  refine nearC_of_den_loc h2 ⟨hd, hq₀⟩ hf fun q₁ hq₁ => ?_
  refine nearC_of_unimodular h2 hn (nearC_of_fam h2 hn (nearC_of_smooth h1 h2 hn hodd (by omega)
    (H₂ j (by omega) o b) (H₃ j (by omega) o b))) hq₁
    (span_of_unit a₀ (isUnit_loc (dvd_mul_right _ _))) (fun c => span_of_unit (a c) (isUnit_loc
      ((Finset.dvd_prod_of_mem (fun c => p c (a c)) (Finset.mem_univ c)).mul_left _))) (hD.comp _)

end GlobalTheory.ZM.NearBuild
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTransferPts
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFam

open GlobalTheory.HeckePoint

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem exists_transfer_pts {B B' : Type} [CommRing B] [CommRing B'] {b : Base l B} {b' : Base l B'} {X S : Scheme.{0}}
    {sX : X ⟶ Sp B} {s : S ⟶ Sp B'} {u : Obj D l b sX} {o : Obj D l b' s} {f : S ⟶ X} (m : ObjMap o u f)
    {k : Type} [Field k] (z : Sp k ⟶ S) :
    ∃ ρ : (Over.mk z ⟶ o.t.G) ≃* (Over.mk (z ≫ f) ⟶ u.t.G),
      (∀ x, (ρ x).left = x.left ≫ m.toSABMap.φ) ∧
      (∀ a x, ρ (x ≫ o.t.act.act a) = ρ x ≫ u.t.act.act a) ∧
      (∀ (n : ℤ) x x' (c : kˣ), Out.WeilIs o.t.G o.t.PP.L n x x' (unitOn c) ↔
        Out.WeilIs u.t.G u.t.PP.L n (ρ x) (ρ x') (unitOn c)) ∧
      (∀ a, ρ (toUnit _ ≫ o.eta a) = toUnit _ ≫ u.eta a) ∧ ∀ a, ρ (toUnit _ ≫ o.etaA a) = toUnit _ ≫ u.etaA a := by
  obtain ⟨ρ, hρ⟩ := exists_ptsEquiv m.cart (Over.mk z) (z ≫ f) rfl
  obtain ⟨w, hw, -⟩ := m.lin
  have tu : (toUnit (Over.mk z)).left = z := by simp
  have tv : (toUnit (Over.mk (z ≫ f))).left = z ≫ f := by simp
  refine ⟨ρ, hρ, fun a x => Over.OverMorphism.ext ?_,
    fun n x x' c => GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ _ _ f m.cm.F _ _ u.t.PP.isLB o.t.PP.isLB m.cart ⟨w, hw⟩
      (Over.mk z) n x x' _ _ _ (hρ x) (hρ x'), fun a => Over.OverMorphism.ext ?_,
    fun a => Over.OverMorphism.ext ?_⟩
  · rw [hρ, Over.comp_left, Over.comp_left, hρ, Category.assoc, m.act, Category.assoc]
  · rw [hρ, Over.comp_left, Over.comp_left, tu, tv, Category.assoc, m.eta a, Category.assoc]
  · rw [hρ, Over.comp_left, Over.comp_left, tu, tv, Category.assoc, m.etaA a, Category.assoc]

theorem pointQuot_snd : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (Z : Corr Xo 𝔓 p i), admitted l 𝔓 p → ∀ (k : Type) [Field k] [IsAlgClosed k] (z : Sp k ⟶ Z.Hk) (y : Sp k ⟶ Xo.X) (C : Subgroup (Over.mk y ⟶ Xo.univ.t.G)), Z.toKerScheme.Carries z y C → PointQuot Xo p y (z ≫ Z.π₂) C := by
  intro E _ _ _ H D l Xo 𝔓 p i Z hA k _ _ z y C hC
  obtain ⟨rfl, hC⟩ := hC
  have hp : p.Prime := hA.2.2.1
  have hL : Out.Laws := GlobalTheory.firstFiveLaws.1
  obtain ⟨⟨hom, hfin, het, hsur, hlin, hiso⟩, hlev⟩ := Z.isog
  have := Xo.smooth
  have := Z.et₁
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  have : IsLocallyNoetherian Xo.X := LocallyOfFiniteType.isLocallyNoetherian Xo.s
  have : IsLocallyNoetherian Z.Hk := LocallyOfFiniteType.isLocallyNoetherian Z.π₁
  obtain ⟨ρ, e₂, e₃, e₄, e₅, e₆⟩ := exists_transfer_pts Z.m₁ z
  obtain ⟨ρ₁, f₂, f₃, f₄, f₅, f₆⟩ := exists_transfer_pts Z.m₂ z
  let σ : (Over.mk z ⟶ Z.o₁.t.G) →* (Over.mk z ⟶ Z.o₂.t.G) :=
    MonoidHom.mk' (fun x => x ≫ Z.ψ) fun a c => MonObj.mul_comp a c Z.ψ
  let ψp := ρ₁.toMonoidHom.comp (σ.comp ρ.symm.toMonoidHom)
  have hψ : ∀ x, ψp (ρ x) = ρ₁ (x ≫ Z.ψ) := fun x => congrArg (fun u => ρ₁ (u ≫ Z.ψ)) (ρ.symm_apply_apply x)
  have c₁ := Z.m₁.cart.1
  have c₂ := Z.m₂.cart.1
  let α : pullback Xo.univ.t.G.hom (z ≫ Z.π₁) ⟶ Z.o₁.t.G.left :=
    c₁.lift (pullback.fst _ _) (pullback.snd _ _ ≫ z) (by rw [pullback.condition, Category.assoc])
  have α₁ : α ≫ Z.m₁.cm.F = pullback.fst _ _ := c₁.lift_fst _ _ _
  have α₂ : α ≫ Z.o₁.t.G.hom = pullback.snd _ _ ≫ z := c₁.lift_snd _ _ _
  have hα : ∀ x, fibPt _ (ρ x) ≫ α = x.left := fun x => c₁.hom_ext
    (by rw [Category.assoc, α₁, fibPt, pullback.lift_fst, e₂])
    (by rw [Category.assoc, α₂, fibPt, pullback.lift_snd_assoc, Over.w x]; exact Category.id_comp _)
  refine ⟨by rw [Category.assoc, Category.assoc, Z.base₂], pullback.lift (α ≫ Z.ψ.left ≫ Z.m₂.cm.F) (pullback.snd _ _)
    (by rw [Category.assoc, Category.assoc, c₂.w, Over.w_assoc, reassoc_of% α₂]), ψp, pullback.lift_snd _ _ _,
    fun x => ?_, fun a x => ?_, fun v => ?_, Subgroup.ext fun x => ?_, fun n x x' c hn h => ?_, fun p' hp' a => ?_⟩
  · obtain ⟨x, rfl⟩ := ρ.surjective x
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, reassoc_of% hα x, hψ, fibPt, pullback.lift_fst, f₂, Over.comp_left,
        Category.assoc]
    · rw [Category.assoc, pullback.lift_snd, fibPt, fibPt, pullback.lift_snd, pullback.lift_snd]
  · obtain ⟨x, rfl⟩ := ρ.surjective x
    rw [← e₃, hψ, hψ, ← f₃, Category.assoc, hlin, Category.assoc]
  · obtain ⟨v, rfl⟩ := ρ₁.surjective v
    obtain ⟨x, rfl⟩ := exists_lift_pt Z.ψ z v
    exact ⟨ρ x, hψ x⟩
  · obtain ⟨x, rfl⟩ := ρ.surjective x
    rw [MonoidHom.mem_ker, hψ, map_eq_one_iff _ ρ₁.injective, Z.ker k z x, hC x _ (e₂ x)]
  · obtain ⟨x, rfl⟩ := ρ.surjective x
    obtain ⟨x', rfl⟩ := ρ.surjective x'
    rw [hψ, hψ]
    refine (f₄ _ _ _ _).1 ?_
    replace h := (e₄ _ _ _ _).2 h
    let P := polOf Z.o₁.t Z.o₁.proper Z.o₁.ample Z.o₁.ktriv (ObjDim.smoothOfRelativeDimension Z.o₁)
    let P' := polOf Z.o₂.t Z.o₂.proper Z.o₂.ample Z.o₂.ktriv (ObjDim.smoothOfRelativeDimension Z.o₂)
    have hn₀ : 0 < n := Nat.pos_of_ne_zero (by
      rintro rfl
      exact hp.one_lt.ne' ((Nat.coprime_zero_left p).1 hn))
    have : Unique (Over.mk z).left := inferInstanceAs (Unique (PrimeSpectrum k))
    obtain ⟨t₁, t₂⟩ := pow_eq_one_of_weilIs hL.kerPow P hn₀ h
    obtain ⟨c', hc', -⟩ := (hL.weil _ P' n _).1 (x ≫ Z.ψ) (x' ≫ Z.ψ)
      (by rw [← MonObj.pow_comp, t₁, MonObj.one_comp]) (by rw [← MonObj.pow_comp, t₂, MonObj.one_comp])
    have e := (weilIs_along_hom hL.globalFns _ _ _ Z.ψ _ _ (p ^ 2) n _ x x' _ _ P.isAb P'.isAb P.isLB P'.isLB hom hiso
      hc').2 h
    rw [unitOn_pow]
    exact e ▸ hc'
  · rw [← e₅, ← e₆, hψ, hψ, Category.assoc, Category.assoc, (hlev p' hp' a).1, (hlev p' hp' a).2, f₅, f₆]
    exact ⟨rfl, rfl⟩

end GlobalTheory.HkFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasQuotOfIsIsogT
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory

open HeckePoint

theorem hasQuot_of_isIsogT : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (S : Scheme.{0}) [IsReduced S] (s : S ⟶ Sp (KA l)) (o : Ob D l s) (t' : SAB H S) (ψ : o.t.G ⟶ t'.G) (K : Set o.t.G.left), 1 ≤ D.p + D.q → admitted l 𝔓 p → IsProper t'.G.hom → Out.RelAmple t'.G t'.PP.L → Out.KTriv t'.G t'.PP.L → IsIsogT o.t t' p ψ → KerSet ψ K → HeckeSet D o.t 𝔓 p i K → HasQuot o p K := by
  intro E _ _ _ H D l 𝔓 p i S _ s o t' ψ K _ ⟨h𝔓, hco, hp, hp𝔓, hpM⟩ hpr ham hkt hI hker hHk
  obtain ⟨hhom, hfin, het, hsur, hlin, hiso⟩ := hI
  have hG : Out.GlobalFnsSt := (show Out.Laws from GlobalTheory.firstFiveLaws.1).globalFns
  have hab := isAbelianScheme_of_proper o.t o.proper
  have hab' := isAbelianScheme_of_proper t' hpr
  have hW := fun (n : ℤ) (T : Over S) (x y : T ⟶ o.t.G) c c' =>
    weilIs_along_hom hG _ o.t.G t'.G ψ o.t.PP.L t'.PP.L (p ^ 2) n T x y c c' hab hab' o.t.PP.isLB t'.PP.isLB hhom hiso
  obtain ⟨p₀, hp₀⟩ := exists_inv_mod hp hpM
  have hMM : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
  have hAM : l.A ∣ l.M' := Nat.dvd_lcm_right _ _
  have etaM : ∀ a, o.eta (l.M • a) = 1 := fun a => o.eta_ker _ (by
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
    exact Submodule.smul_mem_smul (natCast_M_mem l) Submodule.mem_top)
  let o' : Ob D l s :=
    { t := t', proper := hpr, ample := ham, ktriv := hkt
      eta := fun a => o.eta (p₀ • a) ≫ ψ
      eta_add := fun a c => by rw [smul_add, o.eta_add, MonObj.mul_comp]
      eta_ker := fun a ha => by rw [o.eta_ker _ (nsmul_mem ha _), MonObj.one_comp]
      etaA := fun a => o.etaA (p₀ • a) ≫ ψ
      etaA_add := fun a c => by rw [smul_add, o.etaA_add, MonObj.mul_comp]
      etaA_ker := fun a => by rw [smul_comm, o.etaA_ker, MonObj.one_comp]
      geom := by
        intro k _ _ x β hx
        obtain ⟨hdet, I, hζ, hA, hM⟩ := o.geom k x β hx
        refine ⟨fun τ => ?_, ?_⟩
        · simp only [← LieEtale.lieMult_iff_of_etale _ _ _ _ ψ o.t.act t'.act hhom het hlin k x τ]
          exact hdet τ
        obtain ⟨C, hC, -, c₂, c₃, c₄, c₅, -⟩ := hHk k x
        have mem : ∀ z : Over.mk x ⟶ o.t.G, z ≫ ψ = 1 ↔ z ∈ C := fun z => (hker k x z).trans (hC z).symm
        let ψx : (Over.mk x ⟶ o.t.G) →* (Over.mk x ⟶ t'.G) :=
          MonoidHom.mk' (fun z => z ≫ ψ) fun a c => MonObj.mul_comp a c ψ
        have uniq : ∀ (n : ℤ) (z w : Over.mk x ⟶ o.t.G) (c c' : kˣ),
            Out.WeilIs o.t.G o.t.PP.L n z w (unitOn c) → Out.WeilIs o.t.G o.t.PP.L n z w (unitOn c') → c = c' :=
          fun n z w c c' h h' => (unitOn_bijective k).1 (CommutatorPairing.weilIs_unique hG hab o.t.PP.isLB h h')
        obtain ⟨I', hζ', hev⟩ := exists_tateIso_heckeQuotient SimAlg.sim_group E H D 𝔓 p k _ _ _
          (fun a g => g ≫ t'.act.act a) _
          (fun n g g' c => Out.WeilIs t'.G t'.PP.L n g g' (unitOn c)) I ψx h𝔓 hco hp hp𝔓
          (fun y => exists_lift_pt ψ x y)
          (fun a z => by
            show (z ≫ _) ≫ ψ = (z ≫ ψ) ≫ _
            rw [Category.assoc, hlin, Category.assoc])
          (fun J hJ z _ hz' => (mem z).2 (c₂ J hJ hz'))
          (fun z hz => ⟨by
            rw [← comp_act_natCast o.t.act]
            refine c₃ ((mem z).1 hz) _ ?_
            rw [Nat.cast_pow, pow_two]
            refine Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) ?_
            have := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hp𝔓
            rwa [map_natCast] at this, c₃ ((mem z).1 hz)⟩)
          (fun z w hz hw => by
            have h := c₄ z ((mem z).1 hz) w ((mem w).1 hw)
            rw [← Nat.cast_pow] at h
            exact (congrArg (Out.WeilIs o.t.G o.t.PP.L ((p ^ 2 : ℕ) : ℤ) z w) unitOn_one).mpr h)
          (by rw [← c₅, show ψx.ker = C from Subgroup.ext mem])
          (fun n z w c c' _ _ _ h h' => uniq n z w c c' h h')
          (fun n z w c hn hz hw h => by
            obtain ⟨c', hc⟩ := exists_weil t'.cub hz hw
            have hc' := (weilIs_iff t'.cub hG hab' hz hw hc c').2 rfl
            obtain ⟨c', rfl⟩ := (unitOn_bijective k).2 c'
            have h₂ := (hW n _ z w 1 _ hc').1
            rw [← Nat.cast_mul] at h₂
            rw [uniq _ z w c c' h h₂]
            exact hc')
        refine ⟨I', by rw [hζ']; exact hζ, fun a => ?_, fun a ha => ?_⟩
        · rw [hev l.A p₀ l.A_pos (hp₀.of_dvd hAM), ← hA, ← Category.assoc]; rfl
        · rw [hev l.M p₀ (by have := l.three_le; omega) (hp₀.of_dvd hMM), ← hM _ (nsmul_mem ha _),
            ← Category.assoc]; rfl }
  refine ⟨o', ψ, ⟨⟨hhom, hfin, het, hsur, hlin, hiso⟩, fun p' hp' a => ?_⟩, hker⟩
  have e := modEq_of_inv hp' hp₀
  exact ⟨congrArg (· ≫ ψ) (eq_of_modEq o.eta o.eta_add etaM (e.of_dvd hMM) a),
    congrArg (· ≫ ψ) (eq_of_modEq o.etaA o.etaA_add o.etaA_ker (e.of_dvd hAM) a)⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsFiniteAndFlatMulAbelianSchemeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFinite_and_flat_mul_abelianScheme : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ k : ℕ, 1 ≤ k → IsFinite ((𝟙 A) ^ k : A ⟶ A).left ∧ Flat ((𝟙 A) ^ k : A ⟶ A).left := by
  first | exact @GlobalTheory.MulFiniteFlat.isFinite_and_flat_mul | exact GlobalTheory.MulFiniteFlat.isFinite_and_flat_mul | (intros; apply GlobalTheory.MulFiniteFlat.isFinite_and_flat_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaPointDeterminesAndEndDeterminedTorsionStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaPoint_determines_and_end_determined_torsion : GlobalTheory.ThetaPtDeterminesSt ∧ GlobalTheory.EndDeterminedOnTorsionSt := by
  first | exact @GlobalTheory.thetaPtDetermines_and_endDeterminedOnTorsion | exact GlobalTheory.thetaPtDetermines_and_endDeterminedOnTorsion | (intros; apply GlobalTheory.thetaPtDetermines_and_endDeterminedOnTorsion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaUniformisationComplexAbelianVarietiesStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_uniformisation_complex_abelian_varieties : ThetaUnifAV := by
  first | exact @GlobalTheory.thetaUnifAV_closed | exact GlobalTheory.thetaUnifAV_closed | (intros; apply GlobalTheory.thetaUnifAV_closed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionDescentFiniteEtaleCoverStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_descent_finite_etale_cover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (W : (Sp R).Opens) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (k : ℕ), IsSeparated G.hom → TorsFiniteFlat G W k → ∀ N : Over W.toScheme, FinFlatEt N → Surjective N.hom → ∀ (u : genPart (overW W N) ⟶ G) (d : overW W (N ⊗ N) ⟶ G), u ^ k = 1 → d ^ k = 1 → (∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (a b : TF (R := R) F ⟶ genPart (overW W N)) (c : TF (R := R) F ⟶ overW W (N ⊗ N)), c ≫ (Over.map W.ι).map (fst N N) = a ≫ genι _ → c ≫ (Over.map W.ι).map (snd N N) = b ≫ genι _ → a ≫ u = (b ≫ u) * (c ≫ d)) → ∃ v : overW W N ⟶ G, v ^ k = 1 ∧ genι _ ≫ v = u := by
  first | exact @GlobalTheory.FlatTors.exists_tors_ext | exact GlobalTheory.FlatTors.exists_tors_ext | (intros; apply GlobalTheory.FlatTors.exists_tors_ext <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatementsStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformization_laws_and_expansion_statements : GlobalTheory.UT.LL ∧ DVR.TwistBCSpanStatement ∧ DVR.TWM.VRatioGtStatement ∧ DVR.TWStatement ∧ DVR.UUStatement := by
  first | exact @GlobalTheory.lawsAndExpansions | exact GlobalTheory.lawsAndExpansions | (intros; apply GlobalTheory.lawsAndExpansions <;> assumption)
end

