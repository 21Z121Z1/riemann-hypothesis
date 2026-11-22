import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0131
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0125
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsMultiHomogXpow
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PFibreNormDehomRoots
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0034
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0031
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0007
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0139
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0006
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0077
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0109

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianMapTangentCoordinatesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_map_tangent_coordinates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (A : Type) [CommRing A] (i : Sp A ⟶ X) (N : ℕ) (v : Fin N → (epsAt i ⟶ t.G)) (R : Type) [CommRing R] (t' : SAB H (Sp R)) (θ : A →+* R) (m : SABMap t' t (spMap θ ≫ i)) (g : ℕ) (M : LieModel t'.G (𝟙 (Sp R)) (Fin g → R)), (∀ k, IsTanAt t.G i (v k)) → ∃ x : Fin N → Fin g → R, ∀ k, (M.pt (x k)).left ≫ m.φ = spMap (dualMap θ) ≫ (v k).left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PeriodCoord.exists_coords | exact GlobalTheory.CompanionTheory.Ar.PeriodCoord.exists_coords | (intros; apply GlobalTheory.CompanionTheory.Ar.PeriodCoord.exists_coords <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AffineDomainGenericSpecializesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affine_domain_generic_specializes : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (A : X.Opens) (hA : IsAffineOpen A) (p : Cpt ξ), IsCptGen ξ → IsDomain Γ(X, A) → p.1 ∈ A → ∀ z ∈ A, genPt ξ ⤳ z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LocFrames.genPt_specializes_of_isDomain | exact GlobalTheory.CompanionTheory.Ar.LocFrames.genPt_specializes_of_isDomain | (intros; apply GlobalTheory.CompanionTheory.Ar.LocFrames.genPt_specializes_of_isDomain <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AmpleOfSingleCoordBlock
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.AmpleBlock

open MvPolynomial ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open GroundTheory.Heights₂.Heights.HilbertSamuel

variable {K : Type} [Fintype K] [DecidableEq K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]

theorem homog_rename (k₀ : K) {F : MvPolynomial (J k₀) ℤ} {n : ℕ} (h : F.IsHomogeneous n) :
    IsMultiHomog (rename (Sigma.mk k₀) F : MRing J) (Pi.single k₀ n) := by
  classical
  intro m hm k
  rw [support_rename_of_injective sigma_mk_injective] at hm
  obtain ⟨m', hm', rfl⟩ := Finset.mem_image.1 hm
  have hd : ∑ i, m' i = n := by
    have := h (mem_support_iff.1 hm')
    rw [← this, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp
  by_cases hk : k = k₀
  · subst hk
    simp [Finsupp.mapDomain_apply sigma_mk_injective, hd]
  · have h0 : ∀ i, Finsupp.mapDomain (Sigma.mk k₀) m' ⟨k, i⟩ = 0 := fun i =>
      Finsupp.mapDomain_notin_range _ _ (by
        rintro ⟨i', hi'⟩
        exact hk (congrArg Sigma.fst hi').symm)
    simp [h0, Pi.single_apply, hk]

theorem rel_at_point {y : (Σ k, J k) → Ω} (k₀ k : K) {A B : MvPolynomial (J k₀) ℤ} {n : ℕ}
    (hA : A.IsHomogeneous n) (hB : B.IsHomogeneous n) (j j' : J k)
    (hr : aeval (fun i => y ⟨k₀, i⟩) A * y ⟨k, j'⟩ = aeval (fun i => y ⟨k₀, i⟩) B * y ⟨k, j⟩)
    {L : Type} [Field L] {z : (Σ k, J k) → L} (hz : z ∈ Small.ptsOver L (mCoordIdeal y)) :
    aeval (fun i => z ⟨k₀, i⟩) A * z ⟨k, j'⟩ = aeval (fun i => z ⟨k₀, i⟩) B * z ⟨k, j⟩ := by
  have hm : (rename (Sigma.mk k₀) A * X ⟨k, j'⟩ - rename (Sigma.mk k₀) B * X ⟨k, j⟩ : MRing J) ∈ mCoordIdeal y := by
    change mConeMap y _ = 0
    rw [map_sub, map_mul, map_mul, ProjLine.mConeMap_eq_of_isMultiHomog y (homog_rename k₀ hA),
      ProjLine.mConeMap_eq_of_isMultiHomog y (homog_rename k₀ hB)]
    simp only [mConeMap, aeval_X, aeval_rename]
    have := congrArg (C : Ω →+* MvPolynomial K Ω) hr
    rw [map_mul, map_mul] at this
    simp only [Function.comp_def]
    linear_combination ((∏ k, (X k : MvPolynomial K Ω) ^ (Pi.single k₀ n : K → ℕ) k) * X k) * this
  have := hz.2 _ hm
  simp only [map_sub, map_mul, aeval_X, aeval_rename, Function.comp_def] at this
  exact sub_eq_zero.mp this

def gForm (k₀ : K) (i : J k₀) (e : ℕ) (G : K → MvPolynomial (J k₀) ℤ) : MRing J :=
  X ⟨k₀, i⟩ ^ e * ∏ k ∈ Finset.univ.erase k₀, rename (Sigma.mk k₀) (G k)

def hForm (k₀ : K) (j : ∀ k, J k) : MRing J :=
  ∏ k ∈ Finset.univ.erase k₀, X ⟨k, j k⟩

theorem gForm_homog (k₀ : K) (i : J k₀) (e : ℕ) {G : K → MvPolynomial (J k₀) ℤ} {d : K → ℕ}
    (hG : ∀ k, (G k).IsHomogeneous (d k)) :
    IsMultiHomog (gForm k₀ i e G) (Pi.single k₀ (e + ∑ k ∈ Finset.univ.erase k₀, d k)) := by
  have h := isMultiHomog_mul (isMultiHomog_pow (isMultiHomog_X' k₀ i : IsMultiHomog (X ⟨k₀, i⟩ : MRing J) _) e)
    (isMultiHomog_prod (Finset.univ.erase k₀) (fun k => rename (Sigma.mk k₀) (G k))
      (fun k => Pi.single k₀ (d k)) fun k => homog_rename k₀ (hG k))
  rw [gForm]
  convert h using 1
  funext k'
  by_cases hk : k' = k₀
  · subst hk
    simp [Finset.sum_apply]
  · simp [Finset.sum_apply, Pi.single_apply, hk]

def hDeg (k₀ : K) : K → ℕ := fun k => if k = k₀ then 0 else 1

theorem hForm_homog (k₀ : K) (j : ∀ k, J k) : IsMultiHomog (hForm k₀ j) (hDeg k₀) := by
  have h := isMultiHomog_prod (Finset.univ.erase k₀) (fun k => (X ⟨k, j k⟩ : MRing J))
      (fun k => Pi.single k 1) fun k => isMultiHomog_X' k (j k)
  rw [hForm]
  convert h using 1
  funext k'
  by_cases hk : k' = k₀
  · subst hk
    simp [hDeg, Finset.sum_apply, Pi.single_apply]
  · simp [hDeg, Finset.sum_apply, Pi.single_apply, hk]

theorem aeval_gForm {L : Type} [Field L] (z : (Σ k, J k) → L) (k₀ : K) (i : J k₀) (e : ℕ)
    (G : K → MvPolynomial (J k₀) ℤ) :
    aeval z (gForm k₀ i e G) = z ⟨k₀, i⟩ ^ e * ∏ k ∈ Finset.univ.erase k₀, aeval (fun i => z ⟨k₀, i⟩) (G k) := by
  simp [gForm, map_prod, aeval_rename, Function.comp_def]

theorem aeval_hForm {L : Type} [Field L] (z : (Σ k, J k) → L) (k₀ : K) (j : ∀ k, J k) :
    aeval z (hForm k₀ j) = ∏ k ∈ Finset.univ.erase k₀, z ⟨k, j k⟩ := by
  simp [hForm, map_prod]

def sec (y : (Σ k, J k) → Ω) (k₀ : K) (js : ∀ k, J k) (i : J k₀) (e : ℕ) (G : K → MvPolynomial (J k₀) ℤ) : Ω :=
  y ⟨k₀, i⟩ ^ e * ∏ k ∈ Finset.univ.erase k₀, aeval (fun i => y ⟨k₀, i⟩) (G k) / y ⟨k, js k⟩

theorem sec_mul (y : (Σ k, J k) → Ω) (k₀ : K) (js j : ∀ k, J k) (hjs : ∀ k, y ⟨k, js k⟩ ≠ 0) (i : J k₀) (e : ℕ)
    (G G' : K → MvPolynomial (J k₀) ℤ)
    (hr : ∀ k, aeval (fun i => y ⟨k₀, i⟩) (G k) * y ⟨k, j k⟩ = aeval (fun i => y ⟨k₀, i⟩) (G' k) * y ⟨k, js k⟩) :
    aeval y (gForm k₀ i e G') = sec y k₀ js i e G * aeval y (hForm k₀ j) := by
  rw [aeval_gForm, aeval_hForm, sec, _root_.mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  have := hjs k
  field_simp
  exact (hr k).symm

theorem ampleQ_of_forms (y : (Σ k, J k) → Ω) (k₀ : K) (a : K → ℤ) (ha₀ : a k₀ = 1) (ha : ∀ k, k ≠ k₀ → a k = 0)
    (l : K → ℕ) (n : ∀ k, Fin (l k) → ℕ) (F : ∀ k, Fin (l k) → J k → MvPolynomial (J k₀) ℤ)
    (hom : ∀ k t j, (F k t j).IsHomogeneous (n k t))
    (rel : ∀ k t j j', aeval (fun i => y ⟨k₀, i⟩) (F k t j) * y ⟨k, j'⟩ =
      aeval (fun i => y ⟨k₀, i⟩) (F k t j') * y ⟨k, j⟩)
    (pts : ∀ k (L : Type) [Field L] [CharZero L] (z : (Σ k, J k) → L), z ∈ Small.ptsOver L (mCoordIdeal y) →
      ∃ t j, aeval (fun i => z ⟨k₀, i⟩) (F k t j) ≠ 0) :
    Ht.AmpleQ y a := by
  by_cases hy : ∀ k, ∃ j, y ⟨k, j⟩ ≠ 0
  swap
  · push_neg at hy
    obtain ⟨k, hk⟩ := hy
    refine ⟨0, 0, Fin.elim0, fun i => i.elim0, fun L _ _ z hz => ?_⟩
    exfalso
    obtain ⟨i, hi⟩ := hz.1 k
    have hm : (X ⟨k, i⟩ : MRing J) ∈ mCoordIdeal y := by
      change mConeMap y _ = 0
      simp [mConeMap, hk i]
    exact hi (by simpa using hz.2 _ hm)
  choose js hjs using hy

  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ T : ∀ k, Fin (l k), ∑ k ∈ Finset.univ.erase k₀, n k (T k) ≤ N := by
    refine ⟨∑ k, ∑ t, n k t, fun T => ?_⟩
    calc ∑ k ∈ Finset.univ.erase k₀, n k (T k) ≤ ∑ k ∈ Finset.univ.erase k₀, ∑ t, n k t :=
          Finset.sum_le_sum fun k _ => Finset.single_le_sum (f := n k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
      _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)
  let eT : (∀ k, Fin (l k)) → ℕ := fun T => N - ∑ k ∈ Finset.univ.erase k₀, n k (T k)
  have heT : ∀ T, eT T + ∑ k ∈ Finset.univ.erase k₀, n k (T k) = N := fun T => Nat.sub_add_cancel (hN T)
  let I := (∀ k, Fin (l k)) × J k₀
  let S : I → Ω := fun p => sec y k₀ js p.2 (eT p.1) fun k => F k (p.1 k) (js k)
  have hdeg : ∀ k, ((Pi.single k₀ N : K → ℕ) k : ℤ) = hDeg k₀ k + (((N + 1 : ℕ) : ℤ) * a k - 1) := by
    intro k
    by_cases hk : k = k₀
    · subst hk
      simp [hDeg, ha₀]
    · simp [hDeg, Pi.single_apply, hk, ha k hk]

  have hform : ∀ (p : I) (j : ∀ k, J k), IsMultiHomog (gForm k₀ p.2 (eT p.1) fun k => F k (p.1 k) (j k))
      (Pi.single k₀ N) ∧ aeval y (gForm k₀ p.2 (eT p.1) fun k => F k (p.1 k) (j k)) = S p * aeval y (hForm k₀ j) := by
    intro p j
    refine ⟨?_, sec_mul y k₀ js j hjs _ _ _ _ fun k => rel k (p.1 k) (js k) (j k)⟩
    have := gForm_homog k₀ p.2 (eT p.1) (G := fun k => F k (p.1 k) (j k)) (d := fun k => n k (p.1 k))
      fun k => hom k _ _
    rwa [heT] at this
  refine ⟨N + 1, Fintype.card I, fun q => S ((Fintype.equivFin I).symm q), fun q c hc => ?_, fun L _ _ z hz => ?_⟩
  · obtain ⟨h1, h2⟩ := hform ((Fintype.equivFin I).symm q) c
    have h3 := FibreNormDehomRoots.aeval_mem_chartLatNm h1 c hc
    convert h3 using 1
    rw [h2, aeval_hForm, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k₀),
      ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k₀)]
    have e1 : ∏ k ∈ Finset.univ.erase k₀, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * (((N + 1 : ℕ) : ℤ) * a k - 1))) =
        ∏ k ∈ Finset.univ.erase k₀, y ⟨k, c k⟩ := by
      refine Finset.prod_congr rfl fun k hk => ?_
      simp [ha k (Finset.ne_of_mem_erase hk)]
    have e2 : ∏ k ∈ Finset.univ.erase k₀, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * ((1 * (Pi.single k₀ N : K → ℕ) k : ℕ) : ℤ))) = 1 := by
      refine Finset.prod_eq_one fun k hk => ?_
      simp [Pi.single_apply, Finset.ne_of_mem_erase hk]
    rw [e1, e2]
    simp [ha₀]
    ring
  · obtain ⟨i, hi⟩ := hz.1 k₀
    choose T jz hF using fun k => pts k L z hz
    have hzj : ∀ k, z ⟨k, jz k⟩ ≠ 0 := by
      intro k h0
      obtain ⟨j', hj'⟩ := hz.1 k
      have := rel_at_point k₀ k (hom k (T k) (jz k)) (hom k (T k) j') (jz k) j' (rel k _ _ _) hz
      rw [h0, mul_zero] at this
      exact mul_ne_zero (hF k) hj' this
    obtain ⟨h1, h2⟩ := hform (T, i) jz
    have hg : aeval z (gForm k₀ i (eT T) fun k => F k (T k) (jz k)) ≠ 0 := by
      rw [aeval_gForm]
      exact mul_ne_zero (pow_ne_zero _ hi) (Finset.prod_ne_zero_iff.mpr fun k _ => hF k)
    have hh : aeval z (hForm k₀ jz) ≠ 0 := by
      rw [aeval_hForm]
      exact Finset.prod_ne_zero_iff.mpr fun k _ => hzj k
    refine ⟨Fintype.equivFin I (T, i), _ / _, div_ne_zero hg hh, Pi.single k₀ N, hDeg k₀, _, hForm k₀ jz, h1,
      hForm_homog k₀ jz, hdeg, ?_, hh, (div_mul_cancel₀ _ hh).symm⟩
    simpa using h2

theorem ampleQ_of_embeds : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (k₀ : K) (a : K → ℤ), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → EmbedsGeneric ξ (fun i : J k₀ => y ⟨k₀, i⟩) → a k₀ = 1 → (∀ k, k ≠ k₀ → a k = 0) → Ht.AmpleQ y a := by
  intro X Ω _ _ ξ K _ J _ y k₀ a hT hE ha₀ ha
  classical
  choose l n F hom rel pts using GlobalTheory.T.coord_relations_homogeneous X Ω ξ K J y k₀ hT hE
  exact ampleQ_of_forms y k₀ a ha₀ ha l n F hom rel fun k L _ _ z hz => pts k L z hz

end GlobalTheory.CompanionTheory.Ar.AmpleBlock
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AnalyticChartUnitSection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
open ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory.CompanionTheory.Ar.Flat.GagaC

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.GagaC

theorem exists_hChart_of_extendsUnitAt : ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℂ) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (W U N : X.Opens) (F : (Sp ℂ ⟶ X) → ℂ) (T t : Ω) (v : Γ(X, N)) (d : ℕ) (B : Set (Fin d → ℂ)) (Y : (Fin d → ℂ) → (Sp ℂ ⟶ X)) (b₁ : Fin d → ℂ), IsCptGen ξ → IsChart s B Y → b₁ ∈ B → (∀ b ∈ B, centre (Y b) ∈ N ∧ genPt ξ ⤳ centre (Y b)) → N ≤ U → (∀ O : Set (Fin d → ℂ), IsOpen O → O ⊆ B → O.Nonempty → ∃ b ∈ O, centre (Y b) ∈ W) → IsUnit v → (∀ (q : X) (hq : genPt ξ ⤳ q) (h : q ∈ N), genMap ξ ⟨q, hq⟩ (X.presheaf.germ N q h v) = t / T) → T ≠ 0 → ExtendsUnitAt s (RingHom.id ℂ) ξ W F t (Y b₁) → ∃ (B₂ : Set (Fin d → ℂ)) (H : (Fin d → ℂ) → ℂ), b₁ ∈ B₂ ∧ HChart s ξ W U F T B₂ Y H := by
  intro X s Ω _ ξ W U N F T t v d B Y b₁ hξ hY hb₁ hN hNU hW hv hg hT hE
  have hid : spMap (RingHom.id ℂ) = 𝟙 (Sp ℂ) := by
    simp [spMap]
  obtain ⟨ε, h', hε, hd, h0, hrel⟩ := hE d B Y hY.isOpen hY.hol
    (fun b hb => (hY.isOver b hb).trans hid.symm) b₁ hb₁ rfl
  have hopen : IsOpen (ball b₁ ε ∩ h' ⁻¹' {0}ᶜ) :=
    hd.continuousOn.isOpen_inter_preimage isOpen_ball isOpen_compl_singleton
  have hB₂ : IsOpen (B ∩ (ball b₁ ε ∩ h' ⁻¹' {0}ᶜ)) := hY.isOpen.inter hopen
  have hsub : B ∩ (ball b₁ ε ∩ h' ⁻¹' {0}ᶜ) ⊆ B := Set.inter_subset_left
  have htop : ∀ b ∈ B, ⊤ ≤ Y b ⁻¹ᵁ N := fun b hb => (top_le_iff_centre _ _).2 (hN b hb).1
  refine ⟨B ∩ (ball b₁ ε ∩ h' ⁻¹' {0}ᶜ), fun b => h' b * valAt' (Y b) N v,
    ⟨hb₁, Metric.mem_ball_self hε, h0⟩, ?_⟩
  refine
    { chart := hY.mono hB₂ hsub
      inU := fun b hb => hNU (hN b hb.1).1
      cpt := fun b hb => (hN b hb.1).2
      dense := fun O oO sO nO => hW O oO (sO.trans hsub) nO
      hol := ?_
      ne := ?_
      rel := ?_ }
  · refine DifferentiableOn.mul (hd.mono fun b hb => hb.2.1) ?_
    exact (hY.hol N v).2.mono fun b hb => ⟨hb.1, htop b hb.1⟩
  · intro b hb
    refine mul_ne_zero hb.2.2 ?_
    intro hz
    obtain ⟨u, rfl⟩ := hv
    have e := valAt'_mul (Y b) N u.val u⁻¹.val
    rw [Units.mul_inv, valAt'_one (Y b) N (htop b hb.1), hz, zero_mul] at e
    exact one_ne_zero e
  · intro b hb hWb r hr
    have e₁ : ValAt ξ (Y b) (t / T) (valAt' (Y b) N v) :=
      ValAt.of_section (hN b hb.1).1 (hN b hb.1).2 (hg _ _ _)
    have e₂ : ValAt ξ (Y b) t (valAt' (Y b) N v * r) := by
      have := ValAt.mul e₁ hr
      rwa [div_mul_cancel₀ _ hT] at this
    rw [hrel b ⟨hb.1, hb.2.1⟩ ((top_le_iff_centre _ _).2 hWb) _ e₂, _root_.mul_assoc]

end GlobalTheory.CompanionTheory.Ar.Flat.GagaC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AnalyticChartVanishingSection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
open ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory.CompanionTheory.Ar.Flat.GagaC
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.GagaC.ChartAt

variable {X : Scheme.{0}}

abbrev cst (s : X ⟶ Sp ℂ) (V : X.Opens) : ℂ →+* Γ(X, V) :=
  ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ s.appLE ⊤ V (fun _ _ => trivial)).hom

theorem top_le_spMap (hV' : X.Opens) (hV : IsAffineOpen hV') (ψ : Γ(X, hV') →+* ℂ) :
    ⊤ ≤ (spMap ψ ≫ hV.fromSpec) ⁻¹ᵁ hV' := by
  have h : ∀ p, hV.fromSpec p ∈ hV' := fun p => by
    rw [← SetLike.mem_coe, ← hV.range_fromSpec]; exact ⟨p, rfl⟩
  have e := h (spMap ψ (show Sp ℂ from IsLocalRing.closedPoint ℂ))
  rw [← Scheme.Hom.comp_apply] at e
  exact (top_le_iff_centre _ hV').2 e

theorem val_spMap {V : X.Opens} (hV : IsAffineOpen V) (ψ : Γ(X, V) →+* ℂ) (a : Γ(X, V)) :
    valAt' (spMap ψ ≫ hV.fromSpec) V a = ψ a :=
  (valAt'_fromSpec hV _ a).trans (valAt'_spMap ψ a)

theorem eq_spMap {V : X.Opens} (hV : IsAffineOpen V) (y : Sp ℂ ⟶ X) (h : ⊤ ≤ y ⁻¹ᵁ V) :
    y = spMap (valHom y V h) ≫ hV.fromSpec := by
  have hr : Set.range y ⊆ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec]
    rintro _ ⟨p, rfl⟩
    exact h (Set.mem_univ p)
  have hl : IsOpenImmersion.lift hV.fromSpec y hr ≫ hV.fromSpec = y := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨φ, hφ⟩ : ∃ φ : Γ(X, V) →+* ℂ, spMap φ = IsOpenImmersion.lift hV.fromSpec y hr :=
    ⟨(Spec.preimage (IsOpenImmersion.lift hV.fromSpec y hr)).hom, Spec.map_preimage _⟩
  rw [← hφ] at hl
  have e : valHom y V h = φ := RingHom.ext fun a => by
    show valAt' y V a = φ a
    rw [← hl]
    exact val_spMap hV φ a
  rw [e, hl]

theorem fromSpec_comp_structure_map (s : X ⟶ Sp ℂ) {V : X.Opens} (hV : IsAffineOpen V) : hV.fromSpec ≫ s = spMap (cst s V) := by
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec s (isAffineOpen_top _) hV (fun _ _ => trivial),
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
  exact (Spec.map_comp _ _).symm

theorem over_iff (s : X ⟶ Sp ℂ) {V : X.Opens} (hV : IsAffineOpen V) (ψ : Γ(X, V) →+* ℂ) :
    (spMap ψ ≫ hV.fromSpec) ≫ s = 𝟙 _ ↔ ψ.comp (cst s V) = RingHom.id ℂ := by
  rw [Category.assoc, fromSpec_comp_structure_map]
  constructor
  · intro h
    have e : spMap (ψ.comp (cst s V)) = spMap (RingHom.id ℂ) := (Spec.map_comp _ _).trans (h.trans (Spec.map_id _).symm)
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  · intro h
    refine (Spec.map_comp _ _).symm.trans ?_
    exact (congrArg spMap h).trans (Spec.map_id _)

theorem comp_cst (s : X ⟶ Sp ℂ) {V : X.Opens} (hV : IsAffineOpen V) (y : Sp ℂ ⟶ X) (h : ⊤ ≤ y ⁻¹ᵁ V)
    (hy : y ≫ s = 𝟙 _) : (valHom y V h).comp (cst s V) = RingHom.id ℂ :=
  (over_iff s hV _).1 (by rw [← eq_spMap hV y h]; exact hy)

theorem isOpen_near {E : Type} [TopologicalSpace E] {T : Set E} (hT : IsOpen T) {n : ℕ} (v : Fin n → E → ℂ)
    (c : Fin n → ℂ) (ε : ℝ) (hv : ∀ j, ContinuousOn (v j) T) : IsOpen {b ∈ T | ∀ j, ‖v j b - c j‖ < ε} := by
  rw [isOpen_iff_mem_nhds]
  rintro b ⟨hb, hj⟩
  have h : ∀ j, ∀ᶠ y in 𝓝 b, ‖v j y - c j‖ < ε := fun j =>
    (((hv j).continuousAt (hT.mem_nhds hb)).sub continuousAt_const).norm.eventually_lt continuousAt_const (hj j)
  filter_upwards [hT.mem_nhds hb, Filter.eventually_all.2 h] with y h₁ h₂ using ⟨h₁, h₂⟩

theorem isChart_of_data (s : X ⟶ Sp ℂ) {V : X.Opens} (hV : IsAffineOpen V) {D M : ℕ} (g : Fin M → Γ(X, V))
    (f : Fin D → Γ(X, V)) {B₀ : Set (Fin D → ℂ)} {ε : ℝ} (Ψ : (Fin D → ℂ) → (Γ(X, V) →+* ℂ)) (ψ₀ : Γ(X, V) →+* ℂ)
    (o : IsOpen B₀) (a₁ : ∀ b ∈ B₀, (Ψ b).comp (cst s V) = RingHom.id ℂ ∧ ∀ i, Ψ b (f i) = b i)
    (a₂ : ∀ a, DifferentiableOn ℂ (fun b => Ψ b a) B₀)
    (a₃ : ∀ ψ : Γ(X, V) →+* ℂ, ψ.comp (cst s V) = RingHom.id ℂ → (∀ j, ‖ψ (g j) - ψ₀ (g j)‖ < ε) →
      (fun i => ψ (f i)) ∈ B₀ ∧ Ψ (fun i => ψ (f i)) = ψ) :
    IsChart s {b ∈ B₀ | ∀ j, ‖Ψ b (g j) - ψ₀ (g j)‖ < ε} (fun b => spMap (Ψ b) ≫ hV.fromSpec) := by
  have oB : IsOpen {b ∈ B₀ | ∀ j, ‖Ψ b (g j) - ψ₀ (g j)‖ < ε} :=
    isOpen_near o (fun j b => Ψ b (g j)) _ ε fun j => (a₂ (g j)).continuousOn
  refine ⟨oB, ?_, fun b hb => (over_iff s hV _).2 (a₁ b hb.1).1, ?_⟩
  · exact isHolTo_comp (isHolTo_spMap oB fun a => (a₂ a).mono fun b hb => hb.1) hV.fromSpec
  intro m B' y oB' hy ov b₀ h₀ b₁ h₁ e
  have oT : IsOpen {b ∈ B' | ⊤ ≤ y b ⁻¹ᵁ V} := (hy V 0).1
  have dv : ∀ a : Γ(X, V), DifferentiableOn ℂ (fun b => valAt' (y b) V a) {b ∈ B' | ⊤ ≤ y b ⁻¹ᵁ V} := fun a => (hy V a).2
  have oT' := isOpen_near oT (fun j b => valAt' (y b) V (g j)) (fun j => ψ₀ (g j)) ε fun j => (dv (g j)).continuousOn
  have v₀ : ∀ a, valAt' (y b₀) V a = Ψ b₁ a := fun a => by rw [e]; exact val_spMap hV _ a
  have m₀ : b₀ ∈ {b ∈ {b ∈ B' | ⊤ ≤ y b ⁻¹ᵁ V} | ∀ j, ‖valAt' (y b) V (g j) - ψ₀ (g j)‖ < ε} :=
    ⟨⟨h₀, by rw [e]; exact top_le_spMap V hV _⟩, fun j => by rw [v₀]; exact h₁.2 j⟩
  obtain ⟨δ, δ0, hδ⟩ := Metric.isOpen_iff.1 oT' b₀ m₀
  refine ⟨δ, fun b i => valAt' (y b) V (f i), δ0, fun b hb => (hδ hb).1.1,
    differentiableOn_pi.2 fun i => (dv (f i)).mono fun b hb => (hδ hb).1, funext fun i => ?_, fun b hb => ?_⟩
  · show valAt' (y b₀) V (f i) = b₁ i
    rw [v₀]; exact (a₁ b₁ h₁.1).2 i
  · have t := (hδ hb).1.2
    have k := a₃ (valHom (y b) V t) (comp_cst s hV _ t (ov b (hδ hb).1.1)) (hδ hb).2
    have k₂ : Ψ (fun i => valAt' (y b) V (f i)) = valHom (y b) V t := k.2
    refine ⟨⟨k.1, fun j => ?_⟩, ?_⟩
    · rw [k₂]; exact (hδ hb).2 j
    · show y b = spMap (Ψ (fun i => valAt' (y b) V (f i))) ≫ hV.fromSpec
      rw [k₂]; exact eq_spMap hV _ t

theorem res_cst (s : X ⟶ Sp ℂ) {U V : X.Opens} (h : V ≤ U) (c : ℂ) :
    (X.presheaf.map (homOfLE h).op).hom (cst s U c) = cst s V c :=
  congr($(Scheme.Hom.appLE_map s (U := ⊤) (V := U) (fun _ _ => trivial) (homOfLE h).op)
    ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c))

theorem exists_std (s : X ⟶ Sp ℂ) [Smooth s] (q : X) (M : X.Opens) (hq : q ∈ M) :
    ∃ (V : X.Opens) (_ : IsAffineOpen V) (D : ℕ), V ≤ M ∧ q ∈ V ∧ (cst s V).IsStandardSmoothOfRelativeDimension D := by
  obtain ⟨U₀, -, U, hU, hp, hle, hsm⟩ := Smooth.exists_isStandardSmooth s q
  have hU₀ : U₀ = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    have h2 : y = s q := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    rw [h2]; exact hle hp
  subst hU₀
  obtain ⟨n, hn⟩ : ∃ n, RingHom.IsStandardSmoothOfRelativeDimension n (s.appLE ⊤ U hle).hom := by
    let _ := (s.appLE ⊤ U hle).hom.toAlgebra
    have : Algebra.IsStandardSmooth Γ(Sp ℂ, ⊤) Γ(X, U) := hsm
    obtain ⟨_, _, _, _, ⟨P⟩⟩ := this
    exact ⟨P.dimension, _, _, _, ‹_›, P, rfl⟩
  obtain ⟨a, haM, hqa⟩ := hU.exists_basicOpen_le (V := M) ⟨q, hq⟩ hp
  refine ⟨X.basicOpen a, hU.basicOpen a, n, haM, hqa, ?_⟩
  have := hU.isLocalization_basicOpen a
  have h1 : (algebraMap Γ(X, U) Γ(X, X.basicOpen a)).IsStandardSmoothOfRelativeDimension 0 :=
    RingHom.IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway a
  have h2 : (cst s U).IsStandardSmoothOfRelativeDimension n :=
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).symm.commRingCatIsoToRingEquiv hn
  have h3 := h1.comp h2
  rw [zero_add] at h3
  convert h3 using 1
  ext c
  exact (res_cst s (X.basicOpen_le a) c).symm

theorem isDomain_of_le {Z V : X.Opens} [AlgebraicGeometry.IsIntegral Z.toScheme] (h : V ≤ Z) {q : X} (hq : q ∈ V) :
    IsDomain Γ(X, V) := by
  haveI : Nonempty V.toScheme := ⟨⟨q, hq⟩⟩
  haveI : AlgebraicGeometry.IsIntegral V.toScheme := isIntegral_of_isOpenImmersion (X.homOfLE h)
  haveI : Nonempty (⊤ : V.toScheme.Opens) := ⟨⟨⟨q, hq⟩, trivial⟩⟩
  exact MulEquiv.isDomain Γ(V.toScheme, ⊤) (Scheme.Opens.topIso V).symm.commRingCatIsoToRingEquiv.toMulEquiv

theorem exists_chart : (∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] (D : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension D ℂ A] (O : Set (Fin D → ℂ)) (Ψ : (Fin D → ℂ) → (A →+* ℂ))
    (f : Fin D → A) (a : A), IsOpen O → O.Nonempty →
    (∀ b ∈ O, (Ψ b).comp (algebraMap ℂ A) = RingHom.id ℂ ∧ ∀ i, Ψ b (f i) = b i) → (∀ b ∈ O, Ψ b a = 0) → a = 0) →
    ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℂ) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (W N : X.Opens) (x : Sp ℂ ⟶ X), Smooth s →
    IsCptGen ξ → genPt ξ ∈ W → x ≫ s = 𝟙 _ → genPt ξ ⤳ centre x → centre x ∈ N →
    ∃ (d : ℕ) (B : Set (Fin d → ℂ)) (Y : (Fin d → ℂ) → (Sp ℂ ⟶ X)) (b₁ : Fin d → ℂ), IsChart s B Y ∧ b₁ ∈ B ∧
      Y b₁ = x ∧ (∀ b ∈ B, centre (Y b) ∈ N ∧ genPt ξ ⤳ centre (Y b)) ∧
      ∀ O : Set (Fin d → ℂ), IsOpen O → O ⊆ B → O.Nonempty → ∃ b ∈ O, centre (Y b) ∈ W := by
  intro hring X s Ω _ ξ W N x hs hξ hW hxs hgx hxN
  haveI := hs
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  obtain ⟨Z, hZ, -, hZi⟩ := cpt_open_integral X Ω ξ hξ
  obtain ⟨V, hV, D, hVM, hxV, hstd⟩ := exists_std s (centre x) (N ⊓ Z) ⟨hxN, (hZ _).2 hgx⟩
  letI alg : Algebra ℂ Γ(X, V) := (cst s V).toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension D ℂ Γ(X, V) := hstd
  haveI : IsDomain Γ(X, V) := isDomain_of_le (hVM.trans inf_le_right) hxV
  have hxt : ⊤ ≤ x ⁻¹ᵁ V := (top_le_iff_centre x V).2 hxV
  have h₀ : (valHom x V hxt).comp (algebraMap ℂ Γ(X, V)) = RingHom.id ℂ := comp_cst s hV x hxt hxs
  obtain ⟨M, g, f, B₀, ε, Ψ, ε0, o, a₁, a₂, a₃⟩ := anChart_alg D (RingHom.id ℂ) (valHom x V hxt) h₀
  have hc := isChart_of_data s hV g f Ψ (valHom x V hxt) o a₁ a₂ a₃
  have m₁ := a₃ _ h₀ fun _ => by simpa using ε0
  have hY : ∀ b, centre (spMap (Ψ b) ≫ hV.fromSpec) ∈ V := fun b => (top_le_iff_centre _ V).1 (top_le_spMap V hV _)
  refine ⟨D, _, _, fun i => valHom x V hxt (f i), hc, ⟨m₁.1, fun j => ?_⟩, ?_, fun b _ => ⟨(hVM (hY b)).1, (hZ _).1 (hVM (hY b)).2⟩, ?_⟩
  · rw [m₁.2]; simpa using ε0
  · show spMap (Ψ fun i => valHom x V hxt (f i)) ≫ hV.fromSpec = x
    rw [m₁.2]; exact (eq_spMap hV x hxt).symm
  intro O oO sO nO
  have hgV : genPt ξ ∈ V := genPt_mem hgx hxV
  obtain ⟨a, haW, haξ⟩ := hV.exists_basicOpen_le (V := W) ⟨genPt ξ, hW⟩ hgV
  have a0 : a ≠ 0 := by
    rintro rfl
    simp at haξ
  by_contra hc'
  push_neg at hc'
  refine a0 (hring Γ(X, V) D O Ψ f a oO nO (fun b hb => a₁ b (sO hb).1) fun b hb => ?_)
  by_contra hne
  refine hc' b hb (haW ?_)
  have hv : valAt' (spMap (Ψ b) ≫ hV.fromSpec) V a ≠ 0 := by rw [val_spMap]; exact hne
  exact (valAt'_ne_zero_iff _ V (top_le_spMap V hV _) a _).1 hv

end GlobalTheory.CompanionTheory.Ar.Flat.GagaC.ChartAt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AnalyticPointsFiniteCompactStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analytic_points_finite_compact : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)]
    (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X), (∀ q : X, genPt ξ ⤳ q) →
    CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ (Z' : Scheme.{0}) (f : Z' ⟶ XQ X), IsFinite f →
    @CompactSpace (Sp ℂ ⟶ Z') (anTop Z') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TorusUnif.compact_of_finite_generic | exact GlobalTheory.CompanionTheory.Ar.TorusUnif.compact_of_finite_generic | (intros; apply GlobalTheory.CompanionTheory.Ar.TorusUnif.compact_of_finite_generic <;> assumption)
end

