import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0149
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0166
import Development.AbelianVarietyTheory.Proofs.HeightProofs.LeOfFiniteSplitNotSplitBauer
import Formalism.LocalToGlobal.Divisibility.ConjugationAtDistinguishedPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0164
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.CoeNonzeroLocusCanonicalEqComplRange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0163
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0062
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0003
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0030
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0165
import Formalism.UnipotentAdelicQuotients.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMulGaloisConjEqPrimeImagQuadratic
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.RayFieldNorm

theorem normSq_eq_absNorm {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]
    (hK : Module.finrank ℚ K = 2) (φ : K →+* ℂ) (π : 𝓞 K) :
    ‖φ π‖ ^ 2 = (Ideal.absNorm (Ideal.span {π}) : ℝ) := by
  have h1 : Fintype.card (InfinitePlace K) = 1 := by
    have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K
    have h3 := InfinitePlace.card_add_two_mul_card_eq_rank K
    have h4 := IsTotallyComplex.nrRealPlaces_eq_zero K
    omega
  have : Subsingleton (InfinitePlace K) := Fintype.card_le_one_iff_subsingleton.mp h1.le
  have h5 := InfinitePlace.prod_eq_abs_norm (π : K)
  rw [Fintype.prod_subsingleton _ (InfinitePlace.mk φ), IsTotallyComplex.mult_eq,
    InfinitePlace.apply] at h5
  rw [h5, Ideal.absNorm_span_singleton, ← Algebra.coe_norm_int]
  simp

theorem isTotallyComplex_of_isEmpty {K : Type} [Field K] [NumberField K]
    (h : IsEmpty (K →+* ℝ)) : IsTotallyComplex K := by
  rw [isTotallyComplex_iff]
  intro w
  rw [← InfinitePlace.not_isReal_iff_isComplex]
  intro hw
  obtain ⟨φ, hφ, -⟩ := hw
  exact h.elim (NumberField.ComplexEmbedding.IsReal.embedding hφ)

theorem exists_mul_conj_eq_norm : ∀ (K : Type) [Field K] [NumberField K], IsEmpty (K →+* ℝ) → Module.finrank ℚ K = 2 →
    ∀ (j : K →+* Qb) (π : 𝓞 K) (p : ℕ), Ideal.absNorm (Ideal.span {π}) = p →
      ∃ σ : Qb →ₐ[ℚ] Qb, j (π : K) * σ (j (π : K)) = (p : Qb) := by
  intro K _ _ hE hK j π p hp
  haveI := isTotallyComplex_of_isEmpty hE
  haveI : Algebra.IsAlgebraic ℚ Qb := AlgebraicClosure.isAlgebraic ℚ
  let ι : Qb →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := Qb)).toRingHom
  refine ⟨(Formalism.L2.DIV.conjQb ι).toAlgHom, ?_⟩
  apply ι.injective
  have hn := normSq_eq_absNorm hK (ι.comp j) π
  rw [hp] at hn
  have hc : ι (j (π : K)) * starRingEnd ℂ (ι (j (π : K))) = ((‖ι (j (π : K))‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hs := Formalism.L2.DIV.conjQb_spec ι (j (π : K))
  change ι (j (π : K) * (Formalism.L2.DIV.conjQb ι) (j (π : K))) = ι (p : Qb)
  rw [map_mul, hs, hc, map_natCast]
  simp only [RingHom.comp_apply] at hn
  rw [hn]
  simp

end GlobalTheory.RayFieldNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsProjMapProportionalSections
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.ProjSpace GlobalTheory.Cartier

namespace GlobalTheory.ProjBlowup

variable {X W : Scheme.{0}} {L : LB X} {m : ℕ}

theorem exists_unit_appLE_sec (σ : Fin (m + 1) → L.Sec) (g : W ⟶ X) (k l : L.ι) {T : W.Opens}
    (hk : T ≤ g ⁻¹ᵁ L.U k) (hl : T ≤ g ⁻¹ᵁ L.U l) : ∃ u : Γ(W, T)ˣ, ∀ j,
      (g.appLE (L.U k) T hk).hom ((σ j).f k) = u * (g.appLE (L.U l) T hl).hom ((σ j).f l) := by
  have hT : T ≤ g ⁻¹ᵁ (L.U k ⊓ L.U l) := le_inf hk hl
  refine ⟨Units.map (g.appLE (L.U k ⊓ L.U l) T hT).hom.toMonoidHom (L.g k l), fun j => ?_⟩
  have := congrArg (g.appLE (L.U k ⊓ L.U l) T hT).hom
    (sec_compat (σ j) k l (inf_le_left : L.U k ⊓ L.U l ≤ _) inf_le_right)
  rw [map_mul, appLE_resG, appLE_resG, appLE_resG] at this
  exact this

theorem exists_quot_of_span_eq {B : Type} [CommRing B] {ι : Type} [Fintype ι] {f : B} (hf : f ∈ nonZeroDivisors B)
    {s : ι → B} (h : Ideal.span {f} = Ideal.span (Set.range s)) :
    ∃ a c : ι → B, (∀ j, s j = a j * f) ∧ ∑ j, c j * a j = 1 := by
  have h1 : ∀ j, ∃ a, a * f = s j := fun j =>
    Ideal.mem_span_singleton'.1 (h ▸ Ideal.subset_span ⟨j, rfl⟩)
  choose a ha using h1
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 (h ▸ Ideal.mem_span_singleton_self f)
  refine ⟨a, c, fun j => (ha j).symm, (mul_cancel_right_mem_nonZeroDivisors hf).1 ?_⟩
  rw [one_mul, Finset.sum_mul]
  refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) hc
  rw [mul_assoc, ha]

theorem exists_mem_basicOpen_of_sum {A : W.Opens} {a c : Fin (m + 1) → Γ(W, A)} (h : ∑ j, c j * a j = 1)
    {y : W} (hy : y ∈ A) : ∃ j, y ∈ W.basicOpen (a j) := by
  by_contra hne
  have h1 : (W.presheaf.germ A y hy).hom (∑ j, c j * a j) ∈ IsLocalRing.maximalIdeal (W.presheaf.stalk y) := by
    rw [map_sum]
    refine Ideal.sum_mem _ fun j _ => ?_
    rw [map_mul]
    exact Ideal.mul_mem_left _ _ fun hu => hne ⟨j, (W.mem_basicOpen _ y hy).2 hu⟩
  rw [h, map_one] at h1
  exact h1 isUnit_one

theorem exists_proportional (R : Type) [CommRing R] (X W : Scheme.{0}) (I : W.IdealSheafData) (L : LB X) (m : ℕ)
    (σ : Fin (m + 1) → L.Sec) (g : W ⟶ X) (q : W ⟶ Sp R) (hσ : GeneratesAlong I σ g) (hI : FinalTheorems.EffCartier I) :
    ∃ ψ : W ⟶ PSpace R m, ψ ≫ PSpace.str R m = q ∧ Proportional σ g ψ := by
  obtain ⟨D, rfl⟩ := EffCartierData.exists_idealSheaf_eq hI
  have loc : ∀ y : W, ∃ (A : W.Opens) (k : L.ι) (hk : A ≤ g ⁻¹ᵁ L.U k) (i : D.ι) (hi : A ≤ D.U i)
      (a c : Fin (m + 1) → Γ(W, A)), y ∈ A ∧
      (∀ j, (g.appLE (L.U k) A hk).hom ((σ j).f k) = a j * resG W hi (D.f i)) ∧ ∑ j, c j * a j = 1 := by
    intro y
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (hσ.1.ge (Set.mem_univ y))
    obtain ⟨i, hi⟩ := D.exists_mem y
    obtain ⟨A, hy, hA⟩ := EffCartierData.exists_affine_le (V := g ⁻¹ᵁ L.U k ⊓ D.U i) (x := y) ⟨hk, hi⟩
    obtain ⟨a, c, h⟩ := exists_quot_of_span_eq (D.regular i _ (hA.trans inf_le_right))
      ((D.ideal_idealSheaf A i (hA.trans inf_le_right)).symm.trans (hσ.2 k A (hA.trans inf_le_left)))
    exact ⟨A.1, k, _, i, _, a, c, hy, h⟩
  choose A k hk i hi a c hy ha hc using loc
  have ha' : ∀ y {T : W.Opens} (hT : T ≤ A y) j, (g.appLE (L.U (k y)) T (hT.trans (hk y))).hom ((σ j).f (k y)) =
      resG W hT (a y j) * resG W (hT.trans (hi y)) (D.f (i y)) := fun y T hT j => by
    have := congrArg (resG W hT) (ha y j)
    rwa [map_mul, resG_appLE, resG_resG] at this
  have tr : ∀ y z, ∃ u : Γ(W, A y ⊓ A z)ˣ, ∀ j,
      resG W (inf_le_left : A y ⊓ A z ≤ A y) (a y j) =
        (u : Γ(W, A y ⊓ A z)) * resG W (inf_le_right : A y ⊓ A z ≤ A z) (a z j) := fun y z => by
    obtain ⟨u, hu⟩ := exists_unit_appLE_sec σ g (k y) (k z) (T := A y ⊓ A z)
      (inf_le_left.trans (hk y)) (inf_le_right.trans (hk z))
    have hy' : A y ⊓ A z ≤ D.U (i y) := inf_le_left.trans (hi y)
    have hz' : A y ⊓ A z ≤ D.U (i z) := inf_le_right.trans (hi z)
    refine ⟨u * Units.map (resG W (le_inf hz' hy')).toMonoidHom (D.trans (i z) (i y)), fun j => ?_⟩
    refine ((D.regular (i y)).resG hy').mul_right_cancel ?_
    have e := hu j
    rw [ha' y inf_le_left, ha' z inf_le_right, D.trans_spec_on (i z) (i y) hz' hy'] at e
    rw [e]
    change _ = (u : Γ(W, A y ⊓ A z)) * resG W (le_inf hz' hy') (D.trans (i z) (i y)) * _ * _
    ring
  choose u hu using tr
  let B : LB W := { ι := W, U := A, g := u }
  let t : Fin (m + 1) → B.Sec := fun j => { f := fun y => a y j, compat := fun y z => hu y z j }
  have ht : ⨆ j, Out.nonzeroLocus (t j) = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨j, hj⟩ := exists_mem_basicOpen_of_sum (hc y) (hy y)
    exact Opens.mem_iSup.2 ⟨j, (mem_nonzeroLocus_iff (t j) y (hy y)).2 hj⟩
  refine ⟨toProj q t ht, toProj_str q t ht, fun V l hl p hp j => ext_germ fun y hyV => ?_⟩
  have hm : y ∈ V ⊓ A y := ⟨hyV, hy y⟩
  have key : resG W (inf_le_left : V ⊓ A y ≤ V) ((g.appLE (L.U l) V hl).hom ((σ j).f l)) =
      resG W inf_le_left (pullRatio (toProj q t ht) V p hp j * (g.appLE (L.U l) V hl).hom ((σ p).f l)) := by
    obtain ⟨v, hv⟩ := exists_unit_appLE_sec σ g l (k y) (T := V ⊓ A y)
      (inf_le_left.trans hl) (inf_le_right.trans (hk y))
    have e : resG W inf_le_right (a y j) = _ * resG W inf_le_right (a y p) :=
      sec_eq_pullRatio_toProj_mul q t ht p j y (W := V ⊓ A y) (inf_le_left.trans hp) inf_le_right
    rw [map_mul, resG_appLE, resG_appLE, resG_pullRatio, hv, hv, ha' y inf_le_right, ha' y inf_le_right, e]
    ring
  have := congrArg (W.presheaf.germ _ y hm).hom key
  rwa [germ_resG, germ_resG] at this

end GlobalTheory.ProjBlowup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSectionsGenerateIdealProjective
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.ProjBlowup

variable {R : Type} [CommRing R] {N : ℕ} {X : Scheme.{0}}

theorem exists_formOn_eq (a : Fin (N + 1)) (s : Γ(PSpace R N, chart R N a)) :
    ∃ (d : ℕ) (F : MvPolynomial (Fin (N + 1)) R) (hF : F.IsHomogeneous d),
      formOn (chart R N a) a le_rfl d F hF = s := by
  obtain ⟨p, rfl⟩ := (chartAlgEquiv R N a).surjective s
  obtain ⟨x, rfl⟩ := (polyEquivAway R N a).symm.surjective p
  obtain ⟨n, f, hf, rfl⟩ := HomogeneousLocalization.Away.mk_surjective _ (X_mem R N a) x
  refine ⟨n, f, by simpa using hf, ?_⟩
  rw [← chartAlgEquiv_dehom, ← awayToPoly_mk R N a n f hf]
  rfl

def pullForm (φ : X ⟶ PSpace R N) (W : X.Opens) (i : Fin (N + 1)) (hi : W ≤ φ ⁻¹ᵁ chart R N i)
    (d : ℕ) (F : MvPolynomial (Fin (N + 1)) R) (hF : F.IsHomogeneous d) : Γ(X, W) :=
  (φ.appLE (chart R N i) W hi).hom (formOn (chart R N i) i le_rfl d F hF)

section

variable {φ : X ⟶ PSpace R N} {W V : X.Opens} {i j : Fin (N + 1)} {hi : W ≤ φ ⁻¹ᵁ chart R N i}
  {d : ℕ} {F : MvPolynomial (Fin (N + 1)) R}

theorem resG_pullForm (h : V ≤ W) (hF : F.IsHomogeneous d) :
    resG X h (pullForm φ W i hi d F hF) = pullForm φ V i (h.trans hi) d F hF :=
  resG_appLE φ hi h _

theorem pullForm_zero : pullForm φ W i hi d 0 (isHomogeneous_zero _ R d) = 0 := by
  rw [pullForm, formOn_zero, map_zero]

theorem pullForm_eq_pow_mul (hj : W ≤ φ ⁻¹ᵁ chart R N j) (hF : F.IsHomogeneous d) :
    pullForm φ W i hi d F hF = pullRatio φ W i hi j ^ d * pullForm φ W j hj d F hF := by
  have hW : W ≤ φ ⁻¹ᵁ (chart R N i ⊓ chart R N j) := le_inf hi hj
  have := congrArg (φ.appLE _ W hW).hom
    (formOn_eq_ratioOn_pow_mul (U := chart R N i ⊓ chart R N j) (hi := inf_le_left) inf_le_right hF)
  rw [map_mul, map_pow, appLE_ratioOn, ← resG_formOn (hi := le_rfl) inf_le_left,
    ← resG_formOn (hi := le_rfl) inf_le_right, appLE_resG, appLE_resG] at this
  exact this

theorem pullForm_X_pow_mul (n : ℕ) (hF : F.IsHomogeneous d) {e : ℕ}
    (hG : (MvPolynomial.X j ^ n * F).IsHomogeneous e) :
    pullForm φ W i hi e _ hG = pullRatio φ W i hi j ^ n * pullForm φ W i hi d F hF := by
  rw [pullForm, pullForm, pullRatio, formOn_eq_aeval, formOn_eq_aeval, map_mul, map_pow, aeval_X, map_mul,
    map_pow]

end

def pullO (φ : X ⟶ PSpace R N) (e : ℕ) : LB X where
  ι := Fin (N + 1)
  U i := φ ⁻¹ᵁ chart R N i
  g i j := (Units.mkOfMulEqOne (pullRatio φ _ i inf_le_left j) (pullRatio φ _ j inf_le_right i)
    (pullRatio_mul_pullRatio.trans pullRatio_self)) ^ e

def pullFormSec (φ : X ⟶ PSpace R N) {e : ℕ} (F : MvPolynomial (Fin (N + 1)) R) (hF : F.IsHomogeneous e) :
    (pullO φ e).Sec where
  f i := pullForm φ _ i le_rfl e F hF
  compat i j := by
    refine (resG_pullForm inf_le_left hF).trans ((pullForm_eq_pow_mul (j := j) inf_le_right hF).trans ?_)
    exact congrArg₂ (· * ·) (Units.val_pow_eq_pow_val (Units.mkOfMulEqOne _ _ _) e).symm
      (resG_pullForm inf_le_right hF).symm

abbrev affChart (φ : X ⟶ PSpace R N) [IsClosedImmersion φ] (i : Fin (N + 1)) : X.affineOpens :=
  ⟨φ ⁻¹ᵁ chart R N i, (isAffineOpen_chart R N i).preimage φ⟩

theorem exists_pow_mul_pullForm_mem (φ : X ⟶ PSpace R N) [IsClosedImmersion φ] (J : X.IdealSheafData)
    {a : Fin (N + 1)} {d : ℕ} {F : MvPolynomial (Fin (N + 1)) R} (hF : F.IsHomogeneous d)
    (h : pullForm φ _ a le_rfl d F hF ∈ J.ideal (affChart φ a)) (b : Fin (N + 1)) :
    ∃ n, pullRatio φ _ b le_rfl a ^ n * pullForm φ _ b le_rfl d F hF ∈ J.ideal (affChart φ b) := by
  let r : Γ(X, (affChart φ b).1) := pullRatio φ _ b le_rfl a
  have ha : X.basicOpen r ≤ φ ⁻¹ᵁ chart R N a := basicOpen_pullRatio.le.trans inf_le_right
  have h1 : resG X ha (pullForm φ _ a le_rfl d F hF) ∈ J.ideal (X.affineBasicOpen r) :=
    J.ideal_le_comap_ideal (U := X.affineBasicOpen r) (V := affChart φ a) ha h
  have h2 : resG X (X.basicOpen_le r) (pullForm φ _ b le_rfl d F hF) ∈ J.ideal (X.affineBasicOpen r) := by
    rw [resG_pullForm] at h1 ⊢
    rw [pullForm_eq_pow_mul (j := a) ha]
    exact Ideal.mul_mem_left _ _ h1
  rw [← J.map_ideal_basicOpen] at h2
  have inst := (affChart φ b).2.isLocalization_basicOpen r
  obtain ⟨_, ⟨n, rfl⟩, hn⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff (.powers r)
    Γ(X, X.basicOpen r) _ _).1 h2
  exact ⟨n, hn⟩

theorem exists_form_of_mem (φ : X ⟶ PSpace R N) [IsClosedImmersion φ] (J : X.IdealSheafData)
    (a : Fin (N + 1)) (g : Γ(X, (affChart φ a).1)) (hg : g ∈ J.ideal (affChart φ a)) :
    ∃ e₀, ∀ e, e₀ ≤ e → ∃ (F : MvPolynomial (Fin (N + 1)) R) (hF : F.IsHomogeneous e),
      pullForm φ _ a le_rfl e F hF = g ∧ ∀ b, pullForm φ _ b le_rfl e F hF ∈ J.ideal (affChart φ b) := by
  obtain ⟨s, rfl⟩ := φ.app_surjective _ (isAffineOpen_chart R N a) g
  obtain ⟨d, F, hF, rfl⟩ := exists_formOn_eq a s
  have e₁ : pullForm φ _ a le_rfl d F hF = (φ.app (chart R N a)).hom (formOn (chart R N a) a le_rfl d F hF) := by
    rw [pullForm, Scheme.Hom.app_eq_appLE]
  choose n hn using exists_pow_mul_pullForm_mem φ J hF (e₁ ▸ hg)
  refine ⟨Finset.univ.sup n + d, fun e he => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' (le_of_add_le_right he)
  refine ⟨MvPolynomial.X a ^ k * F, (isHomogeneous_X_pow a k).mul hF, ?_, fun b => ?_⟩
  · rw [pullForm_X_pow_mul k hF, pullRatio_self, one_pow, one_mul]
    exact e₁
  · obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le'
      ((Finset.le_sup (f := n) (Finset.mem_univ b)).trans (Nat.le_of_add_le_add_right he))
    rw [pullForm_X_pow_mul _ hF, pow_add, mul_assoc]
    exact Ideal.mul_mem_left _ _ (hn b)

theorem exists_generates (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) (s : X ⟶ Sp R)
    (hs : IsProjOver s) (J : X.IdealSheafData) :
    ∃ (L : LB X) (m : ℕ) (σ : Fin (m + 1) → L.Sec), Generates J σ := by
  classical
  obtain ⟨N, φ, _, -⟩ := hs
  have fg : ∀ a, (J.ideal (affChart φ a)).FG := fun a => by
    have : IsNoetherianRing Γ(PSpace R N, chart R N a) :=
      isNoetherianRing_of_ringEquiv _ (chartAlgEquiv R N a).toRingEquiv
    have : IsNoetherianRing Γ(X, (affChart φ a).1) :=
      isNoetherianRing_of_surjective _ _ _ (φ.app_surjective _ (isAffineOpen_chart R N a))
    exact IsNoetherian.noetherian _
  choose S hS using fg
  choose e₀ he₀ using fun p : Σ a, S a =>
    exists_form_of_mem φ J p.1 p.2.1 (hS p.1 ▸ Ideal.subset_span p.2.2)
  choose F hF hFa hFb using fun p => he₀ p (Finset.univ.sup e₀) (Finset.le_sup (Finset.mem_univ p))
  let q := (Fintype.equivFinOfCardEq (Fintype.card_option (α := Σ a, S a))).symm
  let τ : Option (Σ a, S a) → (pullO φ (Finset.univ.sup e₀)).Sec := fun o =>
    o.elim (pullFormSec φ 0 (isHomogeneous_zero _ R _)) fun p => pullFormSec φ (F p) (hF p)
  refine ⟨_, _, fun j => τ (q j), (isCoordFamily_pullRatio φ).cover, fun k V h => ?_⟩
  have key : J.ideal (affChart φ k) = Ideal.span (Set.range fun j => (τ (q j)).f k) := by
    refine le_antisymm ?_ (Ideal.span_le.2 ?_)
    · rw [← hS k]
      refine Ideal.span_mono fun g hg => ⟨q.symm (some ⟨k, g, hg⟩), ?_⟩
      simp only [q.apply_symm_apply]
      exact hFa ⟨k, g, hg⟩
    · rintro _ ⟨j, rfl⟩
      dsimp only
      cases q j with
      | none =>
        exact (congrArg (· ∈ J.ideal (affChart φ k)) (pullForm_zero (φ := φ) (hi := le_rfl))).mpr (zero_mem _)
      | some p => exact hFb p k
  rw [← J.map_ideal (V := affChart φ k) h, key]
  erw [Ideal.map_span, ← Set.range_comp]
  rfl

end GlobalTheory.ProjBlowup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSpanEqOneModOfSplitsInRayClassField
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.Mem.RaySplit

open GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem.Fld

theorem exists_span_eq_of_splits (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (𝔮 : Ideal (𝓞 K)) (hR : GlobalTheory.Mem.Fld.IsRayField K L 𝔮) (𝔭 : HeightOneSpectrum (𝓞 K)) (hnd : ¬ 𝔭.asIdeal ∣ 𝔮)
    (hs : (𝔭.asIdeal.primesOver (𝓞 L)).ncard = Module.finrank K L) :
    ∃ π : 𝓞 K, 𝔭.asIdeal = Ideal.span {π} ∧ π - 1 ∈ 𝔮 := by
  have := hR.1
  have := 𝔭.isPrime
  have := 𝔭.isMaximal
  have hcop : IsCoprime 𝔭.asIdeal 𝔮 := by
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra h
    exact hnd (Ideal.dvd_iff_le.2 (le_sup_right.trans (𝔭.isMaximal.eq_of_le h le_sup_left).symm.le))
  obtain ⟨σ, P, hP, hPo, hσ⟩ := exists_isFrob L 𝔭
  have hne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot P
  have hPm : P.IsMaximal := hP.isMaximal hne
  have hef := (GlobalTheory.Bauer.ncard_eq_finrank_iff K L 𝔭).1 hs P ⟨hP, hPo⟩
  have hf : 𝔭.asIdeal.inertiaDeg' P = 1 := by
    rw [Ideal.inertiaDeg'_eq_inertiaDeg]
    exact Nat.eq_one_of_mul_eq_one_left hef
  have hN : Ideal.absNorm P = Ideal.absNorm 𝔭.asIdeal := by
    rw [Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver P 𝔭.asIdeal 𝔭.isPrime 𝔭.ne_bot, hf, pow_one]
  have : Finite (𝓞 L ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
  letI := Ideal.Quotient.field P
  letI := Fintype.ofFinite (𝓞 L ⧸ P)
  have hpow : ∀ x : 𝓞 L, x ^ Ideal.absNorm 𝔭.asIdeal - x ∈ P := fun x => by
    rw [← Ideal.Quotient.eq, map_pow, ← hN, Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card _
  have hin : InInertia L 𝔭 σ := ⟨P, hP, hPo, fun x => by
    have := add_mem (hσ x) (hpow x)
    rwa [sub_add_sub_cancel] at this⟩
  have hσ1 : σ = 1 := hR.2.1 𝔭 hnd σ hin
  have hχ : ∀ χ : (L ≃ₐ[K] L) →* ℂˣ, heckeIdeal L χ 𝔭.asIdeal = 1 := fun χ => by
    rw [heckeIdeal_asIdeal, heckeVal_of_unramIn L χ (hR.2.1 𝔭 hnd) ⟨P, hP, hPo, hσ⟩, hσ1, map_one, Units.val_one]
  obtain ⟨α, β, hab, he⟩ := (hR.2.2.2 𝔭.asIdeal 𝔭.ne_bot hcop).1 hχ
  have hα : α ∈ 𝔭.asIdeal * Ideal.span {β} := he ▸ Ideal.mem_span_singleton_self α
  obtain ⟨π, hπ, rfl⟩ := Ideal.mem_mul_span_singleton.1 hα
  have hβ0 : Ideal.span {β} ≠ (0 : Ideal (𝓞 K)) := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hab.2.1
  have hsp : 𝔭.asIdeal = Ideal.span {π} := by
    refine mul_right_cancel₀ hβ0 ?_
    rw [he, Ideal.span_singleton_mul_span_singleton]
  refine ⟨π, hsp, ?_⟩
  obtain ⟨i, hi, j, hj, hij⟩ := Ideal.isCoprime_iff_exists.1 hab.2.2.2.1
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hi
  have h1 : (π - 1) * β ∈ 𝔮 := by
    have := hab.2.2.2.2.1
    rwa [show π * β - β = (π - 1) * β by ring] at this
  have h2 : π - 1 = c * ((π - 1) * β) + (π - 1) * j := by
    linear_combination (π - 1) * hij.symm
  rw [h2]
  exact add_mem (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ hj)

end GlobalTheory.Mem.RaySplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinitePrimitiveRootStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_primitive_root_of_clC_le : ∀ (l : ℕ) [Fact l.Prime] (K₀ L : Loc.FinExt l) (k : ℕ) (h : clC l (Kt l K₀ L) ≤ clC l (Kt l K₀ L ⊔ muK l k)), letI := (Subring.inclusion h).toAlgebra; Module.Finite ↥(clC l (Kt l K₀ L)) ↥(clC l (Kt l K₀ L ⊔ muK l k)) ∧ ∃ z : (↥(clC l (Kt l K₀ L ⊔ muK l k)))ˣ, IsPrimitiveRoot (z : ↥(clC l (Kt l K₀ L ⊔ muK l k))) (l ^ k) ∧ ∀ x : FractionRing ↥(clC l (Kt l K₀ L ⊔ muK l k)), ∃ p : Polynomial ↥(clC l (Kt l K₀ L)), ∃ d : ↥(clC l (Kt l K₀ L)), d ≠ 0 ∧ x * algebraMap _ (FractionRing ↥(clC l (Kt l K₀ L ⊔ muK l k))) (algebraMap _ ↥(clC l (Kt l K₀ L ⊔ muK l k)) d) = algebraMap _ (FractionRing ↥(clC l (Kt l K₀ L ⊔ muK l k))) (Polynomial.aeval (z : ↥(clC l (Kt l K₀ L ⊔ muK l k))) p) := by
  first | exact @GlobalTheory.CycLayers.finite_primitive_root | exact GlobalTheory.CycLayers.finite_primitive_root | (intros; apply GlobalTheory.CycLayers.finite_primitive_root <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasLatticeNormalFormOfBetween
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

noncomputable section

namespace GlobalTheory.Proof.hasLatticeNormalForm_of_between

open GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm GlobalTheory.Proof.normal_form_bounds_unfolding

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n c : ℕ}

omit [StarRing E] in
theorem intV_eN (P : HeightOneSpectrum (𝓞 E)) (N s : ℕ) : IntV P (Loc.eN E N s) := by
  intro l
  unfold Loc.eN
  split_ifs
  · exact intAt_one P
  · exact IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P

theorem read_bounds (P : HeightOneSpectrum (𝓞 E)) (j : ℕ) (h ρ : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E))
    (e : Fin c → ℤ) (z : Fin n → E) (hρ : ρ ∈ Loc.R1 E n c) (h1 : IntHom P h.symm.toLinearMap)
    (h2 : IntHom P (((qOf P : E) ^ j) • h.toLinearMap)) (hL : (ρ * h) '' {v | IntV P v} = nfLat P n c e z) :
    (∀ i, -(j : ℤ) ≤ e i ∧ e i ≤ 0) ∧ (1 ≤ c → IntV P z) := by
  have hq := Proof.NormalFormAtPrime.qOf_ne_zero P
  have hmem : ∀ v, IntV P v → ρ v ∈ nfLat P n c e z := fun v hv => by
    rw [← hL]
    refine ⟨h.symm v, h1 v hv, ?_⟩
    change ρ (h (h.symm v)) = ρ v
    rw [h.apply_symm_apply]
  refine ⟨fun i => ⟨?_, ?_⟩, fun hc a => ?_⟩
  · obtain ⟨v, hv, hrv⟩ : nfGen (qOf P) n c e z i ∈ (ρ * h) '' {v | IntV P v} := hL ▸ nfGen_mem P e z i
    change ρ (h v) = _ at hrv
    have hU : h v ∈ Loc.Ufl E n c (i.1 + 1) := by
      have := hρ.2.1 _ _ (hrv ▸ nfGen_mem_Ufl (qOf P) e z i)
      change ρ.symm (ρ (h v)) ∈ _ at this
      rwa [ρ.symm_apply_apply] at this
    have h3 : h v (Fin.natAdd n i) = (qOf P : E) ^ e i := by
      rw [← atN_natAdd (h v) i, ← atN_of_R1cond hρ.1 hU, hrv, atN_natAdd, nfGen_natAdd, if_pos rfl]
    have h4 : IntAt P ((qOf P : E) ^ j * h v (Fin.natAdd n i)) := h2 v hv (Fin.natAdd n i)
    rw [h3, ← zpow_natCast, ← zpow_add₀ hq] at h4
    have := nonneg_of_intAt_zpow h4
    omega
  · have hc : 1 ≤ c := by have := i.2; omega
    obtain ⟨u, hu, h'⟩ := (coords_of_mem hc (hmem _ (intV_eN P (n + c) (n + i.1)))).1 i
    refine le_of_zpow_eq hu ?_
    rw [← h', ← atN_natAdd (ρ _) i, atN_of_R1cond hρ.1 (eN_mem_Ufl (by omega)), atN_natAdd]
    simp [Loc.eN]
  · have h3 := (coords_of_mem hc (hmem _ (intV_eN P (n + c) n))).2 a
    have h4 : Loc.eN E (n + c) n (Fin.castAdd c a) = 0 := by
      unfold Loc.eN
      rw [if_neg (by have := a.2; simp; omega)]
    have h5 : Loc.eN E (n + c) n (Fin.natAdd n ⟨0, hc⟩) = 1 := by simp [Loc.eN]
    rw [hρ.1.2.1, h4, h5, one_mul, zero_sub] at h3
    simpa using IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_neg h3

theorem nfLat_of_eq_zero (P : HeightOneSpectrum (𝓞 E)) (hc : c = 0) (e : Fin c → ℤ) (z z' : Fin n → E) :
    nfLat P n c e z = nfLat P n c e z' := by
  subst hc
  simp [nfLat]

end General

theorem nf_of_between : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), P ∉ Pr.vGs → ∀ (h ρ : AutY X R j) (e : Fin (cOf R j) → ℤ) (z : Sp X.E (R.N j)), ρ ∈ Loc.R1 X.E (R.N j) (cOf R j) → Between j P h → (ρ * h) '' {v | IntV P v} = GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm.nfLat P (R.N j) (cOf R j) e z → GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm.NF Pr j P (ρ * h) := by
  intro X Pr R j P hP h ρ e z hρ hb hL
  obtain ⟨he, hz⟩ := read_bounds P j h ρ e z hρ hb.1 hb.2 hL
  rcases Nat.eq_zero_or_pos (cOf R j) with hc | hc
  · exact ⟨e, 0, he, zero_mem _, by rw [lamYat_coe hP, hL, nfLat_of_eq_zero P hc e z 0]⟩
  · exact ⟨e, z, he, (mem_stdAt_iff _).2 (hz hc), by rw [lamYat_coe hP, hL]⟩

end GlobalTheory.Proof.hasLatticeNormalForm_of_between

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNormalMvPolynomialOfIsNormal
section
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem isNormalScheme_sp_mvPolynomial :
    ∀ (R : Type) [CommRing R] (r : ℕ), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp R) →
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp (MvPolynomial (Fin r) R)) := by
  intro R _ r h x
  have hs : Algebra.Smooth R (MvPolynomial (Fin r) R) := ⟨inferInstance, inferInstance⟩
  let f : Sp (MvPolynomial (Fin r) R) ⟶ Sp R :=
    Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin r) R)))
  have : Smooth f := by
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
    exact RingHom.smooth_algebraMap.mpr hs
  exact forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth f h x

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSquareAbsNormConjInvariantMovedPrimesIdealStatement
section
open NumberField IsDedekindDomain Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSquare_absNorm_conjInvariant_movedPrimes_ideal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (𝔡 : Ideal (𝓞 E)), 𝔡 ≠ ⊥ → 𝔡.map (H.bar : 𝓞 E →+* 𝓞 E) = 𝔡 → (∀ P : Ideal (𝓞 E), P.IsPrime → 𝔡 ≤ P → P.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ P) → IsSquare (Ideal.absNorm 𝔡) := by
  first | exact @GlobalTheory.SquareNorm.isSquare_absNorm | exact GlobalTheory.SquareNorm.isSquare_absNorm | (intros; apply GlobalTheory.SquareNorm.isSquare_absNorm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MainProofStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weyl_lattice_duality : WeylLatticeDuality.Stmt := by
  first | exact @GlobalTheory.WeylLatDualProof.mainProof | exact GlobalTheory.WeylLatDualProof.mainProof | (intros; apply GlobalTheory.WeylLatDualProof.mainProof <;> assumption)
end

