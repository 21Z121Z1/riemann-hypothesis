import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0047
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjectiveCokerOfIsLocallyConstantFinrankRange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.GermDerivationOfFibreOfKillsBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

noncomputable section
namespace GlobalTheory.KS.VertFib

abbrev epsPt : Sp ℂ ⟶ Sp (DualNumber ℂ) := spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom

abbrev epsStr : Sp (DualNumber ℂ) ⟶ Sp ℂ := spMap (algebraMap ℂ (DualNumber ℂ))

def ringVal {A : Type} [CommRing A] {X : Scheme.{0}} (v : Sp A ⟶ X) (W : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ W) (f : Γ(X, W)) : A :=
  (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom ((v.appLE W ⊤ h).hom f)

theorem epsPt_epsStr : epsPt ≫ epsStr = 𝟙 _ := by
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1

theorem top_le_of_epsPt {X : Scheme.{0}} (v : Sp (DualNumber ℂ) ⟶ X) (W : X.Opens)
    (h : ⊤ ≤ (epsPt ≫ v) ⁻¹ᵁ W) : ⊤ ≤ v ⁻¹ᵁ W := by
  intro q _
  have hq : (q : PrimeSpectrum (DualNumber ℂ)) ∈
      Set.range (PrimeSpectrum.comap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) := by
    rw [range_comap_of_surjective _ _ (fun a => ⟨TrivSqZeroExt.inl a, rfl⟩)]
    intro x hx
    have hx0 : TrivSqZeroExt.fst x = 0 := hx
    apply q.isPrime.mem_of_pow_mem 2
    have : x ^ 2 = 0 := by
      rw [pow_two]; ext <;> simp [hx0]
    rw [this]; exact q.asIdeal.zero_mem
  obtain ⟨s, rfl⟩ := hq
  exact h (Set.mem_univ s)

theorem top_le_epsPt {X : Scheme.{0}} (v : Sp (DualNumber ℂ) ⟶ X) (W : X.Opens)
    (h : ⊤ ≤ v ⁻¹ᵁ W) : ⊤ ≤ (epsPt ≫ v) ⁻¹ᵁ W := fun _ _ => h (Set.mem_univ _)

theorem ringVal_appLE {A : Type} [CommRing A] {X Y : Scheme.{0}} (v : Sp A ⟶ Y) (m : Y ⟶ X) (W : X.Opens) (O : Y.Opens)
    (e : O ≤ m ⁻¹ᵁ W) (h : ⊤ ≤ v ⁻¹ᵁ O) (h' : ⊤ ≤ (v ≫ m) ⁻¹ᵁ W) (f : Γ(X, W)) :
    ringVal v O h ((m.appLE W O e).hom f) = ringVal (v ≫ m) W h' f := by
  rw [ringVal, ringVal, ← CommRingCat.comp_apply (m.appLE W O e), Scheme.Hom.appLE_comp_appLE]

theorem ringVal_app {A : Type} [CommRing A] {X Y : Scheme.{0}} (v : Sp A ⟶ Y) (m : Y ⟶ X) (W : X.Opens)
    (h : ⊤ ≤ v ⁻¹ᵁ (m ⁻¹ᵁ W)) (h' : ⊤ ≤ (v ≫ m) ⁻¹ᵁ W) (f : Γ(X, W)) :
    ringVal v (m ⁻¹ᵁ W) h ((m.app W).hom f) = ringVal (v ≫ m) W h' f := by
  rw [Scheme.Hom.app_eq_appLE]
  exact ringVal_appLE v m W _ _ h h' f

theorem ringVal_spMap {A R : Type} [CommRing A] [CommRing R] (φ : R →+* A) (h : ⊤ ≤ spMap φ ⁻¹ᵁ ⊤) (s : Γ(Sp R, ⊤)) :
    ringVal (spMap φ) ⊤ h s = φ ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom s) := by
  have h1 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  have h2 := congrArg (fun g => g.hom s) h1
  have h3 : (spMap φ).appLE ⊤ ⊤ h = (spMap φ).appTop := (Scheme.Hom.app_eq_appLE (spMap φ) (U := ⊤)).symm
  rw [ringVal, h3]
  exact h2

theorem ringVal_congr {A : Type} [CommRing A] {X : Scheme.{0}} {v v' : Sp A ⟶ X} (e : v = v') (W : X.Opens)
    (h : ⊤ ≤ v ⁻¹ᵁ W) (h' : ⊤ ≤ v' ⁻¹ᵁ W) (f : Γ(X, W)) : ringVal v W h f = ringVal v' W h' f := by
  subst e; rfl

theorem ringVal_constFn {A R : Type} [CommRing A] [CommRing R] {X : Scheme.{0}} (v : Sp A ⟶ X) (p : X ⟶ Sp R)
    (φ : R →+* A) (hv : v ≫ p = spMap φ) (h : ⊤ ≤ v ⁻¹ᵁ ⊤) (r : R) :
    ringVal v ⊤ h (constFn p ⊤ r) = φ r := by
  refine (ringVal_appLE v p ⊤ ⊤ le_top h le_top _).trans ?_
  refine (ringVal_congr hv ⊤ _ le_top _).trans ((ringVal_spMap φ _ _).trans ?_)
  congr 1
  exact (Scheme.ΓSpecIso (CommRingCat.of R)).inv_hom_id_apply r

theorem snd_ringVal_const {X : Scheme.{0}} (z : Sp ℂ ⟶ X) (W : X.Opens) (h : ⊤ ≤ (epsStr ≫ z) ⁻¹ᵁ W) (f : Γ(X, W)) :
    TrivSqZeroExt.snd (ringVal (epsStr ≫ z) W h f) = 0 := by
  have hz : ⊤ ≤ z ⁻¹ᵁ W := by
    have := top_le_epsPt _ W h
    rwa [← Category.assoc, epsPt_epsStr, Category.id_comp] at this
  exact congrArg TrivSqZeroExt.snd
    ((ringVal_appLE epsStr z W ⊤ hz le_top h f).symm.trans (ringVal_spMap _ _ _))

theorem comp_eq_const {R : Type} [CommRing R] (x₀ : R →+* ℂ) {X : Scheme.{0}} (p : X ⟶ Sp R)
    (v : Sp (DualNumber ℂ) ⟶ X) (h₁ : epsPt ≫ v ≫ p = spMap x₀)
    (h₂ : ∀ r, TrivSqZeroExt.snd (ringVal v ⊤ le_top (constFn p ⊤ r)) = 0) :
    v ≫ p = epsStr ≫ spMap x₀ := by
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (v ≫ p)
  have hφ : v ≫ p = spMap ψ.hom := hψ.symm
  rw [hφ, ← Spec.map_comp] at h₁
  have h₃ := Spec.map_injective h₁
  rw [hφ, ← Spec.map_comp]
  congr 1
  refine RingHom.ext fun r => ?_
  have h₄ : TrivSqZeroExt.snd (ψ.hom r : DualNumber ℂ) = 0 :=
    (congrArg TrivSqZeroExt.snd (ringVal_constFn v p ψ.hom hφ le_top r)).symm.trans (h₂ r)
  have h₅ : TrivSqZeroExt.fst (ψ.hom r : DualNumber ℂ) = x₀ r := congrArg (fun g => g.hom r) h₃
  exact TrivSqZeroExt.ext h₅ h₄

end GlobalTheory.KS.VertFib

open GlobalTheory.KS.VertFib in

theorem GlobalTheory.KS.ptDer_of_fibre : ∀ (Y : Over (Sp ℂ)) (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : Y.left ⟶ X), IsPullback m Y.hom p (spMap x₀) → ∀ y : Sp ℂ ⟶ Y.left, y ≫ Y.hom = 𝟙 _ → (∀ δ, PtDer (y ≫ m) δ → (∀ r, δ ⊤ (constFn p ⊤ r) = 0) → ∃ δ₀, PtDer y δ₀ ∧ (∀ a, δ₀ ⊤ (constFn Y.hom ⊤ a) = 0) ∧ ∀ W f, ⊤ ≤ (y ≫ m) ⁻¹ᵁ W → δ W f = δ₀ (m ⁻¹ᵁ W) ((m.app W).hom f)) ∧ ∀ δ₀, PtDer y δ₀ → (∀ a, δ₀ ⊤ (constFn Y.hom ⊤ a) = 0) → (∀ W f, ⊤ ≤ (y ≫ m) ⁻¹ᵁ W → δ₀ (m ⁻¹ᵁ W) ((m.app W).hom f) = 0) → ∀ O f, ⊤ ≤ y ⁻¹ᵁ O → δ₀ O f = 0 := by
  intro Y R _ x₀ X p m hP y hy
  constructor
  · intro δ hδ h0
    obtain ⟨v, ⟨hv, hvδ⟩, -⟩ := (GlobalTheory.T.germDerivation_iff_dualNumberPoint X (y ≫ m)).1 δ hδ
    have hvp : v ≫ p = epsStr ≫ spMap x₀ := by
      refine comp_eq_const x₀ p v ?_ fun r => (hvδ ⊤ le_top _).trans (h0 r)
      rw [← Category.assoc, hv, Category.assoc, hP.w, ← Category.assoc, hy, Category.id_comp]
    have hw₁ := hP.lift_fst v epsStr hvp
    have hw₂ := hP.lift_snd v epsStr hvp
    generalize hP.lift v epsStr hvp = w at hw₁ hw₂
    have hwy : epsPt ≫ w = y := by
      apply hP.hom_ext
      · rw [Category.assoc, hw₁, hv]
      · rw [Category.assoc, hw₂, epsPt_epsStr, hy]
    obtain ⟨δ₀, hδ₀, hw⟩ := (GlobalTheory.T.germDerivation_iff_dualNumberPoint Y.left y).2 w hwy
    refine ⟨δ₀, hδ₀, fun a => ?_, fun W f hW => ?_⟩
    · refine (hw ⊤ le_top _).symm.trans ?_
      exact congrArg TrivSqZeroExt.snd (ringVal_constFn w Y.hom _ hw₂ le_top a)
    · have h1 : ⊤ ≤ v ⁻¹ᵁ W := top_le_of_epsPt v W (by rw [hv]; exact hW)
      have h2 : ⊤ ≤ (w ≫ m) ⁻¹ᵁ W := by rw [hw₁]; exact h1
      refine (hvδ W h1 f).symm.trans (Eq.trans ?_ (hw (m ⁻¹ᵁ W) h2 _))
      exact congrArg TrivSqZeroExt.snd
        ((ringVal_congr hw₁.symm W h1 h2 f).trans (ringVal_app w m W h2 h2 f).symm)
  · intro δ₀ hδ₀ h0 hm O f hO
    obtain ⟨v, ⟨hv, hvδ⟩, -⟩ := (GlobalTheory.T.germDerivation_iff_dualNumberPoint Y.left y).1 δ₀ hδ₀
    have hvp : v ≫ Y.hom = epsStr := by
      have hid : spMap (RingHom.id ℂ) = 𝟙 (Sp ℂ) := Spec.map_id _
      have := comp_eq_const (RingHom.id ℂ) Y.hom v (by rw [← Category.assoc, hv, hy, hid])
        fun r => (hvδ ⊤ le_top _).trans (h0 r)
      rwa [hid, Category.comp_id] at this
    have hz : PtDer (y ≫ m) (fun _ _ => 0) := ⟨by simp, by simp, by simp⟩
    have hvm : v ≫ m = epsStr ≫ y ≫ m := by
      refine ((GlobalTheory.T.germDerivation_iff_dualNumberPoint X (y ≫ m)).1 _ hz).unique ⟨?_, fun W h g => ?_⟩ ⟨?_, fun W h g => ?_⟩
      · rw [← Category.assoc, hv]
      · have hW : ⊤ ≤ (y ≫ m) ⁻¹ᵁ W := by
          have := top_le_epsPt _ W h
          rwa [← Category.assoc, hv] at this
        refine Eq.trans ?_ ((hvδ (m ⁻¹ᵁ W) h _).trans (hm W g hW))
        exact congrArg TrivSqZeroExt.snd (ringVal_app v m W h h g).symm
      · rw [← Category.assoc, epsPt_epsStr, Category.id_comp]
      · exact snd_ringVal_const (y ≫ m) W h g
    have hvc : v = epsStr ≫ y := by
      apply hP.hom_ext
      · rw [hvm, Category.assoc]
      · rw [hvp, Category.assoc, hy, Category.comp_id]
    have h1 : ⊤ ≤ v ⁻¹ᵁ O := top_le_of_epsPt v O (by rw [hv]; exact hO)
    refine (hvδ O h1 f).symm.trans ?_
    have h2 : ⊤ ≤ (epsStr ≫ y) ⁻¹ᵁ O := by rw [← hvc]; exact h1
    exact (congrArg TrivSqZeroExt.snd (ringVal_congr hvc O h1 h2 f)).trans (snd_ringVal_const y O h2 f)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomogeneousComponentMemVanIdeal
section
open scoped TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.FamAlg
open Module MvPolynomial GlobalTheory.Semicont

theorem projective_of_veryDense {R : Type} [CommRing R] [IsReduced R] {P : Set (Ideal R)} (hP : VeryDense P)
    (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] (r : ℚ)
    (h : ∀ q : PrimeSpectrum R, q.asIdeal ∈ P →
      (finrank q.asIdeal.ResidueField (q.asIdeal.ResidueField ⊗[R] M) : ℚ) = r) :
    Module.Projective R M := by
  have key : ∀ q : PrimeSpectrum R,
      (finrank q.asIdeal.ResidueField (q.asIdeal.ResidueField ⊗[R] M) : ℚ) = r := by
    intro q
    obtain ⟨_, ⟨f, rfl⟩, hqf, hf⟩ := (PrimeSpectrum.isTopologicalBasis_basic_opens.mem_nhds_iff).1
      (eventually_finrank_fiber_le (M := M) q)
    obtain ⟨p, hp, hpp, hqp, hfp⟩ := hP q.asIdeal f q.isPrime hqf
    rw [← h ⟨p, hpp⟩ hp]
    congr 1
    refine le_antisymm ?_ (hf (show (⟨p, hpp⟩ : PrimeSpectrum R) ∈ _ from hfp))
    have hs : q ⤳ (⟨p, hpp⟩ : PrimeSpectrum R) := (PrimeSpectrum.le_iff_specializes _ _).1 hqp
    exact (hs.nhds_le_nhds.trans' (pure_le_nhds q)) (eventually_finrank_fiber_le (M := M) ⟨p, hpp⟩)
  refine projective_of_finite_of_isLocallyConstant_finrank_fiber
    (IsLocallyConstant.of_constant _ fun p q => ?_)
  exact_mod_cast (key p).trans (key q).symm

theorem exists_basis (σ R : Type) [CommRing R] (e : ℕ) :
    ∃ b : Basis {u : σ →₀ ℕ | u.degree = e} R (homogeneousSubmodule σ R e),
      ∀ F i, b.repr F i = coeff i.1 F.1 := by
  rw [homogeneousSubmodule_eq_finsupp_supported]
  exact ⟨basisRestrictSupport R _, fun F i => rfl⟩

theorem finrank_forms (σ K : Type) [Field K] (e : ℕ) :
    finrank K (homogeneousSubmodule σ K e) = Nat.card {u : σ →₀ ℕ | u.degree = e} := by
  obtain ⟨b, -⟩ := exists_basis σ K e
  exact finrank_eq_nat_card_basis b

theorem exists_equiv (σ R K : Type) [CommRing R] [CommRing K] [Algebra R K] (e : ℕ) :
    ∃ θ : K ⊗[R] homogeneousSubmodule σ R e ≃ₗ[K] homogeneousSubmodule σ K e,
      ∀ F, (θ (1 ⊗ₜ F)).1 = map (algebraMap R K) F.1 := by
  obtain ⟨b, hb⟩ := exists_basis σ R e
  obtain ⟨c, hc⟩ := exists_basis σ K e
  refine ⟨(b.baseChange K).repr ≪≫ₗ c.repr.symm, fun F => ?_⟩
  have : (b.baseChange K).repr (1 ⊗ₜ F) = c.repr ⟨map (algebraMap R K) F.1, IsHomogeneous.map F.2 _⟩ := by
    ext i
    rw [Basis.baseChange_repr_tmul, hb, hc, coeff_map, Algebra.smul_def, mul_one]
  rw [LinearEquiv.trans_apply, this, LinearEquiv.symm_apply_apply]

theorem map_homogeneousComponent {σ R K : Type} [CommRing R] [CommRing K] (x : R →+* K) (e : ℕ)
    (F : MvPolynomial σ R) : homogeneousComponent e (map x F) = map x (homogeneousComponent e F) := by
  ext u
  simp only [coeff_homogeneousComponent, coeff_map]
  split_ifs <;> simp

theorem mem_span_of_mem_map {σ R K : Type} [CommRing R] [CommRing K] (x : R →+* K)
    (J : Ideal (MvPolynomial σ R)) {F : MvPolynomial σ K} (hF : F ∈ J.map (map x)) :
    F ∈ Submodule.span K (map x '' (J : Set (MvPolynomial σ R))) := by
  refine Submodule.span_induction (fun G hG => Submodule.subset_span hG) (zero_mem _)
    (fun _ _ _ _ => add_mem) (fun a G _ hG => ?_) hF
  rw [smul_eq_mul]
  induction a using MvPolynomial.induction_on' with
  | add a b ha hb => rw [add_mul]; exact add_mem ha hb
  | monomial u c =>
    have : monomial u c = c • map x (monomial u 1) := by simp [smul_monomial]
    rw [this, smul_mul_assoc]
    refine Submodule.smul_mem _ _ ?_
    refine Submodule.span_induction ?_ (by simp) (fun _ _ _ _ h1 h2 => ?_) (fun s _ _ h1 => ?_) hG
    · rintro _ ⟨H, hH, rfl⟩
      exact Submodule.subset_span ⟨_, J.mul_mem_left (monomial u 1) hH, map_mul _ _ _⟩
    · rw [mul_add]; exact add_mem h1 h2
    · rw [mul_smul_comm]; exact Submodule.smul_mem _ _ h1

attribute [local instance] MvPolynomial.gradedAlgebra in
theorem homogeneousComponent_mem_vanIdeal {σ R Hh : Type} [CommRing R] (d : ℕ) (p : Hh → σ → R)
    {F : MvPolynomial σ R} (hF : F ∈ vanIdeal d p) (e : ℕ) : homogeneousComponent e F ∈ vanIdeal d p :=
  homogeneousComponent_mem_of_mem (Ideal.homogeneous_span _ _ fun _ hG => ⟨d, hG.1⟩) hF e

theorem eval_eq_zero_of_mem_vanIdeal {σ R Hh : Type} [CommRing R] (d : ℕ) (p : Hh → σ → R)
    {F : MvPolynomial σ R} (hF : F ∈ vanIdeal d p) (h : Hh) : eval (p h) F = 0 :=
  (Ideal.span_le (I := RingHom.ker (eval (p h)))).2 (fun _ hG => hG.2 h) hF

noncomputable abbrev part {σ R : Type} [CommRing R] (J : Ideal (MvPolynomial σ R)) (e : ℕ) :
    Submodule R (homogeneousSubmodule σ R e) :=
  (J.restrictScalars R).comap (homogeneousSubmodule σ R e).subtype

noncomputable def ev {σ R Hh : Type} [CommRing R] (d : ℕ) (p : Hh → σ → R) :
    homogeneousSubmodule σ R d →ₗ[R] (Hh → R) :=
  LinearMap.pi fun h => (aeval (p h)).toLinearMap ∘ₗ (homogeneousSubmodule σ R d).subtype

theorem ev_apply {σ R Hh : Type} [CommRing R] (d : ℕ) (p : Hh → σ → R) (F) (h : Hh) :
    ev d p F h = eval (p h) F.1 := by
  rw [← coe_aeval_eq_eval]
  rfl

theorem ker_ev {σ R Hh : Type} [CommRing R] (d : ℕ) (p : Hh → σ → R) :
    LinearMap.ker (ev d p) = part (vanIdeal d p) d := by
  ext F
  constructor
  · intro hF
    exact Ideal.subset_span ⟨F.2, fun h => (ev_apply d p F h).symm.trans (congrFun (LinearMap.mem_ker.1 hF) h)⟩
  · intro hF
    have hF' : F.1 ∈ vanIdeal d p := hF
    rw [LinearMap.mem_ker]
    ext h
    rw [ev_apply, eval_eq_zero_of_mem_vanIdeal d p hF' h, Pi.zero_apply]

theorem finrank_part {σ K Hh : Type} [Field K] {I : Ideal (MvPolynomial σ K)} {Q : Polynomial ℚ} {d : ℕ}
    {p : Hh → σ → K} (h : CutBy I Q d p) {e : ℕ} (he : e ≥ d) :
    (finrank K (part (vanIdeal d p) e) : ℚ) = Q.eval (e : ℚ) := by
  have h1 : part (vanIdeal d p) e = part I e := by
    ext F
    exact ((h e he).2 F.1 F.2).symm
  rw [← (h e he).1, h1, dimDeg, ← Submodule.map_comap_subtype, Submodule.finrank_map_subtype_eq]

theorem map_ker_baseChange {σ R Hh : Type} (K : Type) [CommRing R] [CommRing K] [Algebra R K] [Finite Hh]
    (d : ℕ) (p : Hh → σ → R) (θ : K ⊗[R] homogeneousSubmodule σ R d ≃ₗ[K] homogeneousSubmodule σ K d)
    (hθ : ∀ F, (θ (1 ⊗ₜ F)).1 = map (algebraMap R K) F.1) :
    (LinearMap.ker ((ev d p).baseChange K)).map θ.toLinearMap =
      part (vanIdeal d fun h i => algebraMap R K (p h i)) d := by
  classical
  letI := Fintype.ofFinite Hh
  have key : ∀ z, ev d (fun h i => algebraMap R K (p h i)) (θ z) =
      TensorProduct.piScalarRight R K K Hh ((ev d p).baseChange K z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul a F =>
      have : a ⊗ₜ[R] F = a • (1 : K) ⊗ₜ[R] F := by simp [TensorProduct.smul_tmul']
      rw [this, map_smul, map_smul, map_smul, map_smul]
      congr 1
      ext h
      rw [ev_apply, hθ, eval_map]
      have h2 := eval₂_comp_left (algebraMap R K) (RingHom.id R) (p h) F.1
      rw [LinearMap.baseChange_tmul, TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
      beta_reduce
      rw [ev_apply, Algebra.smul_def, mul_one]
      exact h2.symm
  rw [← ker_ev, Submodule.map_equiv_eq_comap_symm]
  ext F
  simp only [Submodule.mem_comap, LinearMap.mem_ker, LinearEquiv.coe_coe]
  rw [← (TensorProduct.piScalarRight R K K Hh).map_eq_zero_iff, ← key, LinearEquiv.apply_symm_apply]

theorem map_part_baseChange {σ R : Type} (K : Type) [CommRing R] [CommRing K] [Algebra R K]
    (J : Ideal (MvPolynomial σ R)) (e : ℕ) (hJ : ∀ F ∈ J, homogeneousComponent e F ∈ J)
    (θ : K ⊗[R] homogeneousSubmodule σ R e ≃ₗ[K] homogeneousSubmodule σ K e)
    (hθ : ∀ F, (θ (1 ⊗ₜ F)).1 = map (algebraMap R K) F.1) :
    ((part J e).baseChange K).map θ.toLinearMap = part (J.map (map (algebraMap R K))) e := by
  apply le_antisymm
  · rw [Submodule.baseChange_eq_span, Submodule.map_span_le]
    rintro _ ⟨F, hF, rfl⟩
    show (θ (1 ⊗ₜ F)).1 ∈ J.map _
    rw [hθ]
    exact Ideal.mem_map_of_mem _ hF
  · intro F hF
    have h1 := mem_span_of_mem_map _ J hF
    have h2 : ∀ G ∈ Submodule.span K (map (algebraMap R K) '' (J : Set (MvPolynomial σ R))),
        (homogeneousComponent e).codRestrict _ (homogeneousComponent_mem e) G ∈
          ((part J e).baseChange K).map θ.toLinearMap := by
      intro G hG
      refine Submodule.span_le (p := (((part J e).baseChange K).map θ.toLinearMap).comap
        ((homogeneousComponent e).codRestrict _ (homogeneousComponent_mem e))) |>.2 ?_ hG
      rintro _ ⟨H, hH, rfl⟩
      refine ⟨1 ⊗ₜ ⟨_, homogeneousComponent_mem e H⟩,
        Submodule.tmul_mem_baseChange_of_mem _ (hJ H hH), Subtype.ext ?_⟩
      exact (hθ _).trans (map_homogeneousComponent _ _ _).symm
    convert h2 _ h1
    exact Subtype.ext (by simp [homogeneousComponent_of_mem F.2])

theorem forms_through_points : ∀ (R : Type) [CommRing R] [IsReduced R] (σ Hh : Type) [Finite σ] [Finite Hh] (p : Hh → σ → R) (Q : Polynomial ℚ) (d : ℕ) (P : Set (Ideal R)), VeryDense P → (∀ q ∈ P, ∃ (K : Type) (_ : Field K) (x : R →+* K) (I : Ideal (MvPolynomial σ K)), RingHom.ker x = q ∧ CutBy I Q d (fun h i => x (p h i))) → (∀ e ≥ d, Module.Projective R (↥(MvPolynomial.homogeneousSubmodule σ R e) ⧸ ((vanIdeal d p).restrictScalars R).comap (MvPolynomial.homogeneousSubmodule σ R e).subtype)) ∧ (vanIdeal d p).FG ∧ ∀ (K : Type) [Field K] (x : R →+* K), (vanIdeal d p).map (MvPolynomial.map x) = vanIdeal d (fun h i => x (p h i)) := by
  intro R _ _ σ Hh _ _ p Q d P hP hcut
  have hfin : ∀ e, Module.Finite R (homogeneousSubmodule σ R e) := fun e =>
    Module.Finite.iff_fg.2 (homogeneousSubmodule_fg σ R e)
  have hcoker : Module.Projective R ((Hh → R) ⧸ LinearMap.range (ev d p)) := by
    refine projective_of_veryDense hP _
      ((Nat.card Hh : ℚ) - (Nat.card {u : σ →₀ ℕ | u.degree = d} - Q.eval (d : ℚ))) fun q hq => ?_
    obtain ⟨K, _, x, I, hx, hI⟩ := hcut _ hq
    letI := x.toAlgebra
    classical
    letI := Fintype.ofFinite Hh
    obtain ⟨θ, hθ⟩ := exists_equiv σ R K d
    have h1 := finrank_baseChange_coker_add_finrank_range K (ev d p)
    have h2 := ((ev d p).baseChange K).finrank_range_add_finrank_ker
    have h3 : (finrank K (LinearMap.ker ((ev d p).baseChange K)) : ℚ) = Q.eval (d : ℚ) := by
      rw [← finrank_part hI le_rfl, ← θ.finrank_map_eq, map_ker_baseChange K d p θ hθ]
      rfl
    rw [θ.finrank_eq, finrank_forms] at h2
    rw [(TensorProduct.piScalarRight R K K Hh).finrank_eq, finrank_fintype_fun_eq_card,
      ← Nat.card_eq_fintype_card] at h1
    rw [← finrank_tensorProduct_eq_finrank_fiber K q hx.symm, ← h1, ← h2, ← h3]
    push_cast
    ring
  obtain ⟨s, hs⟩ := exists_comp_comp_eq_of_projective (ev d p)
  have hmap : ∀ (K : Type) [Field K] (x : R →+* K),
      (vanIdeal d p).map (MvPolynomial.map x) = vanIdeal d (fun h i => x (p h i)) := by
    intro K _ x
    letI := x.toAlgebra
    obtain ⟨θ, hθ⟩ := exists_equiv σ R K d
    have h1 := map_ker_baseChange K d p θ hθ
    rw [← baseChange_ker_of_comp_comp_eq _ s hs, ker_ev, map_part_baseChange K _ d
      (fun F hF => homogeneousComponent_mem_vanIdeal d p hF d) θ hθ] at h1
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      refine Ideal.span_le.2 fun F hF => ?_
      exact (SetLike.ext_iff.1 h1 ⟨map x F, hF.1.map x⟩).1 (Ideal.mem_map_of_mem _ (Ideal.subset_span hF))
    · refine Ideal.span_le.2 fun F hF => ?_
      exact (SetLike.ext_iff.1 h1 ⟨F, hF.1⟩).2 (Ideal.subset_span hF)
  refine ⟨fun e he => ?_, ?_, hmap⟩
  · refine projective_of_veryDense hP _
      ((Nat.card {u : σ →₀ ℕ | u.degree = e} : ℚ) - Q.eval (e : ℚ)) fun q hq => ?_
    obtain ⟨K, _, x, I, hx, hI⟩ := hcut _ hq
    letI := x.toAlgebra
    obtain ⟨θ, hθ⟩ := exists_equiv σ R K e
    have h1 := Submodule.finrank_quotient_add_finrank ((part (vanIdeal d p) e).baseChange K)
    have h3 : (finrank K ((part (vanIdeal d p) e).baseChange K) : ℚ) = Q.eval (e : ℚ) := by
      rw [← finrank_part hI he, ← θ.finrank_map_eq, map_part_baseChange K _ e
        (fun F hF => homogeneousComponent_mem_vanIdeal d p hF e) θ hθ, ← hmap K x]
      rfl
    rw [θ.finrank_eq, finrank_forms, ← (baseChangeQuotEquiv K _).finrank_eq] at h1
    rw [← finrank_tensorProduct_eq_finrank_fiber K q hx.symm, ← h1, ← h3]
    push_cast
    ring
  · obtain ⟨t, ht⟩ := exists_retraction_ker_of_generalizedInverse _ s hs
    have h2 : Module.Finite R (LinearMap.ker (ev d p)) := Module.Finite.of_surjective t
      (Function.RightInverse.surjective (g := (LinearMap.ker (ev d p)).subtype) (LinearMap.congr_fun ht))
    obtain ⟨T, hT⟩ := (Module.Finite.iff_fg.1 h2).map (homogeneousSubmodule σ R d).subtype
    refine ⟨T, le_antisymm (Ideal.span_le.2 fun F hF => ?_) (Ideal.span_le.2 fun F hF => ?_)⟩
    · have : F ∈ (LinearMap.ker (ev d p)).map (homogeneousSubmodule σ R d).subtype :=
        hT ▸ Submodule.subset_span hF
      obtain ⟨G, hG, rfl⟩ := this
      exact (ker_ev d p).le hG
    · have : F ∈ Submodule.span R (T : Set (MvPolynomial σ R)) :=
        hT ▸ ⟨⟨F, hF.1⟩, (ker_ev d p).ge (Ideal.subset_span hF), rfl⟩
      exact Submodule.span_le_restrictScalars R _ _ this

end GlobalTheory.FamAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsGrpPullbackLocalOnBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.GrpLoc

theorem hom_ext_loc {X Y : Scheme.{0}} {f g : X ⟶ Y}
    (h : ∀ p : X, ∃ (W : Scheme.{0}) (a : W ⟶ X), IsOpenImmersion a ∧ p ∈ Set.range a ∧ a ≫ f = a ≫ g) : f = g := by
  choose W a ha hp hfg using h
  exact Scheme.Cover.hom_ext (Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) X W a
    (fun x => by obtain ⟨y, hy⟩ := hp x; exact ⟨x, y, hy⟩) ha) f g hfg

theorem range_of_isPullback {P X Y Z : Scheme.{0}} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback a b f g) (x : X) : x ∈ Set.range a ↔ f x ∈ Set.range g := by
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨b p, by rw [← Scheme.Hom.comp_apply, ← h.w, Scheme.Hom.comp_apply]⟩
  · rintro ⟨y, hy⟩
    obtain ⟨q, hq₁, -⟩ := Scheme.Pullback.exists_preimage_pullback x y hy.symm
    refine ⟨h.isoPullback.inv q, ?_⟩
    rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_fst, hq₁]

theorem mul_left_pre {S : Scheme.{0}} {G : Over S} [GrpObj G] {T T' : Over S} (k : T'.left ⟶ T.left)
    (hk : k ≫ T.hom = T'.hom) (x y : T ⟶ G) (x' y' : T' ⟶ G) (hx : x'.left = k ≫ x.left)
    (hy : y'.left = k ≫ y.left) : (x' * y').left = k ≫ (x * y).left := by
  have ex : x' = Over.homMk k hk ≫ x := by ext; simp [hx]
  have ey : y' = Over.homMk k hk ≫ y := by ext; simp [hy]
  rw [ex, ey, ← MonObj.comp_mul, Over.comp_left]
  rfl

theorem isGrpPullback_id_of_loc {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [GrpObj A'] (φ : A.left ⟶ A'.left) [IsIso φ]
    (w : φ ≫ A'.hom = A.hom)
    (h : ∀ p : S, ∃ (W : Scheme.{0}) (x : W ⟶ S) (B : Over W) (_ : GrpObj B) (a : B.left ⟶ A.left),
      IsOpenImmersion x ∧ p ∈ Set.range x ∧ IsGrpPullback B A x a ∧ IsGrpPullback B A' x (a ≫ φ)) :
    IsGrpPullback A A' (𝟙 S) φ := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simpa using w⟩, ?_⟩
  intro T x y x₀ y₀ hx hy
  apply hom_ext_loc
  intro t
  obtain ⟨W, xS, B, _, a, hxo, ⟨w0, hw0⟩, hB, hB'⟩ := h (T.hom t)
  refine ⟨pullback T.hom xS, pullback.fst T.hom xS, inferInstance,
    (range_of_isPullback (IsPullback.of_hasPullback T.hom xS) t).2 ⟨w0, hw0⟩, ?_⟩
  let TW : Over W := Over.mk (pullback.snd T.hom xS)
  have cx : (pullback.fst T.hom xS ≫ x.left) ≫ A.hom = pullback.snd T.hom xS ≫ xS := by
    rw [Category.assoc, Over.w x, pullback.condition]
  have cy : (pullback.fst T.hom xS ≫ y.left) ≫ A.hom = pullback.snd T.hom xS ≫ xS := by
    rw [Category.assoc, Over.w y, pullback.condition]
  have cx' : (pullback.fst T.hom xS ≫ x.left ≫ φ) ≫ A'.hom = pullback.snd T.hom xS ≫ xS := by
    simpa [w] using cx
  have cy' : (pullback.fst T.hom xS ≫ y.left ≫ φ) ≫ A'.hom = pullback.snd T.hom xS ≫ xS := by
    simpa [w] using cy
  let XB : TW ⟶ B := Over.homMk (hB.1.lift _ _ cx) (hB.1.lift_snd _ _ cx)
  let YB : TW ⟶ B := Over.homMk (hB.1.lift _ _ cy) (hB.1.lift_snd _ _ cy)
  let x' : Over.mk (TW.hom ≫ xS) ⟶ A := Over.homMk (pullback.fst T.hom xS ≫ x.left) cx
  let y' : Over.mk (TW.hom ≫ xS) ⟶ A := Over.homMk (pullback.fst T.hom xS ≫ y.left) cy
  let x₁ : Over.mk (TW.hom ≫ xS) ⟶ A' := Over.homMk (pullback.fst T.hom xS ≫ x.left ≫ φ) cx'
  let y₁ : Over.mk (TW.hom ≫ xS) ⟶ A' := Over.homMk (pullback.fst T.hom xS ≫ y.left ≫ φ) cy'
  have e1 : (x' * y').left = (XB * YB).left ≫ a :=
    hB.2 TW XB YB x' y' (hB.1.lift_fst _ _ cx).symm (hB.1.lift_fst _ _ cy).symm
  have e2 : (x₁ * y₁).left = (XB * YB).left ≫ a ≫ φ := by
    refine hB'.2 TW XB YB x₁ y₁ ?_ ?_
    · simp only [x₁, XB, Over.homMk_left]
      rw [← Category.assoc (hB.1.lift _ _ cx), hB.1.lift_fst, Category.assoc]
    · simp only [y₁, YB, Over.homMk_left]
      rw [← Category.assoc (hB.1.lift _ _ cy), hB.1.lift_fst, Category.assoc]
  have hk : pullback.fst T.hom xS ≫ T.hom = (Over.mk (TW.hom ≫ xS)).hom := by
    simp [TW, pullback.condition]
  have hk' : pullback.fst T.hom xS ≫ (Over.mk (T.hom ≫ 𝟙 S)).hom = (Over.mk (TW.hom ≫ xS)).hom := by
    simp [TW, pullback.condition]
  have m1 := mul_left_pre (pullback.fst T.hom xS) hk x y x' y' rfl rfl
  have m2 := mul_left_pre (pullback.fst T.hom xS) hk' x₀ y₀ x₁ y₁
    (by simp only [x₁, Over.homMk_left, hx]) (by simp only [y₁, Over.homMk_left, hy])
  rw [← m2, e2, ← Category.assoc, ← e1, m1, Category.assoc]

theorem isGrpPullback_local_on_base : ∀ (S : Scheme.{0}) (A A' : Over S) [GrpObj A] [GrpObj A'] (φ : A.left ⟶ A'.left), IsIso φ → φ ≫ A'.hom = A.hom → (∀ p : S, ∃ (V : Scheme.{0}) (x : V ⟶ S) (B : Over V) (_ : GrpObj B) (a : B.left ⟶ A.left), IsOpenImmersion x ∧ p ∈ Set.range x ∧ IsGrpPullback B A x a ∧ IsGrpPullback B A' x (a ≫ φ)) → IsGrpPullback A A' (𝟙 S) φ := by
  intro S A A' _ _ φ hφ w h
  exact isGrpPullback_id_of_loc φ w h

end GlobalTheory.GrpLoc
end
end

