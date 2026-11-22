import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0020
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0087
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0075
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0085
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0009
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0026

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.StalkOfSmoothLocal
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.StabFlat

theorem localization_of_isStandardSmooth_ideal {V R A : Type} [CommRing V] [IsNoetherianRing V] [CommRing R]
    [CommRing A] (m : Ideal V) [m.IsMaximal] {g : ℕ} {ρ : V →+* R}
    (hρ : ρ.IsStandardSmoothOfRelativeDimension g) (n : Ideal R) [n.IsMaximal] [Algebra R A]
    [IsLocalization.AtPrime A n] (hn : m.map ρ ≤ n) :
    IsNoetherianRing A ∧ ((algebraMap R A).comp ρ).Flat ∧
      IsRegularLocalRing (A ⧸ m.map ((algebraMap R A).comp ρ)) ∧
      ringKrullDim (A ⧸ m.map ((algebraMap R A).comp ρ)) = g := by
  have hq : (Ideal.quotientMap (m.map ρ) ρ Ideal.le_comap_map).IsStandardSmoothOfRelativeDimension g := by
    have := RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.2
      (RingHom.isStandardSmoothOfRelativeDimension_isStableUnderBaseChange.{0} g)
    exact MorphismProperty.of_isPushout
      (P := RingHom.toMorphismProperty (@RingHom.IsStandardSmoothOfRelativeDimension g))
      (NilpotentLift.isPushout_quotient_map m (CommRingCat.ofHom ρ)).flip hρ
  letI := ρ.toAlgebra
  have : Algebra.IsStandardSmoothOfRelativeDimension g V R := hρ
  have : Algebra.IsStandardSmooth V R := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth g
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing V R
  refine ⟨IsLocalization.isNoetherianRing n.primeCompl A inferInstance, ?_, ?_⟩
  · have h₁ : ρ.Flat := (inferInstance : Module.Flat V R)
    have h₂ : (algebraMap R A).Flat :=
      RingHom.flat_algebraMap_iff.2 (IsLocalization.flat A n.primeCompl)
    exact h₁.comp h₂
  letI := Ideal.Quotient.field m
  rw [← Ideal.map_map]
  set J := m.map ρ with hJ
  obtain ⟨φ, -, hφ⟩ := hq.exists_etale_mvPolynomial
  have hJn : RingHom.ker (Ideal.Quotient.mk J) ≤ n := by
    rwa [Ideal.mk_ker]
  letI := φ.toAlgebra
  have : Algebra.Etale (MvPolynomial (Fin g) (V ⧸ m)) (R ⧸ J) := hφ.toAlgebra
  have : IsRegularRing (R ⧸ J) := isRegularRing_of_etale (MvPolynomial (Fin g) (V ⧸ m)) _
  have hm : (n.map (Ideal.Quotient.mk J)).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective hJn
  have hle : J ≤ (J.map (algebraMap R A)).comap (algebraMap R A) := Ideal.le_comap_map
  letI : Algebra (R ⧸ J) (A ⧸ J.map (algebraMap R A)) := (Ideal.quotientMap _ _ hle).toAlgebra
  have hl := IsLocalization.of_surjective n.primeCompl A (S' := A ⧸ J.map (algebraMap R A))
    (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective rfl
    (by rw [Ideal.mk_ker, Ideal.mk_ker])
  have e : n.primeCompl.map (Ideal.Quotient.mk J) = (n.map (Ideal.Quotient.mk J)).primeCompl := by
    have hc : (n.map (Ideal.Quotient.mk J)).comap (Ideal.Quotient.mk J) = n := by
      rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, sup_eq_left.2 hJn]
    ext y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    constructor
    · rintro ⟨x', hx', e⟩ hx
      exact hx' (hc.le (show Ideal.Quotient.mk J x' ∈ _ from e ▸ hx))
    · exact fun hx => ⟨x, fun h => hx (Ideal.mem_map_of_mem _ h), rfl⟩
  rw [e] at hl
  refine ⟨?_, (IsLocalization.AtPrime.ringKrullDim_eq_height (n.map (Ideal.Quotient.mk J)) _).trans
    (height_of_etale_mvPolynomial (V ⧸ m) (R ⧸ J) g _)⟩
  have := IsRegularRing.isRegularLocalRing_localization (n.map (Ideal.Quotient.mk J))
  exact IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv (n.map (Ideal.Quotient.mk J)).primeCompl
    (Localization.AtPrime (n.map (Ideal.Quotient.mk J))) _).toRingEquiv

theorem stalk_of_smooth_local : ∀ (V : Type) [CommRing V] [IsNoetherianRing V] [IsLocalRing V] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of V)) (g : ℕ), SmoothOfRelativeDimension g f → ∀ x : X, IsClosed ({x} : Set X) → ∀ σ : V →+* X.presheaf.stalk x, X.fromSpecStalk x ≫ f = Spec.map (CommRingCat.ofHom σ) → IsLocalHom σ → IsNoetherianRing (X.presheaf.stalk x) ∧ σ.Flat ∧ IsRegularLocalRing (X.presheaf.stalk x ⧸ (IsLocalRing.maximalIdeal V).map σ) ∧ ringKrullDim (X.presheaf.stalk x ⧸ (IsLocalRing.maximalIdeal V).map σ) = g := by
  intro V _ _ _ X f g hg x hx σ hσ hn
  obtain ⟨U, hU, W, hW, hxW, e, H⟩ := hg.exists_isStandardSmoothOfRelativeDimension x
  have hfx : f x = IsLocalRing.closedPoint V :=
    ((congrArg f Scheme.fromSpecStalk_closedPoint.symm).trans
      (congrArg (fun q => q (IsLocalRing.closedPoint _)) hσ)).trans (IsLocalRing.comap_closedPoint σ)
  obtain rfl : U = ⊤ := (IsLocalRing.closedPoint_mem_iff U).1 (hfx ▸ e hxW)
  let ρ := (Scheme.ΓSpecIso (CommRingCat.of V)).inv ≫ f.appLE ⊤ W e
  have hρ : ρ.hom.IsStandardSmoothOfRelativeDimension g :=
    (RingHom.isStandardSmoothOfRelativeDimension_respectsIso.cancel_left_isIso _ _).2 H
  have hc : ρ ≫ X.presheaf.germ W x hxW = CommRingCat.ofHom σ := by
    apply Spec.map_injective
    rw [← hσ, ← hW.fromSpecStalk_eq_fromSpecStalk hxW, Spec.map_comp, Spec.map_comp, IsAffineOpen.fromSpecStalk,
      Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec f hU hW e, IsAffineOpen.fromSpec_top,
      Scheme.isoSpec_Spec_inv]
  letI : Algebra Γ(X, W) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hxW⟩
  have hl : IsLocalization.AtPrime (X.presheaf.stalk x) (hW.primeIdealOf ⟨x, hxW⟩).asIdeal :=
    hW.isLocalization_stalk ⟨x, hxW⟩
  haveI := hW.primeIdealOf_isMaximal_of_isClosed ⟨x, hxW⟩ hx
  have hs : (algebraMap Γ(X, W) (X.presheaf.stalk x)).comp ρ.hom = σ := congrArg (fun q => q.hom) hc
  have key := localization_of_isStandardSmooth_ideal (A := X.presheaf.stalk x) (IsLocalRing.maximalIdeal V) hρ
    (hW.primeIdealOf ⟨x, hxW⟩).asIdeal (by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      by_contra hm
      have hu := IsLocalization.map_units (X.presheaf.stalk x)
        (⟨_, hm⟩ : (hW.primeIdealOf ⟨x, hxW⟩).asIdeal.primeCompl)
      have hu' : IsUnit (σ a) := hs ▸ hu
      exact ha (hn.map_nonunit a hu'))
  rw [hs] at key
  exact key

end GlobalTheory.StabFlat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SubmoduleEqTopOfSupSmulOfIsNilpotent
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLaw

theorem submodule_eq_top_of_sup_smul_of_isNilpotent {A B : Type} [CommRing A] [AddCommGroup B] [Module A B]
    {J : Ideal A} (hJ : IsNilpotent J) {N : Submodule A B} (h : ⊤ ≤ N ⊔ J • ⊤) : N = ⊤ := by
  have key : ∀ n : ℕ, ⊤ ≤ N ⊔ J ^ n • (⊤ : Submodule A B) := by
    intro n
    induction n with
    | zero => rw [pow_zero, one_smul]; exact le_sup_right
    | succ n ih =>
      refine ih.trans (sup_le le_sup_left ((Submodule.smul_mono le_rfl h).trans ?_))
      rw [Submodule.smul_sup, pow_succ, Submodule.mul_smul]
      exact sup_le_sup_right Submodule.smul_le_right _
  obtain ⟨n, hn⟩ := hJ
  have := key n
  rw [hn, Ideal.zero_eq_bot, Submodule.bot_smul, sup_bot_eq] at this
  exact top_unique this

theorem surjective_eval₂Hom_of_isPushout {A B C P : CommRingCat.{0}} {α : A ⟶ B} {β : A ⟶ C} {c' : B ⟶ P}
    {d' : C ⟶ P} (h : IsPushout α β c' d') (hβ : Function.Surjective β) (hJ : IsNilpotent (RingHom.ker β.hom))
    {σ : Type} (r : σ → B) (hr : Function.Surjective (MvPolynomial.eval₂Hom d'.hom fun j => c'.hom (r j))) :
    Function.Surjective (MvPolynomial.eval₂Hom α.hom r) := by
  letI : Algebra A B := α.hom.toAlgebra
  have hN : Subalgebra.toSubmodule (MvPolynomial.aeval (R := A) r).range = ⊤ := by
    refine submodule_eq_top_of_sup_smul_of_isNilpotent hJ fun b _ => ?_
    obtain ⟨p, hp⟩ := hr (c'.hom b)
    obtain ⟨q, rfl⟩ := MvPolynomial.map_surjective β.hom hβ p
    have e : c'.hom (MvPolynomial.eval₂Hom α.hom r q) = c'.hom b := by
      rw [← hp, MvPolynomial.eval₂Hom_map_hom, MvPolynomial.map_eval₂Hom]
      exact congrArg (fun c => MvPolynomial.eval₂Hom c _ q) (congrArg CommRingCat.Hom.hom h.w)
    have hk : b - MvPolynomial.eval₂Hom α.hom r q ∈ RingHom.ker c'.hom := by
      rw [RingHom.mem_ker, map_sub, e, sub_self]
    rw [PrimeSection.ker_eq_map_of_isPushout h hβ] at hk
    refine Submodule.mem_sup.2 ⟨MvPolynomial.eval₂Hom α.hom r q, ⟨q, rfl⟩, _, ?_, add_sub_cancel _ _⟩
    rw [Ideal.smul_top_eq_map]
    exact hk
  intro b
  exact (hN.ge (Submodule.mem_top : b ∈ ⊤) :)

theorem surjective_specMap_of_isNilpotent {R R₀ : Type} [CommRing R] [CommRing R₀] (g : R →+* R₀)
    (hg : Function.Surjective g) (hJ : IsNilpotent (RingHom.ker g)) :
    Surjective (Spec.map (CommRingCat.ofHom g)) := ⟨fun x => by
  obtain ⟨n, hn⟩ := hJ
  have hx : x ∈ PrimeSpectrum.zeroLocus (RingHom.ker g : Set R) := fun a ha =>
    x.isPrime.mem_of_pow_mem n (by
      have := Ideal.pow_mem_pow ha n
      rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at this
      rw [this]
      exact zero_mem _)
  rw [← range_comap_of_surjective _ g hg] at hx
  exact hx⟩

theorem veryAmpleBy_of_isNilpotent : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (g : R →+* R₀), Function.Surjective g → IsNilpotent (RingHom.ker g) → ∀ (X X₀ : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (f₀ : X₀ ⟶ Spec (CommRingCat.of R₀)) (j₀ : X₀ ⟶ X), IsPullback j₀ f₀ f (Spec.map (CommRingCat.ofHom g)) → ∀ (H : LB X) (H₀ : LB X₀) (w : LB.Iso H₀ (H.pull j₀)) (n : ℕ) (s : Fin (n + 1) → LB.Sec H) (s₀ : Fin (n + 1) → LB.Sec H₀), H.IsLB → H₀.IsLB → w.IsGen → (∀ j, (∀ z (k : (H).ι) (k' : (H₀).ι), (j₀) z ∈ (H).U k → z ∈ (H₀).U k' → gs (j₀) z _ ((s j).f k) = (Geo.Tor.gw (w) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s₀ j).f k'))) → VeryAmpleBy f₀ H₀ s₀ → VeryAmpleBy f H s := by
  intro R R₀ _ _ g hg hJ X X₀ f f₀ j₀ h H H₀ w n s s₀ hH hH₀ _ hs ⟨hcov, hva⟩
  have hsurj : Surjective j₀ :=
    MorphismProperty.of_isPullback h.flip (surjective_specMap_of_isNilpotent g hg hJ)
  have loc : ∀ i, nonzeroLocus (s₀ i) = j₀ ⁻¹ᵁ nonzeroLocus (s i) := fun i => by
    ext y
    refine (mem_nonzeroLocus _ y).trans (Iff.trans ⟨fun ⟨k, hk, u⟩ => ?_, fun ⟨j, hj, u⟩ => ?_⟩
      (mem_nonzeroLocus _ (j₀ y)).symm)
    · obtain ⟨j, hj⟩ := exists_chart hH (j₀ y)
      have e := hs i y j k hj hk
      rw [gs_stalkMap j₀ y _ hj] at e
      exact ⟨j, hj, (isUnit_map_iff (j₀.stalkMap y).hom _).1 ((congrArg IsUnit e).mpr ((Units.isUnit _).mul u))⟩
    · obtain ⟨k, hk⟩ := exists_chart hH₀ y
      have e := hs i y j k hj hk
      exact ⟨k, hk, isUnit_of_mul_isUnit_right
        ((congrArg IsUnit ((gs_stalkMap j₀ y _ hj _).symm.trans e)).mp (u.map _))⟩
  refine ⟨top_le_iff.1 fun x _ => ?_, fun i => ?_⟩
  · obtain ⟨y, rfl⟩ := j₀.surjective x
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hcov.ge (Set.mem_univ y))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, (loc i).le hi⟩
  obtain ⟨haff₀, r₀, hr₀, hs₀⟩ := hva i
  have haff : IsAffineOpen (nonzeroLocus (s i)) :=
    AffineThickening.isAffine_of_isPullback_of_isNilpotent (RingHom.ker g) hJ (CommRingCat.ofHom g) hg rfl
      ((isPullback_morphismRestrict j₀ (nonzeroLocus (s i))).paste_vert h) (loc i ▸ haff₀ :)
  have hr := fun j => ProjSpace.secRatio_spec (s i) (s j)
  refine ⟨haff, fun j => ProjSpace.secRatio (s i) (s j), hr, ?_⟩
  have e₀ : r₀ = fun j => (j₀.appLE _ _ (loc i).le).hom (ProjSpace.secRatio (s i) (s j)) := funext fun j => by
    refine (ProjSpace.eq_secRatio _ _ (hr₀ j)).trans (ProjSpace.eq_secRatio _ _ fun k => fn_ext fun y hy => ?_).symm
    obtain ⟨l, hl⟩ := exists_chart hH (j₀ y)
    have hm : j₀ y ∈ nonzeroLocus (s i) ⊓ H.U l := ⟨(loc i).le hy.1, hl⟩
    have e := congrArg (gs j₀ y _) (hr j l)
    rw [gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm] at e
    have e₁ := hs j y l k hl hy.2
    have e₂ := hs i y l k hl hy.2
    have e₃ := (Geo.Tor.gw w (𝟙 _) y l k).mul_right_inj.1
      (e₁.symm.trans (e.trans ((congrArg _ e₂).trans (mul_left_comm _ _ _))))
    exact (gs_res _ y _ hy _).trans (e₃.trans (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_res _ y _ hy _).trans ((gs_appLE j₀ _ _ _ (𝟙 _) y hy.1 _).trans (by rw [Category.id_comp])))
      (gs_res _ y _ hy _)))))
  subst e₀
  have po := (isIso_pushoutSection_iff h (US := ⊤) (UT := ⊤) (UX := nonzeroLocus (s i)) le_top le_top
    (UY := nonzeroLocus (s₀ i)) (by rw [loc]; simp)).1
    (isIso_pushoutSection_of_isAffineOpen h _ _ _ (isAffineOpen_top _) (isAffineOpen_top _) haff)
  have po' : IsPushout ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ (nonzeroLocus (s i)) le_top)
      (CommRingCat.ofHom g) (j₀.appLE _ _ (loc i).le)
      ((Scheme.ΓSpecIso (CommRingCat.of R₀)).inv ≫ f₀.appLE ⊤ (nonzeroLocus (s₀ i)) le_top) := by
    refine po.of_iso (Scheme.ΓSpecIso _) (Iso.refl _) (Scheme.ΓSpecIso _) (Iso.refl _)
      (by simp) ?_ (by simp) (by simp)
    rw [← Scheme.ΓSpecIso_naturality]
    congr 1
  exact surjective_eval₂Hom_of_isPushout po' hg hJ _ hs₀

end GlobalTheory.AbLaw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBalOfSubsingleton
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MatDeg

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

variable {R : Type} [CommRing R] [IsDomain R]

theorem c_add' (D : DegPre R) (a b : D.X) : D.c (a + b) = D.c a * D.c b := D.c_add a b

theorem c_zero' (D : DegPre R) : D.c 0 = 1 := by
  have h := c_add' D 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

theorem c_sum (D : DegPre R) {J : Type} (s : Finset J) (x : J → D.X) :
    D.c (∑ l ∈ s, x l) = ∏ l ∈ s, D.c (x l) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using c_zero' D
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, c_add', ih]

theorem comp_prod {S : Scheme.{0}} {T T' A : Over S} [GrpObj A] [IsCommMonObj A] (f : T' ⟶ T)
    {J : Type} (s : Finset J) (x : J → (T ⟶ A)) :
    f ≫ ∏ l ∈ s, x l = ∏ l ∈ s, f ≫ x l := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, MonObj.comp_mul, ih]

theorem act_add {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {O : Type} [Ring O]
    (ρ : RingAct A O) (a b : O) : ρ.act (a + b) = ρ.act a * ρ.act b := ρ.map_add a b

theorem act_zero {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {O : Type} [Ring O]
    (ρ : RingAct A O) : ρ.act 0 = 1 := by
  have h := act_add ρ 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

theorem tauBal_of_subsingleton (D : DegPre R) [Subsingleton D.X] (f g : D.P.A ⟶ D.P.A)
    (a b : D.X → D.X) : D.TauBal f g a b := by
  intro u hu h₀ y y'
  rw [Subsingleton.elim (a y) 0, Subsingleton.elim (b y') 0, Subsingleton.elim y 0,
    Subsingleton.elim y' 0]
  refine corr_of_val D.P.isLB fun z J hJ => ?_
  have e : D.pt2 0 0 = (toUnit (TK R)).left ≫ zero2 D.P.A := by
    rw [DegPre.pt2, c_zero', zero2, ← Over.comp_left, comp_lift]
    simp [Hom.one_def]
  have := val_corr hJ h₀ (toUnit (TK R)).left
  rw [val_pull hJ, val_one] at this
  rw [val_mul hJ, val_pull hJ, Category.id_comp, e, this, _root_.mul_one]

theorem exists_matrix_act : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (D D' : DegPre R) (pD : IsPowDeg D' D j), D.TauBimult → D'.TauBimult → ∀ (O : Type) [Ring O] [StarRing O] [Module O D.X] (ιD : D.OAct O), ∃ (_ : Module (Matrix (Fin j) (Fin j) O) D'.X) (ι' : D'.OAct (Matrix (Fin j) (Fin j) O)), (∀ (m : (Matrix (Fin j) (Fin j) O)) (x : D'.X) (i : Fin j), pD.xe (m • x) i = ∑ l, m i l • pD.xe x l) ∧ (∀ (m : (Matrix (Fin j) (Fin j) O)) (i : Fin j), ι'.onB.act m ≫ pD.pw.pr i = ∏ l, pD.pw.pr l ≫ ιD.onB.act (m i l)) := by
  intro hG R _ _ j D D' pD hB hB' O _ _ _ ιD
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.exists_matrix_order_action_on_power _ D.P D'.P j pD.pw pD.w pD.w_gen ⟨D'.P.L, D'.rig, D'.P.isLB, D'.rig_gen⟩ rfl
    ⟨D'.cub⟩ O ιD.onB
  letI : Module (Matrix (Fin j) (Fin j) O) (Fin j → D.X) := Matrix.Module.matrixModule
  letI mD : Module (Matrix (Fin j) (Fin j) O) D'.X := pD.xe.module _
  have hx : ∀ (m : Matrix (Fin j) (Fin j) O) (x : D'.X) (i : Fin j),
      pD.xe (m • x) i = ∑ l, m i l • pD.xe x l := fun m x i => by
    have : m • x = pD.xe.symm (m • pD.xe x) := rfl
    rw [this, AddEquiv.apply_symm_apply]; rfl
  have hc : ∀ (m : Matrix (Fin j) (Fin j) O) (x : D'.X), D'.c (m • x) = D'.c x ≫ ρ.act m := fun m x => by
    apply pD.pw.lim.hom_ext
    rintro ⟨i⟩
    show D'.c (m • x) ≫ pD.pw.pr i = (D'.c x ≫ ρ.act m) ≫ pD.pw.pr i
    rw [pD.c_pr, hx, c_sum, Category.assoc, hρ, comp_prod]
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [ιD.c_lin, ← Category.assoc, pD.c_pr]
  have hs : ∀ (i l : Fin j) (a : O) (y : D'.X),
      Matrix.single i l a • y = pD.xe.symm (Pi.single i (a • pD.xe y l)) := fun i l a y => by
    apply pD.xe.injective
    rw [AddEquiv.apply_symm_apply]
    funext s
    rw [hx, Finset.sum_eq_single l (fun b _ hb => by rw [Matrix.single_apply_of_col_ne _ _ hb.symm, zero_smul])
      (fun h => absurd (Finset.mem_univ _) h)]
    by_cases h : s = i
    · subst h; simp
    · rw [Matrix.single_apply_of_row_ne (Ne.symm h), zero_smul, Pi.single_eq_of_ne h]
  have hp : ∀ (i l : Fin j) (a : O) (s : Fin j), ρ.act (Matrix.single i l a) ≫ pD.pw.pr s =
      if s = i then pD.pw.pr l ≫ ιD.onB.act a else 1 := fun i l a s => by
    rw [hρ, Finset.prod_eq_single l (fun b _ hb => by
      rw [Matrix.single_apply_of_col_ne _ _ hb.symm, act_zero, MonObj.comp_one])
      (fun h => absurd (Finset.mem_univ _) h)]
    by_cases h : s = i
    · subst h; simp
    · rw [Matrix.single_apply_of_row_ne (Ne.symm h), act_zero, MonObj.comp_one, if_neg h]
  have hel : ∀ (i l : Fin j) (a : O), D'.TauBal (ρ.act (Matrix.single i l a)) (ρ.act (star (Matrix.single i l a)))
      (fun y => Matrix.single i l a • y) (fun y => star (Matrix.single i l a) • y) := fun i l a => by
    have e : star (Matrix.single i l a) = Matrix.single l i (star a) := by
      rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_single]
    haveI := ιD.onB.hom a
    haveI := ιD.onB.hom (star a)
    rw [e, funext (hs i l a), funext (hs l i (star a))]
    exact GlobalTheory.T.rosati_adjoint_balanced_power_lift hG R j D D' pD hB (ιD.onB.act a) (ιD.onB.act (star a)) (fun y => a • y) (fun y => star a • y)
      (ιD.c_lin a) (ιD.c_lin (star a)) (ιD.onB.rosati a) (ιD.tau_bal a) _ _ i l (hp i l a) (hp l i (star a))
  refine ⟨mD, ⟨ρ, hc, fun m => ?_⟩, hx, hρ⟩
  induction m using Matrix.induction_on' with
  | h_zero =>
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · haveI : Subsingleton D'.X := pD.xe.toEquiv.subsingleton
      exact tauBal_of_subsingleton D' _ _ _ _
    · have := hel ⟨0, hj⟩ ⟨0, hj⟩ 0
      rwa [Matrix.single_zero] at this
  | h_add p q hp hq =>
    haveI := ρ.hom p
    haveI := ρ.hom q
    haveI := ρ.hom (star p)
    haveI := ρ.hom (star q)
    have := GlobalTheory.TauBalAdd.tauBal_add hG R D' hB' _ _ _ _ _ _ _ _ (hc p) (hc (star p)) (hc q) (hc (star q))
      (ρ.rosati p) (ρ.rosati q) hp hq
    rw [star_add, act_add, act_add, funext (add_smul p q), funext (add_smul (star p) (star q))]
    exact this
  | h_std_basis i l a => exact hel i l a

end GlobalTheory.MatDeg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorusCoordinatesCompatOfTorusCompat
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory
namespace CoordReduction

theorem exists_ratio {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ φ' : K → (Y ⟶ X)}
    {ε : K → ℤ} (hφ : ∀ k, φ k = φ' k) {u : LB.Gen (LB.LinComb L φ ε)} {u' : LB.Gen (LB.LinComb L φ' ε)}
    (hu : u.IsGen) (hu' : u'.IsGen) :
    ∃ ρ : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      val u r z J = gm r z ⊤ ρ * val u' r z J := by
  obtain ⟨t, -, hv⟩ := exists_gen hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, hφ, mul_inv_cancel])
    (LB.mulGen L _ _ _ _ u (LB.invGen L _ _ u')) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ hu'))
  have le : (⊤ : Y.Opens) ≤ LB.wchart L (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨res le (t.s PEmpty.elim), fun Z r z J hJ => ?_⟩
  have h := hv Z r z J hJ
  rw [val_mul hJ, val_inv, val_of t r z J PEmpty.elim (fun k => k.elim)] at h
  exact mul_inv_eq_iff_eq_mul.1 ((gm_res r z le trivial _).trans h).symm

theorem gm_char_comp {S S' Z : Scheme.{0}} {X : Type} [AddCommGroup X]
    (β : (splitTorus S' X).left ⟶ (splitTorus S X).left) (χ : X)
    (h : β.appTop.hom (charUnit S X χ).val = (charUnit S' X χ).val) (τ : Z ⟶ (splitTorus S' X).left) (z : Z) :
    gm (τ ≫ β) z ⊤ (charUnit S X χ) = gm τ z ⊤ (charUnit S' X χ) :=
  (gm_pull τ β z ⊤ trivial _).symm.trans (congrArg (gm τ z ⊤) (Units.ext h))

section Abstract

variable {X S S' : Scheme.{0}} {L : LB X} {H : Over S} {H' : Over S'} [GrpObj H] [GrpObj H'] {f : S' ⟶ S}
  {F : H'.left ⟶ H.left} (hp : IsGrpPullback H' H f F) {K : Type} [Fintype K] {φ : K → (H.left ⟶ X)} {ε : K → ℤ}
  (t : LB.Gen (LB.LinComb L φ ε))
include hp

theorem val_unit_pull
    (h : ∀ (Z : Over S) (z : Z.left) (J), Good L z J → val t (1 : Z ⟶ H).left z J = 1)
    {Z : Over S'} {z : Z.left} {J} (hJ : Good L z J) : val t ((1 : Z ⟶ H').left ≫ F) z J = 1 := by
  have e := hp.2 Z 1 1 (pushPt hp.1.w 1) (pushPt hp.1.w 1) rfl rfl
  rw [_root_.mul_one] at e
  have h1 : pushPt hp.1.w (1 : Z ⟶ H') = 1 :=
    left_eq_mul.1 (Over.OverMorphism.ext (f := pushPt hp.1.w 1) e.symm)
  have h2 := h (Over.mk (Z.hom ≫ f)) z J hJ
  rw [← h1] at h2
  exact h2

theorem val_torus_pull {M : Type} [AddCommGroup M] {i : splitTorus S M ⟶ H} {i' : splitTorus S' M ⟶ H'}
    (hi : TorusCompat f F i' i) (χ : M)
    (h : ∀ (Z : Over S) (z : Z.left) (J), Good L z J → ∀ (τ : Z ⟶ splitTorus S M) (a : Z ⟶ H),
      val t ((τ ≫ i) * a).left z J = gm τ.left z ⊤ (charUnit S M χ) * val t a.left z J)
    {Z : Over S'} {z : Z.left} {J} (hJ : Good L z J) (τ : Z ⟶ splitTorus S' M) (a : Z ⟶ H') :
    val t (((τ ≫ i') * a).left ≫ F) z J = gm τ.left z ⊤ (charUnit S' M χ) * val t (a.left ≫ F) z J := by
  obtain ⟨β, hβ, hχ, hβi⟩ := hi
  have e := hp.2 Z (τ ≫ i') a (pushPt hβ τ ≫ i) (pushPt hp.1.w a)
    ((Category.assoc _ _ _).trans ((congrArg (τ.left ≫ ·) hβi).trans (Category.assoc _ _ _).symm)) rfl
  have h2 := h (Over.mk (Z.hom ≫ f)) z J hJ (pushPt hβ τ) (pushPt hp.1.w a)
  exact (congrArg (fun r => val t r z J) e).symm.trans
    (h2.trans (congrArg₂ (· * ·) (gm_char_comp β χ (hχ χ) τ.left z) rfl))

end Abstract

theorem isGrpPullback_trans {R : Type} [CommRing R] (I : Ideal R) (e : ℕ) (G : Over (Spec (CommRingCat.of R)))
    [GrpObj G] :
    IsGrpPullback (thickObj R I e G) (thickObj R I (e + 1) G) (thickTrans R I e) (thickMap R I e G) :=
  (isGrpPullback_pullback G (thick R I (e + 1))).cancel
    ((isGrpPullback_pullback G (thick R I e)).congr (thickTrans_comp R I e).symm
      ((pullback.lift_fst _ _ _).trans (Category.comp_id _)).symm) (pullback.lift_snd _ _ _)

end CoordReduction

open CoordReduction in

theorem gtCoord_compat_of_torusCompat : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (g' : GtCoord I D (e + 1) G), thickMap R I e G ≫ g'.pG.left = g.pG.left → TorusCompat (thickTrans R I e) (thickMap R I e G) g.i g'.i → ∀ χ, LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (g'.t χ) (thickMap R I e G)) (g.t χ) := by
  intro hG R _ _ I D e G _ _ g g' hq hi χ
  obtain ⟨ρ, hρ⟩ := exists_ratio D.P.isLB (LevelCompat.thickMap_Oφ g g' hq χ)
    (DVR.pullGen_isGen _ _ _ _ (g'.t_gen χ) (thickMap R I e G)) (g.t_gen χ)
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J), Good D.P.L z J →
      val (g'.t χ) (r ≫ thickMap R I e G) z J = gm r z ⊤ ρ * val (g.t χ) r z J := fun Z r z J hJ =>
    (val_pull hJ _ _ _).symm.trans (hρ Z r z J hJ)
  have := g.q_flat
  have := g.q_surj
  have := g.q_affine
  have h1 : ρ.val = 1 := by
    refine eq_one_of_fibre_const_of_section hG _ _ _ (TLinPf.isAb_pullback _ _ D.P.isAb) g.q _
      (1 : 𝟙_ _ ⟶ thickObj R I e G) (fun Z a b hab => ?_) ?_
    · obtain ⟨τ, hτ⟩ := TorusCoord.exists_torus g a b hab
      refine TorusCoord.appTop_eq_of_gm _ _ ρ fun z => ?_
      obtain ⟨J, hJ⟩ := exists_good_pt D.P.isLB z
      have k := key _ a.left z J hJ
      have t₁ := val_torus_pull (isGrpPullback_trans I e G) (g'.t χ) hi χ
        (fun _ _ _ hJ τ a => TorusCoord.val_torus g' χ hJ τ a) hJ τ b
      have t₂ := TorusCoord.val_torus g χ hJ τ b
      rw [← hτ] at t₁ t₂
      rw [t₁, t₂, key _ b.left z J hJ, mul_left_comm, ← _root_.mul_assoc, ← _root_.mul_assoc] at k
      exact (mul_right_cancel (mul_right_cancel k)).symm
    · have h : Units.map (1 : 𝟙_ _ ⟶ thickObj R I e G).left.appTop.hom.toMonoidHom ρ = 1 := by
        refine unit_ext fun z _ => ?_
        obtain ⟨J, hJ⟩ := exists_good_pt D.P.isLB z
        have k := key _ (1 : 𝟙_ _ ⟶ thickObj R I e G).left z J hJ
        rw [val_unit_pull (isGrpPullback_trans I e G) (g'.t χ) (fun _ _ _ hJ => TorusCoord.val_unit g' χ hJ) hJ,
          TorusCoord.val_unit g χ hJ, _root_.mul_one] at k
        exact (gm_top _ z ρ).symm.trans (k.symm.trans (map_one _).symm)
      exact congrArg Units.val h
  have h2 : ρ = 1 := Units.ext h1
  refine corr_of_val D.P.isLB fun y J hJ => ?_
  rw [hρ _ _ y J hJ, h2, map_one, _root_.one_mul]

end GlobalTheory
end
end

