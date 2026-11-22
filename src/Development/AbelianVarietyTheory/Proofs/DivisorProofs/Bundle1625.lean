import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1593
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0957
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1595
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1598
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0951
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0260
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0153
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0981
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1587
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1594
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0858
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1596
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0724
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1597
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1583
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0102

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqFinsetSumPureTensorCosetIndicatorStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_finset_sum_pureTensor_coset_indicator : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (U : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F))
    (K : Set (κ → FiniteAdeleRing (𝓞 F) F)), IsOpen (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) → IsCompact (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) → IsCompact K →
      ∃ R : Finset (κ → FiniteAdeleRing (𝓞 F) F),
        (∀ r ∈ R, Set.indicator {y | y - r ∈ U} (fun _ => (1 : ℂ)) ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) ∧
        ∀ Φ : (κ → AdeleRing (𝓞 F) F) → ℂ, (∀ x, ∀ u ∈ U, Φ (x + GlobalTheory.WeilAdm.finE F u) = Φ x) →
          (∀ x, (fun i => (x i).2) ∉ K → Φ x = 0) →
            Φ = ∑ r ∈ R, GlobalTheory.WeilM.pureA F (GlobalTheory.WeilAdm.slice F Φ r) (Set.indicator {y | y - r ∈ U} fun _ => (1 : ℂ)) := by
  first | exact @GlobalTheory.WeilAdm.eq_sum_pureA_coset_indicator | exact GlobalTheory.WeilAdm.eq_sum_pureA_coset_indicator | (intros; apply GlobalTheory.WeilAdm.eq_sum_pureA_coset_indicator <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOneOfFiniteOrderOfTrivialModSqTateModuleStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_one_of_finite_order_of_trivial_mod_sq_tateModule : ∀ (l : ℕ) [Fact l.Prime] (M : Type) [CommGroup M] (u : Module.End ℤ_[l] (Tate l M)) (E : ℕ), 0 < E → u ^ E = 1 → (∀ t, (u t).lev 2 = t.lev 2) → u = 1 := by
  first | exact @GlobalTheory.HTLat.Tate.eq_one_of_pow_eq_one_of_lev_two | exact GlobalTheory.HTLat.Tate.eq_one_of_pow_eq_one_of_lev_two | (intros; apply GlobalTheory.HTLat.Tate.eq_one_of_pow_eq_one_of_lev_two <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfDifferentialKernelZeroGerms
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section
namespace GlobalTheory.KerGermInj

open GlobalTheory.AbLaw

theorem gs_id {P : Scheme.{0}} (O : P.Opens) (y : P) (hy : y ∈ O) (a : Γ(P, O)) :
    gs (𝟙 P) y O a = (P.presheaf.germ O y hy).hom a := by
  rw [gs_eq _ y O hy]; rfl

theorem gs_comp {Y Z X : Scheme.{0}} (f : Z ⟶ Y) (h : Y ⟶ X) (z : Z) (U : X.Opens) (hU : h (f z) ∈ U)
    (a : Γ(X, U)) : gs (f ≫ h) z U a = (f.stalkMap z).hom (gs h (f z) U a) := by
  rw [← gs_pull f h z U hU, gs_eq f z (h ⁻¹ᵁ U) hU, gs_eq h (f z) U hU]
  exact (Scheme.Hom.germ_stalkMap_apply f (h ⁻¹ᵁ U) z hU _).symm

theorem fromSpecStalk_comp {R : Type} [CommRing R] {T : Scheme.{0}} (t : T ⟶ Sp R) (x : T) :
    T.fromSpecStalk x ≫ t =
      Spec.map (CommRingCat.ofHom ((T.presheaf.germ ⊤ x trivial).hom.comp (GlobalTheory.FormsLocus.cstT t))) := by
  apply ext_of_isAffine
  rw [← cancel_mono (Scheme.ΓSpecIso _).hom, Scheme.ΓSpecIso_naturality, Scheme.Hom.comp_appTop,
    Scheme.fromSpecStalk_appTop]
  ext r
  simp [GlobalTheory.FormsLocus.cstT]

theorem eq_zero : ∀ (R : Type) [CommRing R] (X T X' : Scheme.{0}) (f : X ⟶ Sp R) (M : LB X) (Q : GlobalTheory.AbLaw.Perf f M) (t : T ⟶ Sp R) (φ : X' ⟶ X) (p : X' ⟶ T), IsPullback φ p f t → ∀ e : Fin Q.a → Γ(T, ⊤), (Q.D₀.map (GlobalTheory.FormsLocus.cstT t)).mulVec e = 0 → (∀ (z : X') (i : Q.I), φ z ∈ Q.W i → ∑ k, gs p z ⊤ (e k) * gs φ z (Q.W i) (Q.u k i) = 0) → e = 0 := by
  intro R _ X T X' f M Q t φ p hpb e he hz
  funext k
  apply TopCat.Presheaf.section_ext T.sheaf ⊤
  intro x hx
  change (T.presheaf.germ ⊤ x hx).hom (e k) = (T.presheaf.germ ⊤ x hx).hom 0
  rw [map_zero]
  let ψ : Γ(T, ⊤) →+* T.presheaf.stalk x := (T.presheaf.germ ⊤ x hx).hom
  let ρ : R →+* T.presheaf.stalk x := ψ.comp (GlobalTheory.FormsLocus.cstT t)
  let g := T.fromSpecStalk x
  let fst := pullback.fst p g
  let snd := pullback.snd p g
  let π := fst ≫ φ
  have hsq : IsPullback π snd f (Spec.map (CommRingCat.ofHom ρ)) := by
    have hg : g ≫ t = Spec.map (CommRingCat.ofHom ρ) := fromSpecStalk_comp t x
    have h3 := (IsPullback.of_hasPullback p g).paste_horiz hpb
    rw [hg] at h3
    exact h3
  obtain ⟨E, hE⟩ := Q.sec _ ρ _ π snd hsq
  have hv : (Q.D₀.map ρ).mulVec (fun k => ψ (e k)) = 0 := by
    funext j
    have h1 := RingHom.map_mulVec ψ (Q.D₀.map (GlobalTheory.FormsLocus.cstT t)) e j
    rw [he, Pi.zero_apply, map_zero, Matrix.map_map] at h1
    exact h1.symm
  have hloc : ∀ w : {v : Fin Q.a → T.presheaf.stalk x // (Q.D₀.map ρ).mulVec v = 0},
      (∀ i, ∑ k, cst snd (π ⁻¹ᵁ Q.W i) (w.1 k) * (π.app (Q.W i)).hom (Q.u k i) = 0) → E w = 0 :=
by
    intro w hw
    have hcov : ⨆ i, π ⁻¹ᵁ Q.W i = ⊤ := Q.iSup_preimage (π := π)
    refine sec_eq_zero_of_local (L := M.pull π) (fun i => π ⁻¹ᵁ Q.W i) hcov
      (fun i => (fun _ => Q.ch i : (M.pull π).ι)) (fun i => le_pull M π (Q.le i)) (E w) ?_
    intro i
    exact (hE w i).trans (hw i)
  have h0 : E ⟨0, by rw [Matrix.mulVec_zero]⟩ = 0 :=
    hloc _ fun i => Finset.sum_eq_zero fun k _ => by
      have hc0 : cst snd (π ⁻¹ᵁ Q.W i) 0 = 0 := map_zero _
      exact (congrArg (· * _) hc0).trans (zero_mul _)
  have h1 : E ⟨fun k => ψ (e k), hv⟩ = 0 := by
    refine hloc _ fun i => ?_
    apply fn_ext
    intro y hy
    have hyi : φ (fst y) ∈ Q.W i := hy
    rw [gs_id _ y hy, gs_id _ y hy, map_zero, map_sum]
    simp only [map_mul]
    have hu : ∀ k, ((pullback p g).presheaf.germ (π ⁻¹ᵁ Q.W i) y hy).hom ((π.app (Q.W i)).hom (Q.u k i)) =
        (fst.stalkMap y).hom (gs φ (fst y) (Q.W i) (Q.u k i)) := by
      intro k
      rw [← gs_id _ y hy, gs_pull (𝟙 _) π y (Q.W i) hyi, Category.id_comp]
      exact gs_comp fst φ y (Q.W i) hyi _
    have hc : ∀ k, ((pullback p g).presheaf.germ (π ⁻¹ᵁ Q.W i) y hy).hom (cst snd (π ⁻¹ᵁ Q.W i) (ψ (e k))) =
        (fst.stalkMap y).hom (gs p (fst y) ⊤ (e k)) := by
      intro k
      have hcond : fst ≫ p = snd ≫ g := pullback.condition
      have hA := congrArg (fun h => h.hom (e k)) (Scheme.fromSpecStalk_appTop (X := T) (x := x))
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hA
      rw [← gs_id _ y hy, ← gs_comp fst p y ⊤ trivial, hcond]
      refine Eq.trans ?_ (gs_pull snd g y ⊤ trivial (e k))
      refine Eq.trans ?_ (congrArg (gs snd y (g ⁻¹ᵁ ⊤)) hA.symm)
      refine Eq.trans ?_ (gs_res snd y _ (show snd y ∈ g ⁻¹ᵁ ⊤ from trivial) _).symm
      refine Eq.trans (gs_res (𝟙 _) y le_top hy _) ?_
      refine Eq.trans (gs_pull (𝟙 _) snd y ⊤ trivial _) ?_
      rw [Category.id_comp]
      rfl
    have hsum : ∀ k, ((pullback p g).presheaf.germ (π ⁻¹ᵁ Q.W i) y hy).hom (cst snd (π ⁻¹ᵁ Q.W i) (ψ (e k))) *
        ((pullback p g).presheaf.germ (π ⁻¹ᵁ Q.W i) y hy).hom ((π.app (Q.W i)).hom (Q.u k i)) =
        (fst.stalkMap y).hom (gs p (fst y) ⊤ (e k) * gs φ (fst y) (Q.W i) (Q.u k i)) := fun k => by
      rw [hc k, hu k, map_mul]
    simp only [hsum]
    rw [← map_sum, hz (fst y) i hyi, map_zero]
  have h2 := congrFun (congrArg Subtype.val (E.injective (h1.trans h0.symm))) k
  exact h2

end GlobalTheory.KerGermInj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqualizerSectionsClosedIdeal
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem sections_eqLocus_ideal : ∀ (R : Type) [CommRing R] (X : Over (Sp R)), IsSeparated X.hom →
    ∀ (x y : Sp R ⟶ X.left), x ≫ X.hom = 𝟙 _ → y ≫ X.hom = 𝟙 _ → ∃ I : Ideal R,
      ∀ (T : Type) [CommRing T] (ψ : R →+* T), (spMap ψ ≫ x = spMap ψ ≫ y ↔ ∀ r ∈ I, ψ r = 0) := by
  first
  | exact @_root_.GlobalTheory.IdealSectionsFactorization.exists_ideal_sections_eq
  | exact _root_.GlobalTheory.IdealSectionsFactorization.exists_ideal_sections_eq
  | (apply _root_.GlobalTheory.IdealSectionsFactorization.exists_ideal_sections_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.IdealSectionsFactorization.exists_ideal_sections_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IdealSectionsFactorization.exists_ideal_sections_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IdealSectionsFactorization.exists_ideal_sections_eq ..)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EulerCharLineBundleFibreModpEqRatProjective
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo
open GlobalTheory.LB (toMod)
open GlobalTheory.VB (degOfRank)

noncomputable section

namespace GlobalTheory.ChiFibre

open GlobalTheory.AbLaw GlobalTheory.Adelic GlobalTheory.FieldChangeInter

theorem alternating_sum_range_telescoping_identity (a r : ℕ → ℤ) (m : ℕ) :
    ∑ n ∈ Finset.range m, (-1 : ℤ) ^ n * (a n + a (n + 1) - r (n + 1)) =
      ∑ n ∈ Finset.range m, (-1 : ℤ) ^ n * r n + (a 0 - r 0) + (-1) ^ m * (r m - a m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, pow_succ]
    ring

theorem homology_subsingleton {R : Type} [Ring R] (K : CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ)
    (h : IsZero (K.X n)) : Subsingleton (K.homology n) :=
  ModuleCat.subsingleton_of_isZero (ShortComplex.isZero_homology_of_isZero_X₂ (K.sc n) h)

theorem finite_int_congr {M : Type*} [AddCommGroup M] {i₁ i₂ : Module ℤ M}
    (h : @Module.Finite ℤ M _ _ i₁) : @Module.Finite ℤ M _ _ i₂ := by
  obtain rfl : i₁ = i₂ := Subsingleton.elim _ _
  exact h

theorem altSum (C : CochainComplex (ModuleCat.{0} ℤ) ℕ) (p : ℕ) [Fact p.Prime]
    (hinj : ∀ (n : ℕ) (x : C.X n), (p : ℤ) • x = 0 → x = 0)
    (hfin : ∀ n, Module.Finite ℤ (C.homology n)) (m : ℕ) (hz : ∀ n, m ≤ n → IsZero (C.X n)) :
    ∑ᶠ n, (-1 : ℤ) ^ n * (Module.finrank (ZMod p) ((((ModuleCat.extendScalars
      (Int.castRingHom (ZMod p))).mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homology n) : ℤ) =
    ∑ᶠ n, (-1 : ℤ) ^ n * (Module.finrank ℚ ((((ModuleCat.extendScalars
      (Int.castRingHom ℚ)).mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homology n) : ℤ) := by
  set a : ℕ → ℤ := fun n => Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) (C.homology n))
  set r : ℕ → ℤ := fun n => Module.finrank ℤ (C.homology n)
  have hsub : ∀ n, m ≤ n → Subsingleton (C.homology n) :=
    fun n hn => homology_subsingleton C n (hz n hn)
  have hr0 : ∀ n, m ≤ n → r n = 0 := fun n hn => by
    haveI := hsub n hn
    simp only [r]
    rw [Module.finrank_zero_of_subsingleton]
    rfl
  have ha0 : ∀ n, m ≤ n → a n = 0 := fun n hn => by
    haveI := hsub n hn
    have : Subsingleton (TensorProduct ℤ (ZMod p) (C.homology n)) := inferInstance
    simp only [a]
    rw [Module.finrank_zero_of_subsingleton]
    rfl
  have hext : ∀ (F : Type) [Field F] (g : ℤ →+* F) (n : ℕ), m ≤ n →
      Module.finrank F ((((ModuleCat.extendScalars g).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj C).homology n) = 0 := by
    intro F _ g n hn
    have hZ : IsZero ((((ModuleCat.extendScalars g).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj C).X n) :=
      (ModuleCat.extendScalars g).map_isZero (hz n hn)
    haveI := homology_subsingleton _ n hZ
    exact Module.finrank_zero_of_subsingleton
  have hsupp : ∀ (F : Type) [Field F] (g : ℤ →+* F),
      (Function.support fun n => (-1 : ℤ) ^ n * (Module.finrank F ((((ModuleCat.extendScalars
        g).mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homology n) : ℤ)) ⊆
        ↑(Finset.range m) := by
    intro F _ g n hn
    by_contra h
    simp only [Finset.coe_range, Set.mem_Iio, not_lt] at h
    exact hn (by simp [hext F g n h])
  rw [finsum_eq_sum_of_support_subset _ (hsupp (ZMod p) _),
    finsum_eq_sum_of_support_subset _ (hsupp ℚ _)]
  have h1 : ∀ n ∈ Finset.range m, (-1 : ℤ) ^ n * (Module.finrank (ZMod p) ((((ModuleCat.extendScalars
      (Int.castRingHom (ZMod p))).mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homology n) : ℤ) =
      (-1 : ℤ) ^ n * (a n + a (n + 1) - r (n + 1)) := fun n _ => by
    rw [GlobalTheory.T.finrank_homology_mod_prime_universal_coefficients C p hinj hfin n]
  have h2 : ∀ n ∈ Finset.range m, (-1 : ℤ) ^ n * (Module.finrank ℚ ((((ModuleCat.extendScalars
      (Int.castRingHom ℚ)).mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homology n) : ℤ) =
      (-1 : ℤ) ^ n * r n := fun n _ => by
    rw [GlobalTheory.T.finrank_rat_homology_eq_finrank_int C n (hfin n)]
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, alternating_sum_range_telescoping_identity]
  have h0 : a 0 = r 0 := by
    simp only [a, r]
    exact_mod_cast GlobalTheory.T.finrank_zmod_tensor_homology_zero_of_noPTorsion C p (hinj 0) (hfin 0)
  rw [h0, hr0 m le_rfl, ha0 m le_rfl]
  ring

theorem hdim_fibre {X X' : Scheme.{0}} {F : Type} [Field F] (g : ℤ →+* F) (f : X ⟶ Sp ℤ)
    (f' : X' ⟶ Sp F) (π : X' ⟶ X) (H : IsPullback π f' f (spMap g)) {κ : Type} [LinearOrder κ]
    [Finite κ] (D : κ → X.Opens) (hc : ⨆ i, D i = ⊤)
    (hD : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (⨅ i ∈ s, D i)) (M : LB X) (hM : M.IsLB)
    (n : ℕ) :
    (letI := GlobalTheory.algebraΓOfHom f'; hdim F (toMod (M.pull π)) n) =
      Module.finrank F ((((ModuleCat.extendScalars g).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (cechLB f M D)).homology n) := by
  letI := GlobalTheory.algebraΓOfHom f'
  have hM' := LB.isLB_pull hM π
  haveI := LB.isQuasicoherent_toMod hM'
  have hc' : ⨆ i, π ⁻¹ᵁ D i = ⊤ := by rw [← Scheme.Hom.preimage_iSup, hc]; rfl
  have hD' : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (⨅ i ∈ s, π ⁻¹ᵁ D i) :=
    fun s hs => isAffineOpen_biInf_preimage H (hD s hs)
  have e₁ := ((HomologicalComplex.homologyFunctor _ _ n).mapIso
    (cechIso f' (M.pull π) (fun i => π ⁻¹ᵁ D i))).toLinearEquiv ≪≫ₗ
    cechHEquivCoh F hc' hD' (toMod (M.pull π)) n
  have e₄ := ((HomologicalComplex.homologyFunctor _ _ n).mapIso
    (cechLBBaseChangeIso hM H hD)).toLinearEquiv
  rw [hdim_def, ← e₁.finrank_eq, ← e₄.finrank_eq]
  rfl

theorem chi_fibres_LB {X Xp Xq : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] (hX : CharZero Γ(X, ⊤))
    (f : X ⟶ Sp ℤ) (p : ℕ) [Fact p.Prime]
    (fp : Xp ⟶ Sp (ZMod p)) (πp : Xp ⟶ X) (Hp : IsPullback πp fp f (spMap (Int.castRingHom (ZMod p))))
    (fq : Xq ⟶ Sp ℚ) (πq : Xq ⟶ X) (Hq : IsPullback πq fq f (spMap (Int.castRingHom ℚ)))
    (M : LB X) (hM : M.IsLB)
    (hfin : ∀ n, letI := GlobalTheory.algebraΓOfHom f; Module.Finite ℤ (coh (twist (structureModule X) M) n)) :
    (letI := GlobalTheory.algebraΓOfHom fp; chi (ZMod p) (toMod (M.pull πp))) =
      (letI := GlobalTheory.algebraΓOfHom fq; chi ℚ (toMod (M.pull πq))) := by
  obtain ⟨m, Dc, hD, hc⟩ := exists_fin_affine_cover (X := X) (V := ⊤) isCompact_univ
  have hD' := isAffineOpen_finset_biInf hD
  have hinj : ∀ (n : ℕ) (x : (cechLB f M Dc).X n), (p : ℤ) • x = 0 → x = 0 :=
    fun n x => GlobalTheory.T.cechComplexLineBundle_term_torsionFree_charZero hX f M Dc n (p : ℤ) (by exact_mod_cast (Fact.out : p.Prime).ne_zero) x
  have hz : ∀ n, m ≤ n → IsZero ((cechLB f M Dc).X n) :=
    fun n hn => isZero_cechLB_X f M Dc (by simpa using hn)
  have hfin' : ∀ n, Module.Finite ℤ ((cechLB f M Dc).homology n) := by
    intro n
    letI := GlobalTheory.algebraΓOfHom f
    obtain ⟨e⟩ := nonempty_coh_equiv f hM hc hD' n
    letI : Module ℤ (coh (twist (structureModule X) M) n) := cohOn.instModule ℤ _ ⊤ n
    haveI hf1 : Module.Finite ℤ (coh (twist (structureModule X) M) n) := finite_int_congr (hfin n)
    exact finite_int_congr (Module.Finite.equiv e.symm)
  letI := GlobalTheory.algebraΓOfHom fp
  letI := GlobalTheory.algebraΓOfHom fq
  rw [chi_def, chi_def]
  have hp := fun n => hdim_fibre (Int.castRingHom (ZMod p)) f fp πp Hp Dc hc hD' M hM n
  have hq := fun n => hdim_fibre (Int.castRingHom ℚ) f fq πq Hq Dc hc hD' M hM n
  simp only [hp, hq]
  exact altSum (cechLB f M Dc) p hinj hfin' m hz

theorem chi_structureModule_eq {X X' : Scheme.{0}} (F : Type) [Field F] [Algebra F Γ(X', ⊤)]
    (π : X' ⟶ X) : chi F (structureModule X') = chi F (toMod ((LB.triv X).pull π)) := by
  have h₀ := LB.isLB_triv X
  have h₁ := Semi.LB.isLB_pull h₀ π
  obtain ⟨e'⟩ := nonempty_twist_iso_of_cls_eq_zero (structureModule X') h₁
    ((CechPic.cls_pull h₀ π h₁).trans (map_zero _))
  rw [← chi_congr F e', chi_congr F (Twist.unitTwistIso _)]

theorem chi_fibre_eq : ∀ (k : Type) [CommRing k] (W : Scheme.{0}) (q : W ⟶ Sp k) (D : ℕ), IsArithVar q D → ∀ (p : ℕ) [Fact p.Prime] (N : LB W), N.IsLB → (letI := GlobalTheory.algebraΓOfHom (pullback.snd (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p)))); chi (ZMod p) (toMod (N.pull (pullback.fst (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p)))))) = chi ℚ (toMod (N.pull (ratFibre.fst q))) ∧ chi (ZMod p) (structureModule (pullback (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p))))) = chi ℚ (structureModule (ratFibre q))) := by
  intro k _ W q D hq p _ N hN
  haveI := hq.isDomain
  haveI := hq.finite
  haveI := hq.isIntegral
  haveI : IsNoetherianRing k := isNoetherian_of_tower ℤ inferInstance
  have hproj := hq.isProjOver
  haveI : IsProper q := (isProper_and_exists_isAmpleLB_of_isProjOver hproj).1
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace q
  haveI := isAffineHom_diagonal_of_isSeparated q
  have hX : CharZero Γ(W, ⊤) := (flat_int_iff_charZero _).1 hq.flat
  have hfin : ∀ M : LB W, M.IsLB → ∀ n,
      letI := GlobalTheory.algebraΓOfHom (q ≫ spMap (Int.castRingHom k))
      Module.Finite ℤ (coh (twist (structureModule W) M) n) := by
    intro M hM n
    letI := GlobalTheory.algebraΓOfHom q
    have h1 : Module.Finite k (coh (twist (structureModule W) M) n) :=
      (((serre_finiteness_vanishing k W (structureModule W)).2 q (fun _ => rfl)).2
        (Or.inl hproj)).2.1 M hM n
    have h2 : Module.Finite ℤ (coh (twist (structureModule W) M) n) := Module.Finite.trans k _
    exact finite_int_congr h2
  refine ⟨chi_fibres_LB hX _ p _ _ (IsPullback.of_hasPullback _ _) _ _ (ratFibre.isPullback q) N hN
    (hfin N hN), ?_⟩
  letI := GlobalTheory.algebraΓOfHom (pullback.snd (q ≫ spMap (Int.castRingHom k))
    (spMap (Int.castRingHom (ZMod p))))
  rw [chi_structureModule_eq (ZMod p) (pullback.fst _ _), chi_structureModule_eq ℚ (ratFibre.fst q)]
  exact chi_fibres_LB hX _ p _ _ (IsPullback.of_hasPullback _ _) _ _ (ratFibre.isPullback q) _
    (LB.isLB_triv W) (hfin _ (LB.isLB_triv W))

end GlobalTheory.ChiFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineEtaleCoordinatesGenericPointStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Points
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_etale_coordinates_generic_point : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}, IsArithVar p D → ∃ U : X.Opens, IsAffineOpen U ∧ genericPoint X ∈ U ∧ ∃ t : Fin D → Γ(X, U), (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U) t).Etale := by
  first | exact @GlobalTheory.GenericCoords.exists_affine_etale_coords | exact GlobalTheory.GenericCoords.exists_affine_etale_coords | (intros; apply GlobalTheory.GenericCoords.exists_affine_etale_coords <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenGeometricallyConnectedFibresOfGenStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basicOpen_geometricallyConnected_fibres_of_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G], Smooth G.hom → QuasiCompact G.hom → ∀ (K : Type) [Field K] (e : R →+* K), Function.Injective e → GeometricallyConnected (pullback.snd G.hom (spMap e)) → ∃ f : R, e f ≠ 0 ∧ ∀ (F : Type) [Field F] (ψ : R →+* F), IsUnit (ψ f) → GeometricallyConnected (pullback.snd G.hom (spMap ψ)) := by
  first | exact @GlobalTheory.SpreadConn.geometricallyConnected_of_generic | exact GlobalTheory.SpreadConn.geometricallyConnected_of_generic | (intros; apply GlobalTheory.SpreadConn.geometricallyConnected_of_generic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenSmoothOfRelativeDimensionOfGeneriStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basicOpen_smoothOfRelativeDimension_of_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (X : Over (Sp R)), Smooth X.hom → QuasiCompact X.hom → ∀ (K : Type) [Field K] (e : R →+* K), Function.Injective e → ∀ g : ℕ, SmoothOfRelativeDimension g (pullback.snd X.hom (spMap e)) → ∃ f : R, e f ≠ 0 ∧ ∀ (F : Type) [Field F] (ψ : R →+* F), IsUnit (ψ f) → SmoothOfRelativeDimension g (pullback.snd X.hom (spMap ψ)) := by
  first | exact @GlobalTheory.SmoothRelDim.exists_basicOpen | exact GlobalTheory.SmoothRelDim.exists_basicOpen | (intros; apply GlobalTheory.SmoothRelDim.exists_basicOpen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisLineBundleSectionsProjectiveOverDvrStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basis_lineBundleSections_projective_over_dvr : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of W)) (M : LB X), Flat f → GlobalTheory.AbLaw.IsProjBy f → M.IsLB → ∃ (n : ℕ) (t : Fin n → LB.Sec M), ∀ u : LB.Sec M, ∃! c : Fin n → W, u = ∑ j, GlobalTheory.AbLaw.cst f ⊤ (c j) • t j := by
  first | exact @GlobalTheory.AbLaw.exists_basis_sec_of_isDiscreteValuationRing | exact GlobalTheory.AbLaw.exists_basis_sec_of_isDiscreteValuationRing | (intros; apply GlobalTheory.AbLaw.exists_basis_sec_of_isDiscreteValuationRing <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmEllipticCurveGaloisTorsionSectionsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PureLift
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cmEllipticCurve_galois_torsion_sections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (n : ℕ), 0 < n → ∃ (N : IntermediateField ℚ ℂ) (_ : NumberField N) (_ : IsGalois ℚ N) (ω : 𝓞 N) (C : GlobalTheory.CM.Ell H (𝓞 N) ω) (C₀ : GlobalTheory.CompRat.Curve H) (ψ : C₀.P.A.left ⟶ C.P.A.left), (2 * ω - 1) ^ 2 = -(H.d : 𝓞 N) ∧ IsGrpPullback C₀.P.A C.P.A (spMap ((algebraMap N ℂ).comp (algebraMap (𝓞 N) N))) ψ ∧ ∀ a : ℤ × ℤ, ∃ y : Over.mk (𝟙 (Sp (𝓞 N))) ⟶ C.P.A, y ^ n = 1 ∧ C₀.pt (GlobalTheory.CompRat.wC H a / n) ≫ ψ = spMap ((algebraMap N ℂ).comp (algebraMap (𝓞 N) N)) ≫ y.left := by
  first | exact @GlobalTheory.TorsionModel.exists_ell_torsion_sections | exact GlobalTheory.TorsionModel.exists_ell_torsion_sections | (intros; apply GlobalTheory.TorsionModel.exists_ell_torsion_sections <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousCosSqAngleFunctionStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_cosSq_angle_function : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (V L L' : X.Modules) (r : ℕ) (h : Met p σ V r) (l : L ⟶ V) (l' : L' ⟶ V), h.IsCInf → IsSubbundle l → IsSubbundle l' → IsVB L 1 → IsVB L' 1 → ∃ v : CxPts p σ → ℝ, IsCosSq h l l' v ∧ Continuous v ∧ ∀ y, 0 ≤ v y ∧ v y ≤ 1 := by
  first | exact @GlobalTheory.CurveDens.exists_isCosSq | exact GlobalTheory.CurveDens.exists_isCosSq | (intros; apply GlobalTheory.CurveDens.exists_isCosSq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDominantOpenNatCastIsUnitNonZeroDivisor
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_schemeTheoreticallyDominant_isUnit_natCast (T : Scheme.{0}) (c : ℕ)
    (hc : ∀ (U : T.Opens) (f : Γ(T, U)), (c : Γ(T, U)) * f = 0 → f = 0) :
    ∃ (U : Scheme.{0}) (j : U ⟶ T), IsSchemeTheoreticallyDominant j ∧ IsUnit (c : Γ(U, ⊤)) := by
  refine ⟨(T.basicOpen (c : Γ(T, ⊤))).toScheme, (T.basicOpen (c : Γ(T, ⊤))).ι, ?_, ?_⟩
  · refine isSchemeTheoreticallyDominant_ι_of_germ_eq_zero_over_affine T T (𝟙 T) _ ?_
    intro U V hU _ _ b hb
    have key : ∀ (n : ℕ) (b : Γ(T, U)), (c : Γ(T, U)) ^ n * b = 0 → b = 0 := by
      intro n
      induction n with
      | zero => intro b h; simpa using h
      | succ n ih =>
        intro b h
        exact hc U b (ih _ (by rw [← _root_.mul_assoc, ← pow_succ]; exact h))
    have hD : T.basicOpen (c : Γ(T, U)) = U ⊓ T.basicOpen (c : Γ(T, ⊤)) := by
      rw [← T.basicOpen_res (c : Γ(T, ⊤)) (homOfLE (le_top : U ≤ ⊤)).op, map_natCast]
    have h0 : T.presheaf.map (homOfLE (T.basicOpen_le (c : Γ(T, U)))).op b = 0 := by
      refine TopCat.Presheaf.section_ext T.sheaf _ _ 0 (fun x hx => ?_)
      show T.presheaf.germ _ x hx (T.presheaf.map _ b) = T.presheaf.germ _ x hx 0
      rw [TopCat.Presheaf.germ_res_apply, map_zero]
      exact hb x _ (hD ▸ hx).2
    letI := hU.isLocalization_basicOpen (c : Γ(T, U))
    obtain ⟨⟨m, n, rfl⟩, hm⟩ :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers (c : Γ(T, U)))
        Γ(T, T.basicOpen (c : Γ(T, U))) b).mp h0
    exact key n b hm
  · have := (T.toRingedSpace.isUnit_res_basicOpen (c : Γ(T, ⊤))).map
      (T.basicOpen (c : Γ(T, ⊤))).topIso.inv.hom
    exact (congrArg IsUnit ((congrArg _ (map_natCast _ c)).trans (map_natCast _ c))).mp this

end GlobalTheory
end

