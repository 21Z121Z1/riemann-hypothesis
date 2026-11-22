import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0125
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FamilyUniformisationFibreTheta
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0021
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0022
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0015
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0112
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0104
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0070
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0127
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsOfFinOrderOfQuadratic
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.CMSpreadCompare

open GlobalTheory.PureType GlobalTheory.IndefiniteRowSideFullHecke.CMUniformizationSpread

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section Unif

theorem exists_pointEquiv {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') {s : T.left ⟶ S} (hs : s = T.hom ≫ f) :
    ∃ p : (T ⟶ G') ≃* (Over.mk s ⟶ G), ∀ x, (p x).left = x.left ≫ φ := by
  subst hs
  exact ⟨MulEquiv.ofBijective (pushHom h T) ⟨fun _ _ e => eq_of_comp_eq h.1 (congrArg (fun z => z.left) e), fun p =>
    ⟨Over.homMk (h.1.lift p.left T.hom (Over.w p)) (h.1.lift_snd _ _ _),
      Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩⟩, fun _ => rfl⟩

theorem isHolTo_precomp {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
    {X : Scheme.{0}} {y : W → (Sp ℂ ⟶ X)} (h : IsHolTo Set.univ y) {f : V → W} (hf : Differentiable ℂ f) :
    IsHolTo Set.univ (fun v => y (f v)) := fun U s =>
  ⟨(h U s).1.preimage hf.continuous, (h U s).2.comp hf.differentiableOn fun _ hv => hv⟩

theorem isHolTo_postcomp {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X Y : Scheme.{0}} {B : Set V}
    {y : V → (Sp ℂ ⟶ X)} (h : IsHolTo B y) (φ : X ⟶ Y) : IsHolTo B (fun b => y b ≫ φ) := by
  intro U s
  rw [show (fun b => valAt' (y b ≫ φ) U s) = fun b => valAt' (y b) (φ ⁻¹ᵁ U) ((φ.app U).hom s) from
    funext fun b => (valAt'_comp _ φ U s).symm]
  exact h (φ ⁻¹ᵁ U) _

theorem exists_const {g : ℕ} (hg : g = 1) {c : ℂ} (hc : c ≠ 0) (x : Fin g → ℂ) : ∃ z, x = fun _ => c * z := by
  subst hg
  exact ⟨c⁻¹ * x 0, funext fun i => by rw [mul_inv_cancel_left₀ hc, Subsingleton.elim i 0]⟩

variable {k : Type} [Field k] {κ : k →+* ℂ} {A : Over (Sp k)} [GrpObj A] {PC : Out.PolAV (Sp ℂ)}
  {ψ : PC.A.left ⟶ A.left} (hψ : IsGrpPullback PC.A A (spMap κ) ψ) (u : HolUnif PC.A PC.L PC.g)

include hψ

theorem exists_param (c : ℂ) :
    ∃ e : ℂ → (Over.mk (spMap κ) ⟶ A), ∀ z, (e z).left = (u.ex fun _ => c * z).left ≫ ψ := by
  obtain ⟨p, hp⟩ := exists_pointEquiv hψ (𝟙_ _) (s := spMap κ) (Category.id_comp _).symm
  exact ⟨fun z => p (u.ex fun _ => c * z), fun z => hp _⟩

theorem exists_scalar (hg : PC.g = 1) (hu : IsThetaUnif u) {e : ℂ → (Over.mk (spMap κ) ⟶ A)}
    (he : IsCMUnif H κ A e) : ∃ c : ℂ, c ≠ 0 ∧ ∀ z, (e z).left = (u.ex fun _ => c * z).left ≫ ψ := by
  obtain ⟨p, hp⟩ := exists_pointEquiv hψ (𝟙_ _) (s := spMap κ) (Category.id_comp _).symm
  obtain ⟨_, _, _, -, h₁, h₂, -⟩ := hu
  have hp' : ∀ z, (p.symm (e z)).left ≫ ψ = (e z).left := fun z => by rw [← hp, p.apply_symm_apply]
  obtain ⟨F, hF, -⟩ := existsUnique_linear_lift_of_isHolTo PC.A PC.isAb PC.L PC.g 1 u h₁ h₂
    (fun z => p.symm (e (z 0))) (fun z w => by rw [← map_mul, ← he.1]; rfl)
    (FibreUnif.isHolTo_of_isPullback hψ.1 (fun z => Over.w (p.symm (e (z 0)))) (by
      simp only [hp']
      exact isHolTo_precomp he.2.2.2 (f := fun z : Fin 1 → ℂ => z 0) (by fun_prop)))
  have hc : ∀ z, (e z).left = (u.ex fun _ => F (fun _ => 1) ⟨0, by omega⟩ * z).left ≫ ψ := fun z => by
    have e₁ : (fun _ => F (fun _ => 1) ⟨0, by omega⟩ * z) = F fun _ => z := by
      funext i
      rw [show (fun _ => z : Fin 1 → ℂ) = z • fun _ => 1 from funext fun _ => by simp, map_smul,
        show i = ⟨0, by omega⟩ from Fin.ext (by omega), Pi.smul_apply, smul_eq_mul, mul_comm]
    rw [e₁, hF, hp']
  refine ⟨_, fun h0 => ?_, hc⟩
  have h1 : ∀ z, e z = 1 := fun z => by
    have : e z = e 0 := Over.OverMorphism.ext (by simp only [hc, h0, zero_mul])
    rw [this]
    exact (he.2.2.1 0).2 ⟨0, 0, by simp⟩
  refine not_countable_complex ((Set.countable_range fun x : ℤ × ℤ => (x.1 : ℂ) + x.2 * omegaC H).mono fun z _ => ?_)
  obtain ⟨m, n, h⟩ := (he.2.2.1 z).1 (h1 z)
  exact ⟨(m, n), h.symm⟩

end Unif

section Quadratic

theorem exists_sign {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)}
    (hP : IsPeriod D ty P) (ρ : ℂ) :
    ∃ s : ℤ, ∀ a ∈ lat hP ρ, ((D.EF (H.w0 • a) a).natAbs : ℤ) = s * D.EF (H.w0 • a) a := by
  obtain ⟨Hm, -, hpos, hE⟩ := hP.2.2.2.2
  have key : ∀ a ∈ lat hP ρ, ∃ r : ℝ, 0 ≤ r ∧ (D.EF (H.w0 • a) a : ℝ) = ρ.im * r := fun a ha => by
    have h1 := hE (H.w0 • a) a
    have h2 := hE a a
    rw [D.alt, Int.cast_zero] at h2
    have h0 : 0 ≤ (hermForm Hm (P a) (P a)).re := by
      by_cases hz : P a = 0
      · simp [hz, hermForm]
      · exact (hpos _ hz).le
    have h3 : hermForm Hm (P (H.w0 • a)) (P a) = ((1 + ρ) / 2) * hermForm Hm (P a) (P a) := by
      rw [period_w0_smul hP ha, hermForm, hermForm, smul_dotProduct, smul_eq_mul]
    rw [h3, Complex.mul_im, h2] at h1
    exact ⟨(hermForm Hm (P a) (P a)).re / 2, by positivity, by rw [← h1]; simp; ring⟩
  rcases le_total 0 ρ.im with h | h
  · refine ⟨1, fun a ha => ?_⟩
    obtain ⟨r, hr, e⟩ := key a ha
    have : (0 : ℝ) ≤ D.EF (H.w0 • a) a := e ▸ mul_nonneg h hr
    rw [_root_.one_mul, Int.natAbs_of_nonneg (by exact_mod_cast this)]
  · refine ⟨-1, fun a ha => ?_⟩
    obtain ⟨r, hr, e⟩ := key a ha
    have : (D.EF (H.w0 • a) a : ℝ) ≤ 0 := e ▸ mul_nonpos_of_nonpos_of_nonneg h hr
    rw [neg_one_mul, Int.ofNat_natAbs_of_nonpos (by exact_mod_cast this)]

end Quadratic

section Transport

variable {D : Datum H} {R : Type} [CommRing R] {t : SAB H (Sp R)} {B B' : Over (Sp R)} [GrpObj B] [GrpObj B']
  {M : LB B.left} {M' : LB B'.left} {L : Submodule (𝓞 E) D.La} {ρ : R} {S S' : Set L} {φ : L → (B ⟶ t.G)}

theorem exists_generators (L : Submodule (𝓞 E) D.La) : ∃ T : Set L, T.Finite ∧ AddSubgroup.closure T = ⊤ := by
  have := D.fin
  have : IsNoetherian (𝓞 E) D.La := isNoetherian_of_isNoetherianRing_of_finite _ _
  have : Module.Finite ℤ L := Module.Finite.trans (𝓞 E) L
  obtain ⟨T, h₁, h₂⟩ := (AddSubgroup.fg_iff _).1 (Module.Finite.iff_addGroup_fg.1 this).out
  exact ⟨T, h₂, h₁⟩

end Transport

section Multiplication

theorem cmHost_bar_halfIntegerGenerator (H : Host E) : H.bar H.w0 = 1 - H.w0 := by
  have h0 : H.rt ≠ 0 := fun h => by
    have e := H.rt_sq
    rw [h, zero_pow two_ne_zero, zero_eq_neg, Nat.cast_eq_zero] at e
    exact H.d_prime.pos.ne' e
  have h1 : H.bar H.rt = -H.rt := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have e : τ (H.bar H.rt : 𝓞 E) = starRingEnd ℂ (τ (H.rt : E)) := by
      rw [H.bar_eq, IsCMField.complexEmbedding_complexConj]
    have e' : starRingEnd ℂ H.rt0 = -H.rt0 := by
      have hs : H.rt0 ^ 2 = (Complex.I * Real.sqrt H.d) ^ 2 := by
        rw [H.sqrt_neg_disc_sq, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
        simp
      rcases sq_eq_sq_iff_eq_or_eq_neg.1 hs with h | h <;> rw [h] <;> simp
    refine RingOfIntegers.coe_injective (τ.injective ?_)
    refine e.trans ?_
    rw [map_neg, map_neg]
    change _ = -τ (H.rt : E)
    rcases map_rt H τ with h | h <;> rw [h] <;> simp [e']
  apply mul_left_cancel₀ (two_ne_zero : (2 : 𝓞 E) ≠ 0)
  have := congrArg H.bar H.two_weight_eq_one_add_root
  rw [map_mul, map_add, map_one, h1, map_ofNat] at this
  linear_combination this + H.two_weight_eq_one_add_root

end Multiplication

end GlobalTheory.CMSpreadCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjOverCompFinite
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem isProjOver_comp_of_finite :
    ∀ (R : Type) [CommRing R] (X Y : Scheme.{0}) (f : Y ⟶ X) (s : X ⟶ Sp R), IsFinite f → IsProjOver s → IsProjOver (f ≫ s) := by
  intro R _ X Y f s hf hs
  exact GlobalTheory.isProjOver_comp_of_isFinite f hs

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjOverFiniteGroupQuotient
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem isProjOver_of_isProper_of_affine_cover {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) [IsProper s]
    {L : LB X} (hL : L.IsLB) {n : ℕ} (σ : Fin n → LB.Sec L) (ha : ∀ i, IsAffineOpen (Out.nonzeroLocus (σ i)))
    (hc : ⨆ i, Out.nonzeroLocus (σ i) = ⊤) : IsProjOver s := by
  have hA : IsAmpleLB L := by
    refine ⟨hL, ⟨?_⟩, ?_⟩
    · have hu : (Set.univ : Set X) = ⋃ i, (Out.nonzeroLocus (σ i) : Set X) := by
        rw [← TopologicalSpace.Opens.coe_iSup, hc]
        rfl
      rw [hu]
      exact isCompact_iUnion fun i => (ha i).isCompact
    · intro x
      have hx : x ∈ (⊤ : X.Opens) := trivial
      rw [← hc] at hx
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
      refine ⟨1, le_rfl, secToPow (σ i) 1, ?_, ?_⟩
      · rw [nonzeroLocus_secToPow (σ i) le_rfl]
        exact hi
      · rw [nonzeroLocus_secToPow (σ i) le_rfl]
        exact ha i
  exact hA.isProjOver s

theorem isProjOver_quotient : ∀ (Γ : Type) [Group Γ] [Finite Γ] (X X' : Scheme.{0}) (ρ : Γ →* Aut X) (π : X ⟶ X'), (IsAffineHom π ∧ (∀ g, (ρ g).hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (s' : X' ⟶ Sp R), IsProjOver (π ≫ s') → IsProjOver s' := by
  intro Γ _ _ X X' ρ π hq R _ _ s' hX
  have hQ : IsAffineQuotient ρ π :=
    ⟨hq.2.1, hq.1, fun W => (hq.2.2 W).1, fun W f hf => (hq.2.2 W).2 f (by
      unfold IsInvariantSection at hf
      exact fun g _ => (hf g).2)⟩
  have hP : IsProper (π ≫ s') := ((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hX).1
  have hs' : IsProper s' := hQ.isProper s'
  have hXs : X.IsSeparated := by
    constructor
    rw [show terminal.from X = (π ≫ s') ≫ terminal.from (Sp R) from terminal.hom_ext _ _]
    infer_instance
  obtain ⟨L, n, σ, hL, ha, ho⟩ := exists_sections_orbit_subset_nonzeroLocus Γ R X (π ≫ s') ρ hX
  obtain ⟨L', n', σ', hL', ha', hc'⟩ :=
    QuotientNorm.exists_affine_cover_of_quotient Γ X X' ρ π hq hXs L n σ hL ha ho
  exact isProjOver_of_isProper_of_affine_cover s' hL' σ' ha' hc'

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjProperRelAmpleOfProjectiveCoordinateRep
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM.Amp
open GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.ProjSpace TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

variable {Z : Scheme.{0}} {T : Type} [CommRing T]

def ev (x : Sp T ⟶ Z) (U : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) : Γ(Z, U) ⟶ CommRingCat.of T :=
  x.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of T)).hom

theorem inv_ev (x : Sp T ⟶ Z) (U : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(Z, U)) :
    (Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom ((ev x U h).hom a) = (x.appLE U ⊤ h).hom a := by
  have : ev x U h ≫ (Scheme.ΓSpecIso (CommRingCat.of T)).inv = x.appLE U ⊤ h := by
    rw [ev, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact congrArg (fun q => q.hom a) this

theorem comp_str {R : Type} [CommRing R] (s : Z ⟶ Sp R) (x : Sp T ⟶ Z) (U : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) :
    x ≫ s = spMap (baseRingHom s U ≫ ev x U h).hom := by
  refine eq_of_baseRingHom_top ?_
  rw [← baseRingHom_appLE s x U ⊤ h, baseRingHom_top, spMap, CommRingCat.ofHom_hom,
    ← Scheme.ΓSpecIso_inv_naturality, ev]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem comp_toSpecΓ (U : Z.Opens) (y : Sp T ⟶ U.toScheme) (h : ⊤ ≤ (y ≫ U.ι) ⁻¹ᵁ U) :
    y ≫ U.toSpecΓ = Spec.map (ev (y ≫ U.ι) U h) := by
  rw [Scheme.Opens.toSpecΓ, Scheme.toSpecΓ_naturality_assoc, ← SpecMap_ΓSpecIso_hom, ev, Spec.map_comp,
    ← Spec.map_comp (U.topIso.inv)]
  congr 2
  rw [← Scheme.Hom.appLE_comp_appLE y U.ι U ⊤ ⊤ (by simp) le_top, Scheme.Opens.ι_appLE, Scheme.Hom.appTop,
    Scheme.Hom.app_eq_appLE]
  rfl

theorem eq_zero_of_ev {U : Z.Opens} (a : Γ(Z, U))
    (H : ∀ (T : Type) [CommRing T] (x : Sp T ⟶ Z) (h : ⊤ ≤ x ⁻¹ᵁ U), (ev x U h).hom a = 0) : a = 0 := by
  refine ext_germ fun z hz => ?_
  have ht : ⊤ ≤ Z.fromSpecStalk z ⁻¹ᵁ U := fun p _ => by
    have : Z.fromSpecStalk z p ∈ Set.range (Z.fromSpecStalk z) := ⟨p, rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    exact this.mem_open U.isOpen hz
  have e : ev (T := Z.presheaf.stalk z) (Z.fromSpecStalk z) U ht = Z.presheaf.germ U z hz := by
    change (Z.fromSpecStalk z).appLE U ⊤ ht ≫ (Scheme.ΓSpecIso (Z.presheaf.stalk z)).hom = _
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hz]
    simp only [Category.assoc]
    have e : (Spec (Z.presheaf.stalk z)).presheaf.map (homOfLE (le_top : Z.fromSpecStalk z ⁻¹ᵁ U ≤ ⊤)).op ≫
        (Spec (Z.presheaf.stalk z)).presheaf.map (homOfLE ht).op = 𝟙 _ := by
      rw [← Functor.map_comp]; exact CategoryTheory.Functor.map_id _ _
    rw [reassoc_of% e, Iso.inv_hom_id, Category.comp_id]
  rw [map_zero, ← e]
  exact H _ _ ht

variable {M : LB Z} {σ : Type} {th : σ → M.Sec}

theorem secCoord_ratio (x : Sp T ⟶ Z) (i : σ) (h : ⊤ ≤ x ⁻¹ᵁ nonzeroLocus (th i)) :
    SecCoord M th x fun j => (ev x _ h).hom (secRatio (th i) (th j)) := by
  have hu : ∀ k, IsUnit ((secPull (th i) x).f k) := fun k => by
    have := isUnit_resG_sec (secPull (th i) x) k
      (le_top.trans (h.trans (nonzeroLocus_secPull (th i) x).ge)) le_rfl
    rwa [resG_self] at this
  refine ⟨⟨fun k => (hu k).unit⟩, fun k l => Units.ext ((secPull (th i) x).compat k l), fun j k e => ?_⟩
  have e' : (M.pull x).U k ≤ x ⁻¹ᵁ (nonzeroLocus (th i) ⊓ M.U (k ⟨⟩)) := le_inf (le_top.trans h) e
  have := congrArg (x.appLE _ _ e').hom (secRatio_spec (th i) (th j) (k ⟨⟩))
  rw [map_mul, appLE_resG, appLE_resG, appLE_resG] at this
  rw [inv_ev, resG_appLE]
  exact this

theorem secCoord_chart (hM : M.IsLB) (x : Sp T ⟶ Z) (k : M.ι) (h : ⊤ ≤ x ⁻¹ᵁ M.U k) :
    SecCoord M th x fun j => (ev x _ h).hom ((th j).f k) := by
  have hle : ∀ l : PUnit → M.ι, (M.pull x).U l ≤ x ⁻¹ᵁ (M.U (l ⟨⟩) ⊓ M.U k) := fun l =>
    le_inf (pull_U M x l).le (le_top.trans h)
  refine ⟨⟨fun l => Units.map (x.appLE _ _ (hle l)).hom.toMonoidHom (M.g (l ⟨⟩) k)⟩,
    (RepBC.isGen_val _).2 fun l l' => ?_, fun j l e => ?_⟩
  · have e' : (M.pull x).U l ⊓ (M.pull x).U l' ≤ x ⁻¹ᵁ (M.U (l ⟨⟩) ⊓ M.U (l' ⟨⟩) ⊓ M.U k) :=
      le_inf (RepBC.pull_inf_le M x l l') (le_top.trans h)
    have := congrArg (fun u => (x.appLE _ _ e').hom (Units.val u)) (hM.cocycle (l ⟨⟩) (l' ⟨⟩) k)
    simp only [Units.val_mul, val_res, map_mul] at this
    rw [appLE_resG, appLE_resG, appLE_resG] at this
    rw [RepBC.pull_g M x l l' (RepBC.pull_inf_le M x l l')]
    exact (resG_appLE x (hle l) _ _).trans (this.symm.trans (congrArg _ (resG_appLE x (hle l') _ _).symm))
  · have := congrArg (x.appLE _ _ (hle l)).hom ((th j).compat (l ⟨⟩) k)
    rw [map_mul] at this
    erw [appLE_resG, appLE_resG] at this
    rw [inv_ev, resG_appLE, mul_comm]
    exact this

theorem mem_locus (hM : M.IsLB) {x : Sp T ⟶ Z} {v : σ → T} (h : SecCoord M th x v) {i : σ} {p : Sp T}
    (hp : v i ∉ p.asIdeal) : x p ∈ nonzeroLocus (th i) := by
  obtain ⟨τ, -, h⟩ := h
  obtain ⟨k, hk⟩ := exists_chart hM (x p)
  have e := congrArg (Sp T).basicOpen (h i (fun _ => k) (pull_U M x _).le)
  rw [Scheme.basicOpen_appLE, Scheme.basicOpen_mul, Scheme.basicOpen_res,
    (Sp T).basicOpen_of_isUnit (Units.isUnit _)] at e
  have hp' : p ∈ (M.pull x).U fun _ => k := (pull_U M x fun _ => k).ge hk
  have h2 : p ∈ (Sp T).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom (v i)) :=
    (basicOpen_eq_of_affine (R := CommRingCat.of T) (v i)).ge hp
  exact Opens.mem_iSup.2 ⟨k, (e.ge ⟨⟨hp', h2⟩, hp'⟩).2⟩

variable {R : Type} [CommRing R] {I : Ideal (MvPolynomial σ R)} {s : Z ⟶ Sp R}

theorem iSup_locus (H : ProjRep I s M th) : ⨆ i, nonzeroLocus (th i) = ⊤ := by
  refine top_le_iff.1 fun z _ => ?_
  obtain ⟨k, hk⟩ := exists_chart H.1 z
  have ht : ⊤ ≤ Z.fromSpecResidueField z ⁻¹ᵁ M.U k := fun p _ => by
    change Z.fromSpecResidueField z p ∈ M.U k
    rwa [Scheme.fromSpecResidueField_apply]
  have hc := secCoord_chart (th := th) (T := Z.residueField z) H.1 (Z.fromSpecResidueField z) k ht
  have hs := (H.2.1 _ _ _ _ (comp_str s _ _ ht) hc).1
  let p : Sp (Z.residueField z) := IsLocalRing.closedPoint (Z.residueField z)
  by_contra hz
  refine p.isPrime.ne_top (top_le_iff.1 (hs.ge.trans (Ideal.span_le.2 ?_)))
  rintro _ ⟨i, rfl⟩
  by_contra hi
  have := mem_locus H.1 hc hi
  erw [Scheme.fromSpecResidueField_apply] at this
  exact hz (Opens.mem_iSup.2 ⟨i, this⟩)

theorem chart_affine (H : ProjRep I s M th) (i : σ) : IsAffineOpen (nonzeroLocus (th i)) ∧ Function.Surjective
    (MvPolynomial.eval₂Hom (baseRingHom s (nonzeroLocus (th i))).hom fun j => secRatio (th i) (th j)) := by
  set D := nonzeroLocus (th i) with hD
  let c : MvPolynomial σ R →+* Γ(Z, D) :=
    MvPolynomial.eval₂Hom (baseRingHom s D).hom fun j => secRatio (th i) (th j)
  let J : Ideal (MvPolynomial σ R) := I ⊔ Ideal.span {MvPolynomial.X i - 1}
  have hJ : ∀ F ∈ J, c F = 0 := by
    change J ≤ RingHom.ker c
    refine sup_le (fun F hF => eq_zero_of_ev _ fun T _ x h => ?_) ((Ideal.span_singleton_le_iff_mem _).2 ?_)
    · have := (H.2.1 _ _ _ _ (comp_str s x D h) (secCoord_ratio x i h)).2 F hF
      exact (MvPolynomial.eval₂_comp_left (ev x D h).hom _ _ F).trans this
    · simp [c, RingHom.mem_ker]
  let ρ : CommRingCat.of (MvPolynomial σ R ⧸ J) ⟶ Γ(Z, D) := CommRingCat.ofHom (Ideal.Quotient.lift J c hJ)
  have hXi : Ideal.Quotient.mk J (MvPolynomial.X i) = 1 :=
    Ideal.Quotient.eq.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
  obtain ⟨φ, ⟨hφ, hv⟩, -⟩ := H.2.2 _ ((Ideal.Quotient.mk J).comp MvPolynomial.C)
    (fun j => Ideal.Quotient.mk J (MvPolynomial.X j))
    ((Ideal.eq_top_iff_one _).2 (Ideal.subset_span ⟨i, hXi⟩)) fun F hF => by
      have := MvPolynomial.eval₂_comp_left (Ideal.Quotient.mk J) MvPolynomial.C MvPolynomial.X F
      rw [MvPolynomial.eval₂_eta] at this
      exact this.symm.trans (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_left hF))
  have hφD : ⊤ ≤ φ ⁻¹ᵁ D := fun p _ => mem_locus H.1 hv (by
    rw [hXi]; exact (Ideal.ne_top_iff_one _).1 p.isPrime.ne_top)
  let φ' : Sp (MvPolynomial σ R ⧸ J) ⟶ D.toScheme := IsOpenImmersion.lift D.ι φ (by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hφD trivial)
  have hφ' : φ' ≫ D.ι = φ := IsOpenImmersion.lift_fac _ _ _
  have hin : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ D.toScheme), ⊤ ≤ (y ≫ D.ι) ⁻¹ᵁ D := fun T _ y p _ => (y p).2
  have e₁ : φ' ≫ D.toSpecΓ ≫ Spec.map ρ = 𝟙 _ := by
    rw [← Category.assoc, comp_toSpecΓ D φ' (hin _ φ'), ← Spec.map_comp, ← Spec.map_id]
    congr 1
    have hc := secCoord_ratio (φ' ≫ D.ι) i (hin _ φ')
    have hs := comp_str s (φ' ≫ D.ι) D (hin _ φ')
    generalize hin _ φ' = w at hc hs ⊢
    rw [hφ'] at w
    simp only [hφ'] at hc hs ⊢
    obtain ⟨u, hu⟩ := Coord.unique H.1 hv hc
    have hu1 : (u : MvPolynomial σ R ⧸ J) = 1 := by
      have := hu i
      rw [secRatio_self, map_one, hXi, _root_.mul_one] at this
      exact this.symm
    have hb := congrArg CommRingCat.Hom.hom (Spec.map_injective (hs.symm.trans hφ))
    refine CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun a => ?_) fun j => ?_))
    · exact (congrArg (ev φ D _).hom (MvPolynomial.eval₂Hom_C _ _ a)).trans (DFunLike.congr_fun hb a)
    · exact (congrArg (ev φ D _).hom (MvPolynomial.eval₂Hom_X' _ _ j)).trans
        ((hu j).trans (by rw [hu1, _root_.one_mul]; rfl))
  have e₂ : (D.toSpecΓ ≫ Spec.map ρ) ≫ φ' = 𝟙 _ := by
    rw [← cancel_mono D.ι, Category.assoc, hφ', Category.id_comp]
    refine D.toScheme.affineCover.hom_ext _ _ fun a => ?_
    have key : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ D.toScheme),
        y ≫ (D.toSpecΓ ≫ Spec.map ρ) ≫ φ = y ≫ D.ι := fun T _ y => by
      have hc := secCoord_ratio (y ≫ D.ι) i (hin _ y)
      have hs := comp_str s (y ≫ D.ι) D (hin _ y)
      obtain ⟨h₁, h₂⟩ := H.2.1 _ _ _ _ hs hc
      refine (H.2.2 _ _ _ h₁ h₂).unique ?_ ⟨hs, hc⟩
      rw [← Category.assoc, ← Category.assoc, comp_toSpecΓ D y (hin _ y), ← Spec.map_comp]
      constructor
      · rw [Category.assoc, hφ, ← Spec.map_comp]
        congr 1
        refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
        exact congrArg (ev (y ≫ D.ι) D (hin _ y)).hom (MvPolynomial.eval₂Hom_C _ _ a)
      · have e : (fun j => (ev (y ≫ D.ι) D (hin _ y)).hom (secRatio (th i) (th j))) = fun j =>
            (ρ ≫ ev (y ≫ D.ι) D (hin _ y)).hom (Ideal.Quotient.mk J (MvPolynomial.X j)) := funext fun j =>
          congrArg (ev (y ≫ D.ι) D (hin _ y)).hom (MvPolynomial.eval₂Hom_X' (baseRingHom s D).hom (fun j => secRatio (th i) (th j)) j).symm
        exact e ▸ Coord.baseChange hv (ρ ≫ ev (y ≫ D.ι) D (hin _ y)).hom
    exact key _ (D.toScheme.affineCover.f a)
  have hiso : IsIso (D.toSpecΓ ≫ Spec.map ρ) := ⟨φ', e₂, e₁⟩
  have ha : IsAffine D.toScheme := .of_isIso (D.toSpecΓ ≫ Spec.map ρ)
  have ha' : IsAffineOpen D := ha
  refine ⟨ha', ?_⟩
  have h1 : IsIso D.toSpecΓ := inferInstanceAs (IsIso ha'.isoSpec.hom)
  have h2 : IsIso (Spec.map ρ) := IsIso.of_isIso_comp_left D.toSpecΓ _
  exact (isIso_SpecMap_iff.1 h2).2.comp Ideal.Quotient.mk_surjective

end GlobalTheory.ZM.Amp

namespace GlobalTheory.ZM
open GlobalTheory.ProjSpace Amp
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

theorem projRep_projective_ample : ∀ (R σ : Type) [CommRing R] [Finite σ] (I : Ideal (MvPolynomial σ R)) (Z : Over (Sp R)) (M : LB Z.left) (th : σ → M.Sec), ProjRep I Z.hom M th → IsProjOver Z.hom ∧ IsProper Z.hom ∧ Out.RelAmple Z M := by
  intro R σ _ _ I Z M th H
  have hp : IsProjOver Z.hom := by
    cases isEmpty_or_nonempty σ with
    | inl h => exact isProjOver_of_disjoint_cover Z.hom _ (iSup_locus H) (fun i => isEmptyElim i) fun i => isEmptyElim i
    | inr h =>
      obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
      obtain _ | m := n
      · exact (h.elim fun i => (e i).elim0)
      have hs : ⨆ i, nonzeroLocus (th (e.symm i)) = ⊤ :=
        (e.symm.iSup_comp (g := fun i => nonzeroLocus (th i))).trans (iSup_locus H)
      refine ⟨m, toProj Z.hom (fun i => th (e.symm i)) hs, (isClosedImmersion_toProj_iff _ _ hs).2 fun i =>
        ⟨(chart_affine H _).1, fun a => ?_⟩, toProj_str _ _ _⟩
      obtain ⟨F, hF⟩ := (chart_affine H (e.symm i)).2 a
      refine ⟨MvPolynomial.rename e F, ?_⟩
      rw [MvPolynomial.eval₂Hom_rename, ← hF]
      congr 2
      funext j
      simp
  have hpr : IsProper Z.hom := ((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hp).1
  refine ⟨hp, hpr, (relAmple_iff_isAmpleLB_of_isAffine Z H.1).2 ?_⟩
  have e : ∀ i, nonzeroLocus (secToPow (th i) 1) = nonzeroLocus (th i) := fun i =>
    nonzeroLocus_secToPow (th i) le_rfl
  exact isAmpleLB_of_cover H.1 le_rfl (fun i => secToPow (th i) 1) ((iSup_congr e).trans (iSup_locus H))
    fun i => (e i).symm ▸ (chart_affine H i).1

end GlobalTheory.ZM
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsVeryAmpleSectionSystemOfProjectiveCoordinatesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isVeryAmpleSectionSystem_of_projectiveCoordinates : ∀ (K σ : Type) [Field K] [Finite σ] (I : Ideal (MvPolynomial σ K)) (Z : Scheme.{0}) (p : Z ⟶ Sp K) (M : LB Z) (th : σ → M.Sec), ProjRep I p M th → VAmp p M th := by
  first | exact @GlobalTheory.ZV.CoordEmbed.vAmp_of_projRep | exact GlobalTheory.ZV.CoordEmbed.vAmp_of_projRep | (intros; apply GlobalTheory.ZV.CoordEmbed.vAmp_of_projRep <;> assumption)
end

