import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverZpOfInFibre
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0040
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0007
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0011
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0062
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0063
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenericCentreSpecializes
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0001
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0059
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0014

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentResidueIntegrality
section
open CategoryTheory AlgebraicGeometry NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT GlobalTheory.CompanionTheory.Ar.Flat ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.HTStalk

section Lattices

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {V : Type} [AddCommGroup V] [Module Ω V]

theorem mem_htW_iff (M : LieModel G ξ V) (L : Semi.LB G.left) (n : ℕ) {R : Type} [CommRing R]
    (ρ : R →+* Module.End Ω V) (σ : R →+* Ω) (𝔡 : Ideal R) (q : Cpt ξ) (e : V) :
    e ∈ M.htW L n ρ σ 𝔡 q ↔ e ∈ GlobalTheory.CompanionTheory.Ar.eigSp ρ σ ∧ ∀ d ∈ 𝔡, σ d • e ∈ M.htDual L n ρ σ q := by
  constructor
  · intro he
    induction he using Submodule.span_induction with
    | mem x hx => exact hx
    | zero => exact ⟨Submodule.zero_mem _, fun d _ => by simp⟩
    | add x y _ _ hx hy =>
      refine ⟨Submodule.add_mem _ hx.1 hy.1, fun d hd => ?_⟩
      rw [smul_add]
      exact Submodule.add_mem _ (hx.2 d hd) (hy.2 d hd)
    | smul c x _ hx =>
      refine ⟨(GlobalTheory.CompanionTheory.Ar.eigSp ρ σ).smul_mem (c : Ω) hx.1, fun d hd => ?_⟩
      have h : σ d • c • x = c • σ d • x := smul_comm _ _ _
      rw [h]
      exact Submodule.smul_mem _ c (hx.2 d hd)
  · exact fun h => Submodule.subset_span h

theorem mem_htW_iff_forms (M : LieModel G ξ V) (L : Semi.LB G.left) (n : ℕ) {R : Type} [CommRing R]
    (ρ : R →+* Module.End Ω V) (σ : R →+* Ω) (𝔡 : Ideal R) (q : Cpt ξ) (e : V) :
    e ∈ M.htW L n ρ σ 𝔡 q ↔
      e ∈ GlobalTheory.CompanionTheory.Ar.eigSp ρ σ ∧ ∀ w ∈ M.htOm L n q, ∀ d ∈ 𝔡, σ d * w e ∈ regAt ξ q := by
  rw [mem_htW_iff]
  refine and_congr_right fun he => ⟨fun h w hw d hd => ?_, fun h d hd => ?_⟩
  · have := ((M.mem_htDual_iff L n ρ σ q _).1 (h d hd)).2 w hw
    simpa [map_smul, smul_eq_mul] using this
  · refine (M.mem_htDual_iff L n ρ σ q _).2 ⟨(GlobalTheory.CompanionTheory.Ar.eigSp ρ σ).smul_mem _ he, fun w hw => ?_⟩
    simpa [map_smul, smul_eq_mul] using h w hw d hd

end Lattices

theorem forall_different_iff {o Ω E : Type} [CommRing o] [Field Ω] [Algebra o Ω] [Field E] [NumberField E]
    (A : Subalgebra o Ω) (B : Subring Ω) (hA : ∀ a : A, (a : Ω) ∈ B) (σ : E →+* Ω) (ds : A)
    (hds : GeneratesDiff σ ds) (t : Ω) :
    (∀ x ∈ differentIdeal ℤ (𝓞 E), σ (x : E) * t ∈ B) ↔ (ds : Ω) * t ∈ B := by
  constructor
  · intro h
    have h1 : algebraMap A Ω ds ∈ Submodule.span A {algebraMap A Ω ds} :=
      Submodule.subset_span rfl
    rw [hds] at h1
    have h2 : ∀ z ∈ Submodule.span A {y : Ω | ∃ x ∈ differentIdeal ℤ (𝓞 E), y = σ (x : E)}, z * t ∈ B := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨x, hx, rfl⟩ := hz
        exact h x hx
      | zero => simpa using B.zero_mem
      | add u v _ _ hu hv =>
        rw [add_mul]
        exact B.add_mem hu hv
      | smul a u _ hu =>
        have : (a • u) * t = (a : Ω) * (u * t) := by
          rw [Algebra.smul_def, mul_assoc]
          rfl
        rw [this]
        exact B.mul_mem (hA a) hu
    exact h2 _ h1
  · intro h x hx
    have h1 : σ (x : E) ∈ Submodule.span A {y : Ω | ∃ x ∈ differentIdeal ℤ (𝓞 E), y = σ (x : E)} :=
      Submodule.subset_span ⟨x, hx, rfl⟩
    rw [← hds, Submodule.mem_span_singleton] at h1
    obtain ⟨a, ha⟩ := h1
    have : σ (x : E) * t = (a : Ω) * ((ds : Ω) * t) := by
      rw [← ha, Algebra.smul_def, mul_assoc]
      rfl
    rw [this]
    exact B.mul_mem (hA a) h

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y)

theorem inv_natCast_mem {p : ℕ} (hp : p.Prime) {q : Cpt 𝔐.ξ} (hq : InFibre 𝔐.ξ p q) (b : ℕ) (hb : ¬ p ∣ b) :
    ((b : Ω))⁻¹ ∈ regAt 𝔐.ξ q := by
  have hZ := ModelTest.overZp_of_inFibre 𝔐 hp q hq
  induction b using Nat.recOnMul with
  | zero => exact absurd (dvd_zero p) hb
  | one => simpa using (regAt 𝔐.ξ q).one_mem
  | prime r hr =>
    have hne : r ≠ p := by
      rintro rfl
      exact hb dvd_rfl
    have hu : unitAt 𝔐.ξ q (r : Ω) := by
      by_contra hnot
      exact hne (hZ r hr hnot)
    exact hu.2.2
  | mul a b ha hb' =>
    have h1 : ¬ p ∣ a := fun h => hb (h.mul_right b)
    have h2 : ¬ p ∣ b := fun h => hb (h.mul_left a)
    rw [Nat.cast_mul, mul_inv]
    exact (regAt 𝔐.ξ q).mul_mem (ha h1) (hb' h2)

theorem chart_mem_regAt {p : ℕ} (hp : p.Prime) {o : Type} [CommRing o] [Algebra o Ω]
    (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω))
    {s : ∀ k, J k} {q : Cpt 𝔐.ξ} (hs : InChart 𝔐.ξ (mseg y) s q) (hq : InFibre 𝔐.ξ p q)
    (a : chartRing o (mseg y) s) : (a : Ω) ∈ regAt 𝔐.ξ q := by
  obtain ⟨a, ha⟩ := a
  change a ∈ regAt 𝔐.ξ q
  change a ∈ Algebra.adjoin o _ at ha
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact hs.2 j
  | algebraMap r =>
    obtain ⟨u, b, hb, h⟩ := (ho _).1 ⟨r, rfl⟩
    rw [h, div_eq_mul_inv]
    exact (regAt 𝔐.ξ q).mul_mem (intCast_mem _ u) (inv_natCast_mem 𝔐 hp hq b hb)
  | add u v _ _ hu hv => exact (regAt 𝔐.ξ q).add_mem hu hv
  | mul u v _ _ hu hv => exact (regAt 𝔐.ξ q).mul_mem hu hv

end Model

theorem mem_V_inl_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (o : Type) [CommRing o] [Algebra o Ω] (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)) (Dc : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, HTChart (chartRing o (mseg y) s.1) Ω (cmConj E) p (𝔐.R p) (D.p + D.q) (Module.Dual Ω 𝔐.Li)), IsHTFamily 𝔐 p o Dc → p ∈ S → ∀ (τ : CMType H) (σ : E →+* Ω), (∀ a : 𝓞 E, σ (a : E) = 𝔐.emb (Sum.inl τ) a) → ∀ (s : {s : ∀ k, J k // mseg y s ≠ 0}) (ds : chartRing o (mseg y) s.1), GeneratesDiff σ ds → ∀ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) s.1 q → InFibre 𝔐.ξ p q → ∀ e : 𝔐.Li, e ∈ 𝔐.V (Sum.inl τ) q ↔ e ∈ HTL.latOn (Dc s) (GlobalTheory.CompanionTheory.Ar.HT.eigSp 𝔐.ρ σ) (ds : Ω) (regAt 𝔐.ξ q) := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J _ y 𝔐 p _ o _ _ ho Dc hD hpS τ σ hσ s ds hds q hs hq e
  have hp : p.Prime := Fact.out
  have hV : 𝔐.V (Sum.inl τ) q = 𝔐.HT p (Sum.inl τ) q :=
    Lat.patch_of_unique S _ _ hpS hq fun p' hp' h =>
      ModelTest.overZp_of_inFibre 𝔐 hp q hq p' (𝔐.S_prime p' hp') h
  have hE : e ∈ GlobalTheory.CompanionTheory.Ar.eigSp 𝔐.ρ (𝔐.emb (Sum.inl τ)) ↔ e ∈ GlobalTheory.CompanionTheory.Ar.HT.eigSp 𝔐.ρ σ := by
    rw [LatBasic.mem_eigSp]
    simp only [GlobalTheory.CompanionTheory.Ar.eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero, hσ]
  have hA := chart_mem_regAt 𝔐 hp ho hs hq
  have hO : omP 𝔐 p q = Submodule.span (regAt 𝔐.ξ q) ((Dc s).om' : Set (Module.Dual Ω 𝔐.Li)) :=
    hD.om'_loc s q hs hq
  rw [hV]
  change e ∈ 𝔐.M.htW _ _ _ _ _ q ↔ _
  rw [mem_htW_iff_forms, hE]
  refine and_congr_right fun _ => ?_
  have hT : ∀ w : Module.Dual Ω 𝔐.Li,
      (∀ d ∈ differentIdeal ℤ (𝓞 E), 𝔐.emb (Sum.inl τ) d * w e ∈ regAt 𝔐.ξ q) ↔
        (ds : Ω) * w e ∈ regAt 𝔐.ξ q := fun w => by
    rw [← forall_different_iff _ _ hA σ ds hds]
    simp only [hσ]
  constructor
  · intro h w hw
    have hw' : w ∈ omP 𝔐 p q := by
      rw [hO]
      exact Submodule.subset_span hw
    exact (hT w).1 (h w hw')
  · intro h w hw
    rw [show 𝔐.M.htOm 𝔐.t.PP.L (p ^ 𝔐.R p) q = omP 𝔐 p q from rfl, hO] at hw
    refine (hT w).2 ?_
    induction hw using Submodule.span_induction with
    | mem w hw => exact h w hw
    | zero => simpa using (regAt 𝔐.ξ q).zero_mem
    | add u v _ _ hu hv =>
      have : (ds : Ω) * (u + v) e = (ds : Ω) * u e + (ds : Ω) * v e := by
        rw [LinearMap.add_apply, mul_add]
      rw [this]
      exact (regAt 𝔐.ξ q).add_mem hu hv
    | smul a u _ hu =>
      have : (ds : Ω) * (a • u) e = (a : Ω) * ((ds : Ω) * u e) := by
        change (ds : Ω) * ((a : Ω) • u) e = _
        rw [LinearMap.smul_apply, smul_eq_mul]
        ring
      rw [this]
      exact (regAt 𝔐.ξ q).mul_mem a.2 hu

end GlobalTheory.CompanionTheory.Ar.Flat.HTStalk
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateWeilEndomorphism
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.HtEnd

theorem pullPow {X : Scheme.{0}} {G : Over X} [GrpObj G] {A B : Over X} (ψ : A ⟶ B) (g : B ⟶ G) (n : ℕ) :
    ψ ≫ g ^ n = (ψ ≫ g) ^ n := by
  induction n with
  | zero => simp only [pow_zero, CategoryTheory.MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, CategoryTheory.MonObj.comp_mul, ih]

theorem homPow {X : Scheme.{0}} {G : Over X} [GrpObj G] {Z : Over X} (a : G ⟶ G) [IsMonHom a] (x : Z ⟶ G) (n : ℕ) :
    (x ^ n) ≫ a = (x ≫ a) ^ n := by
  induction n with
  | zero => simp only [pow_zero, CategoryTheory.MonObj.one_comp]
  | succ n ih => rw [pow_succ, pow_succ, CategoryTheory.MonObj.mul_comp, ih]

theorem epiSp {Ω K : Type} [Field Ω] [Field K] (a : Ω →+* K) : Epi (spMap a) := by
  letI := a.toAlgebra
  haveI : AlgebraicGeometry.Flat (Spec.map (CommRingCat.ofHom a)) := by
    rw [HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Flat)]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  haveI : AlgebraicGeometry.Surjective (Spec.map (CommRingCat.ofHom a)) := by
    rw [AlgebraicGeometry.surjective_iff]
    intro y
    exact ⟨(default : PrimeSpectrum K), Subsingleton.elim (α := PrimeSpectrum Ω) _ _⟩
  exact AlgebraicGeometry.Flat.epi_of_flat_of_surjective _

theorem powDescend {X : Scheme.{0}} {G : Over X} [GrpObj G] {Ω K : Type} [Field Ω] [Field K]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {N : ℕ} (a : Ω →+* K)
    {g₀ : Over.mk ξ ⟶ G} {g : Over.mk (spMap a ≫ ξ) ⟶ G} (e : g.left = spMap a ≫ g₀.left) (hg : g ^ N = 1) :
    g₀ ^ N = 1 := by
  let ψ : Over.mk (spMap a ≫ ξ) ⟶ Over.mk ξ := Over.homMk (spMap a)
  haveI : Epi ψ := Over.epi_of_epi_left ψ (hk := epiSp a)
  have hψ : ψ ≫ g₀ = g := Over.OverMorphism.ext (by simp [ψ, e])
  apply (cancel_epi ψ).mp
  rw [pullPow, hψ, hg, CategoryTheory.MonObj.comp_one]

theorem secVal_app {B : Type} [CommRing B] {Z Z' : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ Z) (φ : Z ⟶ Z')
    (W : Z'.Opens) (f : Γ(Z', W)) (h : ⊤ ≤ x ⁻¹ᵁ (φ ⁻¹ᵁ W)) (h' : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ W) :
    secVal x (φ ⁻¹ᵁ W) h ((φ.app W).hom f) = secVal (x ≫ φ) W h' f := by
  simp only [secVal, Scheme.Hom.comp_appLE]
  rfl

end GlobalTheory.CompanionTheory.Ar.HtEnd

open GlobalTheory.CompanionTheory.Ar.HtEnd in

theorem GlobalTheory.CompanionTheory.Ar.LieModel.isHTAt_end : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → Flat.NormalCpt ξ → ∀ (G : Over X) [GrpObj G], IsSemiAbelian G → ∀ (L : LB G.left) (n : ℕ), 1 ≤ n → FullTorsion G ξ n → ∀ e, GenWeil G L ξ n e → ∀ (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (a : G ⟶ G) [IsMonHom a] (A : E →ₗ[Ω] E), M.IsDiffOf a A → ∀ (y y' : Over.mk ξ ⟶ G), y ^ n = 1 → y' ^ n = 1 → (∀ g, g ^ n = 1 → e y' g = e y (g ≫ a)) → ∀ (q : Cpt ξ) (w : Module.Dual Ω E), M.IsHTAt L n y q w → M.IsHTAt L n y' q (w ∘ₗ A) := by
  intro X _ Ω _ _ ξ _ _ G _ _ L n _ hFT ep hW E _ _ M a _ A hA y y' hy hy' hyy' q w hH
  obtain ⟨hw, W, f, hη, P1, P2⟩ := hH
  have hExt : ∀ {e' : E} {v}, M.Extends q e' v → M.Extends q (A e') (v ≫ a) := by
    intro e' v hv
    refine ⟨?_, ?_⟩
    · have h1 := hv.1
      unfold IsTanAt at h1 ⊢
      rw [Over.comp_left, ← Category.assoc, h1, ← Over.comp_left, CategoryTheory.MonObj.one_comp]
    · rw [hA e', Over.comp_left, hv.2]
      erw [Category.assoc]
  have hlat : ∀ e' ∈ M.lat q, A e' ∈ M.lat q := by
    intro e' he'
    have hle : M.lat q ≤ (M.lat q).comap (A.restrictScalars (regAt ξ q)) := by
      refine Submodule.span_le.mpr ?_
      rintro e'' ⟨v, hv⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.restrictScalars_apply]
      exact Submodule.subset_span ⟨v ≫ a, hExt hv⟩
    exact hle he'
  have hw' : ∀ e' ∈ M.lat q, w e' ∈ regAt ξ q := hw
  refine ⟨?_, a.left ⁻¹ᵁ W, (a.left.app W).hom f, ?_, ?_, ?_⟩
  · show ∀ e' ∈ M.lat q, (w ∘ₗ A) e' ∈ regAt ξ q
    intro e' he'
    exact hw' (A e') (hlat e' he')
  · have h1 : (η[G] ≫ a).left = (η[G]).left := by rw [IsMonHom.one_hom]
    show a.left ((η[G]).left q.1) ∈ W
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, h1]
    exact hη
  · intro k _ _ i xk g c h hx hg hWe
    have h2 : ⊤ ≤ (g.left ≫ a.left) ⁻¹ᵁ W := h
    rw [secVal_app g.left a.left W f h h2]
    obtain ⟨g₀, hg₀⟩ := hFT k i g hg
    have hg₀n : g₀ ^ n = 1 := powDescend i hg₀ hg
    have hga : (g ≫ a) ^ n = 1 := by rw [← homPow, hg, CategoryTheory.MonObj.one_comp]
    have hg₀a : (g₀ ≫ a) ^ n = 1 := by rw [← homPow, hg₀n, CategoryTheory.MonObj.one_comp]
    have hc : (c : k) = i (ep y' g₀) := (hW.weil y' g₀ hy' hg₀n k i xk g c hx hg₀).mp hWe
    rw [hyy' g₀ hg₀n] at hc
    let xk0 : Over.mk (spMap i ≫ ξ) ⟶ G := Over.homMk (spMap i ≫ y.left)
    have hg' : (g ≫ a).left = spMap i ≫ (g₀ ≫ a).left := by
      rw [Over.comp_left, Over.comp_left, hg₀, Category.assoc]
    have hWa := (hW.weil y (g₀ ≫ a) hy hg₀a k i xk0 (g ≫ a) c rfl hg').mpr hc
    exact P1 k i xk0 (g ≫ a) c h2 rfl hga hWa
  · intro e' v hv h
    have h2 : ⊤ ≤ (v.left ≫ a.left) ⁻¹ᵁ W := h
    obtain ⟨r, hr, hE⟩ := P2 (A e') (v ≫ a) (hExt hv) h2
    refine ⟨r, hr, ?_⟩
    rw [LinearMap.comp_apply, secVal_app v.left a.left W f h h2]
    exact hE
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IdealSaturatedVectorBundle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
private theorem exists_open_forall_mem_regAt' {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Sp Ω ⟶ X) (q : Cpt ξ) (w : Ω)
    (hw : w ∈ regAt ξ q) : ∃ W : X.Opens, q.1 ∈ W ∧ ∀ q' : Cpt ξ, q'.1 ∈ W → w ∈ regAt ξ q' := by
  obtain ⟨g, rfl⟩ := hw
  obtain ⟨W, hq, s, rfl⟩ := X.presheaf.exists_germ_eq g
  refine ⟨W, hq, fun q' hq' => ⟨X.presheaf.germ W q'.1 hq' s, ?_⟩⟩
  have key : ∀ (y : X) (hy : y ∈ W) (h : genPt ξ ⤳ y),
      X.presheaf.germ W y hy ≫ X.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo ξ =
        X.presheaf.germ W (genPt ξ) (h.mem_open W.isOpen hy) ≫ Scheme.stalkClosedPointTo ξ := by
    intro y hy h
    exact TopCat.Presheaf.germ_stalkSpecializes_assoc X.presheaf hy h _
  simp only [genMap]
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply]
  erw [key q'.1 hq' q'.2, key q.1 hq q.2]

private theorem exists_mul_eq_one_of_dedekind_ideal_ne_bot {Ω : Type} [Field Ω] (O : Type) [CommRing O] [IsDedekindDomain O] (σ : O →+* Ω)
    (𝔡 : Ideal O) (R : Subring Ω) [IsLocalRing R] (hσ : ∀ a, σ a ∈ R) (hinj : Function.Injective σ)
    (h𝔡 : 𝔡 ≠ ⊥) : ∃ d ∈ 𝔡, ∃ u : Ω, (∀ d' ∈ 𝔡, ∃ o : O, σ d' * u = σ o) ∧ ∃ v ∈ R, σ d * u * v = 1 := by
  obtain ⟨x, hx𝔡, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔡
  obtain ⟨𝔞, h𝔞⟩ : 𝔡 ∣ Ideal.span {x} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hx𝔡)
  have hσx : σ x ≠ 0 := fun h => hx0 (hinj (by rw [h, map_zero]))
  have hgood : ∀ n ∈ 𝔞, ∀ d' ∈ 𝔡, ∃ o : O, σ d' * (σ n / σ x) = σ o := by
    intro n hn d' hd'
    have hmem : d' * n ∈ Ideal.span {x} := h𝔞 ▸ Ideal.mul_mem_mul hd' hn
    obtain ⟨o, ho⟩ := Ideal.mem_span_singleton'.mp hmem
    refine ⟨o, ?_⟩
    rw [← mul_div_assoc, ← map_mul, ← ho, map_mul, mul_div_cancel_right₀ _ hσx]
  by_contra hne
  push_neg at hne
  let C : O → Prop := fun y => ∃ h : σ y / σ x ∈ R, (⟨_, h⟩ : R) ∈ IsLocalRing.maximalIdeal R
  have hx : x ∈ 𝔡 * 𝔞 := h𝔞 ▸ Ideal.mem_span_singleton_self x
  have hC : C x := by
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro m hm n hn
      obtain ⟨o, ho⟩ := hgood n hn m hm
      have hR : σ (m * n) / σ x ∈ R := by
        rw [map_mul, mul_div_assoc, ho]; exact hσ o
      refine ⟨hR, ?_⟩
      by_contra hnot
      have hu : IsUnit (⟨_, hR⟩ : R) := by
        by_contra h'
        exact hnot ((IsLocalRing.mem_maximalIdeal _).mpr h')
      obtain ⟨w, hw⟩ := hu.exists_right_inv
      refine hne m hm (σ n / σ x) (hgood n hn) w w.2 ?_
      have := congrArg Subtype.val hw
      simpa [map_mul, mul_div_assoc] using this
    · rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
      have hab : σ (a + b) / σ x ∈ R := by rw [map_add, add_div]; exact add_mem ha hb
      refine ⟨hab, ?_⟩
      have : (⟨_, hab⟩ : R) = ⟨_, ha⟩ + ⟨_, hb⟩ := by
        ext; simp [map_add, add_div]
      rw [this]; exact add_mem ha' hb'
  obtain ⟨h1, h2⟩ := hC
  have : (⟨_, h1⟩ : R) = 1 := by ext; simp [div_self hσx]
  rw [this] at h2
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr h2)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.ideal_saturated_vector_bundle : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (O : Type) [CommRing O] [IsDedekindDomain O] (σ : O →+* Ω) (𝔡 : Ideal O) (L : Lat ξ Li) (T : Set (Cpt ξ)) (r : ℕ) (V : Submodule Ω Li), Function.Injective σ → 𝔡 ≠ ⊥ → (∀ q ∈ T, ∀ a, σ a ∈ regAt ξ q) → L.IsVBOn T r V → Lat.IsVBOn (fun q => Submodule.span (regAt ξ q) {e | e ∈ V ∧ ∀ d ∈ 𝔡, σ d • e ∈ L q} : Lat ξ Li) T r V := by
  intro X Ω _ ξ Li _ _ O _ _ σ 𝔡 L T r V hinj h𝔡 hσ hL p hp
  obtain ⟨U₀, hpU₀, b, hbV, hb⟩ := hL p hp
  haveI : IsLocalRing (regAt ξ p) :=
    IsLocalRing.of_surjective' (genMap ξ p).rangeRestrict (genMap ξ p).rangeRestrict_surjective
  obtain ⟨d, hd, u, hu, v, hv, hdu⟩ := exists_mul_eq_one_of_dedekind_ideal_ne_bot O σ 𝔡 (regAt ξ p) (hσ p hp) hinj h𝔡
  obtain ⟨W₂, hpW₂, hW₂⟩ := exists_open_forall_mem_regAt' ξ p v hv
  have hu0 : u ≠ 0 := by rintro rfl; simp at hdu
  refine ⟨U₀ ⊓ W₂, ⟨hpU₀, hpW₂⟩, fun i => u • b i, ?_, ?_⟩
  · rw [← hbV]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have : b i = u⁻¹ • (u • b i) := by rw [smul_smul, inv_mul_cancel₀ hu0, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · intro q hq hqU
    obtain ⟨hli, hLq⟩ := hb q hq hqU.1
    have hvq : v ∈ regAt ξ q := hW₂ q hqU.2
    refine ⟨?_, ?_⟩
    · have := hli.units_smul (fun _ => Units.mk0 u hu0)
      convert this using 1
      funext i
      simp [Units.smul_def]
    · apply le_antisymm
      · rw [Submodule.span_le]
        rintro e ⟨heV, he⟩
        have h1 : σ d • e ∈ L q := he d hd
        rw [hLq] at h1
        have h2 : (⟨v, hvq⟩ : regAt ξ q) • (σ d • e) ∈ Submodule.span (regAt ξ q) (Set.range b) :=
          Submodule.smul_mem _ _ h1
        obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp h2
        have he' : e = u • ((⟨v, hvq⟩ : regAt ξ q) • (σ d • e)) := by
          rw [Subring.smul_def, smul_smul, smul_smul]
          rw [show u * v * σ d = 1 by rw [← hdu]; ring, one_smul]
        rw [SetLike.mem_coe, he', ← hc, Finset.smul_sum]
        refine Submodule.sum_mem _ (fun i _ => ?_)
        rw [Subring.smul_def, smul_comm]
        exact Submodule.smul_mem _ (c i) (Submodule.subset_span ⟨i, rfl⟩)
      · rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        apply Submodule.subset_span
        refine ⟨?_, fun d' hd' => ?_⟩
        · rw [← hbV]
          exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
        · obtain ⟨o, ho⟩ := hu d' hd'
          have hbi : b i ∈ L q := by rw [hLq]; exact Submodule.subset_span ⟨i, rfl⟩
          rw [smul_smul, ho]
          exact Submodule.smul_mem (L q) (⟨σ o, hσ q hq o⟩ : regAt ξ q) hbi
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsCombMatrixMul
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.CombMul

theorem pt_sum_ofFn {S : Scheme.{0}} {G : Over S} [GrpObj G] {F : Type} [Field F] {x : Sp F ⟶ S} {V : Type}
    [AddCommGroup V] [Module F V] (M : LieModel G x V) : ∀ {n : ℕ} (u : Fin n → V),
    M.pt (∑ i, u i) = (List.ofFn fun i => M.pt (u i)).prod
  | 0, u => by simp [M.pt_zero]
  | n + 1, u => by
    rw [Fin.sum_univ_succ, M.add, pt_sum_ofFn M (fun i => u i.succ), List.ofFn_succ, List.prod_cons]

theorem isComb_pt_iff {S : Scheme.{0}} {G : Over S} [GrpObj G] {F : Type} [Field F] {x : Sp F ⟶ S} {V : Type}
    [AddCommGroup V] [Module F V] (M : LieModel G x V) {n : ℕ} (c : Fin n → F) (e : Fin n → V)
    (w : epsAt x ⟶ G) : IsComb c (fun i => M.pt (e i)) w ↔ w = M.pt (∑ i, c i • e i) := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    have h : u = fun i => M.pt (c i • e i) :=
      funext fun i => Over.OverMorphism.ext ((hu i).trans (M.smul _ _).symm)
    rw [pt_sum_ofFn, h]
  · rintro rfl
    exact ⟨fun i => M.pt (c i • e i), fun i => M.smul _ _, pt_sum_ofFn M _⟩

theorem isComb_mul : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (F : Type) [Field F] (x : Sp F ⟶ S) (m n k : ℕ) (v : Fin n → (epsAt x ⟶ G)) (u : Fin m → (epsAt x ⟶ G)) (w : Fin k → (epsAt x ⟶ G)) (A : Matrix (Fin k) (Fin m) F) (C : Matrix (Fin m) (Fin n) F), (∀ i, IsTanAt G x (v i)) → (∀ i, IsComb (C i) v (u i)) → (∀ i, IsComb (A i) u (w i)) → ∀ i, IsComb ((A * C) i) v (w i) := by
  intro S G _ _ F _ x m n k v u w A C hv hu hw i
  obtain ⟨E, _, _, ⟨M⟩⟩ := lieModel_exists S G F x
  obtain ⟨e, rfl⟩ : ∃ e : Fin n → E, v = fun i => M.pt (e i) := by
    choose e he using fun i => M.onto (v i) (hv i)
    exact ⟨e, funext fun i => (he i).symm⟩
  obtain rfl : u = fun j => M.pt (∑ l, C j l • e l) :=
    funext fun j => (isComb_pt_iff M (C j) e (u j)).1 (hu j)
  have hwi := (isComb_pt_iff M (A i) _ (w i)).1 (hw i)
  rw [isComb_pt_iff, hwi]
  congr 1
  simp only [Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  exact Finset.sum_comm

end GlobalTheory.CompanionTheory.Ar.CombMul
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeEigenFieldExtensionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_eigen_field_extension : ∀ (F : Type) [Field F] [NumberField F] (Ω Ω' : Type) [Field Ω] [Field Ω'] [CharZero Ω] (i : Ω →+* Ω') (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (j : V →+ V') (ρ : 𝓞 F →+* Module.End Ω V) (ρ' : 𝓞 F →+* Module.End Ω' V') (σ : 𝓞 F →+* Ω) (R : Subring Ω) (R' : Subring Ω') (L : Submodule R V), IsExtOver i j → (∀ a e, ρ' a (j e) = j (ρ a e)) → (∀ a ∈ R, i a ∈ R') → (∀ a, ∀ e ∈ L, ρ a e ∈ L) → (∀ a, σ a ∈ R) → ((NumberField.discr F : ℤ) : Ω)⁻¹ ∈ R → Submodule.span R' (j '' (L : Set V)) ⊓ (eigSp ρ' (i.comp σ)).restrictScalars R' = Submodule.span R' (j '' ((L ⊓ (eigSp ρ σ).restrictScalars R : Submodule R V) : Set V)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.EigLat.span_inf_eigSp | exact GlobalTheory.CompanionTheory.Ar.EigLat.span_inf_eigSp | (intros; apply GlobalTheory.CompanionTheory.Ar.EigLat.span_inf_eigSp <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeFlagFieldExtensionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_flag_field_extension : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω' ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω') (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (j : V →+ V') (jd : Module.Dual Ω V →+ Module.Dual Ω' V') (W : Submodule Ω V) (W' : Submodule Ω' V') (Lo : Lat ξ (Module.Dual Ω V)) (Lo' : Lat ξ' (Module.Dual Ω' V')) (T : Set (Cpt ξ)) (T' : Set (Cpt ξ')) (r : ℕ), GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → IsCptGen ξ' → IsExtOver i j → (∀ w e, jd w (j e) = i (w e)) → W' = Submodule.span Ω' (j '' (W : Set V)) → (Lo.map W.dualRestrict).IsVBOn T r ⊤ → (∀ p' ∈ T', ∃ hq : genPt ξ ⤳ f p'.1, (⟨f p'.1, hq⟩ : Cpt ξ) ∈ T ∧ (0 < r → Lo' p' = Submodule.span (regAt ξ' p') (jd '' (Lo ⟨f p'.1, hq⟩ : Set (Module.Dual Ω V))))) → (Lo'.map W'.dualRestrict).IsVBOn T' r ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.VbPull.isVBOn_dual_pull | exact GlobalTheory.CompanionTheory.Ar.VbPull.isVBOn_dual_pull | (intros; apply GlobalTheory.CompanionTheory.Ar.VbPull.isVBOn_dual_pull <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeFlagVectorBundleStatement
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_flag_vector_bundle : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (T : Set (Cpt ξ)) (g r : ℕ) (W : Submodule Ω E) (b₀ : Fin r → E), LinearIndependent Ω b₀ → (∀ k, b₀ k ∈ W) → L.IsVBOn T g W → (∀ n : ℕ, ∃ s W', (L.map (flagStep Ω b₀ n).mkQ).IsVBOn T s W') → (L.inter (Submodule.span Ω (Set.range b₀))).IsFlagVBOn T b₀ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.isFlagVBOn_inter_of_steps | exact GlobalTheory.CompanionTheory.Ar.isFlagVBOn_inter_of_steps | (intros; apply GlobalTheory.CompanionTheory.Ar.isFlagVBOn_inter_of_steps <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineDegreeSpecialFibre
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem propZ_numerical : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s] (ϖ : O), Irreducible ϖ → Function.Injective (algebraMap O Ω) → ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → IsCptGen ξ → NormalCpt ξ → _root_.IsConnected (zeroSet ξ (algebraMap O Ω ϖ)) → ∀ (L : Lat ξ Ω) (σ : Ω), L.IsVB 1 ⊤ → NumTrivMod L (algebraMap O Ω ϖ) → (∀ p ∈ genFibre O ξ, L.IsGenAt p σ) → ∃ (M : ℕ) (a : ℤ), 0 < M ∧ ∀ p : Cpt ξ, OrderAt L σ (algebraMap O Ω ϖ) M a p :=
  @PositivityTheory.Xgn.normal_proper_line_order

end GlobalTheory.CompanionTheory.Ar.Flat
end

