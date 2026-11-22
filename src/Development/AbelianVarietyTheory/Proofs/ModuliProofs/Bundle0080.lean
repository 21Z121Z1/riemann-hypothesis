import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0070
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedGenericFibreOfDense
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0008

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ResidueGeneric
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.CoordChart

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (h : B →+* C) :
    spMap h ≫ spMap f = spMap (h.comp f) := by
  unfold spMap
  rw [← Spec.map_comp]; rfl

theorem sp_inj {A B : Type} [CommRing A] [CommRing B] {f h : A →+* B} (e : spMap f = spMap h) : f = h := by
  have := Spec.map_injective e
  exact congrArg CommRingCat.Hom.hom this

theorem sp_surj {A B : Type} [CommRing A] [CommRing B] (z : Sp B ⟶ Sp A) : ∃ f : A →+* B, spMap f = z :=
  ⟨(Spec.preimage z).hom, Spec.map_preimage z⟩

theorem lift_chart {o : Type} [CommRing o] {g n N' : ℕ} {I : Ideal (MvPolynomial (Ix g (N' ^ 2)) o)}
    (Y : MMPre n N' I) {R : Type} [CommRing R] (β : o →+* R) (x : Sp R ⟶ Y.MM) (v : Ix g (N' ^ 2) → R)
    {K : Type} [Field K] (y : R →+* K) [IsOpenImmersion x] (hx : x ≫ Y.s = spMap β)
    (hv : SecCoord Y.de Y.th x v) (c : Kˣ)
    {L : Type} [CommRing L] (ψ : L →+* K) (hψ : ∀ l, ψ l ≠ 0 → IsUnit l) (β' : o →+* L)
    (w : Ix g (N' ^ 2) → L) (hβ : ψ.comp β' = y.comp β) (hw : ∀ a, ψ (w a) = c * y (v a))
    (hI : ∀ F ∈ I, MvPolynomial.eval₂ β' w F = 0) :
    ∃ φ : R →+* L, ψ.comp φ = y ∧ φ.comp β = β' ∧ ∃ u : Lˣ, ∀ a, w a = u * φ (v a) := by
  have h1 := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ Y.isLB hv).1 K y
  have h2 := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ Y.isLB h1).2.1 c
  have h3 : (spMap y ≫ x) ≫ Y.s = spMap (y.comp β) := by rw [Category.assoc, hx, sp_comp]
  have hK := Y.loc K _ _ _ h3 h2
  have hL : InMM n N' I β' w := by
    refine ⟨hI, fun q hq a => ?_⟩
    obtain ⟨d, hd⟩ := hK.2 ⊥ Ideal.isPrime_bot a
    refine ⟨d, fun hm => hq.ne_top (Ideal.eq_top_of_isUnit_mem _ hm (hψ _ ?_))⟩
    rw [hw]
    simpa using hd
  obtain ⟨z, ⟨hz1, hz2⟩, -⟩ := Y.pts L β' w hL
  have h4 := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ Y.isLB hz2).1 K ψ
  have h5 : (spMap ψ ≫ z) ≫ Y.s = spMap (y.comp β) := by rw [Category.assoc, hz1, sp_comp, hβ]
  have heq : spMap ψ ≫ z = spMap y ≫ x := by
    refine (Y.pts K _ _ hK).unique ⟨h5, ?_⟩ ⟨h3, h2⟩
    simpa only [hw] using h4
  have hr : Set.range z ⊆ Set.range x := by
    rintro _ ⟨p, rfl⟩
    let p₀ : Sp K := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K)
    have hs : p ⤳ spMap ψ p₀ := by
      refine (PrimeSpectrum.le_iff_specializes (R := L) p (spMap ψ p₀)).1 ?_
      intro l hl
      change ψ l ∈ (⊥ : Ideal K)
      by_contra hne
      exact p.2.ne_top (Ideal.eq_top_of_isUnit_mem _ hl (hψ _ (by simpa using hne)))
    refine (hs.map z.continuous).mem_open x.isOpenEmbedding.isOpen_range ⟨spMap y p₀, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, heq]
  obtain ⟨φ, hφ⟩ := sp_surj (IsOpenImmersion.lift x z hr)
  have hz : spMap φ ≫ x = z := by rw [hφ, IsOpenImmersion.lift_fac]
  refine ⟨φ, sp_inj ?_, sp_inj ?_, ?_⟩
  · rw [← cancel_mono x, ← sp_comp, Category.assoc, hz, heq]
  · rw [← sp_comp, ← hx, ← Category.assoc, hz, hz1]
  · have h6 := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ Y.isLB hv).1 L φ
    rw [hz] at h6
    exact (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ Y.isLB h6).2.2 w hz2

theorem clear_denom {o σ R L : Type} [CommRing o] [CommRing R] [CommRing L] (β : o →+* R) (φ : R →+* L)
    (v : σ → R) (w : σ → L) (t : R) (h : ∀ a, w a * φ t = φ (v a)) (F : MvPolynomial σ o) :
    ∃ (r : R) (m : ℕ), MvPolynomial.eval₂ (φ.comp β) w F * φ t ^ m = φ r := by
  induction F using MvPolynomial.induction_on with
  | C c => exact ⟨β c, 0, by simp⟩
  | add p q hp hq =>
    obtain ⟨r, m, h1⟩ := hp
    obtain ⟨r', m', h2⟩ := hq
    refine ⟨r * t ^ m' + r' * t ^ m, m + m', ?_⟩
    rw [MvPolynomial.eval₂_add, map_add, map_mul, map_mul, ← h1, ← h2, map_pow, map_pow]
    ring
  | mul_X p a hp =>
    obtain ⟨r, m, h1⟩ := hp
    refine ⟨r * v a, m + 1, ?_⟩
    rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, map_mul, ← h1, ← h a]
    ring

theorem residue_generic : ∀ (o : Type) [CommRing o] (g n N' : ℕ) (I : Ideal (MvPolynomial (Ix g (N' ^ 2)) o)) (Y : MMPre n N' I) (R : Type) [CommRing R] (β : o →+* R) (x : Sp R ⟶ Y.MM) (v : Ix g (N' ^ 2) → R) (K : Type) [Field K] (y : R →+* K) (a₀ : Ix g (N' ^ 2)), 0 < N' → IsOpenImmersion x → x ≫ Y.s = spMap β → SecCoord Y.de Y.th x v → (∀ k : K, ∃ r r' : R, y r' ≠ 0 ∧ k * y r' = y r) → y (v a₀) ≠ 0 → Subfield.closure (Set.range (y.comp β) ∪ Set.range (fun a => y (v a) / y (v a₀))) = ⊤ ∧ (RingHom.ker y ∈ minimalPrimes R → RingHom.ker (MvPolynomial.eval₂Hom (y.comp β) (fun a => y (v a) / y (v a₀))) ∈ (I ⊔ Ideal.span {MvPolynomial.X a₀ - 1}).minimalPrimes) := by
  intro o _ g n N' I Y R _ β x v K _ y a₀ _ hox hx hv hfr h0
  let c : Kˣ := (Units.mk0 _ h0)⁻¹
  have hc : ∀ a, y (v a) / y (v a₀) = c * y (v a) := fun a => by
    simp [c, div_eq_inv_mul]
  have h1 := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ Y.isLB hv).1 K y
  have h2 := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ Y.isLB h1).2.1 c
  have h3 : (spMap y ≫ x) ≫ Y.s = spMap (y.comp β) := by rw [Category.assoc, hx, sp_comp]
  have hK : ∀ F ∈ I, MvPolynomial.eval₂ (y.comp β) (fun a => y (v a) / y (v a₀)) F = 0 := by
    simpa only [hc] using (Y.loc K _ _ _ h3 h2).1
  constructor
  · set E := Subfield.closure (Set.range (y.comp β) ∪ Set.range (fun a => y (v a) / y (v a₀))) with hE
    let β' : o →+* E := (y.comp β).codRestrict E fun t => Subfield.subset_closure (Or.inl ⟨t, rfl⟩)
    let w : Ix g (N' ^ 2) → E := fun a => ⟨y (v a) / y (v a₀), Subfield.subset_closure (Or.inr ⟨a, rfl⟩)⟩
    obtain ⟨φ, hφ, -⟩ := lift_chart Y β x v y hx hv c E.subtype
      (fun l hl => IsUnit.mk0 l (fun h => hl (by rw [h, map_zero]))) β' w rfl (fun a => hc a) (by
        intro F hF
        apply E.subtype.injective
        rw [MvPolynomial.eval₂_comp_left, map_zero]
        exact hK F hF)
    have hy : ∀ r, y r ∈ E := fun r => by rw [← hφ]; exact (φ r).2
    rw [eq_top_iff]
    intro k _
    obtain ⟨r, r', hr, hk⟩ := hfr k
    rw [eq_div_of_mul_eq hr hk]
    exact E.div_mem (hy r) (hy r')
  · intro hmin
    set ev := MvPolynomial.eval₂Hom (y.comp β) (fun a => y (v a) / y (v a₀)) with hev
    refine ⟨⟨RingHom.ker_isPrime ev, sup_le (fun F hF => hK F hF) ?_⟩, ?_⟩
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      change ev _ = 0
      simp [hev, h0]
    rintro P ⟨hP, hJ⟩ hle
    let e : (MvPolynomial (Ix g (N' ^ 2)) o ⧸ P) →+* K := Ideal.Quotient.lift P ev fun a ha => hle ha
    haveI : (RingHom.ker e).IsPrime := RingHom.ker_isPrime e
    let L := Localization.AtPrime (RingHom.ker e)
    have hu : ∀ s : (RingHom.ker e).primeCompl, IsUnit (e s) := fun s => IsUnit.mk0 _ s.2
    let ψ : L →+* K := IsLocalization.lift (M := (RingHom.ker e).primeCompl) hu
    let π : MvPolynomial (Ix g (N' ^ 2)) o →+* L := (algebraMap _ L).comp (Ideal.Quotient.mk P)
    have hπ : ∀ F, ψ (π F) = ev F := fun F => by
      simp only [ψ, π, RingHom.comp_apply, IsLocalization.lift_eq]
      rfl
    have hπe : ∀ F, MvPolynomial.eval₂ (π.comp MvPolynomial.C) (fun a => π (MvPolynomial.X a)) F = π F := fun F => by
      conv_rhs => rw [← MvPolynomial.eval₂_eta F, MvPolynomial.eval₂_comp_left]
      rfl
    have hπ0 : ∀ F, π F = 0 ↔ F ∈ P := fun F => by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      exact map_eq_zero_iff _ (IsLocalization.injective L (RingHom.ker e).primeCompl_le_nonZeroDivisors)
    have hψ : ∀ l, ψ l ≠ 0 → IsUnit l := by
      intro l hl
      obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (RingHom.ker e).primeCompl l
      rw [IsLocalization.AtPrime.isUnit_mk'_iff L (RingHom.ker e)]
      intro ha
      apply hl
      change ψ (IsLocalization.mk' L a s) = 0
      rw [IsLocalization.lift_mk'_spec, mul_zero]
      exact ha
    obtain ⟨φ, hφ, hβ, u, hw⟩ := lift_chart Y β x v y hx hv c ψ hψ (π.comp MvPolynomial.C)
      (fun a => π (MvPolynomial.X a)) (by ext t; simp [hπ, hev]) (fun a => by rw [hπ, ← hc]; simp [hev])
      (fun F hF => by rw [hπe, hπ0]; exact hJ (Ideal.mem_sup_left hF))
    have hone : (u : L) * φ (v a₀) = 1 := by
      rw [← hw, ← sub_eq_zero, ← map_one π, ← map_sub, hπ0]
      exact hJ (Ideal.mem_sup_right (Ideal.subset_span rfl))
    have hker : RingHom.ker y ≤ RingHom.ker φ :=
      hmin.2 ⟨RingHom.ker_isPrime φ, bot_le⟩ (fun r hr => by
        rw [RingHom.mem_ker] at hr ⊢
        rw [← hφ, RingHom.comp_apply, hr, map_zero])
    intro F hF
    obtain ⟨r, m, hr⟩ := clear_denom β φ v (fun a => π (MvPolynomial.X a)) (v a₀)
      (fun a => by
        change π (MvPolynomial.X a) * _ = _
        rw [hw a, mul_right_comm, hone, _root_.one_mul]) F
    rw [hβ, hπe] at hr
    have hyr : r ∈ RingHom.ker y := by
      rw [RingHom.mem_ker] at hF ⊢
      rw [← hφ, RingHom.comp_apply, ← hr, map_mul, hπ, hF, zero_mul]
    have hφr : φ r = 0 := hker hyr
    rw [hφr] at hr
    rw [← hπ0]
    exact ((IsUnit.of_mul_eq_one_right _ hone).pow m).mul_left_eq_zero.1 hr

end GlobalTheory.CoordChart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionAndGeometricallyConnect
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.VeryDenseFibres

theorem geometricallyConnected_fiber_iff {X T S : Scheme.{0}} (f : X ⟶ S) (t : T ⟶ S) (y : T) :
    GeometricallyConnected ((pullback.snd f t).fiberToSpecResidueField y) ↔
      GeometricallyConnected (f.fiberToSpecResidueField (t y)) := by
  have hp := isPullback_fiberToSpecResidueField_of_isPullback (IsPullback.of_hasPullback f t) y
  refine ⟨fun h => ?_, fun h => MorphismProperty.of_isPullback (P := @GeometricallyConnected) hp h⟩
  have : Surjective (Spec.map (t.residueFieldMap y)) :=
    ⟨fun z => ⟨default, Subsingleton.elim _ _⟩⟩
  exact GlobalTheory.geometricallyConnected_of_isPullback_of_surjective hp

theorem smooth_fiber_of_smooth_fiber {X T S : Scheme.{0}} (f : X ⟶ S) (t : T ⟶ S) (y : T)
    (h : Smooth ((pullback.snd f t).fiberToSpecResidueField y)) :
    Smooth (f.fiberToSpecResidueField (t y)) := by
  have hp := isPullback_fiberToSpecResidueField_of_isPullback (IsPullback.of_hasPullback f t) y
  refine MorphismProperty.of_isPullback_of_descendsAlong
    (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hp.flip ⟨⟨?_, ?_⟩, ?_⟩ h
  · exact ⟨fun y => ⟨default, Subsingleton.elim _ _⟩⟩
  · infer_instance
  · infer_instance

theorem mem_smoothLocus_of_smooth_fiber {R : CommRingCat.{0}} {X : Scheme.{0}} (f : X ⟶ Spec R)
    [LocallyOfFinitePresentation f] [Flat f] (x : X)
    (h : Smooth (f.fiberToSpecResidueField (f x))) : x ∈ f.smoothLocus := by
  wlog hX : ∃ S, X = Spec S generalizing f X
  · obtain ⟨i, y, rfl⟩ := X.affineCover.exists_eq x
    have _ : Smooth (pullback.snd f ((Spec R).fromSpecResidueField
        ((X.affineCover.f i ≫ f) y))) := h
    have H := this (X.affineCover.f i ≫ f) y (by
      rw [Scheme.Hom.fiberToSpecResidueField, ← pullbackRightPullbackFstIso_inv_snd_snd]
      infer_instance) ⟨_, rfl⟩
    rwa [← Scheme.Hom.preimage_smoothLocus_eq] at H
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  letI := φ.hom.toAlgebra
  haveI : Algebra.FinitePresentation R S :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation) (φ := φ)).mp ‹_›
  haveI : Module.Flat R S :=
    (HasRingHomProperty.Spec_iff (P := @Flat) (φ := φ)).mp ‹_›
  haveI : x.asIdeal.IsPrime := PrimeSpectrum.isPrime x
  let p : PrimeSpectrum R := Spec.map φ x
  haveI : x.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩
  haveI : Algebra.FormallySmooth p.asIdeal.ResidueField (p.asIdeal.Fiber S) := by
    rw [← RingHom.formallySmooth_algebraMap]
    refine RingHom.Smooth.formallySmooth ?_
    rw [← CommRingCat.hom_ofHom (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber ↑S)),
      ← HasRingHomProperty.Spec_iff (P := @Smooth),
      ← MorphismProperty.arrow_mk_iso_iff (P := @Smooth) (Spec.fiberToSpecResidueFieldIso R S p)]
    exact h
  haveI := Algebra.IsSmoothAt.of_formallySmooth_fiber (R := R) p.asIdeal x.asIdeal
  obtain ⟨g, hg, hsm⟩ := Algebra.IsSmoothAt.exists_notMem_smooth R x.asIdeal
  let j : Spec (CommRingCat.of (Localization.Away g)) ⟶ Spec S :=
    Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))
  haveI : IsOpenImmersion j := IsOpenImmersion.of_isLocalization g
  haveI : Smooth (j ≫ Spec.map φ) := by
    rw [← Spec.map_comp, HasRingHomProperty.Spec_iff (P := @Smooth)]
    exact RingHom.smooth_algebraMap.mpr hsm
  obtain ⟨y, rfl⟩ : x ∈ Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away g))) := by
    rw [PrimeSpectrum.localization_away_comap_range _ g]
    exact hg
  have := (j ≫ Spec.map φ).smoothLocus_eq_top.ge (Set.mem_univ y)
  rwa [← Scheme.Hom.preimage_smoothLocus_eq] at this

theorem exists_opens_smoothOfRelativeDimension {X T S : Scheme.{0}} (f : X ⟶ S) [Smooth f]
    (t : T ⟶ S) (g : ℕ) (h : SmoothOfRelativeDimension g (pullback.snd f t)) (x : X) (y : T)
    (hxy : f x = t y) : ∃ W : X.Opens, x ∈ W ∧ SmoothOfRelativeDimension g (W.ι ≫ f) := by
  obtain ⟨n, W, hW, hd⟩ := ReciprocityTheory.ChartRestriction.G.H1.exists_dim f x
  have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} n
  have h1 : SmoothOfRelativeDimension n (pullback.snd (W.ι ≫ f) t) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension n) _ _ hd
  have h2 : SmoothOfRelativeDimension (0 + (0 + g)) (pullback.snd (W.ι ≫ f) t) := by
    rw [← pullbackRightPullbackFstIso_inv_snd_snd]
    infer_instance
  obtain ⟨z, -⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback (W.ι ≫ f) t)
    ⟨x, hW⟩ y hxy
  have e : n = g := by simpa using ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ h1 h2 z
  exact ⟨W, hW, e ▸ hd⟩

theorem eq_top_of_forall_mem {R : Type} [CommRing R] {Z : Scheme.{0}} (s : Z ⟶ Sp R)
    [UniversallyClosed s] (P : Set (Ideal R))
    (hP : ∀ q : Ideal R, q.IsPrime → ∃ p ∈ P, p.IsPrime ∧ q ≤ p) (U : Z.Opens)
    (hU : ∀ z : Z, (s z).asIdeal ∈ P → z ∈ U) : U = ⊤ := by
  rw [← top_le_iff]
  intro x _
  by_contra hx
  have hc : IsClosed (s '' (U : Set Z)ᶜ) := s.isClosedMap _ U.2.isClosed_compl
  obtain ⟨p, hp, hp', hle⟩ := hP (s x).asIdeal (PrimeSpectrum.isPrime _)
  have hs : s x ⤳ (⟨p, hp'⟩ : PrimeSpectrum R) := (PrimeSpectrum.le_iff_specializes _ _).1 hle
  obtain ⟨y, hy, hy'⟩ := hs.mem_closed hc ⟨x, hx, rfl⟩
  exact hy (hU y (by rw [hy']; exact hp))

theorem spMap_apply_asIdeal {R K : Type} [CommRing R] [Field K] (x : R →+* K) (y : Sp K) :
    (spMap x y).asIdeal = RingHom.ker x := by
  have : y.asIdeal = ⊥ := by
    have := PrimeSpectrum.isPrime y
    exact Ideal.eq_bot_of_prime _
  change Ideal.comap x y.asIdeal = _
  rw [this]
  rfl

theorem geometricallyConnected_of_veryDense {R : Type} [CommRing R] [IsNoetherianRing R]
    {Z : Scheme.{0}} (s : Z ⟶ Sp R) [LocallyOfFiniteType s] [QuasiCompact s] (P : Set (Ideal R))
    (hP : ∀ (q₀ : Ideal R) (f₀ : R), q₀.IsPrime → f₀ ∉ q₀ →
      ∃ p₀ ∈ P, p₀.IsPrime ∧ q₀ ≤ p₀ ∧ f₀ ∉ p₀)
    (h : ∀ y : Sp R, y.asIdeal ∈ P → GeometricallyConnected (s.fiberToSpecResidueField y)) :
    GeometricallyConnected s := by
  rw [GeometricallyConnected.iff_geometricallyConnected_fiber]
  intro q
  have hq : q.asIdeal.IsPrime := PrimeSpectrum.isPrime q
  let t : Sp (R ⧸ q.asIdeal) ⟶ Sp R := spMap (Ideal.Quotient.mk q.asIdeal)
  have hd : Dense {y : Sp (R ⧸ q.asIdeal) | (t y).asIdeal ∈ P} := by
    refine (PrimeSpectrum.isTopologicalBasis_basic_opens (R := R ⧸ q.asIdeal)).dense_iff.2 ?_
    rintro _ ⟨a, rfl⟩ ⟨z, hz⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    have ha : a ∉ q.asIdeal := fun ha => hz (by
      rw [Ideal.Quotient.eq_zero_iff_mem.2 ha]; exact Ideal.zero_mem _)
    obtain ⟨p, hp, hp', hle, hap⟩ := hP _ a hq ha
    obtain ⟨y, hy⟩ : (⟨p, hp'⟩ : PrimeSpectrum R) ∈
        Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk q.asIdeal)) := by
      rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
      exact hle
    have hy' : Ideal.comap (Ideal.Quotient.mk q.asIdeal) y.asIdeal = p :=
      congrArg PrimeSpectrum.asIdeal hy
    refine ⟨y, fun hy2 => hap (hy' ▸ hy2), ?_⟩
    change Ideal.comap (Ideal.Quotient.mk q.asIdeal) y.asIdeal ∈ P
    rwa [hy']
  have H := GlobalTheory.geometricallyConnected_genericFibre_of_dense _ (Sp (R ⧸ q.asIdeal))
    (pullback.snd s t) _ hd fun y hy => (geometricallyConnected_fiber_iff s t y).2 (h _ hy)
  rw [geometricallyConnected_fiber_iff] at H
  have e : t (genericPoint (Sp (R ⧸ q.asIdeal))) = q := by
    rw [genericPoint_eq_bot_of_affine]
    exact PrimeSpectrum.ext (Ideal.mk_ker (I := q.asIdeal))
  rwa [e] at H

theorem smoothOfRelativeDimension_and_geometricallyConnected_of_veryDense :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (g : ℕ) (P : Set (Ideal R)), (∀ (q₀ : Ideal R) (f₀ : R), q₀.IsPrime → f₀ ∉ q₀ → ∃ p₀ ∈ P, p₀.IsPrime ∧ q₀ ≤ p₀ ∧ f₀ ∉ p₀) → IsProjOver s → Flat s → (∀ q ∈ P, ∃ (K : Type) (_ : Field K) (x : R →+* K), RingHom.ker x = q ∧ SmoothOfRelativeDimension g (pullback.snd s (spMap x)) ∧ GeometricallyConnected (pullback.snd s (spMap x))) → SmoothOfRelativeDimension g s ∧ GeometricallyConnected s := by
  intro R _ _ Z s g P hP hs hf h
  have : IsProper s := by
    obtain ⟨N, i, hi, rfl⟩ := hs
    have := isProper_str R N
    infer_instance
  have : LocallyOfFinitePresentation s := inferInstance
  have hP' : ∀ q : Ideal R, q.IsPrime → ∃ p ∈ P, p.IsPrime ∧ q ≤ p := fun q hq => by
    obtain ⟨p, h1, h2, h3, -⟩ := hP q 1 hq ((Ideal.ne_top_iff_one q).1 hq.ne_top)
    exact ⟨p, h1, h2, h3⟩
  have h' : ∀ y : Sp R, y.asIdeal ∈ P → ∃ (T : Scheme.{0}) (t : T ⟶ Sp R) (w : T), t w = y ∧
      SmoothOfRelativeDimension g (pullback.snd s t) ∧
      GeometricallyConnected (pullback.snd s t) := fun y hy => by
    obtain ⟨K, _, x, hx, h1, h2⟩ := h _ hy
    exact ⟨_, spMap x, (default : PrimeSpectrum K),
      PrimeSpectrum.ext ((spMap_apply_asIdeal x _).trans hx), h1, h2⟩
  refine ⟨?_, geometricallyConnected_of_veryDense s P hP fun y hy => ?_⟩
  · have : Smooth s := by
      rw [← Scheme.Hom.smoothLocus_eq_top_iff]
      refine eq_top_of_forall_mem s P hP' _ fun z hz => ?_
      obtain ⟨T, t, w, hw, h1, -⟩ := h' _ hz
      refine mem_smoothLocus_of_smooth_fiber s z ?_
      rw [← hw]
      have : Smooth (pullback.snd s t) := SmoothOfRelativeDimension.smooth g _
      exact smooth_fiber_of_smooth_fiber s t w
        (inferInstanceAs (Smooth (pullback.snd (pullback.snd s t) (T.fromSpecResidueField w))))
    let V : {W : Z.Opens // SmoothOfRelativeDimension g (W.ι ≫ s)} → Z.Opens := fun W => W.1
    have htop : iSup V = ⊤ := by
      refine eq_top_of_forall_mem s P hP' _ fun z hz => ?_
      obtain ⟨T, t, w, hw, h1, -⟩ := h' _ hz
      obtain ⟨W, hW, hW'⟩ := exists_opens_smoothOfRelativeDimension s t g h1 z w hw.symm
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨W, hW'⟩, hW⟩
    have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{0} g) :=
      HasRingHomProperty.instIsZariskiLocalAtSource
    exact IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension.{0} g) V htop
      fun W => W.2
  · obtain ⟨T, t, w, rfl, -, h2⟩ := h' _ hy
    exact (geometricallyConnected_fiber_iff s t w).1 inferInstance

end GlobalTheory.VeryDenseFibres
end

