import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0052
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0007
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013

-- bundled from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.CPtsat
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace PositivityTheory.UnitarySelfGeneration

section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {e : ℕ}
  {Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}

theorem ptsat_segre (z : (Σ k, ι k) → ℂ) : segre (star z) = star (segre z) := by
  funext i
  simp [segre]

theorem ptsat_cons (y : Fin e → ℂ) : star (Fin.cons 1 y : Fin (e + 1) → ℂ) = Fin.cons 1 (star y) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem ptsat_mem {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) : star z ∈ mcPts P :=
  ((GlobalTheory.T.complex_conjugation_herm_compat K ι).1 P z).2 hz

theorem ptsat_symm (h : ∀ w, Ψ' w = star (Ψ (star w))) (w) : Ψ w = star (Ψ' (star w)) := by
  rw [h, star_star, star_star]

theorem ptsat_fibre (h : ∀ w, Ψ' w = star (Ψ (star w))) {y w} (hw : w ∈ fibre P Ψ' y) :
    star w ∈ fibre P Ψ (star y) := by
  obtain ⟨z, hz, rfl, h2⟩ := hw
  exact ⟨star z, ptsat_mem hz, ptsat_segre z, by rw [ptsat_symm h, star_star, h2, ptsat_cons]⟩

theorem ptsat_sheet (h : ∀ w, Ψ' w = star (Ψ (star w))) {y w γ} (hγ : IsSheet P Ψ' y w γ) :
    IsSheet P Ψ (star y) (star w) (star ∘ γ ∘ star) := by
  refine ⟨by simp only [Function.comp_apply, star_star, ptsat_segre, hγ.1], ?_⟩
  have ht : Tendsto (star : (Fin e → ℂ) → Fin e → ℂ) (𝓝 (star y)) (𝓝 y) := by
    simpa using (continuous_star (R := Fin e → ℂ)).tendsto (star y)
  filter_upwards [ht.eventually hγ.2] with y' hy'
  refine ⟨by simpa using hy'.1.star_star, ptsat_mem hy'.2.1, ?_⟩
  rw [ptsat_symm h, Function.comp_apply, Function.comp_apply, ptsat_segre, star_star, hy'.2.2, ptsat_cons,
    star_star]

end

theorem c_ptsat : SheetIndepStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ) (Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (L : Fin e → HermLine ι) (A : HermLine ι) (s : MRing ι), IsArithVar P (e + 1) → IsGoodProj P Ψ → (∀ w i, Ψ' w i = starRingEnd ℂ (Ψ (fun c => starRingEnd ℂ (w c)) i)) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSectionOn P A s → IsGoodProj P Ψ' ∧ ptsIntegralAt P Ψ' (pot fun j => conjLine (L j)) (logNorm (conjLine A) s) = ptsIntegralAt P Ψ (pot L) (logNorm A s) := by
  intro hS K _ ι _ P e Ψ Ψ' L A s hP hΨ h0 hL hA hs
  have h : ∀ w, Ψ' w = star (Ψ (star w)) := fun w => funext (h0 w)
  refine ⟨fun z hz h1 => hΨ _ (ptsat_mem hz) (by rw [ptsat_symm h, ptsat_segre, star_star, h1, star_zero]), ?_⟩
  have hm : MeasureTheory.MeasurePreserving (star : (Fin e → ℂ) → Fin e → ℂ) :=
    MeasureTheory.volume_preserving_pi fun _ => Complex.conjLIE.measurePreserving
  have he : MeasurableEmbedding (star : (Fin e → ℂ) → Fin e → ℂ) :=
    (starL' ℝ : (Fin e → ℂ) ≃L[ℝ] (Fin e → ℂ)).toHomeomorph.measurableEmbedding
  unfold ptsIntegralAt
  rw [← hm.integral_comp he (fun y => ∑ᶠ w ∈ fibre P Ψ y, sheetDensity P Ψ (pot L) (logNorm A s) y w)]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [hm.quasiMeasurePreserving.ae (hS K ι P e Ψ L A s hP hΨ hL hA hs)] with y hy
  refine finsum_mem_eq_of_bijOn star ⟨fun w hw => ptsat_fibre h hw, star_injective.injOn, fun w hw =>
    ⟨star w, by simpa using ptsat_fibre (ptsat_symm h) hw, star_star w⟩⟩ fun w _ => ?_
  unfold sheetDensity
  by_cases h1 : ∃ γ, IsSheet P Ψ' y w γ
  · have h2 : ∃ γ, IsSheet P Ψ (star y) (star w) γ := ⟨_, ptsat_sheet h h1.choose_spec⟩
    rw [dif_pos h1, dif_pos h2, hy _ _ _ h2.choose_spec (ptsat_sheet h h1.choose_spec),
      (GlobalTheory.T.complex_conjugation_herm_compat K ι).2.2.2.1]
    have h3 := c_madens e (fun j y' => pot L j ((star ∘ h1.choose ∘ star) y')) y
    congr 1
    · simp only [Function.comp_apply, star_star]
      rfl
    · refine Eq.trans ?_ h3
      congr 1
      funext j y'
      show _ = pot L j (star (h1.choose (star (star y'))))
      rw [star_star]
      rfl
  · have h2 : ¬ ∃ γ, IsSheet P Ψ (star y) (star w) γ := fun ⟨γ, hγ⟩ =>
      h1 ⟨_, by simpa only [star_star] using ptsat_sheet (ptsat_symm h) hγ⟩
    rw [dif_neg h1, dif_neg h2]

end PositivityTheory.UnitarySelfGeneration
end

-- bundled from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.CmTypeLabelTwistPermutation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration

theorem cm_type_label_twist_permutation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (g : HostAut H), ∃ π : CMType H ≃ CMType H, (∀ τ, (π τ).1 = τ.1.comp g.σ.toRingHom) ∧ ∀ s, labelEmb c (Sum.map π π s) = (labelEmb c s).comp g.s.toRingHom := by
  intro E _ _ _ H l c g
  let F : HostAut H → CMType H → CMType H := fun g τ =>
    ⟨τ.1.comp g.σ.toRingHom, by
      show τ.1 (g.σ (H.rt : E)) = _
      rw [g.fix]
      exact τ.2⟩
  refine ⟨⟨F g, F g.symm, fun τ => ?_, fun τ => ?_⟩, fun _ => rfl, ?_⟩
  · refine Subtype.ext (RingHom.ext fun x => ?_)
    show τ.1 (g.σ (g.σ.symm x)) = τ.1 x
    rw [RingEquiv.apply_symm_apply]
  · refine Subtype.ext (RingHom.ext fun x => ?_)
    show τ.1 (g.σ.symm (g.σ x)) = τ.1 x
    rw [RingEquiv.symm_apply_apply]
  · rintro (τ | τ)
    · exact RingHom.ext fun x => Subtype.ext rfl
    · refine RingHom.ext fun x => Subtype.ext ?_
      show τ.1 ((g.s (H.bar x) : 𝓞 E) : E) = τ.1 ((H.bar (g.s x) : 𝓞 E) : E)
      rw [g.s_bar]

end PositivityTheory.UnitarySelfGeneration
end

-- bundled from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.FlagBundleIffUnderIsomorphism
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration

theorem flagiso_reg {X X' : Scheme.{0}} {Ω : Type} [Field Ω] (ξ' : Sp Ω ⟶ X') (e : X' ≅ X) (q : Cpt ξ')
    (h : genPt (ξ' ≫ e.hom) ⤳ e.hom q.1) : regAt ξ' q = regAt (ξ' ≫ e.hom) ⟨e.hom q.1, h⟩ := by
  have key : ∀ y, genMap (ξ' ≫ e.hom) ⟨e.hom q.1, h⟩ y = genMap ξ' q (e.hom.stalkMap q.1 y) := by
    intro y
    simp only [genMap, CommRingCat.comp_apply]
    rw [Scheme.stalkClosedPointTo_comp]
    simp only [CommRingCat.hom_comp, RingHom.comp_apply]
    exact congrArg (Scheme.stalkClosedPointTo ξ').hom
      (Scheme.Hom.stalkSpecializes_stalkMap_apply e.hom _ _ q.2 y)
  have hs : Function.Surjective (e.hom.stalkMap q.1) :=
    (ConcreteCategory.bijective_of_isIso (e.hom.stalkMap q.1)).2
  ext t
  simp only [regAt, RingHom.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := hs y
    exact ⟨z, key z⟩
  · rintro ⟨y, rfl⟩
    exact ⟨_, (key y).symm⟩

theorem flagiso_span {Ω V V' : Type} [Field Ω] [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω V']
    (φ : V ≃ₗ[Ω] V') (R R' : Subring Ω) (h : R' = R) (s : Set V) (v : V) :
    φ v ∈ Submodule.span R' (φ '' s) ↔ v ∈ Submodule.span R s := by
  subst h
  have hsp := Submodule.span_image (R := R') (φ.toLinearMap.restrictScalars R') (s := s)
  change Submodule.span R' (φ '' s) = _ at hsp
  rw [hsp, Submodule.mem_map]
  constructor
  · rintro ⟨w, hw, hwv⟩
    have hwv' : w = v := φ.injective hwv
    exact hwv' ▸ hw
  · intro hv
    exact ⟨v, hv, rfl⟩

theorem flagiso_step {Ω V V' : Type} [Field Ω] [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω V']
    (φ : V ≃ₗ[Ω] V') {r : ℕ} (b : Fin r → V) (i : ℕ) :
    flagStep Ω (fun k => φ (b k)) i = (flagStep Ω b i).map φ.toLinearMap := by
  simp only [flagStep, Submodule.map_span, Set.image_image]
  rfl

theorem flag_bundle_iff_under_isomorphism : ∀ (X X' : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω ⟶ X') (e : X' ≅ X) (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω V'] (φ : V ≃ₗ[Ω] V') (L : Lat ξ V) (L' : Lat ξ' V') (r : ℕ) (b : Fin r → V), ξ' ≫ e.hom = ξ → (∀ (q : Cpt ξ') (h : genPt ξ ⤳ e.hom q.1) (v : V), v ∈ L ⟨e.hom q.1, h⟩ ↔ φ v ∈ L' q) → (L.IsFlagVBOn Set.univ b ↔ L'.IsFlagVBOn Set.univ (fun i => φ (b i))) ∧ ∀ (i : Fin r) (q : Cpt ξ') (h : genPt ξ ⤳ e.hom q.1), (L'.gr (fun i => φ (b i)) i q : Set Ω) = L.gr b i ⟨e.hom q.1, h⟩ := by
  intro X X' Ω _ ξ ξ' e V V' _ _ _ _ φ L L' r b hξ hL
  subst hξ
  have hi : ∀ x : X', e.inv (e.hom x) = x := fun x => by simp
  have hj : ∀ y : X, e.hom (e.inv y) = y := fun y => by simp
  have hfwd : ∀ x : X', genPt ξ' ⤳ x → genPt (ξ' ≫ e.hom) ⤳ e.hom x := fun x hx =>
    e.hom.base.hom.map_specializes hx
  have hbwd : ∀ y : X, genPt (ξ' ≫ e.hom) ⤳ y → genPt ξ' ⤳ e.inv y := by
    intro y hy
    have h1 := e.inv.base.hom.map_specializes hy
    have h2 : e.inv (genPt (ξ' ≫ e.hom)) = genPt ξ' := hi _
    rw [← h2]
    exact h1
  have hframe : ∀ (q : Cpt ξ') (p : Cpt (ξ' ≫ e.hom)), e.hom q.1 = p.1 → ∀ c : Fin r → V,
      (L.IsFrameAt c p ↔ L'.IsFrameAt (fun k => φ (c k)) q) := by
    rintro q ⟨p, hp⟩ hqp c
    simp only at hqp
    subst hqp
    have hR := flagiso_reg ξ' e q hp
    have hli : LinearIndependent Ω (fun k => φ (c k)) ↔ LinearIndependent Ω c :=
      LinearMap.linearIndependent_iff φ.toLinearMap φ.ker
    have hset : φ '' Set.range c = Set.range (fun k => φ (c k)) := (Set.range_comp φ c).symm
    simp only [Lat.IsFrameAt, SetLike.ext_iff]
    rw [hli]
    apply and_congr_right
    intro _
    constructor
    · intro H w
      obtain ⟨v, rfl⟩ := φ.surjective w
      rw [← hset, flagiso_span φ _ _ hR, ← H v, hL q hp v]
    · intro H v
      rw [hL q hp v, H (φ v), ← hset, flagiso_span φ _ _ hR]
  have hstep : ∀ (c : Fin r → V) (i : ℕ),
      (flagStep Ω c i = flagStep Ω b i ↔
        flagStep Ω (fun k => φ (c k)) i = flagStep Ω (fun k => φ (b k)) i) := by
    intro c i
    rw [flagiso_step, flagiso_step]
    exact (Submodule.map_injective_of_injective φ.injective).eq_iff.symm
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro H q' -
    obtain ⟨U, hU, c, hc, hfr⟩ := H ⟨e.hom q'.1, hfwd _ q'.2⟩ trivial
    refine ⟨e.hom ⁻¹ᵁ U, hU, fun k => φ (c k), fun i => (hstep c i).1 (hc i), ?_⟩
    intro q₁ _ hq₁
    exact (hframe q₁ ⟨e.hom q₁.1, hfwd _ q₁.2⟩ rfl c).1 (hfr _ trivial hq₁)
  · rintro H p -
    obtain ⟨U', hU', c', hc', hfr'⟩ := H ⟨e.inv p.1, hbwd _ p.2⟩ trivial
    refine ⟨e.inv ⁻¹ᵁ U', hU', fun k => φ.symm (c' k), fun i => ?_, ?_⟩
    · rw [hstep]
      simpa using hc' i
    · intro q _ hq
      apply (hframe ⟨e.inv q.1, hbwd _ q.2⟩ q (hj q.1) (fun k => φ.symm (c' k))).2
      simpa using hfr' ⟨e.inv q.1, hbwd _ q.2⟩ trivial hq
  · intro i q h
    have hR := flagiso_reg ξ' e q h
    have hS : {t : Ω | ∃ w ∈ L' q, w - t • φ (b i) ∈ flagStep Ω (fun k => φ (b k)) i} =
        {t : Ω | ∃ v ∈ L ⟨e.hom q.1, h⟩, v - t • b i ∈ flagStep Ω b i} := by
      ext t
      simp only [Set.mem_setOf_eq]
      constructor
      · rintro ⟨w, hw, hwt⟩
        obtain ⟨v, rfl⟩ := φ.surjective w
        refine ⟨v, (hL q h v).2 hw, ?_⟩
        rw [flagiso_step] at hwt
        obtain ⟨y, hy, hyv⟩ := Submodule.mem_map.1 hwt
        have hyv' : y = v - t • b i := φ.injective (by simpa using hyv)
        exact hyv' ▸ hy
      · rintro ⟨v, hv, hvt⟩
        refine ⟨φ v, (hL q h v).1 hv, ?_⟩
        rw [flagiso_step]
        have hm := Submodule.mem_map_of_mem (f := φ.toLinearMap) hvt
        simpa using hm
    have key : ∀ (R₁ R₂ : Subring Ω), R₁ = R₂ → ∀ S : Set Ω,
        (Submodule.span R₁ S : Set Ω) = Submodule.span R₂ S := by
      rintro _ _ rfl _
      rfl
    simp only [Lat.gr]
    rw [hS]
    exact key _ _ hR _

end PositivityTheory.UnitarySelfGeneration
end

-- bundled from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.FlagDataMatchUnderTwist
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration

theorem fm_dualMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    dualMap (g.comp f) = (dualMap g).comp (dualMap f) := by
  ext a <;> simp [dualMap]

theorem fm_flagStep_map {Ω : Type} [Field Ω] {V V' : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup V']
    [Module Ω V'] (φ : V →ₗ[Ω] V') {r : ℕ} (b : Fin r → V) (k : ℕ) :
    (flagStep Ω b k).map φ = flagStep Ω (fun a => φ (b a)) k := by
  simp only [flagStep, Submodule.map_span, Set.image_image]

theorem fm_over {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f) {U : Over S'} (v w : U ⟶ t'.G)
    (h : v.left ≫ m.φ = w.left ≫ m.φ) : v = w :=
  Over.OverMorphism.ext (m.cart.1.hom_ext h (by rw [Over.w v, Over.w w]))
section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* c.F} {β' : O' →+* c.F}
  {g : HostAut H} {Φ : Xo.X ⟶ Xo.X} {n : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ} {Y : Model Xo c β}
  {Y' : Model Xo c β'} {T T' : Scheme.{0}} {u₁ : T ⟶ Y.t.G.left} {u₂ u₂' : T ⟶ Y'.t.G.left}

theorem fm_pre (a : T' ⟶ T) (h : TwTan n Y Y' u₁ u₂) : TwTan n Y Y' (a ≫ u₁) (a ≫ u₂) := by
  obtain ⟨u, u', h1, h2, h3, h4⟩ := h
  refine ⟨a ≫ u, a ≫ u', ?_, ?_, ?_, ?_⟩ <;> simp only [Category.assoc, h1, h2, h3, h4]

theorem fm_fun (hβ : Mono (spMap β)) (h : TwTan n Y Y' u₁ u₂) (h' : TwTan n Y Y' u₁ u₂') : u₂ = u₂' := by
  obtain ⟨u, u', h1, h2, h3, h4⟩ := h
  obtain ⟨v, v', k1, k2, k3, k4⟩ := h'
  have hmono : Mono (Y.jQ ≫ pullback.fst Y.s (spMap β)) := by
    have : IsOpenImmersion Y.jQ := Y.jQ_open
    infer_instance
  have e1 : ∀ z : T ⟶ Y.oF.t.G.left,
      z ≫ Y.oF.t.G.hom ≫ (Y.jQ ≫ pullback.fst Y.s (spMap β)) = (z ≫ Y.m.φ) ≫ Y.t.G.hom := by
    intro z
    rw [Category.assoc, Y.m.cart.1.w]
  have huv : u = v := by
    apply Y.m.cart.1.hom_ext
    · exact h1.trans k1.symm
    · rw [← cancel_mono (Y.jQ ≫ pullback.fst Y.s (spMap β)), Category.assoc, Category.assoc, e1, e1, h1, k1]
  subst huv
  have e2 : ∀ z : T ⟶ Y'.oF.t.G.left,
      z ≫ Y'.oF.t.G.hom ≫ pullback.fst _ _ = (z ≫ Y'.m0.φ) ≫ Xo.univ.t.G.hom := by
    intro z
    rw [Category.assoc, Y'.m0.cart.1.w]
  have hu' : u' = v' := by
    apply Y'.m0.cart.1.hom_ext
    · exact h3.trans k3.symm
    · apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, e2, e2, h3, k3]
      · rw [Category.assoc, Category.assoc]
        exact h4.trans k4.symm
  rw [← h2, ← k2, hu']
end

theorem flag_data_match_under_twist : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model Xo c β) (Y' : Model Xo c β') (g : HostAut H) (Φ : Xo.X ≅ Xo.X) (n : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ.hom) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S y) (A' : HodgeCpt Y' S y) (Fl : A.Flag) (Fl' : A'.Flag) (ψ : A'.Ω₀ ≃+* A.Ω₀) (θ : Fl.Li₀ ≃+ Fl'.Li₀) (φ : A.Li ≃ₗ[Ω] A'.Li), Mono (spMap β) → Mono (spMap β') → A.fn.comp ψ.toRingHom = A'.fn → (∀ w, TwTan n Y Y' ((A.M.pt w).left ≫ A.m.φ) ((A'.M.pt (φ w)).left ≫ A'.m.φ)) → (∀ e, TwTan n Y Y' (Fl.M₀.pt e).left (spMap (dualMap ψ.toRingHom) ≫ (Fl'.M₀.pt (θ e)).left)) → (∀ e, φ (Fl.j e) = Fl'.j (θ e)) ∧ ∀ s s' (r : ℕ) (b : Fin r → Fl.Li₀) (u : Matrix (Fin r) (Fin r) Ω), (∀ k, flagStep Ω (Fl.b s) k = flagStep Ω (fun a => ∑ q, u q a • Fl.j (b q)) k) → (∀ k, flagStep Ω (Fl'.b s') k = flagStep Ω (fun a => ∑ q, u q a • Fl'.j (θ (b q))) k) → ∀ k, (flagStep Ω (Fl.b s) k).map φ.toLinearMap = flagStep Ω (Fl'.b s') k := by
  intro E _ _ _ H D l Xo c O O' _ _ β β' Y Y' g Φ n S Ω _ K _ J y A A' Fl Fl' ψ θ φ hβ hβ' hfn hw he
  have hsp : spMap ((dualMap A.fn).comp (dualMap ψ.toRingHom)) =
      spMap (dualMap A.fn) ≫ spMap (dualMap ψ.toRingHom) := by
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  have hj : ∀ e, φ (Fl.j e) = Fl'.j (θ e) := by
    intro e
    apply A'.M.inj
    apply fm_over A'.m
    apply fm_fun hβ (hw (Fl.j e))
    rw [Fl.j_pt e, Fl'.j_pt (θ e), ← hfn, fm_dualMap_comp, hsp, Category.assoc]
    exact fm_pre _ (he e)
  refine ⟨hj, ?_⟩
  intro s s' r b u h1 h2 k
  rw [h1 k, h2 k, fm_flagStep_map]
  congr 1
  funext a
  simp [map_sum, map_smul, hj]

end PositivityTheory.UnitarySelfGeneration
end

-- bundled from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.MapMemDifferentIdealIff
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration

theorem map_mem_differentIdeal (E : Type) [Field E] [NumberField E] (s : 𝓞 E ≃+* 𝓞 E) (d : 𝓞 E)
    (hd : d ∈ differentIdeal ℤ (𝓞 E)) : s d ∈ differentIdeal ℤ (𝓞 E) := by
  have key : IsLocalization.coeSubmodule E (differentIdeal ℤ (𝓞 E)) =
      1 / Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := coeSubmodule_differentIdeal ℤ ℚ (𝓞 E)
  let τ : E ≃+* E := IsFractionRing.ringEquivOfRingEquiv (K := E) (L := E) s
  have hτ : ∀ b : 𝓞 E, τ (algebraMap (𝓞 E) E b) = algebraMap (𝓞 E) E (s b) :=
    fun b => IsFractionRing.ringEquivOfRingEquiv_algebraMap s b
  let τq : E ≃ₐ[ℚ] E := AlgEquiv.ofRingEquiv (f := τ) fun x => τ.toRingHom.map_rat_algebraMap x
  have htr : ∀ x : E, Algebra.trace ℚ E (τ x) = Algebra.trace ℚ E x :=
    fun x => Algebra.trace_eq_of_algEquiv τq x
  have h1 : ∀ a : E, a ∈ (1 : Submodule (𝓞 E) E) → τ a ∈ (1 : Submodule (𝓞 E) E) := by
    intro a ha
    obtain ⟨b, rfl⟩ := Submodule.mem_one.1 ha
    exact Submodule.mem_one.2 ⟨s b, (hτ b).symm⟩
  have hdual : ∀ y ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E),
      τ.symm y ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := by
    intro y hy
    rw [Submodule.mem_traceDual] at hy ⊢
    intro a ha
    have h2 := hy (τ a) (h1 a ha)
    rw [Algebra.traceForm_apply] at h2 ⊢
    rw [← htr, map_mul, RingEquiv.apply_symm_apply]
    exact h2
  have hd' : algebraMap (𝓞 E) E d ∈
      (1 / Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) : Submodule (𝓞 E) E) := by
    rw [← key]
    exact (IsLocalization.mem_coeSubmodule _ _).2 ⟨d, hd, rfl⟩
  have hs : algebraMap (𝓞 E) E (s d) ∈ IsLocalization.coeSubmodule E (differentIdeal ℤ (𝓞 E)) := by
    rw [key, Submodule.mem_div_iff_forall_mul_mem]
    intro y hy
    have h2 := (Submodule.mem_div_iff_forall_mul_mem.1 hd') (τ.symm y) (hdual y hy)
    have h3 := h1 _ h2
    rwa [map_mul, hτ, RingEquiv.apply_symm_apply] at h3
  obtain ⟨y, hy, hyd⟩ := (IsLocalization.mem_coeSubmodule _ _).1 hs
  rwa [IsFractionRing.injective (𝓞 E) E hyd] at hy

theorem map_mem_differentIdeal_iff : ∀ (E : Type) [Field E] [NumberField E] (s : 𝓞 E ≃+* 𝓞 E) (d : 𝓞 E), s d ∈ differentIdeal ℤ (𝓞 E) ↔ d ∈ differentIdeal ℤ (𝓞 E) := by
  intro E _ _ s d
  constructor
  · intro h
    have := map_mem_differentIdeal E s.symm (s d) h
    rwa [RingEquiv.symm_apply_apply] at this
  · exact map_mem_differentIdeal E s d

end PositivityTheory.UnitarySelfGeneration
end

