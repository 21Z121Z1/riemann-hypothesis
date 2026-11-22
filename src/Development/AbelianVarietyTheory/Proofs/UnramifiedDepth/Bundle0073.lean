import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0070
import Formalism.LocalToGlobal.CharacterGerms.Bundle0005
import Formalism.LocalToGlobal.CharacterGerms.Bundle0011
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EvalPowerSeriesEqOneOfTwoAxes
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.AlphaPair

section TwoAxes

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {d : ℕ}

theorem axes_monomial_sub_mem (I : Ideal A) (a : Fin d → A) (ha : ∀ j, a j ∈ I) (m : Fin d → ℕ) :
    (∏ j, a j ^ m j) - ∏ j, (0 : A) ^ m j ∈ I := by
  rw [← Ideal.Quotient.eq]
  simp only [map_prod, map_pow, Ideal.Quotient.eq_zero_iff_mem.2 (ha _), map_zero]

theorem axes_mul_eq_zero {e x y : A} (he : e ^ 2 = 0) (hx : x ∈ Ideal.span {e}) (hy : y ∈ Ideal.span {e}) :
    x * y = 0 := by
  obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.1 hx
  obtain ⟨v, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  linear_combination (u * v) * he

theorem evalPoints_second_difference (f : PS R 3 d) {e : A} (he : e ^ 2 = 0) (a a' b : Fin d → A)
    (ha : ∀ j, a j ∈ Ideal.span {e}) (ha' : ∀ j, a' j ∈ Ideal.span {e}) (hb : ∀ j, IsNilpotent (b j)) :
    evP ![a, a', b] f + evP ![0, 0, b] f = evP ![0, a', b] f + evP ![a, 0, b] f := by
  obtain ⟨N, hN0, hN⟩ := evBasic_exists_pow b hb
  have sq : ∀ x ∈ Ideal.span {e}, x ^ (N + 2) = 0 := fun x hx => by
    rw [pow_add, sq, axes_mul_eq_zero he hx hx, mul_zero]
  have key : ∀ c c' : Fin d → A, (∀ j, c j ∈ Ideal.span {e}) → (∀ j, c' j ∈ Ideal.span {e}) →
      evP ![c, c', b] f = ReciprocityTheory.PGsh.Be2.tEval (N + 2) f
        (fun q : Fin 3 × Fin d => ![c, c', b] q.1 q.2) := fun c c' hc hc' => by
    refine evBasic_nEval_eq_tEval f _ (N + 2) ?_
    rintro ⟨i, j⟩
    fin_cases i
    · exact sq _ (hc j)
    · exact sq _ (hc' j)
    · show b j ^ (N + 2) = 0
      rw [pow_add, hN, zero_mul]
  have h0 : ∀ j, (0 : Fin d → A) j ∈ Ideal.span {e} := fun _ => Ideal.zero_mem _
  rw [key a a' ha ha', key 0 0 h0 h0, key 0 a' h0 ha', key a 0 ha h0]
  unfold ReciprocityTheory.PGsh.Be2.tEval
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [Fintype.prod_prod_type, Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Pi.zero_apply]
  have h := axes_mul_eq_zero he (axes_monomial_sub_mem _ a ha fun j => m (0, j))
    (axes_monomial_sub_mem _ a' ha' fun j => m (1, j))
  rw [← mul_add, ← mul_add]
  congr 1
  linear_combination (∏ j, b j ^ (m (2, j) : ℕ)) * h

theorem evalPoints_eval_axis {u v : Fin d → PS R 2 d} {f : PS R 3 d}
    (hu : ∀ j, MvPowerSeries.constantCoeff (u j) = 0) (hv : ∀ j, MvPowerSeries.constantCoeff (v j) = 0)
    (h : ev (n := 2) ![u, v, pt R d 1] f = 1) (c b : Fin d → A)
    (hc : ∀ j, IsNilpotent (c j)) (hb : ∀ j, IsNilpotent (b j)) (x y : Fin d → A)
    (hx : ∀ j, evP ![c, b] (u j) = x j) (hy : ∀ j, evP ![c, b] (v j) = y j) :
    evP ![x, y, b] f = 1 := by
  have hn : ∀ q : Fin 2 × Fin d, IsNilpotent (![c, b] q.1 q.2) := by
    rintro ⟨i, j⟩
    fin_cases i
    · exact hc j
    · exact hb j
  have h1 := congrArg (evP ![c, b]) h
  unfold evP ev at h1
  rw [nEval_one hn, ChartCompare.nEval_subst _ _ _ _ hn] at h1
  · rw [← h1]
    unfold evP
    congr 1
    funext ⟨i, j⟩
    fin_cases i
    · exact (hx j).symm
    · exact (hy j).symm
    · exact (ChartCompare.nEval_X (R₀ := R) _ hn ((1 : Fin 2), j)).symm
  · rintro ⟨i, j⟩
    fin_cases i
    · exact hu j
    · exact hv j
    · exact MvPowerSeries.constantCoeff_X _

end TwoAxes

theorem evalPoints_eq_one_of_two_axes : ∀ (R : Type) [CommRing R] (d : ℕ) (ph : PS R 3 d), ev (n := 2) ![0, pt R d 0, pt R d 1] ph = 1 → ev (n := 2) ![pt R d 0, 0, pt R d 1] ph = 1 → ∀ (A : Type) [CommRing A] [Algebra R A] (e : A), e ^ 2 = 0 → ∀ a a' b : Fin d → A, (∀ j, a j ∈ Ideal.span {e}) → (∀ j, a' j ∈ Ideal.span {e}) → (∀ j, IsNilpotent (b j)) → evP ![a, a', b] ph = 1 := by
  intro R _ d ph h₁ h₂ A _ _ e he a a' b ha ha' hb
  have nil : ∀ c : Fin d → A, (∀ j, c j ∈ Ideal.span {e}) → ∀ j, IsNilpotent (c j) := fun c hc j =>
    ⟨2, by rw [sq, axes_mul_eq_zero he (hc j) (hc j)]⟩
  have hn : ∀ c : Fin d → A, (∀ j, c j ∈ Ideal.span {e}) →
      ∀ q : Fin 2 × Fin d, IsNilpotent (![c, b] q.1 q.2) := by
    rintro c hc ⟨i, j⟩
    fin_cases i
    · exact nil c hc j
    · exact hb j
  have e₁ : ∀ c : Fin d → A, (∀ j, c j ∈ Ideal.span {e}) → evP ![0, c, b] ph = 1 := fun c hc =>
    evalPoints_eval_axis (fun _ => map_zero _) (fun _ => MvPowerSeries.constantCoeff_X _) h₁ c b (nil c hc) hb 0 c
      (fun _ => ChartCompare.nEval_zero _ (hn c hc))
      (fun j => ChartCompare.nEval_X (R₀ := R) _ (hn c hc) ((0 : Fin 2), j))
  have e₂ : evP ![a, 0, b] ph = 1 :=
    evalPoints_eval_axis (fun _ => MvPowerSeries.constantCoeff_X _) (fun _ => map_zero _) h₂ a b (nil a ha) hb a 0
      (fun j => ChartCompare.nEval_X (R₀ := R) _ (hn a ha) ((0 : Fin 2), j))
      (fun _ => ChartCompare.nEval_zero _ (hn a ha))
  have h := evalPoints_second_difference ph he a a' b ha ha' hb
  rw [e₁ a' ha', e₂, e₁ 0 fun _ => Ideal.zero_mem _] at h
  exact add_right_cancel h

end GlobalTheory.AlphaPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsAlgClosedResidueFieldValuedField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.AlphaPair.ResField

variable {C : Type} [Field C] (V : VF C)

theorem nonneg (x : V.RR) : 0 ≤ V.v (x : C) := by
  have h : ((0 : ℝ) : WithTop ℝ) ≤ V.v (x : C) := x.2
  simpa using h

def mm : Ideal V.RR where
  carrier := {x | V.MM (x : C)}
  add_mem' := fun {x y} hx hy => V.v.map_lt_add hx hy
  zero_mem' := by simp [VF.MM]
  smul_mem' := fun c x hx => by
    show 0 < V.v ((c : C) * x)
    rw [V.v.map_mul]
    exact lt_of_lt_of_le hx (le_add_of_nonneg_left (nonneg V c))

theorem mm_isMaximal : (mm V).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  refine ⟨fun h => ?_, fun J x _ hx hxJ => ?_⟩
  · have h1 : 0 < V.v ((1 : V.RR) : C) := h
    simp at h1
  · have hx' : ¬ 0 < V.v (x : C) := hx
    have hx0 : V.v (x : C) = 0 := le_antisymm (not_lt.mp hx') (nonneg V x)
    have hne : (x : C) ≠ 0 := by
      intro h
      rw [h, AddValuation.map_zero] at hx0
      exact WithTop.top_ne_zero hx0
    have hinv : ((0 : ℝ) : WithTop ℝ) ≤ V.v ((x : C)⁻¹) := by
      rw [AddValuation.map_inv, hx0]
      simp
    let y : V.RR := ⟨(x : C)⁻¹, hinv⟩
    have hyx : y * x = 1 := Subtype.ext (by simp [y, hne])
    rw [← hyx]
    exact J.mul_mem_left y hxJ

theorem integers : (AddValuation.toValuation V.v).Integers V.RR where
  hom_inj := Subtype.val_injective
  map_le_one := fun r => by
    show 0 ≤ V.v (r : C)
    exact nonneg V r
  exists_of_le_one := fun {r} h => by
    have h' : 0 ≤ V.v r := h
    refine ⟨⟨r, ?_⟩, rfl⟩
    show ((0 : ℝ) : WithTop ℝ) ≤ V.v r
    simpa using h'

theorem isAlgClosed_of_surjective [IsAlgClosed C] {Ω : Type} [Field Ω] (ρ : V.RR →+* Ω)
    (hρ : Function.Surjective ρ) : IsAlgClosed Ω := by
  refine IsAlgClosed.of_exists_root Ω fun p hp hirr => ?_
  obtain ⟨q, hqmap, hqdeg, hqmon⟩ :=
    Polynomial.lifts_and_degree_eq_and_monic ((Polynomial.mem_lifts p).2 (Polynomial.map_surjective ρ hρ p)) hp
  have hdeg : (q.map (algebraMap V.RR C)).degree ≠ 0 := by
    rw [Polynomial.degree_map_eq_of_injective (integers V).hom_inj, hqdeg]
    exact (Polynomial.degree_pos_of_irreducible hirr).ne'
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root _ hdeg
  rw [Polynomial.IsRoot, Polynomial.eval_map] at hz
  have hint : IsIntegral V.RR z := ⟨q, hqmon, hz⟩
  obtain ⟨y, rfl⟩ := (integers V).exists_of_le_one ((integers V).mem_of_integral hint)
  rw [Polynomial.eval₂_at_apply] at hz
  have hy : q.eval y = 0 := (integers V).hom_inj (by rw [hz, map_zero])
  refine ⟨ρ y, ?_⟩
  rw [← hqmap, Polynomial.eval_map, Polynomial.eval₂_at_apply, hy, map_zero]

theorem exists_residueField : ∀ (C : Type) [Field C] (V : VF C), IsAlgClosed C → ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (_ : CharP Ω V.l) (ρ : V.RR →+* Ω), ∀ x : V.RR, ρ x = 0 ↔ V.MM (x : C) := by
  intro C _ V _
  have := mm_isMaximal V
  let _ : Field (V.RR ⧸ mm V) := Ideal.Quotient.field (mm V)
  have hl : ((V.l : ℕ) : V.RR ⧸ mm V) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (mm V)), Ideal.Quotient.eq_zero_iff_mem]
    show 0 < V.v (((V.l : ℕ) : V.RR) : C)
    have hc : (((V.l : ℕ) : V.RR) : C) = ((V.l : ℕ) : C) := by simp
    rw [hc, V.v_l]
    exact zero_lt_one
  have : CharP (V.RR ⧸ mm V) V.l := (CharP.charP_iff_prime_eq_zero V.l_prime).2 hl
  exact ⟨V.RR ⧸ mm V, inferInstance, isAlgClosed_of_surjective V _ Ideal.Quotient.mk_surjective,
    inferInstance, Ideal.Quotient.mk (mm V), fun x => Ideal.Quotient.eq_zero_iff_mem⟩

end GlobalTheory.AlphaPair.ResField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsIsTorusExtensionOnPointsModIdeal
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.TorExtPoints

variable {S S' : Scheme.{0}} {Ω : Type} [Field Ω]

theorem exists_lift {X Y : Scheme.{0}} (q : X ⟶ Y) [Smooth q] {A : Type} [CommRing A] [Algebra Ω A]
    (π : A →ₐ[Ω] Ω) (hn : IsNilpotent (RingHom.ker π)) (y : Sp A ⟶ Y) (x₀ : Sp Ω ⟶ X)
    (h : x₀ ≫ q = spMap (π : A →+* Ω) ≫ y) : ∃ x : Sp A ⟶ X, spMap (π : A →+* Ω) ≫ x = x₀ ∧ x ≫ q = y := by
  have hπ : Function.Surjective π := fun a => ⟨algebraMap Ω A a, π.commutes a⟩
  obtain ⟨U, V, hU, hV, hVU, -, hxV⟩ := exists_isAffineOpen_pair q (x₀ (closedPoint Ω)) (O := ⊤) trivial
  refine exists_lift_of_smooth_of_isAffineOpen q hU hV hVU (CommRingCat.ofHom (π : A →+* Ω)) y x₀ h ?_
    (range_subset_opens_of_isLocalRing x₀ hxV) ?_
  · rintro _ ⟨p, rfl⟩
    obtain ⟨z, hz⟩ : p ∈ Set.range (PrimeSpectrum.comap (π : A →+* Ω)) := by
      refine (range_comap_of_surjective _ (π : A →+* Ω) hπ).ge ?_
      obtain ⟨n, hn⟩ := hn
      exact (Ideal.IsPrime.pow_le_iff (P := p.asIdeal) (hP := p.isPrime) n.succ_ne_zero).1 (by
        rw [pow_succ]
        exact Ideal.mul_le_left.trans (hn.le.trans bot_le))
    obtain rfl : z = closedPoint Ω := Subsingleton.elim _ _
    have e : q (x₀ (closedPoint Ω)) = y (spMap (π : A →+* Ω) (closedPoint Ω)) := congr($h (closedPoint Ω))
    rw [← hz]
    exact e ▸ hVU hxV
  · intro R C _ _ _ _ _ _ p hp φ
    have hs : Function.Surjective p := fun c => (hπ c).imp fun b hb => (hp b).trans hb
    have hk : IsNilpotent (RingHom.ker p.toRingHom) := by
      convert hn using 1
      exact Ideal.ext fun b => Eq.congr_left (hp b)
    exact ⟨Algebra.FormallySmooth.liftOfSurjective φ p hs hk,
      Algebra.FormallySmooth.comp_liftOfSurjective φ p hs hk⟩

def torPt (s : Sp Ω ⟶ S) (X : Type) [AddCommGroup X] (A : Type) [CommRing A] [Algebra Ω A] :
    (overAt s A ⟶ splitTorus S X) ≃* (Multiplicative X →* Aˣ) :=
  (splitTorusPointsEquiv S X (overAt s A)).trans
    (Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.toMulEquiv).monoidHomCongrRight

theorem torPt_nat (s : Sp Ω ⟶ S) (X : Type) [AddCommGroup X] {A A' : Type} [CommRing A] [Algebra Ω A]
    [CommRing A'] [Algebra Ω A'] (f : A →ₐ[Ω] A') (t : overAt s A ⟶ splitTorus S X) :
    torPt s X A' (homAt s f ≫ t) = (Units.map (f : A →* A')).comp (torPt s X A t) := by
  ext x
  change (Scheme.ΓSpecIso (CommRingCat.of A')).hom.hom
      (splitTorusPointsEquiv S X _ (homAt s f ≫ t) (Multiplicative.ofAdd x)).val =
    f ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
      (splitTorusPointsEquiv S X _ t (Multiplicative.ofAdd x)).val)
  rw [splitTorusPointsEquiv_val, splitTorusPointsEquiv_val, Over.comp_left, Scheme.Hom.comp_appTop]
  exact congr($(Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (f : A →+* A'))) _)

theorem isTorExt_of_kernel (s : Sp Ω ⟶ S) {G B : Over S} [GrpObj G] [GrpObj B] {X : Type} [AddCommGroup X]
    (i : splitTorus S X ⟶ G) (q : G ⟶ B) [IsMonHom i] [IsMonHom q] [Smooth q.left]
    (hk : IsPullback i (toUnit _) q η[B]) :
    IsTorExt s s G B X (fun A _ _ => IsMonHom.monoidHom q (overAt s A))
      (fun A _ _ => (IsMonHom.monoidHom i (overAt s A)).comp (torPt s X A).symm.toMonoidHom) := by
  refine ⟨fun A A' _ _ _ _ f x => Category.assoc _ x q, fun A A' _ _ _ _ f χ => ?_, fun A _ _ χ χ' h => ?_,
    fun A _ _ x => ⟨fun h => ?_, ?_⟩, fun A _ _ π hn y hy => ?_⟩
  · obtain ⟨t, rfl⟩ := (torPt s X A).surjective χ
    rw [← torPt_nat]
    change (torPt s X A').symm _ ≫ i = _ ≫ (torPt s X A).symm _ ≫ i
    rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply, Category.assoc]
  · exact (torPt s X A).symm.injective (hk.hom_ext h (toUnit_unique _ _))
  · refine ⟨torPt s X A (hk.lift x (toUnit _) h), ?_⟩
    change (torPt s X A).symm _ ≫ i = _
    rw [MulEquiv.symm_apply_apply]
    exact hk.lift_fst _ _ _
  · rintro ⟨χ, rfl⟩
    change (_ ≫ i) ≫ q = toUnit _ ≫ η[B]
    rw [Category.assoc, hk.w, ← Category.assoc, toUnit_unique (_ ≫ _) (toUnit _)]
  · have h1 : (1 : overAt s Ω ⟶ G) ≫ q = homAt s π ≫ y := (map_one (IsMonHom.monoidHom q _)).trans hy.symm
    obtain ⟨x, hx, hq⟩ := exists_lift q.left π hn y.left (1 : overAt s Ω ⟶ G).left (congrArg (·.left) h1)
    exact ⟨Over.homMk x (by rw [← Over.w q, reassoc_of% hq]; exact Over.w y), Over.OverMorphism.ext hx,
      Over.OverMorphism.ext hq⟩

theorem exists_ptEquiv {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G f φ) (T : Over S') {t : T.left ⟶ S} (ht : t = T.hom ≫ f) :
    ∃ E : (T ⟶ G') ≃* (Over.mk t ⟶ G), ∀ x, (E x).left = x.left ≫ φ := by
  subst ht
  refine ⟨MulEquiv.ofBijective (pushHom h T) ⟨fun x y e => Over.OverMorphism.ext
    (h.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w])), fun x => ?_⟩, fun _ => rfl⟩
  exact ⟨Over.homMk (h.1.lift x.left T.hom (Over.w x)) (h.1.lift_snd _ _ _),
    Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩

theorem exists_isTorExt_of_pullback {G B : Over S} {G' B' : Over S'} [GrpObj G] [GrpObj G'] [GrpObj B] [GrpObj B']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} {ψ : B'.left ⟶ B.left} (hG : IsGrpPullback G' G f φ)
    (hB : IsGrpPullback B' B f ψ) {s' : Sp Ω ⟶ S'} {s : Sp Ω ⟶ S} (hs : s' ≫ f = s) {X : Type} [AddCommGroup X]
    {τ' : PtHom s' s' G' B'} {io' : TorHom s' G' X} (h : IsTorExt s' s' G' B' X τ' io') :
    ∃ (τ : PtHom s s G B) (io : TorHom s G X), IsTorExt s s G B X τ io ∧
      ∀ (A : Type) [CommRing A] [Algebra Ω A] (x : overAt s A ⟶ G), ∃ x' : overAt s' A ⟶ G',
        x'.left ≫ φ = x.left ∧ (τ A x).left = (τ' A x').left ≫ ψ := by
  have ht : ∀ (A : Type) [CommRing A] [Algebra Ω A], spMap (algebraMap Ω A) ≫ s = (overAt s' A).hom ≫ f :=
    fun A _ _ => by rw [← hs]; exact (Category.assoc _ _ _).symm
  choose E hE using fun (A : Type) [CommRing A] [Algebra Ω A] => exists_ptEquiv hG (overAt s' A) (ht A)
  choose F hF using fun (A : Type) [CommRing A] [Algebra Ω A] => exists_ptEquiv hB (overAt s' A) (ht A)
  have nE : ∀ (A A' : Type) [CommRing A] [Algebra Ω A] [CommRing A'] [Algebra Ω A'] (g : A →ₐ[Ω] A')
      (x : overAt s' A ⟶ G'), E A' (homAt s' g ≫ x) = homAt s g ≫ E A x := fun A A' _ _ _ _ g x =>
    Over.OverMorphism.ext ((hE A' _).trans ((Category.assoc _ x.left φ).trans
      (congrArg (spMap (g : A →+* A') ≫ ·) (hE A x).symm)))
  have nF : ∀ (A A' : Type) [CommRing A] [Algebra Ω A] [CommRing A'] [Algebra Ω A'] (g : A →ₐ[Ω] A')
      (x : overAt s' A ⟶ B'), F A' (homAt s' g ≫ x) = homAt s g ≫ F A x := fun A A' _ _ _ _ g x =>
    Over.OverMorphism.ext ((hF A' _).trans ((Category.assoc _ x.left ψ).trans
      (congrArg (spMap (g : A →+* A') ≫ ·) (hF A x).symm)))
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := h
  refine ⟨fun A _ _ => ((F A).toMonoidHom.comp (τ' A)).comp (E A).symm.toMonoidHom,
    fun A _ _ => (E A).toMonoidHom.comp (io' A),
    ⟨fun A A' _ _ _ _ g x => ?_, fun A A' _ _ _ _ g χ => ?_, fun A _ _ => (E A).injective.comp (h₃ A),
      fun A _ _ x => ?_, fun A _ _ π hn y hy => ?_⟩, fun A _ _ x => ?_⟩
  · obtain ⟨x, rfl⟩ := (E A).surjective x
    change F A' (τ' A' ((E A').symm _)) = _ ≫ F A (τ' A ((E A).symm _))
    rw [← nE, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply, h₁, nF]
  · change E A' (io' A' _) = _ ≫ E A (io' A χ)
    rw [h₂, nE]
  · obtain ⟨x, rfl⟩ := (E A).surjective x
    change F A (τ' A ((E A).symm _)) = 1 ↔ ∃ χ, E A (io' A χ) = _
    rw [MulEquiv.symm_apply_apply, MulEquiv.map_eq_one_iff, h₄]
    exact exists_congr fun χ => (E A).injective.eq_iff.symm
  · obtain ⟨y, rfl⟩ := (F A).surjective y
    rw [← nF, MulEquiv.map_eq_one_iff] at hy
    obtain ⟨x, hx, rfl⟩ := h₅ A π hn y hy
    refine ⟨E A x, by rw [← nE, hx, map_one], ?_⟩
    change F A (τ' A ((E A).symm _)) = _
    rw [MulEquiv.symm_apply_apply]
  · refine ⟨(E A).symm x, (hE A _).symm.trans ?_, hF A _⟩
    rw [MulEquiv.apply_symm_apply]

theorem exists_isTorExt : ∀ (W : Type) [CommRing W] [IsDomain W] (I : Ideal W) (D : Out.DegPre W) (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G] (gt : Out.GtCoord I D 0 G) (Ω : Type) [Field Ω] (β : W →+* Ω), (∀ a ∈ I, β a = 0) → ∃ (τ : PtHom (spMap β) (spMap β) G D.P.A) (io : TorHom (spMap β) G D.X), IsTorExt (spMap β) (spMap β) G D.P.A D.X τ io ∧ ∀ (A : Type) [CommRing A] [Algebra Ω A] (x : overAt (spMap β) A ⟶ G) (x₀ : Sp A ⟶ (Out.thickObj W I 0 G).left), x₀ ≫ (Out.fstG I 0 G).left = x.left → (τ A x).left = x₀ ≫ gt.pG.left := by
  intro W _ _ I D G _ _ g Ω _ β hβ
  let β₀ : W ⧸ I ^ (0 + 1) →+* Ω := Ideal.Quotient.lift _ β (by simpa using hβ)
  have e : spMap β₀ ≫ Out.thick W I 0 = spMap β := by
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    rfl
  have := g.q_hom
  have := g.i_hom
  have := g.q_flat
  have := g.q_surj
  have := g.q_affine
  have := (H1.torus_dim (Sp (W ⧸ I ^ (0 + 1))) D.X).smooth
  have : Smooth g.q.left := by
    refine MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      ((H1.torsor_pullback g.i g.q g.isKernel).map (Over.forget _)).flip
      ⟨⟨‹_›, ‹_›⟩, inferInstanceAs (QuasiCompact g.q.left)⟩ ?_
    exact smooth_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) this
  obtain ⟨τ, io, h, hτ⟩ := exists_isTorExt_of_pullback (isGrpPullback_pullback G (Out.thick W I 0))
    (isGrpPullback_pullback D.P.A (Out.thick W I 0)) e (isTorExt_of_kernel (spMap β₀) g.i g.q g.isKernel)
  refine ⟨τ, io, h, fun A _ _ x x₀ hx => ?_⟩
  obtain ⟨x', h₁, h₂⟩ := hτ A x
  have : IsClosedImmersion (Out.thick W I 0) := .spec_of_surjective _ Ideal.Quotient.mk_surjective
  obtain rfl : x₀ = x'.left := (cancel_mono (pullback.fst G.hom (Out.thick W I 0))).1 (hx.trans h₁.symm)
  exact h₂.trans (Category.assoc _ _ _)

end GlobalTheory.TorExtPoints
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsRingHomValuationRingOfEmbOK
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem embOK_exists_ringHom :
    ∀ (T : CDVR) (C : Type) [Field C] [CharZero C] (V : VF C) (ι' : T.Fr →+* C), EmbOK T V ι' → ∃ j : T.V →+* V.RR, (∀ x, (j x : C) = ι' (algebraMap T.V T.Fr x)) ∧ ∀ x ∈ maximalIdeal T.V, V.MM (j x : C) := by
  intro T C _ _ V ι' h
  have hnn : ∀ a : T.V, 0 ≤ vV T.V (algebraMap T.V T.Fr a) := by
    intro a
    unfold vV
    by_cases ha : valV T.V (algebraMap T.V T.Fr a) = 0
    · simp [ha]
    have h1 : valV T.V (algebraMap T.V T.Fr a) ≤ 1 :=
      IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ a
    have := (WithZero.log_le_log ha one_ne_zero).2 h1
    simp at this
    omega
  have hl0 : vV T.V ((V.l : ℕ) : T.Fr) ≠ 0 := by
    intro h0
    have hl : ((V.l : ℕ) : T.Fr) ≠ 0 := Nat.cast_ne_zero.2 V.l_prime.ne_zero
    have := h _ hl
    rw [map_natCast, V.v_l, h0] at this
    simp at this
  have hl : (0 : ℝ) < (vV T.V ((V.l : ℕ) : T.Fr) : ℝ) := by
    have h0 := hnn (V.l : T.V)
    rw [map_natCast] at h0
    exact_mod_cast lt_of_le_of_ne h0 hl0.symm
  have hR : ∀ x : T.V, (ι'.comp (algebraMap T.V T.Fr)) x ∈ V.RR := by
    intro x
    show V.Ge 0 (ι' (algebraMap T.V T.Fr x))
    by_cases h0 : algebraMap T.V T.Fr x = 0
    · rw [h0, map_zero]; exact VF.Ge.zero 0
    unfold VF.Ge
    rw [h _ h0]
    exact WithTop.coe_le_coe.2 (div_nonneg (by exact_mod_cast hnn x) hl.le)
  refine ⟨(ι'.comp (algebraMap T.V T.Fr)).codRestrict V.RR hR, fun x => rfl, fun x hx => ?_⟩
  have key : ((0 : ℝ) : WithTop ℝ) < V.v (ι' (algebraMap T.V T.Fr x)) := by
    by_cases h0 : algebraMap T.V T.Fr x = 0
    · rw [h0, map_zero, V.v.map_zero]; exact WithTop.coe_lt_top _
    rw [h _ h0]
    have h2 : valV T.V (algebraMap T.V T.Fr x) < 1 := by
      unfold valV
      rw [IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem]
      exact hx
    have h3 := (WithZero.log_lt_log (valV_ne_zero h0) one_ne_zero).2 h2
    have h4 : 0 < vV T.V (algebraMap T.V T.Fr x) := by
      simp at h3
      unfold vV
      omega
    exact WithTop.coe_lt_coe.2 (div_pos (by exact_mod_cast h4) hl)
  exact key

end GlobalTheory
end

