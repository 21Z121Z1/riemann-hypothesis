import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0008
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0007
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0009
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.NonvanishingDense
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0001
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0038
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0017

-- bundled from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.DenseNonvan
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace PositivityTheory.UnitarySelfGeneration

open HolomorphicMinorCharts in
theorem isClosed_res {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)} {e : ℕ}
    (R : AnLogRes P J e) : IsClosed {q : R.X × ((Σ k, ι k) → ℂ) | Minors (R.lift q.1 q.1) q.2} :=
  isClosed_minors (U := R.U) (lam := R.lift) (V := fun _ : (Σ k, ι k) → ℂ => Set.univ)
    (mu := fun _ w => w) (fun x => ⟨R.isOpen_U x, R.mem_U x⟩)
    (fun x p => holo_continuousAt (R.holo x p) (R.mem_U x)) R.compat (fun _ => ⟨isOpen_univ, trivial⟩)
    (fun _ p => (continuous_apply p).continuousAt) (fun _ _ w _ => so_refl w)

open HolomorphicMinorCharts in
theorem dense_nonvan {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)} {e : ℕ}
    (R : AnLogRes P J e) (hP : IsArithVar P (e + 1)) {g : MRing ι} {a : K → ℕ} (hg : IsMultiHomog g a) (hgP : g ∉ P) :
    Dense {x | eval (R.lift x x) (map (Int.castRingHom ℂ) g) ≠ 0} := by
  rw [dense_iff_inter_open]
  rintro N hN ⟨x₀, hx₀⟩
  obtain ⟨x, hxN, hxJ⟩ : ∃ x ∈ N, R.lift x x ∉ mcPts J := by
    by_contra h
    push Not at h
    obtain ⟨j, hj⟩ := R.A.cover x₀
    have h1 := ((R.A.chart j).isOpen_inter_preimage_symm hN).measure_pos MeasureTheory.volume
      ⟨R.A.chart j x₀, (R.A.chart j).map_source hj, by rwa [Set.mem_preimage, (R.A.chart j).left_inv hj]⟩
    exact h1.ne' (MeasureTheory.measure_mono_null (fun w hw => Set.mem_inter hw.1 (h _ hw.2)) (R.null j))
  have hc := isClosedMap_snd_of_compactSpace _
    ((isClosed_res R).inter (hN.isClosed_compl.preimage continuous_fst))
  have hz := R.mem x x (R.mem_U x)
  have h1 := nonvanishing_dense K ι P (e + 1) g hP hgP hz
  obtain ⟨z, hz1, hz2, hz3⟩ := mem_closure_iff.mp h1 _ hc.isOpen_compl (by
    rintro ⟨⟨x', w⟩, ⟨h2, h3⟩, h4⟩
    obtain rfl : w = R.lift x x := h4
    obtain rfl := R.inj x x' hxJ (so_symm (so_of_minors h2 (R.mem _ _ (R.mem_U _)).1 hz.1))
    exact h3 hxN)
  obtain ⟨x', hx'⟩ := r_onto K ι P J e R hP z hz2
  refine ⟨x', ?_, fun h => hz3 ((eval_ne_so hg hx').mp h)⟩
  by_contra h
  exact hz1 ⟨(x', z), ⟨minors_of_so hx', h⟩, rfl⟩

open HolomorphicMinorCharts in
theorem r_pull : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K₁ : Type) [Fintype K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)] (κ₁ : K₁ → K) (v₁ : (Σ k, ι₁ k) → Σ k, ι k) (P J : Ideal (MRing ι)) (D : ℕ) (σ : Type) (S : AnSys D σ) (Re : Realis S (imageZ v₁ P)) (R : AnLogRes P J D), IsBlockMap κ₁ v₁ → IsArithVar P (D + 1) → AlgOver Re → ∃ (π : R.X → S.X) (hπ : HoloMap R.A S.A π), (∀ (x : R.X) (x₁ : Re.R.X), SameOrbit (Re.R.lift x₁ x₁) (fun p => R.lift x x (v₁ p)) → π x = Re.π x₁) ∧ (∀ a (ref' : HermLine ι), IsPullHerm κ₁ v₁ (Re.ref a) ref' → SamePot R.A Set.univ (potOf R ref') ((S.th a).pullback π hπ.1)) ∧ (∀ a t, 0 < t → t ≤ S.t₀ → ∀ x, Real.log ((Re.line a t).h fun p => R.lift x x (v₁ p)) = Real.log ((Re.ref a).h fun p => R.lift x x (v₁ p)) + S.phT a t (π x)) ∧ ∃ (β : MRing ι) (b : K → ℕ), IsMultiHomog β b ∧ β ∉ P ∧ ∀ x, π x ∈ bdry S.s → evC (R.lift x x) β = 0 := by
  intro K _ ι _ K₁ _ ι₁ _ κ₁ v₁ P J D σ S Re R hv₁ hP hA
  obtain ⟨K₀, _, ι₀, _, κ, v, U, lam, β₀, b₀, hv, hE, hπ₁, hβ, hβP, hβ0⟩ := hA
  obtain ⟨-, hsm, hm₁, hev₁⟩ := j_pull K₁ ι₁ K ι κ₁ v₁ hv₁
  obtain ⟨-, -, hm₀, hev₀⟩ := j_pull K₀ ι₀ K₁ ι₁ κ v hv
  have hmem : ∀ x, ∀ y ∈ R.U x, (fun p => R.lift x y (v₁ p)) ∈ mcPts (imageZ v₁ P) := fun x y hy =>
    hm₁ P _ (R.mem x y hy)
  obtain ⟨π, hπ, hπo⟩ := r_holmap K₀ ι₀ _ D D S.X R.X S.A R.A U lam R.U (fun x y p => R.lift x y (v₁ (v p))) hE
    (fun x => ⟨R.isOpen_U x, R.mem_U x⟩) (fun x p => R.holo x _) (fun x y hy => hm₀ _ _ (hmem x y hy))
    (fun x x' y hy => so_pull hv (so_pull hv₁ (R.compat x x' y hy)))
  have c1 : ∀ (x : R.X) (x₁ : Re.R.X), SameOrbit (Re.R.lift x₁ x₁) (fun p => R.lift x x (v₁ p)) → π x = Re.π x₁ :=
    fun x x₁ h => hE.inj _ _ (so_trans (hπo x) (so_symm (so_trans (hπ₁ x₁) (so_pull hv h))))
  choose ρ hρ using fun x => r_onto K₁ ι₁ _ Re.J D Re.R Re.arith _ (hmem x x (R.mem_U x))
  refine ⟨π, hπ, c1, fun a ref' hr => ?_, fun a t ht ht' x => ?_, ?_⟩
  · obtain ⟨f, af, hfJ, hfP, hf⟩ := exists_homog_not_mem Re.R.homog Re.R.nondeg
    obtain ⟨bf, hbf⟩ := homog_rename hv₁ hf
    have hO := isOpen_nonvan R hbf
    refine r_pluri D R.X R.A _ _ _ (isPotential_potOf R (hsm _ _ hr (Re.ref_smooth a)))
      (isPotentialPullback S.A R.A π hπ _ (S.sing a).1) hO (dense_nonvan R hP hbf hfP) fun x hx => ?_
    set O := {x | eval (R.lift x x) (map (Int.castRingHom ℂ) (rename v₁ f)) ≠ 0} with hOd
    have hoff : ∀ y ∈ O, Re.R.lift (ρ y) (ρ y) ∉ mcPts Re.J := fun y hy h =>
      hy ((hev₁ (R.lift y y) f).trans ((eval_ne_so hf (hρ y)).mp (h.2 f hfJ)))
    have hcl := isClosed_minors (U := Re.R.U) (lam := Re.R.lift) (V := R.U) (mu := fun x y p => R.lift x y (v₁ p))
      (fun x => ⟨Re.R.isOpen_U x, Re.R.mem_U x⟩) (fun x p => holo_continuousAt (Re.R.holo x p) (Re.R.mem_U x))
      Re.R.compat (fun x => ⟨R.isOpen_U x, R.mem_U x⟩) (fun x p => holo_continuousAt (R.holo x _) (R.mem_U x))
      (fun x x' y hy => so_pull hv₁ (R.compat x x' y hy))
    have hcont : ∀ y ∈ O, ContinuousAt ρ y := fun y hy =>
      continuousAt_of_closed_rel hcl (fun y => minors_of_so (hρ y)) fun x' hx' =>
        (Re.R.inj _ _ (hoff y hy) (so_trans (hρ y) (so_symm
          (so_of_minors hx' (Re.R.mem _ _ (Re.R.mem_U _)).1 (hmem y y (R.mem_U y)).1)))).symm
    have hso : ∀ x' x₁ y, y ∈ R.U x' → ρ y ∈ Re.R.U x₁ →
        SameOrbit (Re.R.lift x₁ (ρ y)) fun p => R.lift x' y (v₁ p) := fun x' x₁ y h1 h2 =>
      so_trans (Re.R.compat _ _ _ ⟨h2, Re.R.mem_U _⟩) (so_trans (hρ y) (so_pull hv₁ (R.compat _ _ _ ⟨R.mem_U _, h1⟩)))
    have han : ∀ y ∈ O, ∀ j k, y ∈ (R.A.chart j).source → ρ y ∈ (Re.R.A.chart k).source →
        AnalyticAt ℂ (Re.R.A.chart k ∘ ρ ∘ (R.A.chart j).symm) (R.A.chart j y) := fun y hy j k hj hk =>
      analyticAt_factor (U := Re.R.U (ρ y)) (lam := Re.R.lift (ρ y)) (V := R.U y)
        (mu := fun w p => R.lift y w (v₁ p)) (Re.R.holo _) (Re.R.mem_U _) (fun p => R.holo y _) (R.mem_U y)
        (hcont y hy) (Re.R.mem _ _ (Re.R.mem_U _)).1 (Re.R.immersion _ (hoff y hy))
        (by
          filter_upwards [(R.isOpen_U y).mem_nhds (R.mem_U y),
            hcont y hy ((Re.R.isOpen_U _).mem_nhds (Re.R.mem_U (ρ y)))] with w h1 h2
          exact hso _ _ _ h1 h2) j k hj hk
    obtain ⟨V₁, hV₁, hxV₁, G₁, hG₁, hE₁⟩ := Re.ref_pot a (ρ x) trivial
    have hN : IsOpen (R.U x ∩ (O ∩ ρ ⁻¹' (V₁ ∩ Re.R.U (ρ x)))) := (R.isOpen_U x).inter
      (ContinuousOn.isOpen_inter_preimage (fun y hy => (hcont y hy).continuousWithinAt) hO
        (hV₁.inter (Re.R.isOpen_U _)))
    obtain ⟨W, hW, hxW, hWN, G, hG, hEG⟩ := orbit_re (A := R.A) (Re.ref a) hN
      (lam := fun y p => R.lift x y (v₁ p)) (mu := fun y => Re.R.lift (ρ x) (ρ y))
      (fun p => holo_mono (R.holo x _) Set.inter_subset_left)
      (fun p => holo_comp (Re.R.holo (ρ x) p) (fun y hy => hy.2.2.2) (fun y hy => hcont y hy.2.1)
        fun y hy => han y hy.2.1)
      (fun y hy => (Re.R.mem _ _ hy.2.2.2).1) (fun y hy => so_symm (hso _ _ _ hy.1 hy.2.2.2))
      (x := x) ⟨R.mem_U x, hx, hxV₁, Re.R.mem_U _⟩
    have hG₂ : R.A.HoloOn W fun y => G₁ (ρ y) := holo_comp hG₁ (fun y hy => (hWN hy).2.2.1)
      (fun y hy => hcont y (hWN hy).2.1) fun y hy => han y (hWN hy).2.1
    refine ⟨W, hW, hxW, fun y => G y + G₁ (ρ y), fun j w hw => (hG j w hw).add (hG₂ j w hw), fun y hy => ?_⟩
    have a1 := hEG y hy
    have a2 := hE₁ _ (hWN hy).2.2.1
    simp only [potOf, LocPot.pullback] at a1 a2 ⊢
    rw [hr.2, c1 x _ (hρ x), c1 y _ (hρ y), Complex.add_re]
    linarith
  · have h1 := Re.line_eq a t ht ht' (ρ x)
    obtain ⟨c, hc, h⟩ := hρ x
    have hnz := (hmem x x (R.mem_U x)).1
    rw [h, log_h_orbit _ hc hnz, log_h_orbit _ hc hnz, Re.line_deg] at h1
    rw [c1 x _ (hρ x)]
    linarith
  · obtain ⟨b₁, hb₁⟩ := homog_rename hv hβ
    obtain ⟨b, hb⟩ := homog_rename hv₁ hb₁
    refine ⟨_, b, hb, hβP, fun x hx => ?_⟩
    rw [hev₁, hev₀]
    exact (eval_ne_so hβ (hπo x)).mp (hβ0 _ hx)

end PositivityTheory.UnitarySelfGeneration
end

-- bundled from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.LieFree
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace PositivityTheory.UnitarySelfGeneration

theorem der_coords {B A R : Type} [CommRing B] [CommRing A] [CommRing R] [Nontrivial R] (c : B →+* A) (g : ℕ)
    (hc : c.IsStandardSmoothOfRelativeDimension g) (u : A →+* R) :
    ∃ d : Fin g → A → R, (∀ i a b, d i (a + b) = d i a + d i b) ∧
      (∀ i a b, d i (a * b) = u a * d i b + u b * d i a) ∧ (∀ i b, d i (c b) = 0) ∧
      (∀ e e' : Fin g → R, (∀ a, ∑ i, e i * d i a = ∑ i, e' i * d i a) → e = e') ∧
      ∀ δ : A → R, (∀ a b, δ (a + b) = δ a + δ b) → (∀ a b, δ (a * b) = u a * δ b + u b * δ a) →
        (∀ b, δ (c b) = 0) → ∃ e : Fin g → R, ∀ a, ∑ i, e i * d i a = δ a := by
  classical
  let _ := c.toAlgebra
  let _ := u.toAlgebra
  let _ := (u.comp c).toAlgebra
  have : IsScalarTower B A R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.IsStandardSmoothOfRelativeDimension g B A := hc
  have : Algebra.IsStandardSmooth B A := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth g
  have : Nontrivial A := u.domain_nontrivial
  have hr := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := B) (S := A) g
  have : Module.Finite A (KaehlerDifferential B A) := inferInstance
  let β : Module.Basis (Fin g) A (KaehlerDifferential B A) :=
    Module.finBasisOfFinrankEq A _ (Module.finrank_eq_of_rank_eq hr)
  have hsm : ∀ (a : A) (r : R), a • r = u a * r := fun a r => Algebra.smul_def a r
  have key : ∀ (e : Fin g → R) (w : KaehlerDifferential B A), ∑ i, e i * u (β.repr w i) = β.constr A e w := by
    intro e w
    rw [Module.Basis.constr_apply_fintype]
    exact Finset.sum_congr rfl fun i _ => by rw [hsm, mul_comm]; rfl
  refine ⟨fun i a => u (β.repr (KaehlerDifferential.D B A a) i), fun i a b => by simp, fun i a b => by simp,
    fun i b => ?_, fun e e' h => ?_, fun δ h1 h2 h3 => ?_⟩
  · have : KaehlerDifferential.D B A (c b) = 0 := Derivation.map_algebraMap _ b
    simp [this]
  · have h' : β.constr A e = β.constr A e' := by
      refine Derivation.liftKaehlerDifferential_unique _ _ (Derivation.ext fun a => ?_)
      simpa [key] using h a
    exact (β.constr A).injective h'
  · let D : Derivation B A R := Derivation.mk'
      { toFun := δ
        map_add' := h1
        map_smul' := fun b a => by
          rw [Algebra.smul_def, h2, RingHom.id_apply, Algebra.smul_def]
          have : δ (algebraMap B A b) = 0 := h3 b
          rw [this, mul_zero, add_zero]; rfl }
      (fun a b => by simpa [hsm] using h2 a b)
    refine ⟨fun i => D.liftKaehlerDifferential (β i), fun a => ?_⟩
    rw [key]
    have : β.constr A (fun i => D.liftKaehlerDifferential (β i)) = D.liftKaehlerDifferential :=
      β.ext fun i => by simp
    rw [this, Derivation.liftKaehlerDifferential_comp_D]
    rfl

theorem lie_free : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (g : ℕ), SmoothOfRelativeDimension g G.hom → ∀ (R : Type) [CommRing R] [IsLocalRing R] (x : Spec (CommRingCat.of R) ⟶ S) (E : Type) [AddCommGroup E] [Module R E] (M : LieModel G x E), Nonempty (Module.Basis (Fin g) R E) := by
  intro S G _ g hG R _ _ x E _ _ M
  let t : Spec (CommRingCat.of R) ⟶ G.left := (1 : Over.mk x ⟶ G).left
  obtain ⟨V, hV, U, hU, hq, hUV, hs⟩ :=
    hG.exists_isStandardSmoothOfRelativeDimension (t (IsLocalRing.closedPoint R))
  have hrange : Set.range t ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    rintro _ ⟨y, rfl⟩
    exact (IsLocalRing.specializes_closedPoint y).mem_open (t ⁻¹ᵁ U).isOpen hq
  let l := IsOpenImmersion.lift hU.fromSpec t hrange
  have hl : spMap (Spec.preimage l).hom = l := by simp [spMap]
  have h1 : (1 : Over.mk x ⟶ G).left = spMap (Spec.preimage l).hom ≫ hU.fromSpec := by
    rw [hl]; exact (IsOpenImmersion.lift_fac _ _ _).symm
  obtain ⟨d, d1, d2, d3, d4, d5⟩ := der_coords (G.hom.appLE V U hUV).hom g hs (Spec.preimage l).hom
  obtain ⟨M', -⟩ := PositivityTheory.HtPt.Htat.Lie.exists_lieModel (E := Fin g → R) G U V hU hV hUV R x _ h1
    (fun e a => ∑ i, e i * d i a)
    (fun e a b => by simp only [d1, mul_add, Finset.sum_add_distrib])
    (fun e a b => by
      simp only [d2, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring)
    (fun e b => by simp only [d3, mul_zero, Finset.sum_const_zero])
    (fun e e' a => by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib])
    (fun c e a => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => mul_assoc _ _ _) d4 d5
  obtain ⟨f, -, -⟩ := GlobalTheory.T.lie_model_existsUnique_equiv S G R x E (Fin g → R) M M'
  exact ⟨Module.Basis.ofEquivFun f⟩

end PositivityTheory.UnitarySelfGeneration
end

