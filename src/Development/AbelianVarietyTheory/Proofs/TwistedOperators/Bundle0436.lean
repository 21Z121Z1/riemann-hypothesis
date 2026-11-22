import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.UnitFramesGeneratorRatioModulusOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0093
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0028
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0092
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0059
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0428
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0024
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HkRelFrOfTransportIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0014
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0429
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0419
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0430
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsDerivAt0CompLinearIff
section
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.PullbackSections
noncomputable section

namespace GlobalTheory.ThetaWitness

theorem isDerivAt0_comp_linear_iff {g g' : ℕ} {X : Scheme.{0}} (e : (Fin g → ℂ) → (Sp ℂ ⟶ X))
    (he : IsHolTo Set.univ e) (L : (Fin g' → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (w : Fin g' → ℂ)
    (v : Sp (DualNumber ℂ) ⟶ X) : IsDerivAt0 (fun z => e (L z)) w v ↔ IsDerivAt0 e (L w) v := by
  have key : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = e 0 →
      ∀ (U : X.Opens) (_ : ⊤ ≤ v ⁻¹ᵁ U) (f : Γ(X, U)), fderiv ℂ (fun z => valAt' (e (L z)) U f) 0 w =
        fderiv ℂ (fun z => valAt' (e z) U f) 0 (L w) := by
    intro h0 U hU f
    have hmem : (0 : Fin g → ℂ) ∈ {b ∈ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ e b ⁻¹ᵁ U} := by
      refine ⟨trivial, ?_⟩
      rw [← h0]
      intro x _
      exact hU (Set.mem_univ _)
    have hd : DifferentiableAt ℂ (fun z => valAt' (e z) U f) 0 :=
      ((he U f).2 0 hmem).differentiableAt ((he U f).1.mem_nhds hmem)
    let L' := LinearMap.toContinuousLinearMap L
    have hd' : HasFDerivAt (fun z => valAt' (e z) U f) (fderiv ℂ (fun z => valAt' (e z) U f) 0) (L' 0) := by
      rw [map_zero]; exact hd.hasFDerivAt
    have := (hd'.comp (0 : Fin g' → ℂ) L'.hasFDerivAt).fderiv
    exact DFunLike.congr_fun this w
  unfold IsDerivAt0
  simp only [map_zero]
  exact and_congr_right fun h0 => forall_congr' fun U => forall_congr' fun hU => forall_congr' fun f => by
    rw [key h0 U hU f]

theorem ex_eq_of_der {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}} {t : SAB H S}
    {y₁ y₂ : Sp ℂ ⟶ S} (hy : y₁ = y₂) {D : Datum H} {g₁ g₂ : ℕ} {ty : Fin g₁ → (E →+* ℂ)}
    {P : D.La →+ (Fin g₁ → ℂ)} (hP : IsPeriod D ty P) {e₁ : (Fin g₁ → ℂ) → (Over.mk y₁ ⟶ t.G)}
    (he₁ : GlobalTheory.UnifPoint.IsExp e₁) (hk₁ : ∀ z, e₁ z = 1 ↔ z ∈ P.range)
    {e₂ : (Fin g₂ → ℂ) → (Over.mk y₂ ⟶ t.G)} (he₂ : GlobalTheory.UnifPoint.IsExp e₂) (hc₂ : {z | e₂ z = 1}.Countable)
    (L : (Fin g₁ → ℂ) ≃ₗ[ℂ] (Fin g₂ → ℂ))
    (huniq : ∀ w w' v, IsDerivAt0 (fun z => (e₁ z).left) w v → IsDerivAt0 (fun z => (e₁ z).left) w' v → w = w')
    (hb : ∀ a, ∃ v, IsDerivAt0 (fun z => (e₁ z).left) (Pi.single a 1) v ∧
      IsDerivAt0 (fun z => (e₂ z).left) (L (Pi.single a 1)) v) :
    ∀ z, (e₁ z).left = (e₂ (L z)).left := by
  subst hy
  have hL : Continuous L := L.toLinearMap.continuous_of_finiteDimensional
  have hLd : Differentiable ℂ L := (LinearMap.toContinuousLinearMap L.toLinearMap).differentiable
  have hhol : IsHolTo Set.univ (fun z => (e₂ (L z)).left) := fun U f => by
    obtain ⟨h1, h2⟩ := he₂.2.2.1 U f
    refine ⟨?_, ?_⟩
    · exact h1.preimage hL
    · refine h2.comp hLd.differentiableOn ?_
      intro z hz; exact ⟨trivial, hz.2⟩
  obtain ⟨h, hh⟩ := GlobalTheory.UnifPoint.exists_linearEquiv_of_period hP he₁ hk₁ (e₀ := fun z => e₂ (L z))
    (fun z w => by simp only [map_add]; exact he₂.1 _ _) (he₂.2.1.comp L.surjective) hhol
    (by
      refine (hc₂.preimage_of_injOn L.injective.injOn).mono ?_
      intro z hz; exact hz)
  have hid : ∀ a, h (Pi.single a 1) = Pi.single a 1 := fun a => by
    obtain ⟨v, h1, h2⟩ := hb a
    have d2 := (isDerivAt0_comp_linear_iff _ he₂.2.2.1 L.toLinearMap _ v).2 h2
    have d3 : IsDerivAt0 (fun z => (e₁ (h z)).left) (Pi.single a 1) v := by
      convert d2 using 2 with z
      rw [hh]; rfl
    have d4 := (isDerivAt0_comp_linear_iff _ he₁.2.2.1 h.toLinearMap _ v).1 d3
    exact huniq _ _ v d4 h1
  have hlin : h.toLinearMap = LinearMap.id :=
    LinearMap.pi_ext' fun a => LinearMap.ext_ring (by simpa using hid a)
  have hid' : ∀ z, h z = z := fun z => LinearMap.congr_fun hlin z
  intro z
  rw [← hh z, hid']

end GlobalTheory.ThetaWitness

namespace GlobalTheory.ThetaWitness

theorem theta_value_indep : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
    {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r) (k : U.Comp) (x : (U.X k).dom) (W₁ W₂ : UnfAt U k x)
    (Y₁ : UnitAt W₁) (Y₂ : UnitAt W₂) (v : Fin r → E),
    Complex.exp (-(Real.pi / 2 * hermForm Y₁.Hm (fun j => perFr (U.X k) x.1 v (relab c σ (W₁.e j).1) (W₁.e j).2)
        (fun j => perFr (U.X k) x.1 v (relab c σ (W₁.e j).1) (W₁.e j).2))) *
        Y₁.θ (fun j => perFr (U.X k) x.1 v (relab c σ (W₁.e j).1) (W₁.e j).2) =
      Complex.exp (-(Real.pi / 2 * hermForm Y₂.Hm (fun j => perFr (U.X k) x.1 v (relab c σ (W₂.e j).1) (W₂.e j).2)
        (fun j => perFr (U.X k) x.1 v (relab c σ (W₂.e j).1) (W₂.e j).2))) *
        Y₂.θ (fun j => perFr (U.X k) x.1 v (relab c σ (W₂.e j).1) (W₂.e j).2) := by
  intro E _ _ _ H Dw l Xo c σ r U k x W₁ W₂ Y₁ Y₂ v
  let L : (Fin W₁.g → ℂ) ≃ₗ[ℂ] (Fin W₂.g → ℂ) := LinearEquiv.funCongrLeft ℂ ℂ (W₂.e.trans W₁.e.symm)
  have hL : ∀ z j, L z j = z (W₁.e.symm (W₂.e j)) := fun z j => rfl
  have hLd : Differentiable ℂ L := (LinearMap.toContinuousLinearMap L.toLinearMap).differentiable
  have hp : (fun j => perFr (U.X k) x.1 v (relab c σ (W₂.e j).1) (W₂.e j).2) =
      L (fun j => perFr (U.X k) x.1 v (relab c σ (W₁.e j).1) (W₁.e j).2) := by
    funext j
    rw [hL]
    generalize hs : W₁.e (W₁.e.symm (W₂.e j)) = s
    rw [Equiv.apply_symm_apply] at hs
    subst hs; rfl
  rw [hp]
  generalize (fun j => perFr (U.X k) x.1 v (relab c σ (W₁.e j).1) (W₁.e j).2) = z

  have hPL : ∀ a, L (W₁.Pm a) = W₂.Pm ((W₂.φ k).symm (W₁.φ k a)) := fun a => by
    funext j
    rw [hL, W₁.pm_eq, W₂.pm_eq, LinearEquiv.apply_symm_apply]
    generalize hs : W₁.e (W₁.e.symm (W₂.e j)) = s
    rw [Equiv.apply_symm_apply] at hs
    subst hs; rfl
  have hEF : ∀ a b, (W₂.F.Di (W₂.ik k)).EF ((W₂.φ k).symm (W₁.φ k a)) ((W₂.φ k).symm (W₁.φ k b)) =
      (W₁.F.Di (W₁.ik k)).EF a b := fun a b => by
    have h1 := W₂.isom k ((W₂.φ k).symm (W₁.φ k a)) ((W₂.φ k).symm (W₁.φ k b))
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, ← W₁.isom k a b] at h1
    exact_mod_cast h1

  have hspan : Submodule.span ℝ (Set.range W₁.Pm) = ⊤ := W₁.per.2.2.2.1
  have hHH : ∀ z w, hermForm Y₂.Hm (L z) (L w) = hermForm Y₁.Hm z w := fun z w => by
    have := GlobalTheory.KeyFam.SamePeriod.hermForm_eq_of_im Y₂.Hm L.toLinearMap Y₁.Hm LinearMap.id hspan (by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      simp only [LinearEquiv.coe_coe, LinearMap.id_coe, id_eq]
      rw [hPL, hPL, Y₂.c1, Y₁.c1, hEF]) z w
    simpa using this

  have hexp : ∀ W : UnfAt U k x, GlobalTheory.UnifPoint.IsExp (W.F.ex (W.ik k) W.Pm) := fun W =>
    ⟨W.F.ex_add _ _ W.per, W.F.ex_onto _ _ W.per, GlobalTheory.ClassUniq.isHolTo_ex W.F _ _ W.per,
      (W.F.ex_diff _ _ W.per).1, (W.F.ex_diff _ _ W.per).2⟩
  have hLs : ∀ a, L (Pi.single a 1) = Pi.single (W₂.e.symm (W₁.e a)) 1 := fun a => by
    funext j
    rw [hL]
    simp only [Pi.single_apply]
    exact if_congr (by rw [Equiv.symm_apply_eq, Equiv.eq_symm_apply]) rfl rfl
  have hex : ∀ z, (W₁.F.ex (W₁.ik k) W₁.Pm z).left = (W₂.F.ex (W₂.ik k) W₂.Pm (L z)).left :=
    ex_eq_of_der (t := Xo.univ.t) (W₁.pt.symm.trans W₂.pt) W₁.per (hexp W₁) (W₁.F.ex_ker _ _ W₁.per) (hexp W₂)
      ((GlobalTheory.UnifPoint.countable_periods W₂.per).mono fun z hz => (W₂.F.ex_ker _ _ W₂.per z).1 hz) L
      (fun w w' v h h' => by
        have tn := GlobalTheory.isDerivAt0_ex_isTanAt _ _ _ _ Xo _ _ _ W₁.F (W₁.ik k) W₁.Pm W₁.per
        exact (tn.2.2 v (tn.1 w v h)).unique h h')
      (fun a => ⟨(U.un k x).u (W₁.e a).1 (W₁.e a).2, by simpa using W₁.der (W₁.e a).1 (W₁.e a).2, by
        rw [hLs]; simpa using W₂.der (W₁.e a).1 (W₁.e a).2⟩)

  have hper1 : ∀ a ∈ W₁.Pm.range, ∀ z, W₁.F.ex (W₁.ik k) W₁.Pm (z + a) = W₁.F.ex (W₁.ik k) W₁.Pm z :=
    fun a ha z => by
      rw [W₁.F.ex_add _ _ W₁.per, (W₁.F.ex_ker _ _ W₁.per a).2 ha]
      exact @_root_.mul_one _ (CategoryTheory.Hom.monoid).toMulOneClass _
  have hcov : ∀ z, ∃ j, ⊤ ≤ (W₁.F.ex (W₁.ik k) W₁.Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun z =>
    GlobalTheory.ThetaPtChg.exists_chart_point Xo.univ.t.PP.isLB _
  have tr : ∀ j z, ⊤ ≤ (W₁.F.ex (W₁.ik k) W₁.Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      ⊤ ≤ (W₂.F.ex (W₂.ik k) W₂.Pm (L z)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun j z hz => by rw [← hex]; exact hz
  have hspan' : Submodule.span ℝ (W₁.Pm.range : Set (Fin W₁.g → ℂ)) = ⊤ := by
    rw [AddMonoidHom.coe_range]; exact hspan
  have hfr : ∀ j z, ⊤ ≤ (W₁.F.ex (W₁.ik k) W₁.Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → Y₂.fr j (L z) = Y₁.fr j z :=
    GlobalTheory.UnitFrameGen.frames_eq W₁.Pm.range hspan' (fun j => {z | ⊤ ≤ (W₁.F.ex (W₁.ik k) W₁.Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j})
      (fun j => GlobalTheory.FamilyUnif_isOpen_ex W₁.F _ _ W₁.per _) hcov
      (fun j a ha z hz => by rw [Set.mem_setOf_eq, hper1 a ha]; exact hz)
      Y₁.fr (fun j z => Y₂.fr j (L z))
      (fun j j' z => valAt' (W₁.F.ex (W₁.ik k) W₁.Pm z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j')
        (Xo.univ.t.PP.L.g j j').val)
      (fun a z => Real.exp (Real.pi * (hermForm Y₁.Hm z a).re + Real.pi / 2 * (hermForm Y₁.Hm a a).re))
      Y₁.c2 (fun j => (Y₂.c2 j).comp hLd.differentiableOn fun z hz => tr j z hz) Y₁.c3
      (fun j j' z h1 h2 => Y₁.c4 j j' z ((GlobalTheory.top_le_preimage_inf _ _ _).2 ⟨h1, h2⟩))
      (fun j j' z h1 h2 => by
        have e2 := Y₂.c4 j j' (L z) ((GlobalTheory.top_le_preimage_inf _ _ _).2 ⟨tr _ _ h1, tr _ _ h2⟩)
        rw [← hex] at e2
        exact e2)
      (fun j hz => by
        have t0 := tr j 0 hz
        simp only [map_zero] at t0 ⊢
        rw [Y₁.c5 j hz, Y₂.c5 j t0])
      (by
        rintro j _ ⟨a, rfl⟩ z hz
        exact GlobalTheory.UnitFrameGen.norm_factor Y₁.Hm _ _ _ _ _ (Y₁.c6 a j z).1 ((Y₁.c6 a j z).2 hz))
      (by
        rintro j _ ⟨a, rfl⟩ z hz
        have := GlobalTheory.UnitFrameGen.norm_factor Y₂.Hm _ _ _ _ _ (Y₂.c6 ((W₂.φ k).symm (W₁.φ k a)) j (L z)).1
          ((Y₂.c6 ((W₂.φ k).symm (W₁.φ k a)) j (L z)).2 (tr j z hz))
        rw [← hPL, hHH, hHH, ← map_add] at this
        exact this)

  have hθ : Y₂.θ (L z) = Y₁.θ z := by
    obtain ⟨j, hj⟩ := hcov z
    have hw0 : (W₁.F.ex (W₁.ik k) W₁.Pm z).left ≫ Xo.univ.t.G.hom = (U.un k x).x :=
      (Over.w (W₁.F.ex (W₁.ik k) W₁.Pm z)).trans W₁.pt.symm
    let p : Over.mk (U.un k x).x ⟶ Xo.univ.t.G := Over.homMk (W₁.F.ex (W₁.ik k) W₁.Pm z).left hw0
    have e1 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_snd (𝟙 _) p)
    have e2 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_fst (𝟙 _) p)
    have v1 := Y₁.c7 j z _ e1 e2 hj
    have v2 := Y₂.c7 j (L z) _ (e1.trans (hex z)) e2 (tr j z hj)
    rw [hfr j z hj] at v2
    exact mul_right_cancel₀ (Y₁.c3 j z hj) (v2.symm.trans v1)
  rw [hHH, hθ]

end GlobalTheory.ThetaWitness
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieDividedHomTangentImageBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLieImg IsLinHom IsThGen IsHeckeIsog)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeckeLieBC

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

theorem epsMul_comp_epsMul {R : Type} [CommRing R] (a b : R) :
    (epsMul a).comp (epsMul b) = epsMul (a * b) :=
  RingHom.ext fun z => by
    ext <;> simp [epsMul, mul_smul]

theorem epsMul_one' {R : Type} [CommRing R] : epsMul (1 : R) = RingHom.id _ :=
  RingHom.ext fun z => by
    ext <;> simp [epsMul]

theorem spMap_epsMul_cancel {R : Type} [CommRing R] {u : R} (hu : IsUnit u) {Z : Scheme.{0}}
    {f g : Sp (DualNumber R) ⟶ Z} (h : spMap (epsMul u) ≫ f = spMap (epsMul u) ≫ g) : f = g := by
  obtain ⟨u, rfl⟩ := hu
  have e : spMap (epsMul ((u⁻¹ : Rˣ) : R)) ≫ spMap (epsMul (u : R)) = 𝟙 _ := by
    rw [GlobalTheory.Frames.ChgBC.spMap_comp_ring, epsMul_comp_epsMul, Units.inv_mul, epsMul_one',
      GlobalTheory.Frames.ChgBC.spMap_id]
  calc f = spMap (epsMul ((u⁻¹ : Rˣ) : R)) ≫ spMap (epsMul (u : R)) ≫ f := by
        rw [← Category.assoc, e, Category.id_comp]
    _ = g := by rw [h, ← Category.assoc, e, Category.id_comp]

end GlobalTheory.HeckeLieBC

namespace GlobalTheory.HeckeLieBC

open GlobalTheory.HeckeFrCompare (toFib_fst toFib_snd)

theorem lieImg_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (T Ω : Type) [CommRing T] [CommRing Ω] (χ : T →+* Ω) (x x' : Sp T ⟶ Xo.X)
    (x₁ x₁' : Sp Ω ⟶ Xo.X) (Ψ : Gx x ⟶ Gx x') (Ψ₁ : Gx x₁ ⟶ Gx x₁') (p : ℕ)
    (v w : Sp (DualNumber T) ⟶ Xo.univ.t.G.left) (w₁ : Sp (DualNumber Ω) ⟶ Xo.univ.t.G.left),
    IsUnit (p : Ω) → IsFib χ Ψ Ψ₁ → IsLieImg p Ψ v w → IsLieImg p Ψ₁ (spMap (dualMap χ) ≫ v) w₁ →
      w₁ = spMap (dualMap χ) ≫ w := by
  intro E _ _ _ H Dw l Xo T Ω _ _ χ x x' x₁ x₁' Ψ Ψ₁ p v w w₁ hp hF hL hL₁
  obtain ⟨pm, pm', hc, hc', hcomm, -⟩ := hF
  obtain ⟨-, -, a, ha, hw⟩ := hL
  obtain ⟨-, -, a₁, ha₁, hw₁⟩ := hL₁

  have hfib : GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori.toFib x₁ (spMap (algebraMap Ω (DualNumber Ω))) a₁ ≫ pm =
      spMap (dualMap χ) ≫ GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori.toFib x (spMap (algebraMap T (DualNumber T))) a := by
    apply GlobalTheory.Frames.ChgBC.gx_ext
    · rw [Category.assoc, hc.2.1, toFib_snd, Category.assoc, toFib_snd, ha₁, ha]
    · rw [Category.assoc, hc.2.2, GlobalTheory.HeckeFrCompare.toFib_fst_assoc, Category.assoc, toFib_fst,
        GlobalTheory.Frames.ChgBC.spMap_comp_ring, GlobalTheory.Frames.ChgBC.spMap_comp_ring, GlobalTheory.Frames.ChgBC.dualMap_alg]
  have hpush : GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori.push Ψ₁ (spMap (algebraMap Ω (DualNumber Ω))) a₁ =
      spMap (dualMap χ) ≫ GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori.push Ψ (spMap (algebraMap T (DualNumber T))) a := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori.push
    rw [← hc'.2.1, reassoc_of% hcomm, reassoc_of% hfib]
  apply spMap_epsMul_cancel hp
  rw [hw₁, hpush, ← hw, ← Category.assoc, ← Category.assoc, GlobalTheory.Frames.ChgBC.spMap_comp_ring,
    GlobalTheory.Frames.ChgBC.spMap_comp_ring, GlobalTheory.Frames.ChgBC.dualMap_eps, map_natCast]

end GlobalTheory.HeckeLieBC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieImageCompatibleWithBaseChange
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.LieImageBC

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) :=
  (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

theorem epi_of_local {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] (d : A →+* B)
    [IsLocalHom d] (hd : Function.Injective d) : Epi (spMap d) := by
  refine ⟨fun {X} a b h => ?_⟩
  obtain ⟨⟨x, f, hf⟩, rfl⟩ := (SpecToEquivOfLocalRing X (CommRingCat.of A)).symm.surjective a
  obtain ⟨⟨y, g, hg⟩, rfl⟩ := (SpecToEquivOfLocalRing X (CommRingCat.of A)).symm.surjective b
  have h1 : IsLocalHom (f ≫ CommRingCat.ofHom d).hom := by
    rw [CommRingCat.hom_comp]; exact RingHom.isLocalHom_comp d f.hom
  have h2 : IsLocalHom (g ≫ CommRingCat.ofHom d).hom := by
    rw [CommRingCat.hom_comp]; exact RingHom.isLocalHom_comp d g.hom
  have h3 : (SpecToEquivOfLocalRing X (CommRingCat.of B)).symm ⟨x, _, h1⟩ =
      (SpecToEquivOfLocalRing X (CommRingCat.of B)).symm ⟨y, _, h2⟩ := by
    simpa [SpecToEquivOfLocalRing] using h
  have h4 := (SpecToEquivOfLocalRing X (CommRingCat.of B)).symm.injective h3
  obtain rfl : x = y := congrArg Sigma.fst h4
  have h5 : f ≫ CommRingCat.ofHom d = g ≫ CommRingCat.ofHom d :=
    congrArg Subtype.val (eq_of_heq (Sigma.mk.inj h4).2)
  obtain rfl : f = g := by
    ext s
    exact hd (congrArg (fun k => k.hom s) h5)
  rfl

theorem epi_dualMap {K L : Type} [Field K] [Field L] (φ : K →+* L) : Epi (spMap (dualMap φ)) := by
  have : IsLocalHom (dualMap φ) := ⟨fun a ha => by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, isUnit_iff_ne_zero] at ha ⊢
    intro h
    exact ha (by simp [dualMap, h])⟩
  refine epi_of_local _ fun a b h => ?_
  have h1 := congrArg TrivSqZeroExt.fst h
  have h2 := congrArg TrivSqZeroExt.snd h
  ext
  · exact φ.injective (by simpa [dualMap] using h1)
  · exact φ.injective (by simpa [dualMap] using h2)

theorem dual_eps {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (a : S) :
    spMap (dualMap ψ) ≫ spMap (epsMul a) = spMap (epsMul (ψ a)) ≫ spMap (dualMap ψ) := by
  rw [sp_comp, sp_comp]
  congr 1
  ext s <;> simp [dualMap, epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem dual_alg {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) :
    spMap (dualMap ψ) ≫ spMap (algebraMap S (DualNumber S)) = spMap (algebraMap T (DualNumber T)) ≫ spMap ψ := by
  rw [sp_comp, sp_comp]
  congr 1
  ext s <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem isLieImageH_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K L : Type) [Field K] [Field L] (φ : K →+* L) (x x' : Sp K ⟶ Xo.X) (w w' : Sp L ⟶ Xo.X) (f : Fib Xo x ⟶ Fib Xo x') (g : Fib Xo w ⟶ Fib Xo w') (p : ℕ) (v u : Sp (DualNumber K) ⟶ Xo.univ.t.G.left), IsBC φ f g → IsTanAt x v → (IsLieImageH p f.left v u ↔ IsLieImageH p g.left (spMap (dualMap φ) ≫ v) (spMap (dualMap φ) ≫ u)) := by
  intro E _ _ _ H Dw l Xo K L _ _ φ x x' w w' f g p v u hbc hv
  obtain ⟨rfl, rfl, hbc⟩ := hbc
  let π : pullback Xo.univ.t.G.hom (spMap φ ≫ x) ⟶ pullback Xo.univ.t.G.hom x :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ spMap φ) (by rw [pullback.condition, Category.assoc])
  let π' : pullback Xo.univ.t.G.hom (spMap φ ≫ x') ⟶ pullback Xo.univ.t.G.hom x' :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ spMap φ) (by rw [pullback.condition, Category.assoc])
  have hπ1 : π ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _
  have hπ2 : π ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap φ := pullback.lift_snd _ _ _
  have hπ1' : π' ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _
  have hπ2' : π' ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap φ := pullback.lift_snd _ _ _
  have hc := hbc π π' hπ1 hπ2 hπ1' hπ2'
  generalize hF : (f.left : pullback Xo.univ.t.G.hom x ⟶ pullback Xo.univ.t.G.hom x') = F at hc ⊢
  generalize hG : (g.left : pullback Xo.univ.t.G.hom (spMap φ ≫ x) ⟶ pullback Xo.univ.t.G.hom (spMap φ ≫ x')) = G
    at hc ⊢
  have key : ∀ (a : Sp (DualNumber K) ⟶ pullback Xo.univ.t.G.hom x)
      (b : Sp (DualNumber L) ⟶ pullback Xo.univ.t.G.hom (spMap φ ≫ x)),
      a ≫ pullback.fst _ _ = v → a ≫ pullback.snd _ _ = spMap (algebraMap K (DualNumber K)) →
      b ≫ pullback.fst _ _ = spMap (dualMap φ) ≫ v → b ≫ pullback.snd _ _ = spMap (algebraMap L (DualNumber L)) →
      spMap (dualMap φ) ≫ spMap (epsMul ((p : K)⁻¹)) ≫ a ≫ F ≫ pullback.fst _ _ =
        spMap (epsMul ((p : L)⁻¹)) ≫ b ≫ G ≫ pullback.fst _ _ := by
    intro a b ha1 ha2 hb1 hb2
    have hab : b ≫ π = spMap (dualMap φ) ≫ a := by
      apply pullback.hom_ext
      · rw [Category.assoc, hπ1, hb1, Category.assoc, ha1]
      · rw [Category.assoc, hπ2, ← Category.assoc, hb2, Category.assoc, ha2, dual_alg]
    have hGF : G ≫ pullback.fst _ _ = π ≫ F ≫ pullback.fst _ _ := by
      rw [← hπ1', ← Category.assoc, hc, Category.assoc]
    rw [hGF, ← Category.assoc b, hab, ← Category.assoc, dual_eps, map_inv₀, map_natCast]
    simp only [Category.assoc]
  constructor
  · rintro ⟨a, ha1, ha2, rfl⟩
    refine ⟨pullback.lift (spMap (dualMap φ) ≫ v) (spMap (algebraMap L (DualNumber L))) ?_,
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _,
      key a _ ha1 ha2 (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)⟩
    rw [Category.assoc, hv.1, ← Category.assoc, dual_alg, Category.assoc]
  · rintro ⟨b, hb1, hb2, hu⟩
    refine ⟨pullback.lift v (spMap (algebraMap K (DualNumber K))) hv.1,
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, ?_⟩
    have := epi_dualMap φ
    rw [← cancel_epi (spMap (dualMap φ)), hu]
    exact (key _ b (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) hb1 hb2).symm

end GlobalTheory.LieImageBC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemKernelOfGeometricFibresReducedBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeEx

attribute [local instance] Over.cartesianMonoidalCategory

theorem mem_transKer_of_geometric
    (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (T : Type) [CommRing T] [IsReduced T] (x x' : Sp T ⟶ Xo.X) (Ψ : Gx x ⟶ Gx x') (a : Over.mk x ⟶ Xo.univ.t.G)
    (hΨ : Ψ ≫ (fst (Over.mk x') Xo.univ.t.G).left = (fst (Over.mk x) Xo.univ.t.G).left)
    (hk : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (χ : T →+* Ω) (x₁ x₁' : Sp Ω ⟶ Xo.X) (Ψ₁ : Gx x₁ ⟶ Gx x₁'),
      IsFib χ Ψ Ψ₁ → ∃ b ∈ transKer Xo.univ.t.G Ψ₁, b.left = spMap χ ≫ a.left) :
    a ∈ transKer Xo.univ.t.G Ψ := by
  have := Xo.univ.t.semi.smooth
  have := Xo.univ.t.semi.separated
  have : Smooth (fst (Over.mk x) Xo.univ.t.G).left := by
    show Smooth (pullback.fst x Xo.univ.t.G.hom)
    infer_instance
  have : IsSeparated (fst (Over.mk x') Xo.univ.t.G).left := by
    show IsSeparated (pullback.fst x' Xo.univ.t.G.hom)
    infer_instance
  have : IsReduced (Over.mk x).left := (affine_isReduced_iff _).2 ‹IsReduced T›
  have : IsReduced (Gx x) := GlobalTheory.isReduced_of_smooth_of_isReduced (fst (Over.mk x) Xo.univ.t.G).left
  have hT : ∀ {Y : Scheme.{0}} (y : Y ⟶ Xo.X) (c : Over.mk y ⟶ Xo.univ.t.G),
      (translT Xo.univ.t.G c).left ≫ (fst (Over.mk y) Xo.univ.t.G).left = (fst (Over.mk y) Xo.univ.t.G).left :=
    fun y c => by rw [← Over.comp_left, translT, lift_fst]
  rw [mem_transKer]
  refine hom_ext_of_geometric_points (Gx x) (Gx x') (Sp T) (fst (Over.mk x') Xo.univ.t.G).left _ _
    (by rw [Category.assoc, hΨ, hT]) fun Ω _ _ q => ?_
  let φ : CommRingCat.of T ⟶ CommRingCat.of Ω := Spec.preimage (q ≫ (fst (Over.mk x) Xo.univ.t.G).left)
  let χ : T →+* Ω := φ.hom
  have hχ : spMap χ = q ≫ (fst (Over.mk x) Xo.univ.t.G).left := Spec.map_preimage _
  obtain ⟨Ψ₁, pm, pm', hp, hp', hc, h1⟩ :=
    exists_isFib χ (x₁ := spMap χ ≫ x) (x₁' := spMap χ ≫ x') rfl rfl Ψ hΨ
  obtain ⟨b, hb, hba⟩ := hk Ω χ _ _ Ψ₁ ⟨pm, pm', hp, hp', hc, h1⟩
  let q₁ : Sp Ω ⟶ Gx (spMap χ ≫ x) := ReciprocityTheory.ChartRestriction.G.PullbackSections.gxLift (spMap χ ≫ x) (𝟙 _)
    (q ≫ (snd (Over.mk x) Xo.univ.t.G).left)
    (by rw [Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.gx_w x, ← Category.assoc, ← hχ, Category.id_comp])
  have hq₁ : q₁ ≫ pm = q := by
    refine ReciprocityTheory.ChartRestriction.G.PullbackSections.gx_ext x _ _ ?_ ?_
    · rw [Category.assoc, hp.2.2, ← Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.gxLift_fst, Category.id_comp, hχ]
    · rw [Category.assoc, hp.2.1, ReciprocityTheory.ChartRestriction.G.PullbackSections.gxLift_snd]
  let pmO : Over.mk (spMap χ ≫ x) ⊗ Xo.univ.t.G ⟶ Over.mk x ⊗ Xo.univ.t.G := Over.homMk pm (by
    rw [← Over.w (fst (Over.mk x) Xo.univ.t.G), ← Over.w (fst (Over.mk (spMap χ ≫ x)) Xo.univ.t.G),
      ← Category.assoc, hp.2.2]
    rfl)
  let φo : Over.mk (spMap χ ≫ x) ⟶ Over.mk x := Over.homMk (spMap χ) rfl
  have hb' : b = φo ≫ a := Over.OverMorphism.ext hba
  have hpf : pmO ≫ fst (Over.mk x) Xo.univ.t.G = fst _ Xo.univ.t.G ≫ φo := Over.OverMorphism.ext hp.2.2
  have hps : pmO ≫ snd (Over.mk x) Xo.univ.t.G = snd _ Xo.univ.t.G := Over.OverMorphism.ext hp.2.1
  have tp : ∀ {Y : Over Xo.X} (c : Y ⟶ Xo.univ.t.G),
      translPt Xo.univ.t.G c = (fst Y Xo.univ.t.G ≫ c) * snd Y Xo.univ.t.G := fun _ => rfl
  have key : translT Xo.univ.t.G b ≫ pmO = pmO ≫ translT Xo.univ.t.G a := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, translT, lift_fst, lift_fst_assoc, hpf]
    · simp only [Category.assoc, translT, lift_snd, lift_snd_assoc, hps, tp, MonObj.comp_mul, reassoc_of% hpf, hb']
  have keyL : (translT Xo.univ.t.G b).left ≫ pm = pm ≫ (translT Xo.univ.t.G a).left :=
    congrArg (fun f => f.left) key
  rw [← hq₁, Category.assoc, Category.assoc, ← reassoc_of% keyL, ← hc, reassoc_of% (mem_transKer.1 hb)]

end GlobalTheory.HeckeEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PullConstantToPointEqRingImage
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PullConst

theorem pull_const_apply : ∀ {T Ω : Type} [CommRing T] [CommRing Ω] (χ : T →+* Ω) {Y : Scheme.{0}} (q : Y ⟶ Sp T) (U : Y.Opens) (w : Sp Ω ⟶ Y) (h : ⊤ ≤ w ⁻¹ᵁ U), w ≫ q = spMap χ → ∀ a : T, (w.appLE U ⊤ h).hom ((q.appLE ⊤ U le_top).hom (toΓ T a)) = toΓ Ω (χ a) := by
  intro T Ω _ _ χ Y q U w h hwq a
  have key : q.appLE ⊤ U le_top ≫ w.appLE U ⊤ h = (w ≫ q).appTop :=
    (Scheme.Hom.appLE_comp_appLE w q ⊤ U ⊤ le_top h).trans
      (Scheme.Hom.appLE_eq_app (f := w ≫ q) (U := ⊤))
  have k1 : (w.appLE U ⊤ h).hom ((q.appLE ⊤ U le_top).hom (toΓ T a)) =
      (w ≫ q).appTop.hom (toΓ T a) := by
    have := congrArg (fun g => g.hom (toΓ T a)) key
    simpa only [CommRingCat.comp_apply] using this
  refine k1.trans ?_
  rw [hwq]
  have h3 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom χ)
  have h4 := congrArg (fun g => g.hom a) h3
  simp only [CommRingCat.comp_apply] at h4
  exact h4.symm

end GlobalTheory.PullConst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryArchimedeanCoordinateActionLinearMulStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord GlobalTheory.ArchLine
open scoped Matrix Classical SchwartzMap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_archimedean_coordinate_action_linear_mul : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W),
    (∀ (h : UA σ W.J) (v v' : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)),
      archAct M h (v + v') = archAct M h v + archAct M h v') ∧
    (∀ (h : UA σ W.J) (c : ℝ) (v : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)),
      archAct M h (c • v) = c • archAct M h v) ∧
    (∀ (h h' : UA σ W.J) (v : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)),
      archAct M (h * h') v = archAct M h (archAct M h' v)) := by
  first | exact @GlobalTheory.ArchLine.archAct_linear_mul | exact GlobalTheory.ArchLine.archAct_linear_mul | (intros; apply GlobalTheory.ArchLine.archAct_linear_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittTowerRestrictionIntertwinesWeilUpToCharacterStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wittTowerRestriction_intertwines_weil_upToCharacter : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT χS' χT' : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ)), IsWeilDatumO ψ V W χS χT ω → IsWeilDatumO ψ V' W χS' χT' ω' → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∃ c : GA D W →* Circle, ∀ h f, IsThetaFunO ψ V W f → res V V' W C B μ 𝓨 (ω (1, h) f) = (c h : ℂ) • ω' (1, h) (res V V' W C B μ 𝓨 f) := by
  first | exact @GlobalTheory.TowerRestrictScalar.main | exact GlobalTheory.TowerRestrictScalar.main | (intros; apply GlobalTheory.TowerRestrictScalar.main <;> assumption)
end

