import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2819
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPdivGroupForPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2825
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2587
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2836
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2835
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2827
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2660
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2817
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2773
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2631
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2818
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteStalkGermQuotientIntegralUnitDenominator
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem GlobalTheory.Poinc.finite_stalk_quot_integral : ∀ (X Y : Scheme.{0}) (p : Y ⟶ X), IsFinite p → ∀ (y : Y) (a : Y.presheaf.stalk y), ∃ b s : Y.presheaf.stalk y, IsUnit s ∧ a * s = b ∧ (∃ P : Polynomial (X.presheaf.stalk (p y)), P.Monic ∧ P.eval₂ (p.stalkMap y).hom b = 0) ∧ ∃ Q : Polynomial (X.presheaf.stalk (p y)), Q.Monic ∧ Q.eval₂ (p.stalkMap y).hom s = 0 := by
  intro X Y p hp y a
  obtain ⟨U, hU', hyU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := p y) trivial
  have hV : IsAffineOpen (p ⁻¹ᵁ U) := hU'.preimage p
  have hyV : y ∈ p ⁻¹ᵁ U := hyU
  letI : Algebra Γ(Y, p ⁻¹ᵁ U) (Y.presheaf.stalk y) := Y.presheaf.algebra_section_stalk ⟨y, hyV⟩
  haveI := hV.isLocalization_stalk ⟨y, hyV⟩
  obtain ⟨⟨c, t⟩, hct⟩ := IsLocalization.mk'_surjective (hV.primeIdealOf ⟨y, hyV⟩).asIdeal.primeCompl a
  have hfin : (p.app U).hom.Finite := p.finite_app U hU'
  have hint := hfin.to_isIntegral
  have key : ∀ z : Γ(Y, p ⁻¹ᵁ U), ∃ P : Polynomial (X.presheaf.stalk (p y)), P.Monic ∧
      P.eval₂ (p.stalkMap y).hom (algebraMap Γ(Y, p ⁻¹ᵁ U) (Y.presheaf.stalk y) z) = 0 := by
    intro z
    obtain ⟨P', hm, hP'⟩ := hint z
    refine ⟨P'.map (X.presheaf.germ U (p y) hyU).hom, hm.map _, ?_⟩
    have hc : (p.stalkMap y).hom.comp (X.presheaf.germ U (p y) hyU).hom
        = (Y.presheaf.germ (p ⁻¹ᵁ U) y hyV).hom.comp (p.app U).hom := by
      rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, Scheme.Hom.germ_stalkMap]
    rw [Polynomial.eval₂_map, hc]
    change Polynomial.eval₂ _ ((Y.presheaf.germ (p ⁻¹ᵁ U) y hyV).hom z) P' = 0
    rw [← Polynomial.hom_eval₂, hP', map_zero]
  refine ⟨algebraMap _ _ c, algebraMap _ _ (t : Γ(Y, p ⁻¹ᵁ U)), IsLocalization.map_units _ t, ?_, key c, key t⟩
  rw [← hct]
  exact IsLocalization.mk'_spec _ c t
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankEqOfRankAtStalk
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.Cris GlobalTheory.CurveRootGeometry GlobalTheory.AbDatum GlobalTheory.ConjSeq

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SymmPoincare

universe u

section Linear

variable {K : Type} [Field K] {V : Type u} [AddCommGroup V] [Module K V]
  {ψ : Module.Dual K V →ₗ[K] Module.Dual K V →ₗ[K] K} {β : V →ₗ[K] Module.Dual K V}

theorem bijective_of_eval [Module.Finite K V] (h : ∀ s y, ψ (β s) y = y s) : Function.Bijective β := by
  have inj : Function.Injective β := (injective_iff_map_eq_zero _).2 fun s hs ↦
    (Module.forall_dual_apply_eq_zero_iff K s).1 fun y ↦ by rw [← h, hs, map_zero, LinearMap.zero_apply]
  exact ⟨inj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq (K := K) (V := V)).symm).1 inj⟩

theorem mem_iff_of_isotropic [Module.Finite K V] (h : ∀ s y, ψ (β s) y = y s) (F : Submodule K V)
    (hF : Module.finrank K V = 2 * Module.finrank K F)
    (iso : ∀ x ∈ F.dualAnnihilator, ∀ y ∈ F.dualAnnihilator, ψ x y = 0) (s : V) :
    s ∈ F ↔ ∀ w ∈ F, β s w = 0 := by
  let e := LinearEquiv.ofBijective β (bijective_of_eval h)
  have le : F.dualAnnihilator.map e.symm.toLinearMap ≤ F := by
    rintro _ ⟨x, hx, rfl⟩
    refine (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff F _).1 fun y hy ↦ ?_
    rw [← h]
    exact (congrArg (fun z ↦ ψ z y) (e.apply_symm_apply x)).trans (iso x hx y hy)
  have eq : F.dualAnnihilator.map e.symm.toLinearMap = F := by
    refine Submodule.eq_of_le_of_finrank_eq le ?_
    rw [LinearEquiv.finrank_map_eq]
    have := Subspace.finrank_add_finrank_dualAnnihilator_eq F
    omega
  rw [← Submodule.mem_dualAnnihilator]
  conv_lhs => rw [← eq]
  rw [Submodule.mem_map_equiv]
  rfl

end Linear

section Swap

variable {R : Type} [CommRing R] {I : Ideal R} {S : Scheme.{0}} {κ : DividedPowers I} {t : S ⟶ Sp R}
  {A B : Over S} [GrpObj A] [GrpObj B]

theorem isCorrForm_swap {P : LB (A ⊗ B).left} {φ : Crys κ t A →ₗ[R] Crys κ t B →ₗ[R] R}
    (H : IsCorrForm κ t A B P φ) : IsCorrForm κ t B A (swap P) (-φ.flip) := by
  obtain ⟨n, a, b, hc, hφ⟩ := H
  have m : IsMor κ ((A ⊗ B).hom ≫ t) κ ((B ⊗ A).hom ≫ t) (RingHom.id R) (lift (snd B A) (fst B A)).left :=
    (homMor κ t (lift (snd B A) (fst B A))).isMor
  have k := isChern_pull m hc
  rw [crystallinePull2_sum_cup] at k
  refine ⟨n, fun i ↦ -b i, a, ?_, fun x y ↦ ?_⟩
  · convert k using 2 with i
    rw [pullOver_pullOver, pullOver_pullOver, lift_fst, lift_snd, Submodule.coe_neg, map_neg, map_neg,
      LinearMap.neg_apply, neg_eq_of_add_eq_zero_right (cup_add_cup _ _ _)]
  · simp only [LinearMap.neg_apply, LinearMap.flip_apply, hφ, map_neg, ← Finset.sum_neg_distrib, neg_mul]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [mul_comm]

theorem isCorrForm_of_iso {P Q : LB (A ⊗ B).left} {φ : Crys κ t A →ₗ[R] Crys κ t B →ₗ[R] R}
    (H : IsCorrForm κ t A B P φ) (hP : P.IsLB) (hQ : Q.IsLB) (e : LBIso P Q) : IsCorrForm κ t A B Q φ := by
  obtain ⟨n, a, b, hc, hφ⟩ := H
  exact ⟨n, a, b, (isChern_existsUnique_and_iso R _ κ _ _).2 _ _ hP hQ e _ hc, hφ⟩

theorem skew_of_symm (C : CupSquare κ t (A ⊗ A)) {P : LB (A ⊗ A).left} (hP : P.IsLB) (hs : LBIso (swap P) P)
    {φ : Crys κ t A →ₗ[R] Crys κ t A →ₗ[R] R} (H : IsCorrForm κ t A A P φ) (x y : Crys κ t A) :
    φ x y = -φ y x :=
  LinearMap.congr_fun₂ (H.unique C hP (isCorrForm_of_iso (isCorrForm_swap H) (pull_isLB hP _) hP hs)) x y

theorem isPerfect_of_symm {P : LB (A ⊗ A).left} (hd : IsDual A A P) (hs : LBIso (swap P) P) :
    IsPerfect A A P := by
  have hP := hd.isLB
  have hs' : (swap P).IsLB := pull_isLB hP _
  have sym {Y : Over S} (x y : Y ⟶ A) : evc hP x y = evc hP y x := by
    rw [← evc_swap hP hs', evc, (CechPic.cls_eq_iff hs' hP).2 hs, evc]
  refine ⟨hP, (triv_ev_iff hP _ _).2 (hd.additive.evc_one hP _), hd.zero, fun Y x hx ↦ hd.eq_one x ?_,
    fun _ ↦ hd.eq_one⟩
  have k := congrArg (CechPic.pull (lift (snd A Y) (fst A Y)).left) ((triv_ev_iff hP _ _).1 hx)
  rw [pull_evc, map_zero, lift_fst_assoc, lift_snd] at k
  rw [triv_ev_iff hP, sym, k]

end Swap

theorem finrank_eq_of_rankAtStalk {K : Type} [Field K] {V : Type u} [AddCommGroup V] [Module K V] {n : ℕ}
    (h : ∀ q : PrimeSpectrum K, Module.rankAtStalk V q = n) : Module.finrank K V = n := by
  have e := h ⊥
  rwa [Module.rankAtStalk_eq_finrank_of_free] at e

theorem skew_lagrangian : GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.ConjugateFiltration → ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (hK : (p : K) = 0) (A : Over (Sp K)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A), SmoothOfRelativeDimension g A.hom → ∀ P : LB (A ⊗ A).left, IsDual A A P → LBIso (swap P) P → ∀ (ψ : HdR A →ₗ[K] HdR A →ₗ[K] K) (β : primDR A →ₗ[K] HdR A), IsCorrForm (dp0 K) (𝟙 _) A A P ψ → (∀ s y, ψ (β s) y = y s) → Module.Finite K (primDR A) ∧ Function.Bijective β ∧ (∀ s w, β s w = - β w s) ∧ (∀ s, s ∈ PrimitiveSubmodule A ↔ ∀ w ∈ PrimitiveSubmodule A, β s w = 0) ∧ ∀ s, s ∈ conjDR p K hK A ↔ ∀ w ∈ conjDR p K hK A, β s w = 0 := by
  intro hD hC p _ K _ hK A _ g hA hg P hd hs ψ β hψ hβ
  obtain ⟨hfin, -, hrk⟩ := GlobalTheory.Published.AbelianDeRham.Free.prim hD.1 hA hg
  have hV := finrank_eq_of_rankAtStalk hrk
  have sk := skew_of_symm (cupSquare_of_free hD.1 (AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA) (smooth_prod hg hg))
    hd.isLB hs hψ
  obtain ⟨-, h₁, -⟩ := hψ.perfect hD hA hg hA hg (isPerfect_of_symm hd hs)
  obtain ⟨-, -, -, -, hF⟩ := hD.2.1 K A g hA hg
  obtain ⟨-, -, hG, h₂⟩ := hC p K hK A g hA hg (cast_left p K hK A) (frobMor p K hK A (cast_left p K hK A))
  refine ⟨hfin, bijective_of_eval hβ, fun s w ↦ by rw [← hβ w, sk, hβ],
    mem_iff_of_isotropic hβ _ (by rw [hV, finrank_eq_of_rankAtStalk hF]) fun x hx ↦ (h₁ x).1 hx,
    mem_iff_of_isotropic hβ _ (hV.trans (congrArg (2 * ·) (finrank_eq_of_rankAtStalk hG).symm))
      fun x hx y hy ↦ ?_⟩
  exact h₂ A hA hg _ (frobMor p K hK A (cast_left p K hK A)) P hd ψ hψ x y
    (fun c ↦ (Submodule.mem_dualAnnihilator x).1 hx _ (Submodule.subset_span ⟨c, rfl⟩))
    fun c ↦ (Submodule.mem_dualAnnihilator y).1 hy _ (Submodule.subset_span ⟨c, rfl⟩)

end GlobalTheory.SymmPoincare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernDualNeg
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LineForm

theorem c1F_dual : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ)
    (hX : IsRegVar p D) (σ : k →+* ℂ),
    ∀ L : HermLB p, c1F hX σ L.dual = -c1F hX σ L := by
  intro k _ X _ p D hX σ L
  funext x
  have e : (fun v => (L.dual.φ σ).φ (pick (L.dual.φ σ).isLB x.pt) (x.ch.symm v)) =
      fun v => -(L.φ σ).φ (pick (L.φ σ).isLB x.pt) (x.ch.symm v) := rfl
  have e₂ : ∀ (u : ReciprocityTheory.L2DbarEstimates.V D → ℝ) (z : ReciprocityTheory.L2DbarEstimates.V D),
      GlobalTheory.HermFrame.ddc (fun v => -u v) z = fun ξ η => -GlobalTheory.HermFrame.ddc u z ξ η := by
    intro u z
    funext ξ η
    simp only [GlobalTheory.HermFrame.ddc, GlobalTheory.leviForm_neg, neg_apply, mul_neg]
  simp only [c1F, Pi.neg_apply]
  rw [e, e₂, ofValues, ofValues]
  simp only [neg_smul, Finset.sum_neg_distrib]

end GlobalTheory.LineForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernIsometricEq
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

namespace GlobalTheory.LineForm

theorem c1F_eq_of_isometric (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ)
    (hX : IsRegVar p D) (σ : k →+* ℂ) :
    ∀ L M : HermLB p, L.Isometric M → c1F hX σ L = c1F hX σ M := by
  intro L M h
  obtain ⟨w, -, hw⟩ := h.exists_units
  funext x
  obtain ⟨⟨c, y⟩, hy⟩ := x
  have ha : y ∈ ptsIn p σ (M.B.U (pick (M.φ σ).isLB y)) := mem_pick _ y
  have hb : y ∈ ptsIn p σ (L.B.U (pick (L.φ σ).isLB y)) := mem_pick _ y
  set a := pick (M.φ σ).isLB y
  set b := pick (L.φ σ).isLB y
  have hy' : y ∈ c.e.source := hy
  have ho := ChartGlue.isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (M.B.U a ⊓ L.B.U b))
  have hm := ChartGlue.mem_over c.e hy' (mem_ptsIn_inf.2 ⟨ha, hb⟩)
  have hg := c.holo _ (w a b).val
  have hf : ContDiffAt ℂ 2 (ev p σ _ (w a b).val ∘ c.e.symm) (c.e y) :=
    (SCV.analyticAt_of_differentiableOn (hg.mono fun v hv => ⟨hv.1, hv.2⟩) (ho.mem_nhds hm)).contDiffAt
  have h0 : (ev p σ _ (w a b).val ∘ c.e.symm) (c.e y) ≠ 0 := ev_ne_zero hm.2 (w a b).isUnit
  have hL : ContDiffAt ℝ 2 (fun v => (L.φ σ).φ b (c.e.symm v)) (c.e y) := (L.cInf σ).contDiffAt c hy' hb
  have hlog : ContDiffAt ℝ 2 (fun v => Real.log (‖(ev p σ _ (w a b).val ∘ c.e.symm) v‖ ^ 2)) (c.e y) :=
    ((hf.restrict_scalars ℝ).norm_sq ℂ).log (by simpa using h0)
  have key : leviForm (fun v => (M.φ σ).φ a (c.e.symm v)) (c.e y) =
      leviForm (fun v => (L.φ σ).φ b (c.e.symm v)) (c.e y) := by
    rw [leviForm_congr (u' := fun v => (L.φ σ).φ b (c.e.symm v) +
        Real.log (‖(ev p σ _ (w a b).val ∘ c.e.symm) v‖ ^ 2)), leviForm_add hL hlog,
      leviForm_log_normSq_eq_zero hf h0, add_zero]
    filter_upwards [ho.mem_nhds hm] with v hv
    exact hw σ a b _ (mem_ptsIn_inf.1 hv.2).1 (mem_ptsIn_inf.1 hv.2).2
  have eL : c1F hX σ L ⟨(c, y), hy⟩ =
      ofValues (HermFrame.ddc (fun v => (L.φ σ).φ b (c.e.symm v)) (c.e y)) := rfl
  have eM : c1F hX σ M ⟨(c, y), hy⟩ =
      ofValues (HermFrame.ddc (fun v => (M.φ σ).φ a (c.e.symm v)) (c.e y)) := rfl
  rw [eL, eM]
  unfold HermFrame.ddc
  rw [key]

end GlobalTheory.LineForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstOrderDeformationFormLiftValuesSub
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechKS.LiftDiff

theorem spMap_fst_surjective {B : Type} [CommRing B] (f : DualNumber B →+* B) (hf : ∀ c, f c = c.fst) :
    Function.Surjective (spMap f) := by
  intro q
  refine ⟨spMap (algebraMap B (DualNumber B)) q, ?_⟩
  refine PrimeSpectrum.ext (Ideal.ext fun c ↦ ?_)
  change algebraMap B (DualNumber B) (f c) ∈ q.asIdeal ↔ c ∈ q.asIdeal
  rw [hf]
  have hn : c - algebraMap B (DualNumber B) c.fst ∈ q.asIdeal := by
    refine q.isPrime.mem_of_pow_mem 2 ?_
    have : (c - algebraMap B (DualNumber B) c.fst) ^ 2 = 0 := by
      ext <;> simp [pow_two, TrivSqZeroExt.algebraMap_eq_inl]
    rw [this]; exact zero_mem _
  exact ⟨fun hc ↦ by simpa using add_mem hn hc, fun hc ↦ by simpa using sub_mem hc hn⟩

theorem le_preimage_of_red {B : Type} [CommRing B] {X : Scheme.{0}} (f : DualNumber B →+* B)
    (hf : ∀ c, f c = c.fst) {y : Sp (DualNumber B) ⟶ X} {x : Sp B ⟶ X} (e : spMap f ≫ y = x) {U : X.Opens}
    (h : ⊤ ≤ x ⁻¹ᵁ U) : ⊤ ≤ y ⁻¹ᵁ U := by
  intro p _
  obtain ⟨q, rfl⟩ := spMap_fst_surjective f hf p
  have := h (Set.mem_univ q)
  rw [← e] at this
  exact this

theorem ev_eq_of_triv {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R} (ω : Form s)
    {T₁ T₂ T : Thick (dp0 R) s} (a : T₁ ⟶ T₂) (ψ : T₂ ⟶ T) (φ : T₁ ⟶ T) (h₁ : T₁.J = ⊥) (h₂ : T₂.J = ⊥)
    (e : a ≫ ψ = φ) : ev ω.1 φ = ev ω.1 ψ := by
  rw [← e, ev_comp, show ev ω.1 a = 0 from ω.2 a h₁ h₂, map_zero, zero_add]

variable {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {A' : Over (Sp (DualNumber K))} [GrpObj A']
  {i : A.left ⟶ A'.left}

theorem ev_sec_sub_ev_tan (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i)
    (ω : Form (A'.hom ≫ 𝟙 (Sp (DualNumber K)))) (P : GPt A) {v : epsR K ⟶ A} (hv : IsTangent v) :
    ∃ (hc : (spMap (algebraMap P.B (DualNumber P.B)) ≫ P.x ≫ i) ≫ A'.hom ≫ 𝟙 _ =
        spMap (algebraMap (DualNumber K) ((fibMor h).isMor.obj P.ext).B))
      (ec : spMap ((fibMor h).isMor.obj P.ext).π ≫ spMap (algebraMap P.B (DualNumber P.B)) ≫ P.x ≫ i =
        ((fibMor h).isMor.obj P.ext).x)
      (ht : (P.trx v ≫ i) ≫ A'.hom ≫ 𝟙 _ = spMap (algebraMap (DualNumber K) ((fibMor h).isMor.obj P.ext).B))
      (et : spMap ((fibMor h).isMor.obj P.ext).π ≫ P.trx v ≫ i = ((fibMor h).isMor.obj P.ext).x),
      ev ((fibMor h).isMor.pullForm ω).1 P.sec - ev ((fibMor h).isMor.pullForm ω).1 (P.tan hv) =
        ev ω.1 (idLift _ _ hc ec) - ev ω.1 (idLift _ _ ht et) := by
  let g : DualNumber K →+* P.B := (algebraMap K P.B).comp (TrivSqZeroExt.fstHom K K K).toRingHom
  have w : (P.x ≫ i) ≫ A'.hom ≫ 𝟙 _ = spMap g := ((fibMor h).isMor.obj P.triv).w
  have hc : (spMap (algebraMap P.B (DualNumber P.B)) ≫ P.x ≫ i) ≫ A'.hom ≫ 𝟙 _ =
      spMap (algebraMap (DualNumber K) ((fibMor h).isMor.obj P.ext).B) := by
    rw [Category.assoc, w]
    exact (Cris.spMap_comp g (algebraMap P.B (DualNumber P.B))).symm.trans (congrArg spMap (RingHom.ext fun _ ↦ rfl))
  have ec : spMap ((fibMor h).isMor.obj P.ext).π ≫ spMap (algebraMap P.B (DualNumber P.B)) ≫ P.x ≫ i =
      ((fibMor h).isMor.obj P.ext).x := by
    let π' : DualNumber P.B →+* P.B := TrivSqZeroExt.fstHom K P.B P.B
    have e : π'.comp (algebraMap P.B (DualNumber P.B)) = RingHom.id _ := RingHom.ext fun _ ↦ rfl
    show spMap π' ≫ spMap (algebraMap P.B (DualNumber P.B)) ≫ P.x ≫ i = P.x ≫ i
    rw [← Category.assoc, ← Cris.spMap_comp, e, Cris.spMap_id, Category.id_comp]
  have ht : (P.trx v ≫ i) ≫ A'.hom ≫ 𝟙 _ =
      spMap (algebraMap (DualNumber K) ((fibMor h).isMor.obj P.ext).B) :=
    ((fibMor h).isMor.obj (P.tr v).triv).w
  have et : spMap ((fibMor h).isMor.obj P.ext).π ≫ P.trx v ≫ i = ((fibMor h).isMor.obj P.ext).x :=
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ i) ((P.isTransl_trx v).red hv))
  refine ⟨hc, ec, ht, et, ?_⟩
  refine congrArg₂ (· - ·) (ev_eq_of_triv ω ?a (idLift _ _ hc ec) ((fibMor h).isMor.functor.map P.sec) rfl rfl ?ea)
    (ev_eq_of_triv ω ?b (idLift _ _ ht et) ((fibMor h).isMor.functor.map (P.tan hv)) rfl rfl ?eb)
  case a =>
    exact { φ := { algebraMap P.B (DualNumber P.B) with commutes' := fun _ ↦ rfl }
            φ₀ := algebraMap P.B (DualNumber P.B)
            comm := fun _ ↦ rfl
            dp := isDPMorphism_of_eq_bot _ rfl _ _
            pt := rfl }
  case b =>
    exact { φ := { RingHom.id (DualNumber P.B) with commutes' := fun _ ↦ rfl }
            φ₀ := RingHom.id _
            comm := fun _ ↦ rfl
            dp := isDPMorphism_of_eq_bot _ rfl _ _
            pt := by
              show spMap (RingHom.id (DualNumber P.B)) ≫ P.trx v ≫ i = P.trx v ≫ i
              rw [Cris.spMap_id, Category.id_comp] }
  case ea => exact Thick.hom_ext fun _ ↦ rfl
  case eb => exact Thick.hom_ext fun _ ↦ rfl

theorem liftVal_sub_snd : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i), IsAbelianScheme A → ∀ (ω : Form (A'.hom ≫ 𝟙 (Sp (DualNumber K)))) (U : A'.left.Opens), IsAffineOpen U → ∀ (P : GPt A), P.In (i ⁻¹ᵁ U) → ∀ (y₁ y₂ : Sp (DualNumber P.B) ⟶ A'.left) (h₁ : IsLift i P y₁) (h₂ : IsLift i P y₂) (n : ℕ) (u : Fin n → (epsR K ⟶ A)) (c : Fin n → P.B), (∀ a, IsTangent (u a)) → (∀ f : Γ(A'.left, U), valR y₁ U f - valR y₂ U f = (TrivSqZeroExt.inr (∑ a, c a * (valR (P.trx (u a)) (i ⁻¹ᵁ U) ((i.app U).hom f)).snd) : DualNumber P.B)) → (liftVal h ω.1 h₁ - liftVal h ω.1 h₂).snd = -∑ a, c a * algebraMap K P.B (tanVal (u a) ((fibMor h).isMor.pullForm ω)) := by
  intro K _ A _ A' _ i h hA ω U hU P hP y₁ y₂ h₁ h₂ n u c hu hdiff
  obtain ⟨m, r, t, H⟩ := GlobalTheory.T.exists_crystallineForm_lift_difference_eq_sum (DualNumber K) A'.left (A'.hom ≫ 𝟙 _) ω U hU
  have hPU : ⊤ ≤ (P.x ≫ i) ⁻¹ᵁ U := hP
  have red : ∀ c : DualNumber P.B, (TrivSqZeroExt.fstHom K P.B P.B : DualNumber P.B →+* P.B) c = c.fst :=
    fun _ ↦ rfl
  have hU₁ : ⊤ ≤ y₁ ⁻¹ᵁ U := le_preimage_of_red _ red h₁.2 hPU
  have hU₂ : ⊤ ≤ y₂ ⁻¹ᵁ U := le_preimage_of_red _ red h₂.2 hPU
  have k1 := H ((liftMor (epsDP K) h).isMor.obj P.eps) (SqExt.ofModule K P.B P.B).sq rfl y₁ y₂ h₁.1 h₂.1
    h₁.2 h₂.2 hU₁ hU₂
  have e1 : liftVal h ω.1 h₁ - liftVal h ω.1 h₂ =
      -∑ k, valR y₂ U (r k) * (valR y₁ U (t k) - valR y₂ U (t k)) := by
    rw [← neg_sub]; exact congrArg Neg.neg k1
  have f2 : ∀ f, (valR y₂ U f).fst = valR P.x (i ⁻¹ᵁ U) ((i.app U).hom f) := fun f ↦ by
    rw [← GlobalTheory.Points.valR_comp, ← h₂.2, GlobalTheory.Points.valR_spMap_comp _ _ _ hU₂]; exact (red _).symm
  have step2 : ∀ a, ∑ k, valR P.x (i ⁻¹ᵁ U) ((i.app U).hom (r k)) *
      (valR (P.trx (u a)) (i ⁻¹ᵁ U) ((i.app U).hom (t k))).snd =
        algebraMap K P.B (tanVal (u a) ((fibMor h).isMor.pullForm ω)) := by
    intro a
    have X := ev_sec_sub_ev_tan (K := K) (A := A) (A' := A') (i := i) h ω P (hu a)
    obtain ⟨hc, ec, ht, et, E⟩ := X
    have F := GlobalTheory.T.invariantForm_abelianVariety_translate_value K A hA (u a) (hu a) ((fibMor h).isMor.pullForm ω) P
    have hUt : ⊤ ≤ (P.trx (u a) ≫ i) ⁻¹ᵁ U := fun p hp ↦ hP.tr (hu a) hp
    have hUc : ⊤ ≤ (spMap (algebraMap P.B (DualNumber P.B)) ≫ P.x ≫ i) ⁻¹ᵁ U :=
      fun _ _ ↦ hPU (Set.mem_univ _)
    have k2 := H ((fibMor h).isMor.obj P.ext) (SqExt.ofModule K P.B P.B).sq rfl _ _ ht hc et ec hUt hUc
    have F3 : (∑ k, valR (spMap (algebraMap P.B (DualNumber P.B)) ≫ P.x ≫ i) U (r k) *
        (valR (P.trx (u a) ≫ i) U (t k) - valR (spMap (algebraMap P.B (DualNumber P.B)) ≫ P.x ≫ i) U (t k))) =
        TrivSqZeroExt.inr (algebraMap K P.B (tanVal (u a) ((fibMor h).isMor.pullForm ω))) := k2.symm.trans (E.symm.trans F)
    have F' := congrArg (fun z : DualNumber P.B ↦ z.snd) F3
    simp only [TrivSqZeroExt.snd_inr, TrivSqZeroExt.snd_sum] at F'
    rw [← F']
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [GlobalTheory.Points.valR_spMap_comp _ _ _ hPU, GlobalTheory.Points.valR_spMap_comp _ _ _ hPU, GlobalTheory.Points.valR_comp,
      GlobalTheory.Points.valR_comp, GlobalTheory.Points.valR_comp]
    simp [TrivSqZeroExt.algebraMap_eq_inl]
  have D : ∀ k, valR y₁ U (t k) - valR y₂ U (t k) = TrivSqZeroExt.inr (∑ a, c a *
      (valR (P.trx (u a)) (i ⁻¹ᵁ U) ((i.app U).hom (t k))).snd) := fun k ↦ hdiff (t k)
  refine (congrArg (fun z : DualNumber P.B ↦ z.snd) e1).trans ?_
  have G := Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) ↦ congrArg (valR y₂ U (r k) * ·) (D k)
  refine (congrArg (fun z : DualNumber P.B ↦ (-z).snd) G).trans ?_
  simp only [TrivSqZeroExt.snd_neg, TrivSqZeroExt.snd_sum, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inr,
    TrivSqZeroExt.snd_inr, f2, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.op_zero,
    MulOpposite.unop_zero, mul_zero, zero_smul, add_zero, neg_inj]
  simp only [← step2, Finset.mul_sum]
  clear H k1 e1 hdiff D G step2 f2 red
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
  ring

end GlobalTheory.CechKS.LiftDiff
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagAgree
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCov

variable {D : D7} {O : Setup D} {c : O.s.Comp} {Bs : Scheme.{0}} {E : D.what₂.Tau × Bool → Bs.Modules}

def FlagAgree (hE : ∀ a, IsVB (E a) (rkB D.what₂.Tau O.N O.j a)) {Bg : Scheme.{0}} (jB : Bg ⟶ Bs)
    (πB : Bg ⟶ gen O.s.T.Z) (u : ∀ a, FrAssign O.s.T.Z (E a) (rkB D.what₂.Tau O.N O.j a) jB) {Y₀ : Scheme.{0}}
    (π₀ : Y₀ ⟶ Bs) (fl₀ : ∀ a, Vert.Flag ((Scheme.Modules.pullback π₀).obj (E a)) (rkB D.what₂.Tau O.N O.j a))
    {G : Scheme.{0}} [IsIntegral G] (j : G ⟶ Y₀) (φ : (O.var c).Fn →+* G.functionField) (jG : G ⟶ Bg)
    (a : D.what₂.Tau × Bool) (hr : rkB D.what₂.Tau O.N O.j a = O.S.Dw.mult (embB D a)) : Prop :=
  haveI := (hE a).isQuasicoherent
  (∀ (k : Fin (rkB D.what₂.Tau O.N O.j a + 1)) (V : Bs.Opens) (f : Fin (rkB D.what₂.Tau O.N O.j a) → Γ(E a, V))
    (hf : IsFrame f) (W : Y₀.Opens) (hWV : W ≤ π₀ ⁻¹ᵁ V) (t : Γ((fl₀ a).F k, W))
    (hx : ⊤ ≤ (genPt G ≫ j) ⁻¹ᵁ W) (hxV : ⊤ ≤ ((genPt G ≫ jG) ≫ jB) ⁻¹ᵁ V),
      let aG : Fin (rkB D.what₂.Tau O.N O.j a) → G.functionField := fun b =>
        TangentOrigin.evalPt (genPt G ≫ j) W hx (((hf.pullback π₀).basis hWV).repr (((fl₀ a).ι k).app W t) b)
      let uu := u a V f hf G.functionField (genPt G ≫ jG) hxV
      let v : Fin (O.S.Dw.mult (embB D a)) → (Sp (DualNumber G.functionField) ⟶ O.s.T.Z.t.G.left) :=
        fun l => spMap (dualMap φ) ≫ (O.Φ.C c).f0.v (embB D a) l
      let x := genPt G ≫ jG ≫ πB ≫ genι O.s.T.Z
      cond a.2
        (∃ (w : Sp (DualNumber G.functionField) ⟶ O.s.T.Z.t.G.left)
            (cf : Fin (O.S.Dw.mult (embB D a)) → G.functionField),
          IsCombAtG O.s.T.Z.t x uu aG w ∧ IsCombAtG O.s.T.Z.t x v cf w ∧ ∀ l : Fin (O.S.Dw.mult (embB D a)), (k : ℕ) ≤ l → cf l = 0)
        (∀ (l : Fin (O.S.Dw.mult (embB D a))) (d : Fin (rkB D.what₂.Tau O.N O.j a) → G.functionField),
          IsCombAtG O.s.T.Z.t x uu d (v l) → (l : ℕ) + k < rkB D.what₂.Tau O.N O.j a → ∑ b, aG b * d b = 0)) ∧
  ∀ (i : Fin (rkB D.what₂.Tau O.N O.j a)) (ch : (((fl₀ a).root i).pull j).ι) (V : Bs.Opens)
    (f : Fin (rkB D.what₂.Tau O.N O.j a) → Γ(E a, V)) (hf : IsFrame f) (W : Y₀.Opens) (hW : W ≤ (ch PUnit.unit).U)
    (hWV : W ≤ π₀ ⁻¹ᵁ V) (t : Γ((fl₀ a).F i.succ, W)), ((fl₀ a).π i).app W t = Twist.resM _ hW ((ch PUnit.unit).e 0) →
    ∀ (hx : ⊤ ≤ (genPt G ≫ j) ⁻¹ᵁ W) (hxV : ⊤ ≤ ((genPt G ≫ jG) ≫ jB) ⁻¹ᵁ V),
      let aG : Fin (rkB D.what₂.Tau O.N O.j a) → G.functionField := fun b =>
        TangentOrigin.evalPt (genPt G ≫ j) W hx
          (((hf.pullback π₀).basis hWV).repr (((fl₀ a).ι i.succ).app W t) b)
      let uu := u a V f hf G.functionField (genPt G ≫ jG) hxV
      let v : Fin (O.S.Dw.mult (embB D a)) → (Sp (DualNumber G.functionField) ⟶ O.s.T.Z.t.G.left) :=
        fun l => spMap (dualMap φ) ≫ (O.Φ.C c).f0.v (embB D a) l
      let x := genPt G ≫ jG ≫ πB ≫ genι O.s.T.Z
      cond a.2
        (∃ (w : Sp (DualNumber G.functionField) ⟶ O.s.T.Z.t.G.left)
            (cf : Fin (O.S.Dw.mult (embB D a)) → G.functionField),
          IsCombAtG O.s.T.Z.t x uu aG w ∧ IsCombAtG O.s.T.Z.t x v cf w ∧ cf (Fin.cast hr i) ≠ 0)
        (∀ (l : Fin (O.S.Dw.mult (embB D a))) (d : Fin (rkB D.what₂.Tau O.N O.j a) → G.functionField),
          IsCombAtG O.s.T.Z.t x uu d (v l) → (l : ℕ) + i + 1 = rkB D.what₂.Tau O.N O.j a → ∑ b, aG b * d b ≠ 0)

end GlobalTheory.FlagCov

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleBaseChangeAltBis
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFlagBundle_pullback' : ∀ (B Y B' : Scheme.{0}) (π : Y ⟶ B) (g : B' ⟶ B) (ι : Type) (E : ι → B.Modules) (r : ι → ℕ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl → IsFlagBundle (Limits.pullback.snd π g) (fun a => (Scheme.Modules.pullback g).obj (E a)) r (fun a => GlobalTheory.FlagBaseChange.pullFlag π g (fl a)) := by
  first | exact @GlobalTheory.FlagBaseChange.isFlagBundle_pullFlag | exact GlobalTheory.FlagBaseChange.isFlagBundle_pullFlag | (intros; apply GlobalTheory.FlagBaseChange.isFlagBundle_pullFlag <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleProjectiveOverBaseStatement
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_projective_over_base : ∀ (k : Type) [CommRing k] [IsNoetherianRing k] (B Y : Scheme.{0}) (q : B ⟶ Sp k) (π : Y ⟶ B) (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsProjOver q → (∀ a, GlobalTheory.VB.IsVB (E a) (r a)) → IsFlagBundle π E r fl → IsProjOver (π ≫ q) := by
  first | exact @GlobalTheory.FlagProj.isProjOver_of_isFlagBundle | exact GlobalTheory.FlagProj.isProjOver_of_isFlagBundle | (intros; apply GlobalTheory.FlagProj.isProjOver_of_isFlagBundle <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagFramesTriangularChangeStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical
open GlobalTheory.FlagCell GlobalTheory.FlagConnect

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_frames_triangular_change : ∀ (X : Scheme.{0}) (F : X.Modules) (m : ℕ) (fl : Vert.Flag F m) (V : X.Opens) (v v' : Fin m → Γ(F, V)), Spans fl V v → Spans fl V v' → ∃ M : Matrix (Fin m) (Fin m) Γ(X, V), M.BlockTriangular id ∧ IsUnit M.det ∧ ∀ j, v' j = ∑ k, M k j • v k := by
  first | exact @GlobalTheory.FlagCell.spans_change | exact GlobalTheory.FlagCell.spans_change | (intros; apply GlobalTheory.FlagCell.spans_change <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalAlgebraisationTowerStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_algebraisation_tower : ∀ (R : Type) [CommRing R] (I : Ideal R) (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)), Alg f I → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → (∀ e, IsProper (Y e).hom) → ∀ j : ∀ e, (Y e).left ⟶ W, (∀ e, IsClosedImmersion (j e)) → (∀ e, j e ≫ f = (Y e).hom ≫ thick R I e) → (∀ e, β e ≫ j (e + 1) = j e) → ∃ (T : Scheme.{0}) (i : T ⟶ W) (c : ∀ e, (Y e).left ⟶ T), IsClosedImmersion i ∧ IsProper (i ≫ f) ∧ (∀ e, c e ≫ i = j e) ∧ ∀ e, IsPullback (c e) (Y e).hom (i ≫ f) (thick R I e) := by
  first | exact @GlobalTheory.FormalAlg.alg_tower | exact GlobalTheory.FormalAlg.alg_tower | (intros; apply GlobalTheory.FormalAlg.alg_tower <;> assumption)
end

