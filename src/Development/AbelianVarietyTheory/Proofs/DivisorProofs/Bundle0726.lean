import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0705
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0689
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0632
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0646
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0594
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0709
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0656
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0706
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0707
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0663

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ObstructionClassNatural
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem isClosedImmersion_of_isPullback_spMap_surj {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'}
    (hσ : Function.Surjective σ) {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X}
    (h : IsPullback φ s' s (spMap σ)) : IsClosedImmersion φ := by
  have : IsClosedImmersion (spMap σ) := IsClosedImmersion.spec_of_surjective _ hσ
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) h.flip this

theorem restrict_pull1_preRes_pairFst {R' : Type} [CommRing R'] {X Y Y' : Scheme.{0}} (ψ : Y ⟶ X)
    (χ : Y' ⟶ Y) [IsAffineHom χ] (q' : Y' ⟶ Sp R') (y : HO1 q') :
    (CoefMap.restrict (OPre χ q') (pairFst ψ)).pull1 ((preRes χ q').pull1 y) =
      (CoefMap.restrict (OAff q') (pairFst ψ ⋙ preAff χ)).pull1 y := by
  obtain ⟨y, rfl⟩ := H1.mk_surjective _ y
  rfl

theorem restrict_pull2_preRes_pairFst {R' : Type} [CommRing R'] {X Y Y' : Scheme.{0}} (ψ : Y ⟶ X)
    (χ : Y' ⟶ Y) [IsAffineHom χ] (q' : Y' ⟶ Sp R') (y : HO2 q') :
    (CoefMap.restrict (OPre χ q') (pairFst ψ)).pull2 ((preRes χ q').pull2 y) =
      (CoefMap.restrict (OAff q') (pairFst ψ ⋙ preAff χ)).pull2 y := by
  obtain ⟨y, rfl⟩ := H2.mk_surjective _ y
  rfl

set_option maxHeartbeats 1000000 in

theorem bock_natural : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : IsPullback φ s' s (spMap σ)) (h₀ : IsPullback φ₀ s₀ s (spMap σ₀)) (Y Y' Y₀ : Scheme.{0}) (q : Y ⟶ Sp R) (q' : Y' ⟶ Sp R') (q₀ : Y₀ ⟶ Sp R₀) (χ : Y' ⟶ Y) (χ₀ : Y₀ ⟶ Y) (k : IsPullback χ q' q (spMap σ)) (k₀ : IsPullback χ₀ q₀ q (spMap σ₀)) (ψ : Y ⟶ X) (ψ' : Y' ⟶ X') (ψ₀ : Y₀ ⟶ X₀) (w : ψ ≫ s = q ≫ spMap (RingHom.id R)) (w' : ψ' ≫ s' = q' ≫ spMap (RingHom.id R')) (w₀ : ψ₀ ≫ s₀ = q₀ ≫ spMap (RingHom.id R₀)), ψ' ≫ φ = χ ≫ ψ → ψ₀ ≫ φ₀ = χ₀ ≫ ψ → SmallExt t σ σ₀ → Flat s → Flat q → ∀ (x : HO1 s') (z : HO2 s₀) (z' : HO2 q₀), Bock h.w h₀.w t x z → Bock k.w k₀.w t (pullHO1 w' x) z' → z' = pullHO2 w₀ z := by
  intro R R' R₀ _ _ _ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ Y Y' Y₀ q q' q₀ χ χ₀ k k₀ ψ ψ' ψ₀ w w' w₀ hc hc₀
    hS hs hq x z z' hB hB'
  obtain ⟨f, v, hfv, hf, hv⟩ := hB
  obtain ⟨f₂, v₂, hfv₂, hf₂, hv₂⟩ := hB'
  haveI : IsClosedImmersion φ := isClosedImmersion_of_isPullback_spMap_surj hS.1 h
  haveI : IsClosedImmersion φ₀ := isClosedImmersion_of_isPullback_spMap_surj hS.2.2.1 h₀
  haveI : IsClosedImmersion χ := isClosedImmersion_of_isPullback_spMap_surj hS.1 k
  haveI : IsClosedImmersion χ₀ := isClosedImmersion_of_isPullback_spMap_surj hS.2.2.1 k₀
  have hsec := GlobalTheory.AbCoh.preα_surjective_and_ker R R' R₀ t σ σ₀ Y Y' Y₀ q q' q₀ χ χ₀ k k₀ hS hq
  obtain ⟨c₁, hc₁, hC₁⟩ :=
    (GlobalTheory.AbCoh.red_preimage_pairs R R' σ X X' Y Y' s s' q q' φ χ h.w ψ ψ' w w' hc inferInstance).1 f x hf
  obtain ⟨c₂, hc₂, hC₂⟩ := ((GlobalTheory.AbCoh.red_iff_pre R R' Y Y' q q' σ χ k.w).1 f₂ (pullHO1 w' x)).1 hf₂
  obtain ⟨e₁, he₁, hE₁⟩ :=
    (GlobalTheory.AbCoh.red_preimage_pairs R R₀ σ₀ X X₀ Y Y₀ s s₀ q q₀ φ₀ χ₀ h₀.w ψ ψ₀ w w₀ hc₀ inferInstance).2 v z hv
  obtain ⟨e₂, he₂, hE₂⟩ := ((GlobalTheory.AbCoh.red_iff_pre R R₀ Y Y₀ q q₀ σ₀ χ₀ k₀.w).2.1 v₂ z').1 hv₂
  have nat : ∀ {U V : AffOp Y} (a : U ⟶ V) (b : (OAff q).obj U),
      preα χ q q' V (mp (OAff q) a b) = mp (OPre χ q') a (preα χ q q' U b) :=
    fun a b ↦ (preCoef k.w).naturality a b
  have nat₀ : ∀ {U V : AffOp Y} (a : U ⟶ V) (b : (OAff q).obj U),
      preα χ₀ q q₀ V (mp (OAff q) a b) = mp (OPre χ₀ q₀) a (preα χ₀ q q₀ U b) :=
    fun a b ↦ (preCoef k₀.w).naturality a b

  obtain ⟨g', hg'⟩ := (H1.mk_eq_mk (f := c₁)
    (f' := (CoefMap.restrict (OPre χ q') (pairFst ψ)).pullbackOneCocycle c₂)).1 (by
      rw [hC₁, ← CoefMap.pullCohomologyOne_class, hC₂, restrict_pull1_preRes_pairFst])
  choose g hg using fun p : (Pair ψ)ᵒᵖ ↦ (hsec ((pairFst ψ).obj p)).1 (g' p)
  obtain ⟨F1, hF1⟩ : ∃ F1 : C1 (OPair ψ q), ∀ a b (u : a ⟶ b),
      F1 a b u = (pairPull w).α b (f _ _ ((pairPull w).G.map u)) := ⟨_, fun _ _ _ ↦ rfl⟩
  obtain ⟨F2, hF2⟩ : ∃ F2 : C1 (OPair ψ q), ∀ a b (u : a ⟶ b),
      F2 a b u = f₂ _ _ ((pairFst ψ).map u) := ⟨_, fun _ _ _ ↦ rfl⟩
  have hred : ∀ a b (u : a ⟶ b),
      preα χ q q' ((pairFst ψ).obj b) ((F1 - F2 - d0 (OPair ψ q) g) a b u) = 0 := by
    intro a b u
    have hc₂' : ((CoefMap.restrict (OPre χ q') (pairFst ψ)).pullbackOneCocycle c₂).1 a b u =
        preα χ q q' ((pairFst ψ).obj b) (f₂ _ _ ((pairFst ψ).map u)) := hc₂ _ _ _
    have e : g' b - mp (pairFst ψ ⋙ OPre χ q') u (g' a) =
        c₁.1 a b u - ((CoefMap.restrict (OPre χ q') (pairFst ψ)).pullbackOneCocycle c₂).1 a b u :=
      congrFun (congrFun (congrFun hg' a) b) u
    have e' : preα χ q q' ((pairFst ψ).obj b) (mp (OPair ψ q) u (g a)) =
        mp (pairFst ψ ⋙ OPre χ q') u (g' a) := by
      have := nat ((pairFst ψ).map u) (g a)
      rw [hg a] at this
      exact this
    simp only [Pi.sub_apply, amitsur_d0_apply, map_sub]
    rw [hF1, hF2, ← hc₁, ← hc₂', hg b, e', e, sub_self]
  choose u₀ hu₀ using fun a b (u : a ⟶ b) ↦ ((hsec ((pairFst ψ).obj b)).2.1 _).1 (hred a b u)
  have hD : F1 - F2 - d0 (OPair ψ q) g = t • (u₀ : C1 (OPair ψ q)) := by
    funext a b u; exact hu₀ a b u
  obtain ⟨W1, hW1⟩ : ∃ W1 : C2 (OPair ψ q), ∀ a b c (u : a ⟶ b) (u' : b ⟶ c),
      W1 a b c u u' = (pairPull w).α c (v _ _ _ ((pairPull w).G.map u) ((pairPull w).G.map u')) :=
    ⟨_, fun _ _ _ _ _ ↦ rfl⟩
  obtain ⟨W2, hW2⟩ : ∃ W2 : C2 (OPair ψ q), ∀ a b c (u : a ⟶ b) (u' : b ⟶ c),
      W2 a b c u u' = v₂ _ _ _ ((pairFst ψ).map u) ((pairFst ψ).map u') := ⟨_, fun _ _ _ _ _ ↦ rfl⟩
  have hdF1 : d1 (OPair ψ q) F1 = t • W1 := by
    funext a b c u u'
    have e := congrFun (congrFun (congrFun (congrFun (congrFun hfv _) _) _)
      ((pairPull w).G.map u)) ((pairPull w).G.map u')
    simp only [d1_apply, Pi.smul_apply] at e ⊢
    rw [hF1, hF1, hF1, hW1, ← (pairPull w).naturality, Functor.map_comp, ← map_sub, ← map_add, e,
      (pairPull w).smul]
    rfl
  have hdF2 : d1 (OPair ψ q) F2 = t • W2 := by
    funext a b c u u'
    have e := congrFun (congrFun (congrFun (congrFun (congrFun hfv₂ _) _) _)
      ((pairFst ψ).map u)) ((pairFst ψ).map u')
    simp only [d1_apply, Pi.smul_apply] at e ⊢
    rw [hF2, hF2, hF2, hW2, Functor.map_comp]
    exact e
  have hdd : d1 (OPair ψ q) (d0 (OPair ψ q) g) = 0 := by
    have := commAlgFunctorCoboundaryZero_mem_cocyclesOne (OPair ψ q) g
    rw [commAlgFunctorCocyclesOne_eq_ker] at this
    exact this
  have hmain : t • (W1 - W2 - d1 (OPair ψ q) u₀) = 0 := by
    rw [smul_sub, smul_sub, ← hdF1, ← hdF2, ← (d1 (OPair ψ q)).map_smul, ← hD, map_sub, map_sub, hdd,
      sub_zero, sub_self]
  have hzero : ∀ a b c (u : a ⟶ b) (u' : b ⟶ c),
      preα χ₀ q q₀ ((pairFst ψ).obj c) ((W1 - W2 - d1 (OPair ψ q) u₀) a b c u u') = 0 := by
    intro a b c u u'
    refine ((hsec ((pairFst ψ).obj c)).2.2.2 _).2 ?_
    exact congrFun (congrFun (congrFun (congrFun (congrFun hmain a) b) c) u) u'
  obtain ⟨ub, hub⟩ : ∃ ub : C1 (pairFst ψ ⋙ OPre χ₀ q₀), ∀ a b (u : a ⟶ b),
      ub a b u = preα χ₀ q q₀ ((pairFst ψ).obj b) (u₀ a b u) := ⟨_, fun _ _ _ ↦ rfl⟩
  have hH2 : H2.mk _ e₁ = H2.mk _ ((CoefMap.restrict (OPre χ₀ q₀) (pairFst ψ)).pullbackTwoCocycle e₂) := by
    refine H2.mk_eq_mk.2 ⟨ub, ?_⟩
    funext a b c u u'
    have E := hzero a b c u u'
    simp only [Pi.sub_apply, d1_apply, map_sub, map_add] at E
    have E1 : preα χ₀ q q₀ ((pairFst ψ).obj c) (mp (OPair ψ q) u' (u₀ a b u)) =
        mp (pairFst ψ ⋙ OPre χ₀ q₀) u' (ub a b u) := by
      rw [hub]; exact nat₀ ((pairFst ψ).map u') (u₀ a b u)
    have E2 : e₁.1 a b c u u' = preα χ₀ q q₀ _ (W1 a b c u u') := by rw [he₁, hW1]
    have E3 : ((CoefMap.restrict (OPre χ₀ q₀) (pairFst ψ)).pullbackTwoCocycle e₂).1 a b c u u' =
        preα χ₀ q q₀ _ (W2 a b c u u') := by
      rw [hW2]; exact he₂ _ _ _ _ _
    simp only [d1_apply, Pi.sub_apply]
    rw [E2, E3, ← E1, hub, hub]
    linear_combination -E
  rw [hE₁, ← CoefMap.pullCohomologyTwo_class, hE₂, restrict_pull2_preRes_pairFst] at hH2
  exact ((GlobalTheory.AbCoh.pair_pre_bijective R₀ X Y Y₀ ψ χ₀ q₀).2.1.1 hH2).symm

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupFormalChartEvNatMultipleEqConvPower
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

open TensorProduct WithConv Coalgebra

namespace GlobalTheory.NMul

theorem isAdicComplete_ring_of_module {O A : Type} [CommRing O] [CommRing A] [Algebra O A]
    (p : ℕ) [h : IsAdicComplete (Ideal.span {(p : O)}) A] :
    IsAdicComplete (Ideal.span {(p : A)}) A := by
  have key : ∀ (n : ℕ) (x : A), x ∈ (Ideal.span {(p : A)} ^ n • ⊤ : Submodule A A) ↔
      x ∈ (Ideal.span {(p : O)} ^ n • ⊤ : Submodule O A) := by
    intro n x
    rw [GlobalTheory.mem_span_singleton_pow_smul_top_iff_exists, GlobalTheory.mem_span_singleton_pow_smul_top_iff_exists]
    simp [Algebra.smul_def]
  exact
    { haus' := fun x hx => IsHausdorff.haus h.toIsHausdorff x fun n =>
        SModEq.sub_mem.2 ((key n _).1 (SModEq.sub_mem.1 (hx n)))
      prec' := fun f hf => by
        obtain ⟨L, hL⟩ := IsPrecomplete.prec h.toIsPrecomplete (f := f) fun {m n} hmn =>
          SModEq.sub_mem.2 ((key _ _).1 (SModEq.sub_mem.1 (hf hmn)))
        exact ⟨L, fun n => SModEq.sub_mem.2 ((key _ _).2 (SModEq.sub_mem.1 (hL n)))⟩ }

end GlobalTheory.NMul

namespace GlobalTheory.NMul

theorem ev_nmul : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O →
    ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (n k : ℕ) (i : Fin d),
      c.ev n (nmul c.μ k i) = PDiv.mulBy O (G.A n) k (c.x n i) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ G d c n k
  haveI : IsAdicComplete (Ideal.span {(p : O)}) (G.A n) :=
    GlobalTheory.isAdicComplete_of_finite_projective _ _
  haveI : IsAdicComplete (Ideal.span {(p : G.A n)}) (G.A n) := isAdicComplete_ring_of_module (O := O) p
  have hT := (GlobalTheory.T.padicContinuousEvaluation_existsUnique_subst_natural p O (G.A n) (Fin d) (c.x n) (c.nil n)).2 (c.ev n) (c.isEval n)
  have hsucc : ∀ (k : ℕ) (j : Fin d), nmul c.μ (k + 1) j =
      subst (Sum.elim (nmul c.μ k) fun i => (X i : MvPowerSeries (Fin d) O)) (c.μ j) := by
    intro k j
    simp only [nmul, Function.iterate_succ_apply']
    rfl
  have hmul : ∀ (j : ℕ) (a : G.A n),
      PDiv.mulBy O (G.A n) j a = (toConv (AlgHom.id O (G.A n)) ^ j).ofConv a := fun j a =>
    DFunLike.congr_fun (PDiv.comp_mulBy_pts (AlgHom.id O (G.A n)) j) a
  induction k with
  | zero =>
    intro i
    have h0 : nmul c.μ 0 i = 0 := rfl
    rw [h0, map_zero, hmul]
    simp [c.aug n i]
  | succ k ih =>
    intro i
    have hu : ∀ s, constantCoeff
        (Sum.elim (nmul c.μ k) (fun i => (X i : MvPowerSeries (Fin d) O)) s) = 0 := by
      have hc : ∀ (k : ℕ) (j : Fin d), constantCoeff (nmul c.μ k j) = 0 := by
        intro k
        induction k with
        | zero => intro j; rfl
        | succ k ihk =>
          intro j
          rw [hsucc]
          refine constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero ?_) ?_
            (c.isLaw.const j) <;>
          · rintro (l | l)
            · simpa using ihk l
            · simp
      rintro (l | l)
      · simpa using hc k l
      · simp
    let ψ : MvPowerSeries (Fin d ⊕ Fin d) O →ₐ[O] G.A n :=
      (Algebra.TensorProduct.lift (PDiv.mulBy O (G.A n) k : G.A n →ₐ[O] G.A n)
        (AlgHom.id O (G.A n)) fun _ _ => Commute.all _ _).comp (c.ev₂ n)
    have hψ : IsEval p (fun s => c.ev n
        (Sum.elim (nmul c.μ k) (fun i => (X i : MvPowerSeries (Fin d) O)) s)) ψ := by
      constructor
      · rintro (l | l)
        · simp only [ψ, AlgHom.comp_apply, (c.isEval₂ n).1 (Sum.inl l), Sum.elim_inl,
            Algebra.TensorProduct.lift_tmul, map_one, mul_one, ih]
          rfl
        · simp only [ψ, AlgHom.comp_apply, (c.isEval₂ n).1 (Sum.inr l), Sum.elim_inr,
            Algebra.TensorProduct.lift_tmul, map_one, one_mul, (c.isEval n).1 l]
          rfl
      · intro m
        obtain ⟨N, hN⟩ := (c.isEval₂ n).2 m
        refine ⟨N, fun f hf => ?_⟩
        obtain ⟨y, hy⟩ := hN f hf
        refine ⟨(Algebra.TensorProduct.lift (PDiv.mulBy O (G.A n) k : G.A n →ₐ[O] G.A n)
          (AlgHom.id O (G.A n)) fun _ _ => Commute.all _ _) y, ?_⟩
        simp only [ψ, AlgHom.comp_apply, hy, map_mul, map_pow, map_natCast]
    rw [hsucc, hT.1 _ _ ψ hu hψ (c.μ i)]
    simp only [ψ, AlgHom.comp_apply, c.comul n i]
    rw [hmul (k + 1), pow_succ, AlgHom.convMul_apply]
    have e : (toConv (AlgHom.id O (G.A n)) ^ k).ofConv =
        (PDiv.mulBy O (G.A n) k : G.A n →ₐ[O] G.A n) := by
      ext a; exact (hmul k a).symm
    simp only [e]

end GlobalTheory.NMul
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialZetaDenominatorExponentLeOfIntegral
section
open NumberField Module Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals GlobalTheory.ZetaDenom
open scoped nonZeroDivisors

namespace GlobalTheory.DenomBound

theorem cE_le_of_inZl : ∀ {F : Type} [Field F] [NumberField F] (z : ClassGroup (𝓞 F) → ℚ) (l a n : ℕ) [Fact l.Prime], 2 ≤ a → 1 ≤ n →
    (∀ C, InZl l (((a ^ n - 1 : ℕ) : ℚ) * z C)) → cE z l ≤ finrank ℚ F * padicValNat l 2 + padicValNat l (a ^ n - 1) := by
  intro F _ _ z l a n _ ha hn h
  unfold cE
  apply Finset.sup_le
  intro C _
  unfold denomExp
  by_cases hz : z C = 0
  · simp [hz]
  have hpow : 2 ≤ a ^ n := le_trans ha (Nat.le_self_pow (by omega) a)
  have hA : (a ^ n - 1 : ℕ) ≠ 0 := by omega
  have hAq : ((a ^ n - 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hA
  have h1 := h C
  rw [inZl_iff, padicValRat.mul hAq hz, padicValRat.of_nat] at h1
  have h2 : (2 : ℚ) ^ finrank ℚ F ≠ 0 := pow_ne_zero _ two_ne_zero
  have h3 : padicValRat l (z C / 2 ^ finrank ℚ F) = padicValRat l (z C) - (finrank ℚ F : ℤ) * (padicValNat l 2 : ℤ) := by
    rw [padicValRat.div hz h2, padicValRat.pow (q := (2:ℚ))]
    have : padicValRat l (2 : ℚ) = padicValNat l 2 := by
      have := padicValRat.of_nat (p := l) (n := 2)
      simpa using this
    rw [this]
  rw [h3]
  omega

end GlobalTheory.DenomBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodCompTranslationGroupHom
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer.Reindex

open GlobalTheory.CatCoh

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] (F : Fam I g Λ) {Λ' : Type} [AddCommGroup Λ'] (A : Λ' →+ Λ)

abbrev fam : Fam I g Λ' := ⟨F.V, F.τ.comp A, fun l ↦ F.hol (A l)⟩

variable {F A} (K' : Charts (fam F A))

@[reducible] def charts : Charts F where
  K := K'.K
  W := K'.W
  base := K'.base
  le m k' k := ∃ l, A l = m ∧ K'.le l k' k
  le_refl k := ⟨0, map_zero A, K'.le_refl k⟩
  le_trans := by
    rintro _ _ k k' k'' ⟨l, rfl, h⟩ ⟨m, rfl, h'⟩
    exact ⟨l + m, map_add A l m, K'.le_trans h h'⟩
  maps := by
    rintro _ k k' ⟨l, rfl, h⟩
    exact K'.maps h

@[reducible] def obj (T : K'.Obj) : (charts K').Obj where
  k := T.k
  C := T.C
  alg := T.alg
  J := T.J
  nil := T.nil
  ρ := T.ρ
  ρ_cst := T.ρ_cst

def hom {T T' : K'.Obj} (f : T ⟶ T') : obj K' T ⟶ obj K' T' where
  φ := f.φ
  deg := A f.deg
  le := ⟨f.deg, rfl, Charts.Hom.le f⟩
  mem := f.mem
  close := f.close

theorem isPeriod_comp : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (u : Unif F s σ) {Λ' : Type} [AddCommGroup Λ'] (A : Λ' →+ Λ) (u' : Unif (⟨F.V, F.τ.comp A, fun l ↦ F.hol (A l)⟩ : Fam I g Λ') s σ), u'.E = u.E → ∀ (c : FirstDeRham s) (per : Λ →+ Hol F.V), IsPeriod u c per → IsPeriod u' c (per.comp A) := by
  intro I _ g Λ _ F B _ X s σ u Λ' _ A u' hE c per h K' r' hr
  let r : Real (charts K') s σ :=
    { x := r'.x
      w := r'.w
      compat := by
        rintro _ k k' ⟨l, rfl, e⟩
        exact r'.compat e }
  have h1 := h (charts K') r (fun k p hp ↦ (hr k p hp).trans (congrFun hE p))
  obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
  obtain ⟨G, hG⟩ := H1.mk_eq_mk.1 h1
  refine H1.mk_eq_mk.2 ⟨fun T ↦ G (obj K' T), ?_⟩
  funext T T' φ
  exact congrFun (congrFun (congrFun hG (obj K' T)) (obj K' T')) (hom K' φ)

end GlobalTheory.AnPer.Reindex
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodOverRingRestrictFamilyClass
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.CatCoh GlobalTheory.Cris
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.AnPer

variable {I I₀ : Type} [Fintype I] [Fintype I₀] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {F₀ : Fam I₀ g Λ}
  (K : Charts F) (K₀ : Charts F₀) {R : Type} [CommRing R] (et : Hol F₀.V →+* R) (M : Ideal R) (θ : Hol F.V →+* R)
  (ka : K₀.K → K.K) (hka : ∀ {l k' k}, K₀.le l k' k → K.le l (ka k') (ka k))
  (ρ' : ∀ S : K₀.DObj et M, Hol (K.W (ka S.T.k)) →+* S.T.C)
  (h1 : ∀ S f, ρ' S (K.cst _ f) = algebraMap R S.T.C (θ f))
  (h3 : ∀ (S S' : K₀.DObj et M) (f : S ⟶ S'), Close S'.T.J ((ρ' S').comp (Charts.sh (hka (Charts.Hom.le f.1))))
    ((f.1.φ : S.T.C →+* S'.T.C).comp (ρ' S)))

def famObj (S : K₀.DObj et M) : K.Obj where
  k := ka S.T.k
  C := S.T.C
  alg := ((algebraMap R S.T.C).comp θ).toAlgebra
  J := S.T.J
  nil := S.T.nil
  ρ := ρ' S
  ρ_cst := h1 S

def famCoef : CoefMap θ K.Oc (K₀.OD et M) where
  G :=
    { obj := famObj K K₀ et M θ ka ρ' h1
      map {S S'} f :=
        { φ := { (f.1.φ : S.T.C →+* S'.T.C) with commutes' := fun x ↦ f.2 (θ x) }
          deg := f.1.deg
          le := hka (Charts.Hom.le f.1)
          mem := f.1.mem
          close := h3 S S' f }
      map_id _ := Charts.hom_ext (fun _ ↦ rfl) rfl
      map_comp _ _ := Charts.hom_ext (fun _ ↦ rfl) rfl }
  α S := RingHom.id S.T.C
  naturality _ _ := rfl
  smul S d c := (Algebra.smul_def (A := S.T.C) (θ d) c).symm

theorem famCoef_perCl (per : Λ →+ Hol F.V) :
    (famCoef K K₀ et M θ ka hka ρ' h1 h3).pull1 (K.perCl per) = K₀.perClD et M (θ.toAddMonoidHom.comp per) :=
  congrArg (H1.mk _) (Subtype.ext (funext fun _ ↦ funext fun _ ↦ funext fun _ ↦ rfl))

theorem coefD_pull1_of_family (res : ∀ k, Hol (K.W (ka k)) →+* Hol (K₀.W k))
    (h2 : ∀ S h, ρ' S h - S.T.ρ (res _ h) ∈ S.T.J)
    {B B₀ D : Type} [CommRing B] [CommRing B₀] [CommRing D] {X X₀ : Scheme.{0}} {s : X ⟶ Sp B} {s₀ : X₀ ⟶ Sp B₀}
    {σ : B →+* Hol F.V} {σ₀ : B₀ →+* Hol F₀.V} (r : Real K s σ) (r₀ : Real K₀ s₀ σ₀) {J : Ideal D}
    (dl : DividedPowers J) {s' : X₀ ⟶ Sp D} {π : D →+* B₀} {io : D →+* R} (H : IsOver et M s₀ σ₀ J s' π io)
    (j : B →+* D) (φ₀ : X₀ ⟶ X) (n : IsMor (dp0 B) s dl s' j φ₀) (h4 : ∀ b, θ (σ b) = io (j b))
    (h5 : ∀ k, spMap (res k) ≫ r.x (ka k) = r₀.x k ≫ φ₀) (c : FirstDeRham s) (per : Λ →+ Hol F.V)
    (hc : r.coef.pull1 c = K.perCl per) (h1 : ∀ S f, ρ' S (K.cst _ f) = algebraMap R S.T.C (θ f))
    (h3 : ∀ (S S' : K₀.DObj et M) (f : S ⟶ S'), Close S'.T.J ((ρ' S').comp (Charts.sh (hka (Charts.Hom.le f.1))))
      ((f.1.φ : S.T.C →+* S'.T.C).comp (ρ' S))) :
    (r₀.coefD dl H).pull1 (n.pull1 c) = K₀.perClD et M (θ.toAddMonoidHom.comp per) := by
  let t : (r.coef.comp (famCoef K K₀ et M θ ka hka ρ' h1 h3)).G ⟶ (n.coef.comp (r₀.coefD dl H)).G :=
    { app S :=
        { φ := { RingHom.id S.T.C with commutes' := fun b ↦ congrArg (algebraMap R S.T.C) (h4 b) }
          φ₀ := RingHom.id (S.T.C ⧸ S.T.J)
          comm := fun _ ↦ rfl
          dp := letI := S.T.ratAlg; isDPMorphism_of_rat (C := S.T.C) (C' := S.T.C) _ _ (RingHom.id S.T.C) fun _ h ↦ h
          pt := by
            have e : (Ideal.Quotient.mk S.T.J).comp (ρ' S) = ((Ideal.Quotient.mk S.T.J).comp S.T.ρ).comp (res _) :=
              RingHom.ext fun h ↦ Ideal.Quotient.eq.2 (h2 S h)
            change spMap (RingHom.id (S.T.C ⧸ S.T.J)) ≫ spMap ((Ideal.Quotient.mk S.T.J).comp (ρ' S)) ≫ r.x (ka S.T.k) =
              (spMap ((Ideal.Quotient.mk S.T.J).comp S.T.ρ) ≫ r₀.x S.T.k) ≫ φ₀
            rw [Cris.spMap_id, Category.id_comp, Category.assoc, ← h5, e, Cris.spMap_comp (res _), Category.assoc] }
      naturality _ _ _ := Thick.hom_ext fun _ ↦ rfl }
  refine (n.coef.pullCohomologyOne_comp (r₀.coefD dl H) c).symm.trans ?_
  refine (CoefMap.pullCohomologyOne_eq_of_natTrans _ _ t (fun _ _ ↦ rfl) c).symm.trans ?_
  rw [CoefMap.pullCohomologyOne_comp, hc, famCoef_perCl]

end GlobalTheory.AnPer

open GlobalTheory.AnPer in

theorem GlobalTheory.AnPer.period_restrict_family : ∀ {I I₀ : Type} [Fintype I] [Fintype I₀] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {F₀ : Fam I₀ g Λ} (K : Charts F) (K₀ : Charts F₀) {R : Type} [CommRing R] (et : Hol F₀.V →+* R) (M : Ideal R) (θ : Hol F.V →+* R) (ka : K₀.K → K.K) (hka : ∀ {l k' k}, K₀.le l k' k → K.le l (ka k') (ka k)) (res : ∀ k, Hol (K.W (ka k)) →+* Hol (K₀.W k)) (ρ' : ∀ S : K₀.DObj et M, Hol (K.W (ka S.T.k)) →+* S.T.C), (∀ S f, ρ' S (K.cst _ f) = algebraMap R S.T.C (θ f)) → (∀ S h, ρ' S h - S.T.ρ (res _ h) ∈ S.T.J) → (∀ (S S' : K₀.DObj et M) (f : S ⟶ S'), Close S'.T.J ((ρ' S').comp (Charts.sh (hka (Charts.Hom.le f.1)))) ((f.1.φ : S.T.C →+* S'.T.C).comp (ρ' S))) → ∀ {B B₀ D : Type} [CommRing B] [CommRing B₀] [CommRing D] {X X₀ : Scheme.{0}} {s : X ⟶ Sp B} {s₀ : X₀ ⟶ Sp B₀} {σ : B →+* Hol F.V} {σ₀ : B₀ →+* Hol F₀.V} (r : GlobalTheory.AnPer.Real K s σ) (r₀ : GlobalTheory.AnPer.Real K₀ s₀ σ₀) {J : Ideal D} (dl : DividedPowers J) {s' : X₀ ⟶ Sp D} {π : D →+* B₀} {io : D →+* R} (H : IsOver et M s₀ σ₀ J s' π io) (j : B →+* D) (φ₀ : X₀ ⟶ X) (n : IsMor (dp0 B) s dl s' j φ₀), (∀ b, θ (σ b) = io (j b)) → (∀ k, spMap (res k) ≫ r.x (ka k) = r₀.x k ≫ φ₀) → ∀ (c : FirstDeRham s) (per : Λ →+ Hol F.V), r.coef.pull1 c = K.perCl per → (r₀.coefD dl H).pull1 (n.pull1 c) = K₀.perClD et M (θ.toAddMonoidHom.comp per) :=
  fun K K₀ _ _ et M θ ka hka res ρ' h1 h2 h3 _ _ _ _ _ _ _ _ _ _ _ _ r r₀ _ dl _ _ _ H j φ₀ n h4 h5 c per hc ↦
    coefD_pull1_of_family K K₀ et M θ ka hka ρ' res h2 r r₀ dl H j φ₀ n h4 h5 c per hc h1 h3
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageCochainRestrictionBijectiveClosedImmersiStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.preimageCochainRestriction_bijective_closedImmersion : ∀ (R' : Type) [CommRing R'] (X X' : Scheme.{0}) (φ : X' ⟶ X) [IsClosedImmersion φ] (s' : X' ⟶ Sp R'), Function.Bijective (preRes φ s').pull1 ∧ Function.Bijective (preRes φ s').pull2 ∧ (CohomZeroIsConstants (OAff s') → CohomZeroIsConstants (OPre φ s')) := by
  first | exact @GlobalTheory.AbCoh.preRes_bijective | exact GlobalTheory.AbCoh.preRes_bijective | (intros; apply GlobalTheory.AbCoh.preRes_bijective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiDeterminantValuationBoundStatement
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_determinant_valuation_bound : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (ψ : RL p O Λ →+* RL p O Λ), IsPsi ψ → ∀ τ : Λ →+* O, ∃ (κ₀ : ℝ) (κ : (Λ →+* O) → ℝ), ∀ (N : ℕ) (Δ : RL p O Λ) (a : (Λ →+* O) → ℕ) (c : (Λ →+* O) → C), IsDetElt ε ψ N Δ → HasOrders C ε N Δ a c → Real.log (v (c τ)) = N * κ₀ + ∑ᶠ σ, (a σ : ℝ) * κ σ := by
  first | exact @GlobalTheory.DetInv.log_val_lead_linear | exact GlobalTheory.DetInv.log_val_lead_linear | (intros; apply GlobalTheory.DetInv.log_val_lead_linear <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullH1SurjectiveOfBijectiveStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pull_h1_surjective_of_bijective : ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (φ : X' ⟶ X) (h : IsPullback φ s' s (spMap σ)), Function.Bijective σ → Function.Surjective (pullHO1 h.w) := by
  first | exact @GlobalTheory.AbCoh.pullHO1_surjective_of_bijective_base | exact GlobalTheory.AbCoh.pullHO1_surjective_of_bijective_base | (intros; apply GlobalTheory.AbCoh.pullHO1_surjective_of_bijective_base <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmPullbackTeichmullerLiftStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiLogarithm_pullback_teichmullerLift : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d e : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k) (hμ : IsLaw μ) (hν : IsLaw ν) (φ : Fin e → MvPowerSeries (Fin d) k), IsHom μ ν φ → ∀ f ∈ quasiLog p hν, subst (fun j => Katz.lift p (φ j)) f ∈ quasiLog p hμ ∧ (∀ c, Red p (cob1 (fun j => Katz.lift p (ν j)) f) c → Red p (cob1 (fun i => Katz.lift p (μ i)) (subst (fun j => Katz.lift p (φ j)) f)) (pull2 φ c)) ∧ ∀ w, RedV p (lin f) w → RedV p (lin (subst (fun j => Katz.lift p (φ j)) f)) (pullLin φ w) := by
  first | exact @GlobalTheory.KatzPull.quasiLog_pull | exact GlobalTheory.KatzPull.quasiLog_pull | (intros; apply GlobalTheory.KatzPull.quasiLog_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionQuotientHolomorphicMeasurableStatement
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sectionQuotient_holomorphic_measurable : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (la : La) (U Ω : Set Y) (β h : ι → Y → ℂ), IsOpen U → IsOpen Ω → A.IsFrameOn la U β → A.IsSecOn la Ω h → (∀ i y, y ∉ Ω → h i y = 0) → (∀ i, DifferentiableOn ℂ (GlobalTheory.OTY.TwEst.quot A h β ∘ (A.chart i).symm) ((A.chart i).target ∩ (A.chart i).symm ⁻¹' (U ∩ Ω))) ∧ Measurable (GlobalTheory.OTY.TwEst.ext0 U (fun y : U => GlobalTheory.OTY.TwEst.quot A h β y)) ∧ ∀ y ∈ U, h (A.pick y) y = β (A.pick y) y * GlobalTheory.OTY.TwEst.quot A h β y := by
  first | exact @GlobalTheory.OTY.TwEst.quot_holo_measurable | exact GlobalTheory.OTY.TwEst.quot_holo_measurable | (intros; apply GlobalTheory.OTY.TwEst.quot_holo_measurable <;> assumption)
end

