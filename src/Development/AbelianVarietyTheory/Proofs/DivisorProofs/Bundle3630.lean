import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3627
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2890
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3278
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1305
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1194
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1196
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2180
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0345
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3618
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2930
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2332
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0148
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.AdelicGL2ExtOfLocalComponents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3620
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3626
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3628
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSystemClassSumsValuesOfFunctions
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistAtEach
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeparateTwoPointsNefBig
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.NefBigSep

variable {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)] {H N A B : LB X} {Z : Closeds X}

theorem deg_of_cls_eq (hZ : IsCompleteCurve k Z) (hH : IsAmpleLB H) (hN : N.IsLB) (hA : A.IsLB)
    (hB : B.IsLB) (a b : ℕ) (e : cls N hN = a • cls A hA + b • cls B hB) :
    interNumRed k Z ![N] = a * interNumRed k Z ![A] + b * interNumRed k Z ![B] := by
  rw [hZ.interNumRed_of_cls_eq_add hH hN (isLB_lbPow hA a) (isLB_lbPow hB b)
    (by rw [cls_lbPow hA, cls_lbPow hB, e]), hZ.interNumRed_lbPow hH hA,
    hZ.interNumRed_lbPow hH hB]

theorem exists_budget (ρ S c : ℚ) (a : ℕ) (hρ : 0 < ρ) (hS : S < ρ) (hS0 : 0 ≤ S) (hc : 0 < c) :
    ∃ q m' : ℕ, 0 < m' ∧ (q : ℚ) = ρ * m' ∧ a < q ∧ 1 / (m' : ℚ) ≤ c ∧ (m' : ℚ) * S < q - a := by
  have hd : (0 : ℚ) < ρ.den := by exact_mod_cast ρ.den_pos
  have hu : (0 : ℤ) ≤ ρ.num := (Rat.num_pos.2 hρ).le
  have hρ' : ((ρ.num.toNat : ℕ) : ℚ) = ρ * ρ.den := by
    rw [show ((ρ.num.toNat : ℕ) : ℚ) = ((ρ.num.toNat : ℤ) : ℚ) from rfl, Int.toNat_of_nonneg hu]
    exact (Rat.mul_den_eq_num ρ).symm
  have hgap : 0 < (ρ.den : ℚ) * (ρ - S) := mul_pos hd (sub_pos.2 hS)
  obtain ⟨t, ht⟩ := exists_nat_gt (max (1 / c) (a / ((ρ.den : ℚ) * (ρ - S))))
  have ht1 : 1 / c < t := lt_of_le_of_lt (le_max_left _ _) ht
  have ht2 : a / ((ρ.den : ℚ) * (ρ - S)) < t := lt_of_le_of_lt (le_max_right _ _) ht
  have htpos : (0 : ℚ) < t := lt_trans (by positivity) ht1
  have ht2' : (a : ℚ) < t * ((ρ.den : ℚ) * (ρ - S)) := by
    rw [div_lt_iff₀ hgap] at ht2; linarith
  refine ⟨ρ.num.toNat * t, ρ.den * t, ?_, ?_, ?_, ?_, ?_⟩
  · exact Nat.mul_pos ρ.den_pos (by exact_mod_cast htpos)
  · push_cast; rw [hρ']; ring
  · have : (a : ℚ) < ((ρ.num.toNat * t : ℕ) : ℚ) := by
      push_cast; rw [hρ']; nlinarith [mul_nonneg (mul_nonneg hd.le htpos.le) hS0]
    exact_mod_cast this
  · push_cast
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ hc] at ht1
    have : (1 : ℚ) ≤ ρ.den := by exact_mod_cast ρ.den_pos
    nlinarith
  · push_cast; rw [hρ']; nlinarith

end GlobalTheory.NefBigSep

namespace GlobalTheory.NefBigSep

theorem separate_nef_big : GlobalTheory.Published.Principalisation → GlobalTheory.Published.NadelVanishingPair → GlobalTheory.Published.NefNumerics → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → letI := algebraΓOfHom p; ∀ (M : LB X) (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (N : LB X) (ρ : ℚ) (h : ℕ → ℚ) (x₁ x₂ : X), M.IsLB → IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < m → IsLogCanonicalMultiple p n Δ m G → IsNef ℂ N → IsBig ℂ N → (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![M] : ℚ) = interNumRed ℂ C ![toLB G] / m + ρ * interNumRed ℂ C ![N]) → IsClosed ({x₁} : Set X) → IsClosed ({x₂} : Set X) → x₁ ≠ x₂ → (∀ e, 0 < h e) → (∀ (z : X) (e : ℕ), z ⤳ x₁ ∨ z ⤳ x₂ → 1 ≤ e → topologicalKrullDim (closure ({z} : Set X)) = e → 2 * (e : ℚ) ^ e < h e ^ e * (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N : ℤ)) → ∑ e ∈ Finset.Icc 1 n, h e < ρ → 0 < ρ → ∃ s : M.Sec, (x₁ ∈ nonzeroLocus s ∧ x₂ ∉ nonzeroLocus s) ∨ (x₂ ∈ nonzeroLocus s ∧ x₁ ∉ nonzeroLocus s) := by
  intro hPr hNad hNef X _ _ _ p n hp hdim M Δ m G N ρ h x₁ x₂ hM hΔ hklt hm hG hNn hNb
    hcurve hx₁ hx₂ hne hh hz hsum hρ
  letI := algebraΓOfHom p
  obtain ⟨a, A, hA, E₀, ha, hAmp, hE₀, hcls⟩ :=
    GlobalTheory.T.exists_ample_add_effective_of_nef_big hNef X p hp N hNn.isLB hNn hNb
  obtain ⟨c, hc, hkltc⟩ := GlobalTheory.T.exists_pos_klt_add_smul_effective_divisor hPr X p n hp hdim Δ m G (qWeil E₀ 1) hm hG hklt
    ⟨1, E₀, one_pos, hE₀, rfl⟩
  have hS0 : 0 ≤ ∑ e ∈ Finset.Icc 1 n, h e := Finset.sum_nonneg fun e _ => (hh e).le
  obtain ⟨q, m', hm', hq, haq, hmc, hbud⟩ := exists_budget ρ _ c a hρ hsum hS0 hc
  have hNp := isLB_lbPow hNn.isLB (q - a)
  have hN'lb := isLB_tens hA hNp
  have hclsN' : cls _ hN'lb = cls A hA + (q - a) • cls N hNn.isLB := by
    rw [cls_tens hA hNp, cls_lbPow hNn.isLB]
  have hN'amp : IsAmpleLB (tens A (lbPow N (q - a))) :=
    IsAmpleLB.tens_of_isNef hNef ℂ X p hp A _ hAmp (hNn.pow hAmp _)
  have hqa : (0 : ℚ) < q - a := sub_pos.2 (by exact_mod_cast haq)
  have hqa' : (((q - a : ℕ) : ℚ)) = q - a := by rw [Nat.cast_sub haq.le]
  have hB : qWeil E₀ m' = (1 / (m' : ℚ)) • qWeil E₀ 1 := by
    funext z; simp [qWeil]; ring
  refine GlobalTheory.T.exists_section_separating_two_points_ample hPr hNad hNef X p n hp hdim M (Δ + qWeil E₀ m') (m * m') (m' • G + m • E₀)
    (tens A (lbPow N (q - a))) (1 / (m' : ℚ)) (fun e => h e / ((q : ℚ) - a)) x₁ x₂ hM
    (isEffQDiv_add_of_isQCart X p hp Δ _ hΔ ⟨m', E₀, hm', hE₀, rfl⟩) ?_ (Nat.mul_pos hm hm')
    (isLogCanonicalMultiple_add_qWeil X p n Δ m m' G E₀ hm hm' hG) hN'amp ?_ hx₁ hx₂ hne
    (fun e => div_pos (hh e) hqa) ?_ ?_
  · intro y
    rw [hB]
    exact (GlobalTheory.T.kltAt_and_lcAt_antitone_coeff X p n hp hdim Δ (qWeil E₀ 1) (1 / (m' : ℚ)) c y
      ⟨1, E₀, one_pos, hE₀, rfl⟩ hmc).1 (hkltc y)
  · intro C hC
    have h1 := hcurve C hC
    have dN' := deg_of_cls_eq hC hAmp hN'lb hA hNn.isLB 1 (q - a) (by rw [hclsN', one_nsmul])
    have dK := hC.interNumRed_of_cls_eq_add hAmp (isLB_lbPow hNn.isLB a) hA (isLB_toLB E₀)
      (by rw [cls_lbPow hNn.isLB, hcls])
    rw [hC.interNumRed_lbPow hAmp hNn.isLB] at dK
    have dG := deg_of_cls_eq hC hAmp (isLB_toLB (m' • G + m • E₀)) (isLB_toLB G) (isLB_toLB E₀)
      m' m (by rw [← toPic_apply, ← toPic_apply, ← toPic_apply, map_add, map_nsmul, map_nsmul])
    rw [h1, dN', dG]
    have dK' : (a : ℚ) * interNumRed ℂ C ![N] = interNumRed ℂ C ![A] + interNumRed ℂ C ![toLB E₀] := by
      exact_mod_cast dK
    have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
    have hm0' : (m' : ℚ) ≠ 0 := by exact_mod_cast hm'.ne'
    push_cast
    rw [hqa']
    field_simp
    linear_combination (m : ℚ) * dK' - (m : ℚ) * (interNumRed ℂ C ![N] : ℚ) * hq
  · intro z e hze he hdz
    have hmix := mixExp_interNumRed hNef ℂ X p hp N A (tens A (lbPow N (q - a))) hNn.isLB hA hN'lb
      (q - a) 1 (Closeds.closure {z}) e hNn hAmp.isNef (by rw [hclsN', one_nsmul, add_comm])
      (by rw [Closeds.coe_closure]; exact hdz)
    have key : ((q : ℚ) - a) ^ e * (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N : ℤ)
        ≤ (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => tens A (lbPow N (q - a)) : ℤ) := by
      have := (Int.cast_le (R := ℚ)).2 hmix
      push_cast at this
      rwa [hqa'] at this
    have h0 := hz z e hze he hdz
    have e1 : h e ^ e * ((interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N : ℤ) : ℚ) =
        (h e / ((q : ℚ) - a)) ^ e * (((q : ℚ) - a) ^ e *
          (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N : ℤ)) := by
      rw [div_pow]; field_simp
    calc 2 * (e : ℚ) ^ e < _ := h0
      _ = _ := e1
      _ ≤ _ := mul_le_mul_of_nonneg_left key (pow_nonneg (div_pos (hh e) hqa).le _)
  · rw [← Finset.sum_div, div_lt_div_iff₀ hqa (by exact_mod_cast hm')]
    linarith

end GlobalTheory.NefBigSep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFibrePowerPointLiftsToLowerBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LowLift

theorem etCompl : ∀ {o : Type} [CommRing o] [IsNoetherianRing o] {ζ : o} {h n : ℕ} (F : SFam h n ζ) {r : ℕ} (y : (GlobalTheory.LowChart.powA F r).left) (R' : Type) [CommRing R'] [IsLocalRing R'] (ρ : GlobalTheory.LowChart.W F y →+* R'), IsLocalHom ρ → ρ.Finite → ρ.Etale → IsEtaleCompletion (Scheme.stalkClosedPointTo (spMap ρ ≫ GlobalTheory.LowChart.toPow F y)).hom ∧ ((residue R').comp (Scheme.stalkClosedPointTo (spMap ρ ≫ GlobalTheory.LowChart.toPow F y)).hom).FormallyUnramified := by
  intro o _ _ ζ h n F r y R' _ _ ρ hloc hfin het
  let y₀ : Sp (GlobalTheory.LowChart.W F y) ⟶ (GlobalTheory.LowChart.powA F r).left := GlobalTheory.LowChart.toPow F y
  obtain ⟨hEt₀, hres₀⟩ := GlobalTheory.InteriorChart.completedStalk_chart (GlobalTheory.LowChart.powA F r).left y
  change IsEtaleCompletion (Scheme.stalkClosedPointTo y₀).hom at hEt₀
  change Function.Surjective ((residue (GlobalTheory.LowChart.W F y)).comp (Scheme.stalkClosedPointTo y₀).hom) at hres₀
  have hfu : ρ.FormallyUnramified ∧ ρ.Flat := by
    algebraize [ρ]
    exact ⟨inferInstanceAs (Algebra.FormallyUnramified _ R'), inferInstanceAs (Module.Flat _ R')⟩
  have hm' : (maximalIdeal (GlobalTheory.LowChart.W F y)).map ρ = maximalIdeal R' := by
    algebraize [ρ]
    haveI : IsLocalHom (algebraMap (GlobalTheory.LowChart.W F y) R') := hloc
    exact Algebra.FormallyUnramified.map_maximalIdeal
  let ξ₀ : Sp R' ⟶ (GlobalTheory.LowChart.powA F r).left := spMap ρ ≫ y₀
  have hcp : ξ₀ (closedPoint R') = y₀ (closedPoint (GlobalTheory.LowChart.W F y)) := by
    show y₀ (spMap ρ (closedPoint R')) = _
    rw [show spMap ρ (closedPoint R') = closedPoint (GlobalTheory.LowChart.W F y) from IsLocalRing.comap_closedPoint ρ]
  have hs : ξ₀ (closedPoint R') ⤳ y₀ (closedPoint (GlobalTheory.LowChart.W F y)) := specializes_of_eq hcp
  have key := GlobalTheory.TorRef.stalkClosedPointTo_comp_spMap_specializes (GlobalTheory.LowChart.powA F r).left y₀ ρ hs
  let E := RingEquiv.ofBijective ((GlobalTheory.LowChart.powA F r).left.presheaf.stalkSpecializes hs).hom
    (GlobalTheory.InteriorChart.bijective_stalkSpecializes hcp hs)
  have hξ : (Scheme.stalkClosedPointTo ξ₀).hom =
      (ρ.comp (Scheme.stalkClosedPointTo y₀).hom).comp E.symm.toRingHom := by
    ext b
    obtain ⟨a, rfl⟩ := E.surjective b
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.symm_apply_apply]
    exact key a
  refine ⟨?_, ?_⟩
  · show IsEtaleCompletion (Scheme.stalkClosedPointTo ξ₀).hom
    rw [hξ]
    exact isEtaleCompletion_comp_bij _ E.symm.bijective _
      (GlobalTheory.InteriorChart.isEtaleCompletion_comp _ ρ hEt₀ hfu.2 hm' hfin)
  · show ((residue R').comp (Scheme.stalkClosedPointTo ξ₀).hom).FormallyUnramified
    have hmap : (ResidueField.map ρ).FormallyUnramified := by
      apply RingHom.FormallyUnramified.of_comp (f := residue (GlobalTheory.LowChart.W F y))
      rw [ResidueField.map_comp_residue]
      exact RingHom.FormallyUnramified.comp hfu.1 (RingHom.FormallyUnramified.of_surjective residue_surjective)
    have e2 : (residue R').comp (Scheme.stalkClosedPointTo ξ₀).hom = (ResidueField.map ρ).comp
        (((residue (GlobalTheory.LowChart.W F y)).comp (Scheme.stalkClosedPointTo y₀).hom).comp E.symm.toRingHom) := by
      rw [hξ, ← RingHom.comp_assoc, ← RingHom.comp_assoc, ← ResidueField.map_comp_residue]
      rfl
    rw [e2]
    exact RingHom.FormallyUnramified.comp
      (RingHom.FormallyUnramified.of_surjective (hres₀.comp E.symm.surjective)) hmap

theorem prodPush : ∀ {S S' T : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}, IsGrpPullback G' G f φ → ∀ {r : ℕ} (p : Fin r → (𝟙_ (Over S') ⟶ G')) (t : T ⟶ S) (q : Fin r → (Over.mk t ⟶ G)) (g : T ⟶ S'), g ≫ f = t → (∀ i, g ≫ (p i).left ≫ φ = (q i).left) → ∀ a : Fin r → ℤ, g ≫ (∏ i, p i ^ a i).left ≫ φ = (∏ i, q i ^ a i).left := by
  intro S S' T G G' _ _ _ _ f φ hG r p t q g ht hq a
  subst ht
  let U : Over.mk g ⟶ 𝟙_ (Over S') := toUnit _
  let Φ : (𝟙_ (Over S') ⟶ G') →* (Over.mk ((Over.mk g).hom ≫ f) ⟶ G) := (pushHom hG (Over.mk g)).comp (preHom U)
  have hΦ : ∀ x, (Φ x).left = g ≫ x.left ≫ φ := fun x => by
    show (U ≫ x).left ≫ φ = _
    rw [Over.comp_left, Category.assoc]
    rfl
  have hpq : ∀ i, Φ (p i) = q i := fun i => Over.OverMorphism.ext ((hΦ _).trans (hq i))
  have e : Φ (∏ i, p i ^ a i) = ∏ i, q i ^ a i := by
    rw [map_prod]
    simp only [map_zpow, hpq]
  exact (hΦ _).symm.trans (congrArg (fun z => z.left) e)

end GlobalTheory.LowLift

namespace GlobalTheory.LowLift

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem main : ∀ (n : ℕ), 3 ≤ n → Odd n → ∀ (h : ℕ) (F : SFam h n (zetaAway n)) (r : ℕ) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsDiscreteValuationRing V₁ → ∀ (b₁ : cycAway n →+* V₁) (v : Sp V₁ ⟶ (GlobalTheory.LowChart.powA F r).left) (hs : v ≫ GlobalTheory.LowChart.toO F r = spMap b₁), ∃ (L : LowBase (zetaAway n) n) (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (f : V₁ →+* V') (κ : L.W →+* V') (e : (Fin L.T.r → ℤ) ≃+ (Fin r → ℤ)), L.h = h ∧ IsCN V' ∧ IsDiscreteValuationRing V' ∧ Function.Injective f ∧ f.Finite ∧ IsLocalHom f ∧ IsLocalHom κ ∧ κ.comp L.T.b = f.comp b₁ ∧ ∃ (B' : Over (Sp V')) (_ : GrpObj B') (β' : B'.left ⟶ (GlobalTheory.LowChart.siegAt F v _ hs).A.left) (β'' : B'.left ⟶ L.T.B.left) (β₂ : (G2 B').left ⟶ (G2 (GlobalTheory.LowChart.siegAt F v _ hs).A).left) (β₂' : (G2 B').left ⟶ (G2 L.T.B).left), IsGrpPullback B' (GlobalTheory.LowChart.siegAt F v _ hs).A (spMap f) β' ∧ IsGrpPullback B' L.T.B (spMap κ) β'' ∧ IsSquare β' β₂ ∧ IsSquare β'' β₂' ∧ LBIso ((GlobalTheory.LowChart.siegAt F v _ hs).P.pull β₂) ((abelian₂ L.T.B L.T.M.L).pull β₂') ∧ ∀ a : Fin L.T.r → ℤ, ∃ x : Sp V' ⟶ B'.left, x ≫ B'.hom = 𝟙 _ ∧ x ≫ β' = spMap f ≫ (GlobalTheory.LowChart.cAt F v _ hs ((n : ℤ) • e a)).left ∧ x ≫ β'' = spMap κ ≫ (L.T.c₀ ((n : ℤ) • a)).left := by
  intro n hn _ h F r V₁ _ _ _ hV hdvr b₁ v hs
  have hV0 := hV
  obtain ⟨-, -, hVc, -⟩ := hV
  haveI := hVc
  let w := v (closedPoint V₁)
  obtain ⟨ψ, hψl, hψ⟩ := GlobalTheory.LowChart.exists_local_hom F w V₁ v rfl
  haveI : IsNoetherianRing (GlobalTheory.LowChart.W F w) := GlobalTheory.LowChart.isNoetherianRing_completedStalkSiegelFibrePower F w
  obtain ⟨R', _, _, ρ, hc', hloc, hinj, hfin, het, B, _, _, β, β₂, M, cub, hpb, hsq, hamp, hk, hiso⟩ :=
    GlobalTheory.T.exists_rigidified_cubical_root_polarisation_etale F (GlobalTheory.LowChart.W F w) (GlobalTheory.LowChart.isAdicComplete_completedStalkSiegelFibrePower F w) (GlobalTheory.LowChart.toPow F w ≫ (GlobalTheory.LowChart.powA F r).hom)

  let pt : Fin r → (𝟙_ (Over (Sp R')) ⟶ B) := fun i => Over.homMk
    (hpb.1.lift (spMap ρ ≫ GlobalTheory.LowChart.toPow F w ≫ (GlobalTheory.LowChart.coord F i).left) (𝟙 _) (by
      rw [Category.id_comp, Category.assoc, Category.assoc, Over.w (GlobalTheory.LowChart.coord F i)])) (hpb.1.lift_snd _ _ _)
  have hpt : ∀ i, (pt i).left ≫ β = spMap ρ ≫ GlobalTheory.LowChart.toPow F w ≫ (GlobalTheory.LowChart.coord F i).left := fun i =>
    hpb.1.lift_fst _ _ _
  let c : (Fin r → ℤ) → (𝟙_ (Over (Sp R')) ⟶ B) := fun a => ∏ i, pt i ^ a i
  have hc : ∀ a a', c (a + a') = c a * c a' := fun a a' => by
    simp only [c, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]
  obtain ⟨τ, hτg, hτs, hτa⟩ := GlobalTheory.TauLocal.exists_tau_local M cub c hc
  have hab : IsAbelianScheme B :=
    { comm := inferInstance
      smooth := MorphismProperty.of_isPullback (P := @Smooth) hpb.1 F.univ.ab.smooth
      proper := MorphismProperty.of_isPullback (P := @IsProper) hpb.1 F.univ.ab.proper
      geomConnected := MorphismProperty.of_isPullback (P := @GeometricallyConnected) hpb.1 F.univ.ab.geomConnected }
  have hdim : SmoothOfRelativeDimension h B.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange h).of_isPullback hpb.1
      (GlobalTheory.SiegSharpCover.smoothDim F.univ (by omega) (GlobalTheory.LowChart.isUnit_zetaAway n hn) (isUnit_natCast (show n ≠ 0 by omega)))

  let T : TautBase (cycAway n) R' :=
    { b := ρ.comp (GlobalTheory.LowChart.base F w)
      B := B
      isAb := hab
      g := h
      smoothDim := hdim
      M := M
      cub := cub
      ample := hamp
      ktriv := hk
      r := r
      c₀ := c
      c₀_add := hc
      τ₀ := τ
      τ₀_gen := hτg
      τ₀_symm := hτs
      τ₀_add := hτa }
  have hcomp : IsNoetherianRing R' := by
    algebraize [ρ]
    exact Algebra.FiniteType.isNoetherianRing (GlobalTheory.LowChart.W F w) R'
  obtain ⟨hEt, hur⟩ := etCompl F w R' ρ hloc hfin het
  have hcart : IsGrpPullback B F.univ.A ((spMap ρ ≫ GlobalTheory.LowChart.toPow F w) ≫ (GlobalTheory.LowChart.powA F r).hom) β := by
    rw [Category.assoc]; exact hpb
  have hsingle : ∀ i, c (Pi.single i 1) = pt i := fun i => by
    classical
    show ∏ j, pt j ^ (Pi.single i 1 : Fin r → ℤ) j = _
    rw [Finset.prod_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zpow_zero]) (by simp),
      Pi.single_eq_same, zpow_one]
  let L : LowBase (zetaAway n) n :=
    { h := h
      F := F
      W := R'
      noeth := hcomp
      complete := hc'
      T := T
      u := spMap ρ ≫ GlobalTheory.LowChart.toPow F w
      u_et := hEt
      u_sep := hur
      u_base := by
        show _ = spMap (ρ.comp (GlobalTheory.LowChart.base F w))
        rw [spMap_comp', GlobalTheory.LowChart.spMap_base, Category.assoc]
      dim := rfl
      β := β
      β₂ := β₂
      cart := hcart
      sq := hsq
      lb := hiso
      coord := fun i => by
        show (c (Pi.single i 1)).left ≫ β = _
        rw [hsingle, hpt, Category.assoc] }

  obtain ⟨V', _, _, _, f, κ, hV', hdvr', hfi, hff, hfl, hκl, hκρ⟩ :=
    GlobalTheory.T.exists_completeDVR_of_finite_etale_baseChange (GlobalTheory.LowChart.W F w) R' V₁ ρ ψ hloc hfin het hV0 hdvr hψl
  have hspec : spMap κ ≫ (spMap ρ ≫ GlobalTheory.LowChart.toPow F w) = spMap f ≫ v := by
    rw [← Category.assoc, ← spMap_comp', hκρ, spMap_comp', Category.assoc, hψ]
  have hb : κ.comp T.b = f.comp b₁ := by
    have e : spMap (κ.comp T.b) = spMap (f.comp b₁) := by
      show spMap (κ.comp (ρ.comp (GlobalTheory.LowChart.base F w))) = _
      rw [spMap_comp', spMap_comp', spMap_comp', GlobalTheory.LowChart.spMap_base, ← hs]
      simpa only [Category.assoc] using congrArg (· ≫ GlobalTheory.LowChart.toO F r) hspec
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)

  let SA := (GlobalTheory.LowChart.siegAt F v _ hs).A
  have hSA : IsGrpPullback SA F.univ.A (v ≫ (GlobalTheory.LowChart.powA F r).hom)
      (Pdiv.PullbackComparison.pφ (v ≫ (GlobalTheory.LowChart.powA F r).hom) F.univ.A) :=
    Pdiv.PullbackComparison.isGrpPullback _ _
  have hB' : IsGrpPullback ((Over.pullback (spMap f)).obj SA) SA (spMap f) (Pdiv.PullbackComparison.pφ (spMap f) SA) :=
    Pdiv.PullbackComparison.isGrpPullback _ _
  have hcomm : spMap κ ≫ ((spMap ρ ≫ GlobalTheory.LowChart.toPow F w) ≫ (GlobalTheory.LowChart.powA F r).hom) =
      spMap f ≫ (v ≫ (GlobalTheory.LowChart.powA F r).hom) := by
    rw [← Category.assoc, hspec, Category.assoc]
  obtain ⟨β'', hβ'', hββ⟩ := GlobalTheory.isGrpPullback_paste F.univ.A B SA ((Over.pullback (spMap f)).obj SA) _ _ (spMap f)
    (spMap κ) β _ _ hcart hSA hB' hcomm
  obtain ⟨β₂', hsq'⟩ : ∃ β₂', IsSquare β'' β₂' := ⟨_, GlobalTheory.LamPull.exists_isSquare hβ''.1.w⟩
  refine ⟨L, V', inferInstance, inferInstance, inferInstance, f, κ, AddEquiv.refl _, rfl, hV', hdvr', hfi, hff, hfl, hκl, hb,
    (Over.pullback (spMap f)).obj SA, inferInstance, Pdiv.PullbackComparison.pφ (spMap f) SA, β'', Pdiv.PullbackComparison.pφ₂ (spMap f) SA, β₂', hB',
    hβ'', Pdiv.PullbackComparison.isSquare _ _, hsq', ?_, ?_⟩
  · have key : β₂' ≫ β₂ = Pdiv.PullbackComparison.pφ₂ (spMap f) SA ≫ Pdiv.PullbackComparison.pφ₂ (v ≫ (GlobalTheory.LowChart.powA F r).hom) F.univ.A :=
      GlobalTheory.LamPull.isSquare_unique (isSquare_comp hsq' hsq)
        (by rw [hββ]; exact isSquare_comp (Pdiv.PullbackComparison.isSquare _ _) (Pdiv.PullbackComparison.isSquare _ _))
    have e1 : LBIso ((abelian₂ B M.L).pull β₂') (F.univ.P.pull (β₂' ≫ β₂)) := GlobalTheory.GenSpread.lbIso_pull_of_lbIso hiso β₂' rfl
    have e2 : LBIso (F.univ.P.pull (Pdiv.PullbackComparison.pφ₂ (spMap f) SA ≫ Pdiv.PullbackComparison.pφ₂ (v ≫ (GlobalTheory.LowChart.powA F r).hom) F.univ.A))
        ((F.univ.P.pull (Pdiv.PullbackComparison.pφ₂ (v ≫ (GlobalTheory.LowChart.powA F r).hom) F.univ.A)).pull (Pdiv.PullbackComparison.pφ₂ (spMap f) SA)) :=
      GlobalTheory.GenSpread.lbIso_pull_pull F.univ.isLB _ rfl
    rw [key] at e1
    exact LBIso.trans (pull_isLB (pull_isLB F.univ.isLB _) _) (pull_isLB F.univ.isLB _)
      (pull_isLB (DVR.linComb_isLB M.L M.isLB _ _) _) (LBIso.symm e2) (LBIso.symm e1)
  · intro a
    let q : Fin r → (Over.mk (spMap κ ≫ ((spMap ρ ≫ GlobalTheory.LowChart.toPow F w) ≫ (GlobalTheory.LowChart.powA F r).hom)) ⟶ F.univ.A) :=
      fun i => Over.homMk (spMap f ≫ v ≫ (GlobalTheory.LowChart.coord F i).left) (by
        show _ = spMap κ ≫ _
        rw [hcomm, Category.assoc, Category.assoc, Over.w (GlobalTheory.LowChart.coord F i)])
    have cA : (GlobalTheory.LowChart.cAt F v _ hs ((n : ℤ) • a)).left ≫ SA.hom = 𝟙 _ := Over.w _
    have h0 : (spMap f ≫ (GlobalTheory.LowChart.cAt F v _ hs ((n : ℤ) • a)).left) ≫ SA.hom = 𝟙 _ ≫ spMap f := by
      rw [Category.assoc, cA]
      simp
    obtain ⟨x, lf, ls⟩ : ∃ x : Sp V' ⟶ ((Over.pullback (spMap f)).obj SA).left,
        x ≫ Pdiv.PullbackComparison.pφ (spMap f) SA = spMap f ≫ (GlobalTheory.LowChart.cAt F v _ hs ((n : ℤ) • a)).left ∧
          x ≫ ((Over.pullback (spMap f)).obj SA).hom = 𝟙 _ :=
      ⟨hB'.1.lift _ _ h0, hB'.1.lift_fst _ _ _, hB'.1.lift_snd _ _ _⟩
    refine ⟨x, ls, lf, ?_⟩
    have e1 := prodPush hSA (GlobalTheory.LowChart.ptAt F v _ hs) _ q (spMap f) hcomm.symm
      (fun i => by rw [GlobalTheory.LowChart.ptAt_left]; rfl) ((n : ℤ) • a)
    have e2 := prodPush hcart pt _ q (spMap κ) rfl (fun i => by
      rw [hpt]
      show _ = spMap f ≫ v ≫ _
      simpa only [Category.assoc] using congrArg (· ≫ (GlobalTheory.LowChart.coord F i).left) hspec) ((n : ℤ) • a)
    apply hcart.1.hom_ext
    · calc (x ≫ β'') ≫ β = x ≫ Pdiv.PullbackComparison.pφ (spMap f) SA ≫ Pdiv.PullbackComparison.pφ (v ≫ (GlobalTheory.LowChart.powA F r).hom) F.univ.A := by
            rw [Category.assoc, hββ]
        _ = spMap f ≫ (GlobalTheory.LowChart.cAt F v _ hs ((n : ℤ) • a)).left ≫
            Pdiv.PullbackComparison.pφ (v ≫ (GlobalTheory.LowChart.powA F r).hom) F.univ.A :=
          (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ Pdiv.PullbackComparison.pφ (v ≫ (GlobalTheory.LowChart.powA F r).hom) F.univ.A) lf).trans
            (Category.assoc _ _ _))
        _ = (∏ i, q i ^ ((n : ℤ) • a) i).left := e1
        _ = (spMap κ ≫ (c ((n : ℤ) • a)).left) ≫ β := e2.symm.trans (Category.assoc _ _ _).symm
    · calc (x ≫ β'') ≫ B.hom = x ≫ ((Over.pullback (spMap f)).obj SA).hom ≫ spMap κ := by
            rw [Category.assoc, hβ''.1.w]
        _ = spMap κ := (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ spMap κ) ls).trans (Category.id_comp _))
        _ = spMap κ ≫ (c ((n : ℤ) • a)).left ≫ B.hom := by rw [Over.w (c ((n : ℤ) • a))]; exact (Category.comp_id _).symm
        _ = (spMap κ ≫ (c ((n : ℤ) • a)).left) ≫ B.hom := (Category.assoc _ _ _).symm

end GlobalTheory.LowLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionsLowerBoundAmpleMinusTwistStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smallSections_lowerBound_ample_minus_twist : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ c : ℕ, GenAt P c → Regime P D → NefFib P.L → P.L.SemiPos D → ∀ a : ℝ, P.L.IsSelfInter a → ∀ ε : ℝ, 0 < ε → ∀ᶠ M : ℕ in atTop, (a / (D + 1).factorial - ε) * (M : ℝ) ^ (D + 1) ≤ P.lc M (-c) 1 := by
  first | exact @GlobalTheory.HSLowerTwist.main | exact GlobalTheory.HSLowerTwist.main | (intros; apply GlobalTheory.HSLowerTwist.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalChartEqOfSameGenericPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tautologicalChart_eq_of_same_genericPoint : ∀ {g n : ℕ} {φ : InvFun ℤ}, 3 ≤ n → ∀ (F : SFam g n (zetaAway n)) (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing C.R) ⟶ F.X) (α₁ : pullback G₁.hom (jK C.R) ⟶ F.univ.A.left), C.IsFam F G₁ y α₁ → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (θ₁ θ₂ : C.R →+* R'), IsCN R' → Function.Injective θ₁ → Function.Injective θ₂ → IsLocalHom θ₁ → IsLocalHom θ₂ → ∀ (κ₁ κ₂ : Sp (FractionRing R') ⟶ Sp (FractionRing C.R)), κ₁ ≫ jK C.R = jK R' ≫ spMap θ₁ → κ₂ ≫ jK C.R = jK R' ≫ spMap θ₂ → κ₁ ≫ y = κ₂ ≫ y → spMap (θ₁.comp C.iw) ≫ C.u = spMap (θ₂.comp C.iw) ≫ C.u ∧ (θ₁.comp C.iw = θ₂.comp C.iw → ∀ k, θ₁ (C.s k) = θ₂ (C.s k)) := by
  first | exact @GlobalTheory.TInj.tautChart_eq_of_genPt | exact GlobalTheory.TInj.tautChart_eq_of_genPt | (intros; apply GlobalTheory.TInj.tautChart_eq_of_genPt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSystemClassSumsValuesOfFunctionsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSystem_classSums_values_of_functions : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam) (Φ : VPre (id : ℤ → ℤ) g W (X₁.M.Z.presheaf.stalk z₁)) (lab : Φ.Q → X₁.S.Gam), IsGeo X₁ z₁ act x₀ Φ lab → Φ.Exact (X₁.S.r * X₁.S.N) := by
  first | exact @GlobalTheory.Poinc.Sep.ExactSums.exact_of_isGeo | exact GlobalTheory.Poinc.Sep.ExactSums.exact_of_isGeo | (intros; apply GlobalTheory.Poinc.Sep.ExactSums.exact_of_isGeo <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedSumZetaPowerResidueDividingLabelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedSum_zeta_power_residue_dividing_label : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (t1 : Y1 → V1) (δ1 : I → Y1 → Y1) (𝔪1 : GlobalTheory.GSep.GMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : Y1 → C → V1, 𝔪1.Terms x₀ lab T → ∀ (c : C), lab c ∈ X₁.S.supI X₁.M z₁ → ∀ τ ∈ X₁.S.TT X₁.M z₁, ∀ (sg : ℤˣ) (e : ℕ), GlobalTheory.GSep.TwistSum X₁ z₁ act x₀ 𝔪1 lab T sg c τ e → ∀ s u : X₁.M.Z.presheaf.stalk z₁, X₁.M.stalkHom z₁ s = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ e) → X₁.M.stalkHom z₁ u = X₁.S.th (lab c + τ) / X₁.S.th (lab c) → ev1 (s * u) - 1 ∈ maximalIdeal V1 := by
  first | exact @GlobalTheory.GSep.TwistResid.twist_resid | exact GlobalTheory.GSep.TwistResid.twist_resid | (intros; apply GlobalTheory.GSep.TwistResid.twist_resid <;> assumption)
end

