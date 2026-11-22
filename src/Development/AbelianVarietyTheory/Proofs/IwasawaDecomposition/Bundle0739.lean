import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAdmissibleFanOfCellMultOneCMField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0445
import Development.AbelianVarietyTheory.Counterexamples.DegenerateExamples.NotExistsExponentConditionCard
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0006
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CMTypeEmbeddings
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0733
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0980
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0363
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0199
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0423
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0333
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0718
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0655
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0673
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0705
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0719
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0028
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0707
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Formalism.DegreeFormula.Statement

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOfPrimitiveBalancedFormSameRealRay
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan.SmoothEnd

theorem eq_of_isPrim_of_toReal_eq_smul : ∀ {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X] (x y : LinearMap.BilinForm ℤ X)
    (hx : x ∈ balForms bar X) (hy : y ∈ balForms bar X), IsPrim bar (⟨x, hx⟩ : balForms bar X) →
    IsPrim bar (⟨y, hy⟩ : balForms bar X) → ∀ b : ℝ, 0 < b → toReal x = b • toReal y → x = y := by
  intro O _ bar X _ _ x y hx hy px py b hb h
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact not_isPrim_zero (bar := bar) py
  obtain ⟨a, c, hac⟩ : ∃ a c, y a c ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hy0 (LinearMap.ext₂ hc)
  have hR : ∀ u v, (x u v : ℝ) = b * (y u v : ℝ) := fun u v => by
    have := LinearMap.congr_fun₂ h u v
    simpa [toReal_apply] using this
  have hacR : (y a c : ℝ) ≠ 0 := by exact_mod_cast hac
  have hxac : x a c ≠ 0 := by
    have : (x a c : ℝ) ≠ 0 := by rw [hR]; exact mul_ne_zero hb.ne' hacR
    exact_mod_cast this
  have habs : |(x a c : ℝ)| = b * |(y a c : ℝ)| := by
    rw [hR, abs_mul, abs_of_pos hb]
  refine eq_of_isPrim hx hy px py (k := (y a c).natAbs) (n := (x a c).natAbs)
    (Int.natAbs_pos.2 hac) (Int.natAbs_pos.2 hxac) (LinearMap.ext₂ fun u v => ?_)
  simp only [LinearMap.smul_apply, smul_eq_mul, Int.natCast_natAbs]
  have e : |(y a c : ℝ)| * (x u v : ℝ) = |(x a c : ℝ)| * (y u v : ℝ) := by
    rw [hR u v, habs]; ring
  exact_mod_cast e

end GlobalTheory.PolFan.SmoothEnd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EsymmMapMulConst
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspFrobSplit

theorem esymm_map_mul_const (s : Multiset ℂ) (c : ℂ) (k : ℕ) :
    (s.map (fun x => x * c)).esymm k = c ^ k * s.esymm k := by
  unfold Multiset.esymm
  rw [Multiset.powersetCard_map, Multiset.map_map, ← Multiset.sum_map_mul_left]
  congr 1
  refine Multiset.map_congr rfl fun t ht => ?_
  have hk : Multiset.card t = k := (Multiset.mem_powersetCard.1 ht).2
  simp only [Function.comp_apply, Multiset.prod_map_mul, Multiset.map_id', Multiset.map_const',
    Multiset.prod_replicate, hk]
  ring

theorem galPol_lifts_ae : ∀ (D : D7) (cf : CharFrame D) (Rw : GlobalTheory.HeightCounting.RowSide D) (Sb : Finset (PlE D.host)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0), ValLL0 D cf → GlobalTheory.TwInputs.EigTrue D cf Rw Sb eig → ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ σ, D.what₂.isot j σ ≠ ⊥ → D.nd.goodRow σ → ∀ π : D.naut.CG D.R.r, D.naut.csd π → (∀ w, IsSplitPl D.host w → D.naut.locG π w = Rw.locR σ w) → ∀ᶠ w in Filter.cofinite, IsSplitPl D.host w → galPol D.naut (D.naut.lpTw (D.naut.locG π w) ((1 - (D.R.r : ℝ)) / 2)) ∈ Polynomial.lifts (embLL0 D) := by
  intro D cf Rw Sb eig hV hE j hj1 hj2 σ hiso hgood π hcsd hloc
  obtain ⟨bar, hinj, hbar⟩ := GlobalTheory.ConjPoly.exists_conj D
  let j' : Fin D.R.m := ⟨j - 1, by omega⟩
  have hjj : (j' : ℕ) + 1 = j := by simp only [j']; omega
  have hfin : (bar ⁻¹' ((Sb : Set (PlE D.host)) ∪ {v | ¬ (cf.mu0 j').UnrAt v})).Finite :=
    (Sb.finite_toSet.union (GlobalTheory.Mem.UnrAe.finite_ramified _)).preimage hinj.injOn
  refine Filter.eventually_cofinite.2 (hfin.subset ?_)
  intro w hw
  simp only [Set.mem_setOf_eq] at hw
  by_contra hw'
  apply hw
  intro hsplit
  simp only [Set.mem_preimage, Set.mem_union, Finset.mem_coe, Set.mem_setOf_eq, not_or, not_not] at hw'
  obtain ⟨hSb, hunrμ⟩ := hw'
  obtain ⟨hc, -, hsp⟩ := hbar w
  have hPs : IsSplitPl D.host (bar w) := hsp hsplit
  have hE' := hE j' σ (by rw [hjj]; exact hiso) hgood (bar w) hPs hSb
  rw [hjj] at hE'
  obtain ⟨hunrP, heig⟩ := hE'
  rw [← hloc (bar w) hPs] at hunrP heig
  obtain ⟨hunrw, hfw⟩ := D.naut.csd_unr π (bar w) w hcsd (GlobalTheory.ToricDenomCheck.isConj_symm hc) hunrP
  have hfP : D.naut.frobEig (D.naut.locG π (bar w)) =
      (D.naut.frobEig (D.naut.locG π w)).map (fun x => x⁻¹) := by
    rw [hfw, Multiset.map_map]; simp
  have hcard : (D.naut.frobEig (D.naut.locG π w)).card = D.R.r := by
    rw [D.naut.frobEig_card _ hunrw, D.naut.locG_dim]
  have hmemS : ∀ x, x ∈ (embLL0 D).fieldRange → x ∈ Set.range (embLL0 D) :=
    fun x h => (RingHom.mem_fieldRange).1 h
  have hNS : ∀ n : ℕ, (n : ℂ) ∈ (embLL0 D).fieldRange := fun n => natCast_mem _ n
  have hN0 : (Formalism.ConjugateSelfDual.normV (bar w) : ℂ) ≠ 0 := by exact_mod_cast GlobalTheory.ConjPoly.normV_ne_zero (bar w)
  have hμ0 : (((cf.mu0 j').val (bar w) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  obtain ⟨yμ, hyμ⟩ := hV.mu0 j' (bar w) hunrμ
  have hμS : (((cf.mu0 j').val (bar w) : ℂˣ) : ℂ) ∈ (embLL0 D).fieldRange :=
    ⟨yμ, by rw [hyμ]; simp [Formalism.L2.Host.HChar.valTw]⟩
  have hAk : ∀ k, 1 ≤ k → k ≤ D.R.r →
      (D.naut.frobEig (D.naut.locG π w)).esymm k ∈ (embLL0 D).fieldRange := by
    intro k hk1 hk2
    have h := heig k hk1 hk2
    rw [hfP, Multiset.map_map] at h
    have hfun : (fun a : ℂ => a⁻¹ * (((cf.mu0 j').val (bar w) : ℂˣ) : ℂ)⁻¹ *
          ((Formalism.ConjugateSelfDual.normV (bar w) : ℂ) ^ (D.R.nV / 2))⁻¹) ∘ (fun x : ℂ => x⁻¹) =
        fun x => x * ((((cf.mu0 j').val (bar w) : ℂˣ) : ℂ)⁻¹ *
          ((Formalism.ConjugateSelfDual.normV (bar w) : ℂ) ^ (D.R.nV / 2))⁻¹) := by
      funext x; simp [mul_assoc]
    rw [hfun, esymm_map_mul_const] at h
    have hd : ((((cf.mu0 j').val (bar w) : ℂˣ) : ℂ)⁻¹ *
        ((Formalism.ConjugateSelfDual.normV (bar w) : ℂ) ^ (D.R.nV / 2))⁻¹) ≠ 0 := by
      simp [hμ0, hN0]
    have hdS : ((((cf.mu0 j').val (bar w) : ℂˣ) : ℂ)⁻¹ *
        ((Formalism.ConjugateSelfDual.normV (bar w) : ℂ) ^ (D.R.nV / 2))⁻¹) ∈ (embLL0 D).fieldRange :=
      Subfield.mul_mem _ (Subfield.inv_mem _ hμS) (Subfield.inv_mem _ (Subfield.pow_mem _ (hNS _) _))
    have hpow : ((Formalism.ConjugateSelfDual.normV (bar w) : ℂ) ^ (k * (D.R.r - k) / 2)) ≠ 0 := pow_ne_zero _ hN0
    have heq : (D.naut.frobEig (D.naut.locG π w)).esymm k =
        D.what₂.embLL ↑(eig j σ k (bar w)) * ((Formalism.ConjugateSelfDual.normV (bar w) : ℂ) ^ (k * (D.R.r - k) / 2))⁻¹ *
          (((((cf.mu0 j').val (bar w) : ℂˣ) : ℂ)⁻¹ *
            ((Formalism.ConjugateSelfDual.normV (bar w) : ℂ) ^ (D.R.nV / 2))⁻¹) ^ k)⁻¹ := by
      rw [h]; field_simp
    rw [heq]
    refine Subfield.mul_mem _ (Subfield.mul_mem _ ⟨eig j σ k (bar w), rfl⟩
      (Subfield.inv_mem _ (Subfield.pow_mem _ (hNS _) _))) (Subfield.inv_mem _ (Subfield.pow_mem _ hdS _))
  have hr : Odd D.R.r := by
    obtain ⟨a, ha⟩ := D.R.k_even
    obtain ⟨b, hb⟩ := D.R.m_even
    have := D.R.two_le_m
    exact ⟨a + b - 1, by simp only [Formalism.BasicNotions.Ranks.r]; omega⟩
  obtain ⟨q, hq⟩ := hr
  have hs : ((Formalism.ConjugateSelfDual.normV w : ℕ) : ℂ) ^ ((((1 - (D.R.r : ℝ)) / 2 : ℝ)) : ℂ) =
      ((Formalism.ConjugateSelfDual.normV w : ℂ) ^ q)⁻¹ := by
    have : ((((1 - (D.R.r : ℝ)) / 2 : ℝ)) : ℂ) = -(q : ℂ) := by
      rw [hq]; push_cast; ring
    rw [this, Complex.cpow_neg, Complex.cpow_natCast]
  rw [Polynomial.lifts_iff_coeff_lifts]
  intro n
  unfold Formalism.MainNotions.N.galPol
  rw [D.naut.frobEig_tw _ _ hunrw, hs]
  have hBk : ∀ k, k ≤ D.R.r →
      ((D.naut.frobEig (D.naut.locG π w)).map (fun x => x * ((Formalism.ConjugateSelfDual.normV w : ℂ) ^ q)⁻¹)).esymm k ∈
        (embLL0 D).fieldRange := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · have : Multiset.esymm ((D.naut.frobEig (D.naut.locG π w)).map (fun x => x * ((Formalism.ConjugateSelfDual.normV w : ℂ) ^ q)⁻¹)) 0 = 1 := by
        simp [Multiset.esymm, Multiset.powersetCard_zero_left]
      rw [this]; exact Subfield.one_mem _
    rw [esymm_map_mul_const]
    exact Subfield.mul_mem _ (Subfield.pow_mem _ (Subfield.inv_mem _ (Subfield.pow_mem _ (hNS _) _)) _)
      (hAk k hk1 hk)
  have hBc : ((D.naut.frobEig (D.naut.locG π w)).map
      (fun x => x * ((Formalism.ConjugateSelfDual.normV w : ℂ) ^ q)⁻¹)).card = D.R.r := by
    rw [Multiset.card_map, hcard]
  rcases le_or_gt n D.R.r with hn | hn
  · rw [Multiset.prod_X_sub_C_coeff _ (hBc.symm ▸ hn), hBc]
    exact hmemS _ (Subfield.mul_mem _ (Subfield.pow_mem _ (Subfield.neg_mem _ (Subfield.one_mem _)) _)
      (hBk _ (by omega)))
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt
      (by rw [Polynomial.natDegree_multiset_prod_X_sub_C_eq_card, hBc]; exact hn)]
    exact ⟨0, map_zero _⟩

end GlobalTheory.CuspFrobSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyAuxiliaryPlacesSplitDistinct
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.TwInputs.PlacesAt

theorem evLgG_placesOk : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt),
    ∃ w0, GlobalTheory.LamTie.PlacesOk (w.D Z).host (AbsolutelyIrreducibleSpan.q0 (w.D Z)) w0 := by
  refine evG_good.imp fun K C5 c6 Cb hG _ => ?_
  refine (GlobalTheory.TwInputs.SmallField.lg_lam K).imp fun B f _ hO _ _ T w Z => ?_
  have hq := GlobalTheory.TwInputs.SmallField.auxiliary_prime_ne_type_prime K C5 c6 Cb hG B.toPre hO
  have hqp := (GlobalTheory.EX.DC.globalTwisting_spec_fact B.toPre.host).1
  obtain ⟨w0, hw0⟩ := GlobalTheory.TwInputs.SmallField.exists_over B.toPre.host.E hqp
  have hmod : ∀ p ∈ [B.toPre.host.g 0, B.toPre.host.g 1, B.toPre.host.pde, B.toPre.host.pde', GlobalTheory.EX.DC.q0H B.toPre.host],
      p ≡ 1 [MOD B.toPre.host.QS * B.toPre.host.q * B.toPre.host.d] := by
    intro p hp
    rw [Nat.ModEq, Nat.mod_eq_of_lt (GlobalTheory.TwInputs.SmallField.one_lt_cond B.toPre)]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    exacts [B.toPre.g_cond 0, B.toPre.g_cond 1, B.toPre.pde_cond.1, B.toPre.pde_cond.2, GlobalTheory.EX.DC.mod_cond _]
  exact ⟨w0, (GlobalTheory.LamTie.placesOk_of_modEq_one B.toPre.R B.toPre.host _ w0 hqp hmod hq
    (GlobalTheory.EX.DC.q0H_ne_pde_and_ne_pde' _).1 (GlobalTheory.EX.DC.q0H_ne_pde_and_ne_pde' _).2 hw0).1⟩

end GlobalTheory.TwInputs.PlacesAt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyBaseChangeHypothesesColumnChoices
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.Mem.HypCMRec

theorem hypCM_all (D : D7) : SphericalInertData.HypCM D := by
  refine ⟨?_, GlobalTheory.DesignBC.two_le_finrank D, fun w hw h2 => hw (GlobalTheory.DesignBC.isSplitPl_of_two_mem D w h2)⟩
  letI := D.host.cmStar
  exact D.sp.cm.cmUnram

theorem hypCM_at_record : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), SphericalInertData.HypCM (w.D Z) :=
  evG_all fun K => lg_all K fun _ _ _ _ _ _ _ _ => hypCM_all _

end GlobalTheory.Mem.HypCMRec

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyCoeffFieldContainsRootOfUnityGroupOrde
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.HeightCounting.Up

theorem isAlgebraic_exp_two_pi_div (n : ℕ) (hn : 0 < n) :
    IsAlgebraic ℚ (Complex.exp (2 * Real.pi * Complex.I / n)) :=
  (((Complex.isPrimitiveRoot_exp n hn.ne').isIntegral hn).tower_top (A := ℚ)).isAlgebraic

theorem rootsLL_evLgG :
    EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), RootsLL (w.D Z) := by
  have hLg : ∀ K : Ctx, large₂ K fun B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), RootsLL (w.D Z) := by
    intro K
    refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅,
      fun B _ _ _ _ => {Complex.exp (2 * Real.pi * Complex.I / B.restRowsFiniteGroupCard)}, by simp, ?_, ?_⟩
    · intro B _ _ _ _ z hz
      rw [Finset.mem_singleton] at hz
      subst hz
      exact isAlgebraic_exp_two_pi_div _ B.restRowsFiniteGroupCard_pos
    · intro B f T₀ _ hH _ _ _ T w Z
      obtain ⟨x, hx⟩ : ∃ x : B.LL, B.embLL x = Complex.exp (2 * Real.pi * Complex.I / B.toPre.restRowsFiniteGroupCard) :=
        hH.2 _ (Finset.mem_singleton_self _)
      refine ⟨x, ?_⟩
      show IsPrimitiveRoot x B.toPre.restRowsFiniteGroupCard
      rw [← IsPrimitiveRoot.map_iff_of_injective (f := B.embLL) B.embLL.injective, hx]
      exact Complex.isPrimitiveRoot_exp _ B.toPre.restRowsFiniteGroupCard_pos.ne'
  exact EvG.imp evG_good fun K _ _ _ _ _ => hLg K

end GlobalTheory.HeightCounting.Up
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyHostEqCompositumTotallyRealImagQuadrat
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.Mem.HostEFK

theorem hypEFK_ev : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), SphericalInertData.HypEFK (w.D Z) :=
  evG_all fun K => lg_all K fun B f T _ _ T' w Z => GlobalTheory.DesignBC.hypEFK (w.D Z)

end GlobalTheory.Mem.HostEFK
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyHundredLeHermitianRankColumnChoices
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.Mem.RankSize

theorem rank_ge_hundred : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), 100 ≤ (w.D Z).R.r := by
  refine ⟨1, one_pos, fun _ _ _ _ _ _ _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ =>
    ⟨0, fun _ _ => ⟨0, fun _ _ => ⟨100, fun K _ _ _ _ hx _ => ?_⟩⟩⟩⟩⟩
  refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, by simp, by simp,
    fun B f _ hO _ _ _ _ T w Z => ?_⟩
  show 100 ≤ B.R.r
  obtain ⟨sp, hT, hY, hA, hV, hz, hB, -⟩ := hO
  have hRK : B.toPre.R = K.P.R := by rw [hB]; rfl
  have hR : GlobalTheory.EX.RankVal K.s B.toPre.R := hRK ▸ K.ok.rank
  obtain ⟨-, -, ⟨hk, -⟩, -⟩ := hR
  have hx1 := K.s.one_lt_alt
  have he := K.s.eps_pos
  have hk1 : K.s.x ≤ (B.toPre.R.k : ℝ) := by
    calc K.s.x = K.s.x ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ K.s.x ^ (9 / 2 + 10 * K.s.eps) := Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
      _ ≤ _ := hk
  have h100 : (100 : ℝ) ≤ (B.toPre.R.k : ℝ) := hx.trans hk1
  have hk100 : 100 ≤ B.toPre.R.k := by exact_mod_cast h100
  have h2m := B.toPre.R.two_le_m
  have hmk := B.toPre.R.m_add_three_le_k
  have hkr : B.toPre.R.k ≤ B.toPre.R.r := by unfold Ranks.r; omega
  exact hk100.trans hkr

end GlobalTheory.Mem.RankSize
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallySpacesVDefiniteColumnChoices
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.Mem.DefSpaces

theorem v_isDefinite : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), ∀ j, 1 ≤ j → j ≤ (w.D Z).R.m → ((w.D Z).sp.V j).IsDefinite := by
  refine (GlobalTheory.Mem.Top.evG_of_ev GlobalTheory.Mem.StdSize.vstd_size_ev).imp fun K _ _ _ _ hK =>
    GlobalTheory.Mem.Top.GroupRetwisting.lg_all K fun B f _ hO _ T w Z j hj1 hj2 => ?_
  obtain ⟨hV, -⟩ := hK (w.st Z) hO
  have hm : (w.st Z).toD7.R.m = (w.D Z).R.m := rfl
  have hp := GlobalTheory.RepsObj.isPosDef_of_vStd (D := (w.st Z).toD7) ⟨j - 1, by omega⟩ (hV ⟨j - 1, by omega⟩)
  change ((w.st Z).toD7.sp.V j).IsDefinite
  intro τ
  left
  have e : j - 1 + 1 = j := by omega
  have := hp τ
  simp only [Formalism.IndefR.Links.Vc, e] at this
  exact this

end GlobalTheory.Mem.DefSpaces
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyTwoMulRankLeLevelPrime
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.Mem.Top.Bl

theorem two_mul_r_le_g_level : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), ∀ k,
    2 * (w.D Z).R.r ≤ (w.D Z).host.g k := by
  refine evG_all fun K => lg_all K fun B f T hO _ T' w Z k => ?_
  obtain ⟨sp, hT, hY, hA, hV, hz, hB, -⟩ := hO
  have hR' : B.toPre.R = K.P.R := by rw [hB]; rfl
  have hg : B.toPre.host.g = K.P.H.g := by rw [hB]; rfl
  show 2 * B.R.r ≤ B.host.g k
  rw [show B.host.g k = K.P.H.g k from congrFun hg k, show B.R.r = K.P.R.r from by rw [hR']]
  have hgk : ((K.P.R.k : ℝ) * K.s.b) ^ 8 ≤ (K.P.H.g k : ℝ) := (K.ok.val.2.2.2.2.1 k).1
  have hb : 1 ≤ K.s.b := Real.one_le_exp (Real.rpow_nonneg (by linarith [K.s.one_lt_alt]) _)
  have hk0 : (0 : ℝ) ≤ K.P.R.k := Nat.cast_nonneg _
  have hkb : (K.P.R.k : ℝ) ^ 8 ≤ (K.P.H.g k : ℝ) :=
    le_trans (pow_le_pow_left₀ hk0 (le_mul_of_one_le_right hk0 hb) 8) hgk
  have hk8 : (K.P.R.k) ^ 8 ≤ K.P.H.g k := by exact_mod_cast hkb
  have h2k : 2 ≤ K.P.R.k := by
    have := K.P.R.f_le_k
    have : 0 < K.P.R.ord := K.P.R.ord_pos
    omega
  have hr : 2 * K.P.R.r ≤ 4 * K.P.R.k := by
    have := K.P.R.m_add_three_le_k
    simp only [Ranks.r]
    omega
  have h4 : 4 * K.P.R.k ≤ K.P.R.k ^ 8 := by
    calc 4 * K.P.R.k ≤ K.P.R.k ^ 7 * K.P.R.k := by
          apply Nat.mul_le_mul_right
          calc 4 ≤ 2 ^ 7 := by norm_num
            _ ≤ K.P.R.k ^ 7 := Nat.pow_le_pow_left h2k 7
      _ = K.P.R.k ^ 8 := by ring
  omega

end GlobalTheory.Mem.Top.Bl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCellOfContactSetIntInequalitiesStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cell_of_contactSet_intInequalities : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (ψ : InvFun O) (K : ℕ) (Λ : (X × X) →₀ ℤ) (m : ℕ) (u : Fin m → LinearMap.BilinForm ℤ X) (A : Set (Fin m → ℤ)), A.Finite → 0 < K → (∀ i y z, u i y z = u i z y) → (∀ i y, 0 ≤ u i y y) → (∀ (β : LinearMap.BilinForm ℤ X) (t : Fin m → ℝ), toReal β = ∑ i, t i • toReal (u i) → ∀ i, ∃ z : ℤ, t i = z) → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → (K : ℝ) * ψ.evalZ β ≤ evalW Λ (toReal β)) → (∀ B ∈ psdCone bar X, (K : ℝ) * evalR ψ B = evalW Λ B → ∃ t : Fin m → ℝ, (∀ i, 0 ≤ t i) ∧ (∀ v ∈ A, ∑ i, (v i : ℝ) * t i ≤ 0) ∧ B = ∑ i, t i • toReal (u i)) → (∀ t : Fin m → ℝ, (∀ i, 0 ≤ t i) → (∀ v ∈ A, ∑ i, (v i : ℝ) * t i ≤ 0) → ∑ i, t i • toReal (u i) ∈ realForms bar X → (K : ℝ) * evalR ψ (∑ i, t i • toReal (u i)) = evalW Λ (∑ i, t i • toReal (u i))) → ∃ (s : ℕ) (γ : Fin s → LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧ ∀ B ∈ psdCone bar X, (K : ℝ) * evalR ψ B = evalW Λ B → B ∈ rcone γ := by
  first | exact @GlobalTheory.PolCell.exists_isCell_of_contact | exact GlobalTheory.PolCell.exists_isCell_of_contact | (intros; apply GlobalTheory.PolCell.exists_isCell_of_contact <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsComparisonDataStepsUpToRankStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_comparisonData_steps_upTo_rank : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ (Fl : ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
        G.Fills ((w.D Z).gat u v hg)),
      (∀ u v hg, (Fl u v hg).t = (w.D Z).R.t ∧ (Fl u v hg).mm = (w.D Z).R.m) →
      (∀ u v hg (x : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' x)), ∀ j ∈ SizeData₂.lifts (w.D Z),
        ((Fl u v hg).w x j s : ℝ) = wj (w.D Z) j (t.Gt.gat_pos u v hg ⟨x, s⟩) - G.kaJ (w.D Z) j) →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      (w.D Z).what₂.muAt v = (w.D Z).what₂.mu0 →
      ∃ (Lv : G.Levels (Fl u v hg)) (I : Formalism.MainNotions.G.CmpJ.CmpJIn (w.tw Z) u ((w.D Z).what₂.muAt v) v hg Lv),
        Formalism.MainNotions.G.CmpJ.CmpJHyp t.cmp I ∧
        (∀ j hj, (I.at' j hj).C = (w.D Z).chTw u ((w.D Z).what₂.muAt v)) ∧
        (∀ j hj, Formalism.MainNotions.G.KAat.ChX (I.at' j hj).st) ∧
        (∀ j, (w.D Z).R.m ≤ j → IsEmpty (Lv.compS j)) := by
  first | exact @GlobalTheory.Mem.Top.KerOne.CertEq.exists_comparisonData_steps_at_baseCharacter | exact GlobalTheory.Mem.Top.KerOne.CertEq.exists_comparisonData_steps_at_baseCharacter | (intros; apply GlobalTheory.Mem.Top.KerOne.CertEq.exists_comparisonData_steps_at_baseCharacter <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsComponentUniformisationBoundedDomainCompleStatement
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_componentUniformisation_boundedDomain_complexPoints : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∃ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) := by
  first | exact @GlobalTheory.LieBase.UnifExists.exists_unif | exact GlobalTheory.LieBase.UnifExists.exists_unif | (intros; apply GlobalTheory.LieBase.UnifExists.exists_unif <;> assumption)
end

