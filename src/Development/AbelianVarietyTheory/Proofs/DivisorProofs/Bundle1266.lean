import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0050
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1230
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1187
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1043
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1217
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1231
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0116
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0148
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GraphIdealLocalizationMaximalIdealEqSpan
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1167
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1213
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1219
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0229
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportPushforwardSubschemeSubset
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0317
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1241

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapConditionsOfLargeGaps
section
section
open GlobalTheory.PsCo.PcEG

noncomputable section

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap

namespace GlobalTheory.PsCo.PcEF

namespace GapNumber

theorem chain {r : ℕ} {lam : Fin r → ℤ} {H : ℤ} (hH : 0 ≤ H)
    (hg : ∀ i j : Fin r, (j : ℕ) = i + 1 → H ≤ lam i - lam j) :
    ∀ i j : Fin r, i < j → H ≤ lam i - lam j := by
  suffices h : ∀ (k : ℕ) (i j : Fin r), (j : ℕ) = i + k + 1 → H ≤ lam i - lam j by
    intro i j hij
    have : (i : ℕ) < j := hij
    exact h ((j : ℕ) - i - 1) i j (by omega)
  intro k
  induction k with
  | zero => intro i j h; exact hg i j (by omega)
  | succ k ih =>
    intro i j h
    have hm : (i : ℕ) + k + 1 < r := by have := j.isLt; omega
    have h1 := ih i ⟨(i : ℕ) + k + 1, hm⟩ rfl
    have h2 := hg ⟨(i : ℕ) + k + 1, hm⟩ j (by show (j : ℕ) = (i : ℕ) + k + 1 + 1; omega)
    linarith

end GapNumber

theorem gapConditions_of_largeGaps : GapNum := by
  intro r hr ε lam hg
  obtain ⟨k, hk⟩ := hr
  have hr1 : 1 ≤ r := by omega
  have hH : (0 : ℤ) ≤ 100 * (r : ℤ) ^ 4 := by positivity
  have hc := GapNumber.chain hH hg
  have hcR : ∀ i j : Fin r, i < j → 100 * (r : ℝ) ^ 4 ≤ (lam i : ℝ) - lam j := fun i j h => by
    exact_mod_cast hc i j h
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  have hpos : (0 : ℝ) < 100 * (r : ℝ) ^ 4 := by positivity
  have hanti : StrictAnti (fun a => (lam a : ℝ)) := fun i j h => by
    have := hcR i j h
    show (lam j : ℝ) < lam i
    linarith
  have hgap : GapAtLeast ε (fun a => (lam a : ℝ)) (100 * (r : ℝ) ^ 4) := by
    intro a b hab
    have hne : a ≠ b := fun h => hab (h ▸ rfl)
    show 100 * (r : ℝ) ^ 4 ≤ |(lam a : ℝ) - lam b|
    rcases lt_or_gt_of_ne hne with h | h
    · exact (hcR a b h).trans (le_abs_self _)
    · rw [abs_sub_comm]; exact (hcR b a h).trans (le_abs_self _)
  have hp : pOf ε ≤ r := (Finset.card_filter_le _ _).trans_eq (by simp)
  have hq : qOf ε ≤ r := (Finset.card_filter_le _ _).trans_eq (by simp)
  have hq0 : S7.q0 ε ≤ r := (min_le_left _ _).trans hp
  have hpR : (pOf ε : ℝ) ≤ r := by exact_mod_cast hp
  have hqR : (qOf ε : ℝ) ≤ r := by exact_mod_cast hq
  have hq0R : (S7.q0 ε : ℝ) ≤ r := by exact_mod_cast hq0
  have h1 : (1 : ℝ) ≤ (r : ℝ) ^ 4 := one_le_pow₀ hrR
  have h4 : (r : ℝ) ≤ (r : ℝ) ^ 4 := le_self_pow₀ hrR (by norm_num)
  have h2 : (r : ℝ) ^ 2 ≤ (r : ℝ) ^ 4 := pow_le_pow_right₀ hrR (by norm_num)
  have h3 : (r : ℝ) ^ 3 ≤ (r : ℝ) ^ 4 := pow_le_pow_right₀ hrR (by norm_num)
  have hbig : (r : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < 100 * (r : ℝ) ^ 4 := by
    have : (r : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) ≤ r * r * r := by gcongr
    nlinarith
  refine ⟨⟨hanti, fun a => ⟨lam a - k, ?_⟩⟩, ⟨hanti, _, hgap, hbig⟩, ⟨hanti, _, hgap, by linarith⟩, _, hgap, ?_⟩
  · have hkR : (r : ℝ) = 2 * k + 1 := by exact_mod_cast hk
    show (lam a : ℝ) - ((r : ℝ) - 1) / 2 = ((lam a - k : ℤ) : ℝ)
    rw [hkR]; push_cast; ring
  · unfold thrStar
    refine max_lt hbig ?_
    have hs : Real.sqrt (2 * (S7.q0 ε : ℝ)) ≤ 2 * r := by
      rw [show (2 : ℝ) * r = Real.sqrt ((2 * r) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
      exact Real.sqrt_le_sqrt (by nlinarith)
    have hm : (r : ℝ) * (S7.q0 ε : ℝ) ≤ r * r := mul_le_mul_of_nonneg_left hq0R (by positivity)
    nlinarith

end GlobalTheory.PsCo.PcEF

end
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericMemberSectionNeZeroIsPrimeAffineChartStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.GenericMember
open GlobalTheory.ThickeningDetermines (secIdeal)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericMemberSection_ne_zero_isPrime_affineChart : ∀ (k : Type) [Field k] (N : ℕ) (X X' : Scheme.{0}) [IsIntegral X] (f : X ⟶ Sp k) (f' : X' ⟶ Sp (FractionRing (MvPolynomial (Fin N) k))) (π : X' ⟶ X) (L : LB X) (hL : L.IsLB) (b : Fin N → L.Sec) (V : X.Opens) (hne : (V : Set X).Nonempty) (hW : IsAffineOpen (π ⁻¹ᵁ V)) (c : L.ι) (hVc : V ≤ L.U c) (j : Fin N), IsUnit (resG X hVc ((b j).f c)) → letI : Algebra k Γ(X, V) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ V le_top).hom.toAlgebra; ∀ e : FractionRing (MvPolynomial (Fin N) k) ⊗[k] Γ(X, V) ≃+* Γ(X', π ⁻¹ᵁ V), (∀ a, e (1 ⊗ₜ a) = (π.app V).hom a) → (∀ q, e (q ⊗ₜ 1) = ((Scheme.ΓSpecIso _).inv ≫ f'.appLE ⊤ (π ⁻¹ᵁ V) le_top).hom q) → (genSec k N f' π L b).f (fun _ => c) ≠ 0 ∧ ((secIdeal (LB.isLB_pull hL π) (genSec k N f' π L b)).ideal ⟨π ⁻¹ᵁ V, hW⟩ = ⊤ ∨ ((secIdeal (LB.isLB_pull hL π) (genSec k N f' π L b)).ideal ⟨π ⁻¹ᵁ V, hW⟩).IsPrime ∧ ((secIdeal (LB.isLB_pull hL π) (genSec k N f' π L b)).ideal ⟨π ⁻¹ᵁ V, hW⟩).comap (π.app V).hom = ⊥) := by
  first | exact @GlobalTheory.GenericMember.genSec_chart_ne_zero_and_isPrime | exact GlobalTheory.GenericMember.genSec_chart_ne_zero_and_isPrime | (intros; apply GlobalTheory.GenericMember.genSec_chart_ne_zero_and_isPrime <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPairSpecializesDiagonalGenericPointStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericPair_specializes_diagonal_genericPoint : ∀ (F : Type) [Field F] (Y : Var F) (K : Type) [Field K] (ψ₁ ψ₂ : Y.Fn →+* K), GenPair Y ψ₁ ψ₂ → ∃ h : (spMap ψ₁ ≫ (ratOf Y).pt) ≫ Y.str = (spMap ψ₂ ≫ (ratOf Y).pt) ≫ Y.str, Limits.pullback.lift (f := Y.str) (g := Y.str) (spMap ψ₁ ≫ (ratOf Y).pt) (spMap ψ₂ ≫ (ratOf Y).pt) h (IsLocalRing.closedPoint K) ⤳ Limits.pullback.diagonal Y.str (genericPoint Y.X) := by
  first | exact @GlobalTheory.FlagPush.genPair_specializes_diagonal | exact GlobalTheory.FlagPush.genPair_specializes_diagonal | (intros; apply GlobalTheory.FlagPush.genPair_specializes_diagonal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricActionCoveringGroupOfCoreEquivariance
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.geoAct_of_eqAt : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), IsInfFam R.θ → R.models_HW → TieIn T R κ v₀ → (∀ i, OMPins T R κ v₀ O i) → (∀ i σ, GoodEmb T.Q.c σ → ∀ hV, EqAt T R κ (O i) σ hV (T.cE ((i : ℕ) + 1) σ)) → GeoAct T R κ v₀ := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ O hθ hm ht hp he i
  have hact : ActLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c (O i).lev2 := (hp i).2.act.1
  have hlift : ∀ g, ∃ k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k := fun g =>
    ((hp i).2.lift.lev g).imp fun _ h => h.1
  have hs : GoodEmb T.Q.c (O i).s0 := by
    have e : (O i).s0 = T.toCore.σ₀ := sOv_eq T.toCore (O i).c' (O i).hle
    rw [e]
    exact T.toCore.good_σ₀
  obtain ⟨ρC, hρ⟩ := GlobalTheory.T.exists_level_action_cusp_form_representation T κ i (O i).lev2 ht.laws hact
    (fun g f hf => (hlift g).elim fun k hk =>
      (he i (O i).s0 hs (O i).hV g k hk f hf).1)
  refine ⟨ρC, fun σ g f => ?_, fun g f hf => ?_⟩
  · by_cases hσ : GoodEmb T.Q.c (res T σ)
    · exact GlobalTheory.T.cuspFormReading_equivariant_good_embedding T R κ v₀ O hθ hm ht i hlift (he i) ρC hρ σ hσ g f
    · exact GlobalTheory.T.cuspFormReading_equivariant_not_good_embedding T R κ v₀ O hθ hm ht i hlift (he i) ρC hρ σ hσ g f
  · exact GlobalTheory.T.level_action_preserves_integral_cusp_forms T κ i (O i).lev2 ht.laws hact g f (ρC g f) (hρ g f) hf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramMatrixTraceFormBasisChangeStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gramMatrix_traceForm_basis_change : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (L : Type) [Field L] (e : K.E ≃+* L) (c : L →+* L), (∀ x, e (K.c x) = c (e x)) → ∀ (a : ℕ) (β : B.A) (b : Module.Basis (Fin a) K.E B.A), (∀ P : GL (Fin a) L, ∃ b' : Module.Basis (Fin a) K.E B.A, (Matrix.of fun i j => e (B.herm β (b' i) (b' j))) = P.valᵀ * (Matrix.of fun i j => e (B.herm β (b i) (b j))) * P.val.map c) ∧ ∀ b' : Module.Basis (Fin a) K.E B.A, ∃ P : GL (Fin a) L, (Matrix.of fun i j => e (B.herm β (b' i) (b' j))) = P.valᵀ * (Matrix.of fun i j => e (B.herm β (b i) (b j))) * P.val.map c := by
  first | exact @GlobalTheory.GramChange.gram_basis_change | exact GlobalTheory.GramChange.gram_basis_change | (intros; apply GlobalTheory.GramChange.gram_basis_change <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GraphIdealLocalizationMaximalIdealEqSpanStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graphIdeal_localization_maximalIdeal_eq_span : ∀ {K κ κ' L : Type} [Field K] [Field κ] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ']
    [Algebra (K ⊗[ℂ] κ') L] [IsFractionRing (K ⊗[ℂ] κ') L]
    (k : ℕ) (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ') (E : Place (algebraMap ℂ K))
    (hER : E.Contains R) (t : E.ring) (zR : Fin k → R)
    (𝔭 : Ideal (tens (κ' := κ') (placeAlg E))) [𝔭.IsPrime],
  (∃ O' : Subring κ', IsLocModel (algebraMap ℂ κ') O') →
  (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
  (∀ a, algebraMap ℂ K a ∈ R) → (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) →
  (∀ r : R, (r : K) ≠ 0 → (π r = 0 ↔ 0 < E.ord r)) →
  Irreducible t → TrBasis (algebraMap ℂ κ) (fun i => π (zR i)) →
  𝔭 ∈ (graphIdeal E R π ρ).minimalPrimes →
  letI := isLocalRing_locAt (L := L) 𝔭 (IsFractionRing.injective (K ⊗[ℂ] κ') L)
  IsLocalRing.maximalIdeal (locAt (L := L) 𝔭) =
    Ideal.span (Set.range fun i => toQ 𝔭 (gens E R π ρ hER t zR i)) := by
  first | exact @GlobalTheory.GraphLocal.MaxGen.maximalIdeal_locAt_eq_span | exact GlobalTheory.GraphLocal.MaxGen.maximalIdeal_locAt_eq_span | (intros; apply GlobalTheory.GraphLocal.MaxGen.maximalIdeal_locAt_eq_span <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.H1GrowthNoSectionsNef
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

theorem GlobalTheory.noSection_H1_bound_riemann_roch : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ (d : ℕ) (L : LB X), L.IsLB → ∀ (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d + 1 : ℕ) → (∀ m : ℕ, 1 ≤ m → hdim k (twist F (lbPow L m)) 0 = 0) → 0 ≤ interNum k F (fun _ : Fin (d + 1) => L) → (∀ i, 2 ≤ i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist F (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d))) → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist F (lbPow L m)) 1 ≤ C * ((d + 1) * (m + 1) ^ d)) := by
  intro k _ _ X _ hX d L hL F _ hF h0 hI hi
  obtain ⟨C2, hC2⟩ := GlobalTheory.T.abs_factorial_mul_eulerChar_twist_pow_sub_le k X hX (d+1) F hF L hL
  obtain ⟨C1, hC1⟩ := GlobalTheory.T.euler_char_h0_h1_bound_higher k X hX (d+1) L hL F hF (fun m => (d+1)*(m+1)^d) hi
  refine ⟨C1 + C2 + hdim k (twist F (lbPow L 0)) 1, fun m => ?_⟩
  have he1 : 1 ≤ (d+1)*(m+1)^d := Nat.one_le_iff_ne_zero.mpr (by positivity)
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · calc hdim k (twist F (lbPow L 0)) 1 ≤ hdim k (twist F (lbPow L 0)) 1 * ((d+1)*(0+1)^d) :=
          Nat.le_mul_of_pos_right _ he1
      _ ≤ (C1 + C2 + hdim k (twist F (lbPow L 0)) 1) * ((d+1)*(0+1)^d) :=
          Nat.mul_le_mul_right _ (by omega)
  · have a1 := hC1 m
    have a2 := hC2 m
    rw [h0 m hm] at a1
    simp only [Nat.add_sub_cancel] at a2
    have hfac : (1 : ℤ) ≤ ((d+1).factorial : ℤ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hImp : 0 ≤ interNum k F (fun _ : Fin (d + 1) => L) * (m : ℤ)^(d+1) := mul_nonneg hI (by positivity)
    have hE : (((d+1)*(m+1)^d : ℕ) : ℤ) = ((d+1 : ℕ) : ℤ) * ((m : ℤ) + 1) ^ d := by push_cast; ring
    rw [← hE] at a2
    have hEpos : (1 : ℤ) ≤ (((d+1)*(m+1)^d : ℕ) : ℤ) := by exact_mod_cast he1
    suffices h : (hdim k (twist F (lbPow L m)) 1 : ℤ) ≤
        ((C1 + C2 + hdim k (twist F (lbPow L 0)) 1 : ℕ) : ℤ) * (((d+1)*(m+1)^d : ℕ) : ℤ) by
      exact_mod_cast h
    generalize (((d+1)*(m+1)^d : ℕ) : ℤ) = E at a1 a2 hEpos ⊢
    generalize chi k (twist F (lbPow L m)) = c at a1 a2
    generalize interNum k F (fun _ : Fin (d + 1) => L) * (m : ℤ)^(d+1) = I at a2 hImp
    generalize (((d+1).factorial : ℕ) : ℤ) = f at a2 hfac
    generalize (hdim k (twist F (lbPow L m)) 1 : ℤ) = H at a1 ⊢
    push_cast
    have hh0 : (0 : ℤ) ≤ (hdim k (twist F (lbPow L 0)) 1 : ℤ) := by positivity
    generalize (hdim k (twist F (lbPow L 0)) 1 : ℤ) = h00 at hh0 ⊢
    have hC1' : (0:ℤ) ≤ C1 := by positivity
    have hC2' : (0:ℤ) ≤ C2 := by positivity
    rw [abs_le] at a1 a2
    simp only [CharP.cast_eq_zero, sub_zero] at a1
    have hc : -c ≤ (C2 : ℤ) * E := by
      rcases le_or_gt 0 c with hc | hc
      · nlinarith
      · nlinarith
    nlinarith
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarIntegralNormalizedIntegralMatricesTwoSidedMu
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.HintInv

theorem rStab_comp_equiv {H : Type} [Group H] (φ : H ≃* H) (u : H → ℂ) :
    rStab (u ∘ φ) = (rStab u).comap (φ : H →* H) := by
  ext k
  simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom]
  show (∀ x, u (φ (x * k)) = u (φ x)) ↔ ∀ x, u (x * φ k) = u x
  constructor
  · intro h x
    have := h (φ.symm x)
    simpa using this
  · intro h x
    rw [map_mul]; exact h _

theorem hint_comp_equiv {H : Type} [Group H] (K : Subgroup H) (φ : H ≃* H) (hK : K.map (φ : H →* H) = K)
    (u : H → ℂ) : hint K (u ∘ φ) = hint K u := by
  set S := rStab u ⊓ K with hS
  have hS' : rStab (u ∘ φ) ⊓ K = S.comap (φ : H →* H) := by
    rw [rStab_comp_equiv, hS, Subgroup.comap_inf]
    congr 1
    have h1 : (K.map (φ : H →* H)).comap (φ : H →* H) = K :=
      Subgroup.comap_map_eq_self_of_injective φ.injective K
    rw [hK] at h1
    exact h1.symm
  unfold hint
  rw [hS', Subgroup.relIndex_comap, hK]
  congr 1
  let e : H ⧸ S.comap (φ : H →* H) ≃ H ⧸ S :=
    Quotient.congr φ.toEquiv (fun a b => by
      simp only [QuotientGroup.leftRel_apply, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, map_mul, map_inv]
      rfl)
  rw [← finsum_comp_equiv e]
  refine finsum_congr fun q => ?_
  obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul S (φ q.out)
  have he : e q = ((φ q.out : H) : H ⧸ S) := by
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  rw [he, hs]
  exact ((Subgroup.mem_inf.1 s.2).1 _).symm

section Integral

variable {L : Type} [Field L] {a b : ℕ}

theorem entries_of_mem_GLint {O : Subring L} {A : GL (Fin a) L} (hA : A ∈ GLint (Fin a) O) (i j : Fin a) :
    A.val i j ∈ O ∧ (A⁻¹).val i j ∈ O := by
  obtain ⟨y, rfl⟩ := hA
  rw [← map_inv]
  exact ⟨(y.val i j).2, ((y⁻¹).val i j).2⟩

theorem mul_mul_mem {O : Subring L} {P : Matrix (Fin a) (Fin a) L} {X : Matrix (Fin a) (Fin b) L}
    {Q : Matrix (Fin b) (Fin b) L} (hP : ∀ i j, P i j ∈ O) (hX : ∀ i j, X i j ∈ O) (hQ : ∀ i j, Q i j ∈ O)
    (i : Fin a) (j : Fin b) : (P * X * Q) i j ∈ O := by
  rw [Matrix.mul_apply]
  refine Subring.sum_mem _ fun l _ => Subring.mul_mem _ ?_ (hQ l j)
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hP i k) (hX k l)

def lrEquiv (A : GL (Fin a) L) (B : GL (Fin b) L) : Matrix (Fin a) (Fin b) L ≃+ Matrix (Fin a) (Fin b) L where
  toFun X := A.val * X * B.val
  invFun X := (A⁻¹).val * X * (B⁻¹).val
  left_inv X := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc A.val X, ← Matrix.mul_assoc (A⁻¹).val, ← Matrix.mul_assoc (A⁻¹).val]
    rw [Units.inv_mul, Matrix.one_mul, Units.mul_inv, Matrix.mul_one]
  right_inv X := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (A⁻¹).val X, ← Matrix.mul_assoc A.val, ← Matrix.mul_assoc A.val]
    rw [Units.mul_inv, Matrix.one_mul, Units.inv_mul, Matrix.mul_one]
  map_add' X Y := by simp only [Matrix.mul_add, Matrix.add_mul]

end Integral

theorem map_intMat {E : Type} [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (A : GLw a w) (B : GLw b w)
    (hA : A ∈ GlobalTheory.LFun.KGL w a) (hB : B ∈ GlobalTheory.LFun.KGL w b) :
    (intMat a b w).map ((lrEquiv A B).toMultiplicative : _ →* _) = intMat a b w := by
  have hint' : ∀ X : Matrix (Fin a) (Fin b) (w.adicCompletion E),
      (∀ i j, Valued.v (X i j) ≤ 1) ↔ ∀ i j, X i j ∈ Ov E w := fun X =>
    forall_congr' fun i => forall_congr' fun j => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).symm
  have hA1 := fun i j => (entries_of_mem_GLint hA i j).1
  have hA2 := fun i j => (entries_of_mem_GLint hA i j).2
  have hB1 := fun i j => (entries_of_mem_GLint hB i j).1
  have hB2 := fun i j => (entries_of_mem_GLint hB i j).2
  have key : ∀ (P : GLw a w) (Q : GLw b w), (∀ i j, P.val i j ∈ Ov E w) → (∀ i j, Q.val i j ∈ Ov E w) →
      (intMat a b w).map ((lrEquiv P Q).toMultiplicative : _ →* _) ≤ intMat a b w := by
    intro P Q hP hQ
    rw [intMat, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨X, hX, rfl⟩
    refine Subgroup.subset_closure ?_
    show ∀ i j, Valued.v ((P.val * Multiplicative.toAdd X * Q.val) i j) ≤ 1
    rw [hint']
    exact mul_mul_mem hP ((hint' _).1 hX) hQ
  refine le_antisymm (key A B hA1 hB1) ?_
  have h2 := key A⁻¹ B⁻¹ hA2 hB2
  intro X hX
  refine ⟨(lrEquiv A⁻¹ B⁻¹).toMultiplicative X, h2 ⟨X, hX, rfl⟩, ?_⟩
  show Multiplicative.ofAdd (A.val * ((A⁻¹).val * Multiplicative.toAdd X * (B⁻¹).val) * B.val) = X
  rw [show A.val * ((A⁻¹).val * Multiplicative.toAdd X * (B⁻¹).val) * B.val = Multiplicative.toAdd X from
    (lrEquiv A B).right_inv _]
  rfl

theorem hint_intMat_mul_mul :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E)
    (u : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) → ℂ) (A : GLw a w) (B : GLw b w),
    A ∈ GlobalTheory.LFun.KGL w a → B ∈ GlobalTheory.LFun.KGL w b →
    hint (intMat a b w) (fun X => u (Multiplicative.ofAdd (A.val * Multiplicative.toAdd X * B.val))) =
      hint (intMat a b w) u := by
  intro E _ _ _ a b w u A B hA hB
  exact hint_comp_equiv (intMat a b w) (lrEquiv A B).toMultiplicative (map_intMat a b w A B hA hB) u

end GlobalTheory.BCT.HintInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarIntegralNormalizedOpenCompactEqIntegralDiv
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.HaarSum
open MeasureTheory

theorem vol_mul_relIndex {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (H H' : Subgroup G) (hle : H' ≤ H)
    (hc : IsCompact (H : Set G)) (ho : IsOpen (H' : Set G)) :
    μ.real H' * (H'.relIndex H : ℝ) = μ.real H ∧ H'.relIndex H ≠ 0 := by
  haveI : CompactSpace H := isCompact_iff_compactSpace.1 hc
  have hHo : IsOpen (H : Set G) := Subgroup.isOpen_mono hle ho
  have ho' : IsOpen ((H'.subgroupOf H : Subgroup H) : Set H) := ho.preimage continuous_subtype_val
  haveI : Finite (H ⧸ H'.subgroupOf H) := (H'.subgroupOf H).quotient_finite_of_isOpen ho'
  haveI : (H'.subgroupOf H).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hemb : MeasurableEmbedding (H.subtype : H → G) := MeasurableEmbedding.subtype_coe hHo.measurableSet
  have : (μ.comap (H.subtype : H → G)).IsMulLeftInvariant := Measure.IsMulLeftInvariant.comap μ hemb
  have key := (H'.subgroupOf H).index_mul_measure ho'.measurableSet (μ.comap (H.subtype : H → G))
  rw [hemb.comap_apply, hemb.comap_apply] at key
  have e1 : (H.subtype : H → G) '' Set.univ = (H : Set G) := by ext x; simp
  have e2 : (H.subtype : H → G) '' ((H'.subgroupOf H : Subgroup H) : Set H) = (H' : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hle hx⟩, hx, rfl⟩
  rw [e1, e2] at key
  refine ⟨?_, Subgroup.FiniteIndex.index_ne_zero⟩
  rw [Subgroup.relIndex, Measure.real, Measure.real, ← key, ENNReal.toReal_mul, mul_comm]
  simp

theorem integral_eq_sum_cosets {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (S : Subgroup G) (hS : IsOpen (S : Set G))
    (hfin : μ (S : Set G) ≠ ⊤) (u : G → ℂ) (hu : ∀ x, ∀ s ∈ S, u (x * s) = u x) (F : Finset (G ⧸ S))
    (hF : ∀ q : G ⧸ S, q ∉ F → u q.out = 0) :
    ∫ x, u x ∂μ = (μ.real (S : Set G) : ℂ) * ∑ q ∈ F, u q.out := by
  have key : ∀ x : G, u ((x : G ⧸ S).out) = u x := fun x => by
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul S x
    rw [hh]
    exact hu x h h.2
  have hset : ∀ q : G ⧸ S, {x : G | (x : G ⧸ S) = q} = (fun x => q.out⁻¹ * x) ⁻¹' (S : Set G) := by
    intro q
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe]
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rw [eq_comm]
    exact QuotientGroup.eq
  have hmeas : ∀ q : G ⧸ S, MeasurableSet {x : G | (x : G ⧸ S) = q} := fun q => by
    rw [hset]
    exact (hS.preimage (continuous_mul_left _)).measurableSet
  have hμ : ∀ q : G ⧸ S, μ {x : G | (x : G ⧸ S) = q} = μ (S : Set G) := fun q => by
    rw [hset]
    exact measure_preimage_mul μ _ _
  have hfun : u = fun x => ∑ q ∈ F, ({x : G | (x : G ⧸ S) = q}.indicator (fun _ => u q.out) x) := by
    funext x
    rw [Finset.sum_eq_single (x : G ⧸ S)]
    · simp [Set.indicator, key]
    · intro q _ hq
      simp [Set.indicator, Ne.symm hq]
    · intro hx
      have h0 := hF _ hx
      rw [key] at h0
      simp [Set.indicator, key, h0]
  conv_lhs => rw [hfun]
  rw [integral_finset_sum]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [integral_indicator_const _ (hmeas q), Measure.real, hμ q, Complex.real_smul, Measure.real]
  · intro q _
    exact (integrableOn_const (hμ q ▸ hfin)).integrable_indicator (hmeas q)

theorem finite_cosets {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (S : Subgroup G)
    (hS : IsOpen (S : Set G)) {C : Set G} (hC : IsCompact C) : ((fun x : G => (x : G ⧸ S)) '' C).Finite := by
  haveI : DiscreteTopology (G ⧸ S) := QuotientGroup.discreteTopology hS
  exact (hC.image (continuous_coinduced_rng : Continuous fun x : G => (x : G ⧸ S))).finite_of_discrete

theorem hint_eq_integral : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    (μ : @MeasureTheory.Measure V (borel V)), @MeasureTheory.Measure.IsAddHaarMeasure V _ _ (borel V) μ →
    ∀ (Λ : AddSubgroup V), IsOpen (Λ : Set V) → IsCompact (Λ : Set V) → ∀ u : V → ℂ,
    (∃ U : AddSubgroup V, IsOpen (U : Set V) ∧ ∀ x, ∀ y ∈ U, u (x + y) = u x) → HasCompactSupport u →
    GlobalTheory.BCT.hint (AddSubgroup.toSubgroup Λ) (fun X : Multiplicative V => u (Multiplicative.toAdd X)) =
      ((μ (Λ : Set V)).toReal : ℂ)⁻¹ * ∫ x, u x ∂μ := by
  intro V _ _ _ μ hμ Λ hΛo hΛc u ⟨U, hUo, hU⟩ hsupp
  letI : MeasurableSpace V := borel V
  haveI : BorelSpace V := ⟨rfl⟩
  haveI := hμ
  let G := Multiplicative V
  letI : MeasurableSpace G := borel V
  haveI : BorelSpace G := ⟨rfl⟩
  let ν : Measure G := μ
  haveI : ν.IsMulLeftInvariant := ⟨fun g => Measure.IsAddLeftInvariant.map_add_left_eq_self (μ := μ) (Multiplicative.toAdd g)⟩
  let u' : G → ℂ := fun X => u (Multiplicative.toAdd X)
  let K : Subgroup G := AddSubgroup.toSubgroup Λ
  let S : Subgroup G := rStab u' ⊓ K
  have hSK : S ≤ K := inf_le_right
  have hSo : IsOpen (S : Set G) := by
    refine Subgroup.isOpen_mono (H₁ := AddSubgroup.toSubgroup (U ⊓ Λ)) ?_ ?_
    · intro x hx
      refine ⟨fun y => hU _ _ hx.1, hx.2⟩
    · exact hUo.inter hΛo
  have hKc : IsCompact (K : Set G) := hΛc
  obtain ⟨hvol, hidx⟩ := vol_mul_relIndex ν K S hSK hKc hSo
  have hKpos : 0 < μ (Λ : Set V) := hΛo.measure_pos μ ⟨0, Λ.zero_mem⟩
  have hKfin : μ (Λ : Set V) < ⊤ := hΛc.measure_lt_top
  have hSfin : ν (S : Set G) ≠ ⊤ := ne_top_of_le_ne_top hKfin.ne (measure_mono hSK)
  have hfinC := finite_cosets S hSo (C := tsupport u') hsupp
  have hF : ∀ q : G ⧸ S, q ∉ hfinC.toFinset → u' q.out = 0 := by
    intro q hq
    by_contra h
    apply hq
    rw [Set.Finite.mem_toFinset]
    exact ⟨q.out, subset_tsupport _ h, QuotientGroup.out_eq' q⟩
  have hint_eq := integral_eq_sum_cosets ν S hSo hSfin u' (fun x s hs => hs.1 x) hfinC.toFinset hF
  have hsum : ∑ᶠ q : G ⧸ S, u' q.out = ∑ q ∈ hfinC.toFinset, u' q.out := by
    refine finsum_eq_sum_of_support_subset _ fun q hq => ?_
    by_contra h
    exact hq (hF q h)
  have hKr : (μ (Λ : Set V)).toReal = ν.real (S : Set G) * (S.relIndex K : ℝ) := hvol.symm
  have hKne : (μ (Λ : Set V)).toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hKpos.ne', hKfin.ne⟩
  have hSne : ν.real (S : Set G) ≠ 0 := by
    intro h0
    rw [hKr, h0, zero_mul] at hKne
    exact hKne rfl
  change (((S.relIndex K : ℕ) : ℂ))⁻¹ * ∑ᶠ q : G ⧸ S, u' q.out = _ * ∫ x : G, u' x ∂ν
  rw [hint_eq, hsum, hKr]
  have hidx' : ((S.relIndex K : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hidx
  have hSne' : ((ν.real (S : Set G) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hSne
  push_cast
  field_simp

end GlobalTheory.HaarSum
end
end

