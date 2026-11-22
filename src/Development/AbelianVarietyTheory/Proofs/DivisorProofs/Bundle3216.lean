import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3186
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1703
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1739
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1738
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1768
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3187
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2212
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2243
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsSeparateQuotientGenericFibreDescends
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1331
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1171
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2377
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3134
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0180
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0638
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3202
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3197
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleNonzeroConstantSecond
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0085
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3188
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1084

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineOpenMeetingFibresIsNonvanishingLocusStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affineOpen_meeting_fibres_is_nonvanishingLocus : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsDomain R] [IsIntegrallyClosed R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ V : A.left.Opens, IsAffineOpen V → (∀ s : Sp R, ∃ x ∈ V, A.hom x = s) → ∃ c : Pic A.left, IsLocus c V := by
  first | exact @GlobalTheory.AffineLocus.isLocus_of_isAffineOpen_of_meets_fibres | exact GlobalTheory.AffineLocus.isLocus_of_isAffineOpen_of_meets_fibres | (intros; apply GlobalTheory.AffineLocus.isLocus_of_isAffineOpen_of_meets_fibres <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomEvalCompEqEvAMapStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_eval_eq_evA_map_of_isEval_of_pow_eq_zero : ∀ (p m : ℕ) (O A k A' σ : Type) [CommRing O] [CommRing A] [Algebra O A] [CommRing k] [CommRing A'] [Algebra k A'] [Fintype σ] (x : σ → A) (E : MvPowerSeries σ O →ₐ[O] A), IsEval p x E → ∀ (r : O →+* k) (g : A →+* A'), (∀ c, g (algebraMap O A c) = algebraMap k A' (r c)) → (p : A') ^ m = 0 → ∀ hx : ∀ i, IsNilpotent (g (x i)), ∀ f, g (E f) = evA k (fun i => g (x i)) hx (map r f) := by
  first | exact @GlobalTheory.algHom_eval_comp_eq_evA_map | exact GlobalTheory.algHom_eval_comp_eq_evA_map | (intros; apply GlobalTheory.algHom_eval_comp_eq_evA_map <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraiseOfIsImmersionProjectiveCompleteNoethStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraise_of_isImmersion_projective_completeNoeth : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (W P : Scheme.{0}) (j : W ⟶ P) (p : P ⟶ Spec (CommRingCat.of R)), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver p → IsImmersion j → Alg (j ≫ p) I := by
  first | exact @GlobalTheory.FormalAlg.alg_of_isImmersion_isProjOver | exact GlobalTheory.FormalAlg.alg_of_isImmersion_isProjOver | (intros; apply GlobalTheory.FormalAlg.alg_of_isImmersion_isProjOver <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleVanishing
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.AmpleGen

namespace GlobalTheory.AmpleGen

theorem stepTwo {K : Type} [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] (hA : IsAbelianScheme A)
    (h2 : (2 : K) ≠ 0) (L : LB A.left) (hL : L.IsLB) (a b j : ℕ) (h : NV A (mix A L a b) j) :
    ∃ j₁ j₂ : ℕ, j₁ + j₂ = 2 * j ∧ NV A (mix A L (2 * a : ℕ) (2 * b : ℕ)) j₁ ∧
      NV A (mix A L (a + b : ℕ) (a + b : ℕ)) j₂ := by
  have hd : (((1 : ℤ) * (-1) - 1 * 1 : ℤ) : K) ≠ 0 := by
    have : (((1 : ℤ) * (-1) - 1 * 1 : ℤ) : K) = -2 := by push_cast; ring
    rw [this]; exact neg_ne_zero.2 h2
  obtain ⟨j₁, j₂, e, h₁, h₂⟩ := GlobalTheory.T.cech_nonvanishing_invMix_pair_kunneth_isogeny K A hA 1 1 1 (-1) (by norm_num) hd L hL a b j h
  have t1 : tri 1 = 1 := by decide
  have t0 : tri (-1) = 0 := by decide
  simp only [t1, t0, neg_neg] at h₁ h₂
  refine ⟨j₁, j₂, e, ?_, ?_⟩
  · convert h₁ using 2 <;> push_cast <;> ring
  · convert h₂ using 2 <;> push_cast <;> ring

theorem stepFive {K : Type} [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] (hA : IsAbelianScheme A)
    (h5 : (5 : K) ≠ 0) (L : LB A.left) (hL : L.IsLB) (a b j : ℕ) (h : NV A (mix A L a b) j) :
    ∃ j₁ j₂ : ℕ, j₁ + j₂ = 2 * j ∧ NV A (mix A L (4 * a + b : ℕ) (a + 4 * b : ℕ)) j₁ ∧
      NV A (mix A L (3 * a + 2 * b : ℕ) (2 * a + 3 * b : ℕ)) j₂ := by
  have hd : (((1 : ℤ) * (-1) - 2 * 2 : ℤ) : K) ≠ 0 := by
    have : (((1 : ℤ) * (-1) - 2 * 2 : ℤ) : K) = -5 := by push_cast; ring
    rw [this]; exact neg_ne_zero.2 h5
  obtain ⟨j₁, j₂, e, h₁, h₂⟩ := GlobalTheory.T.cech_nonvanishing_invMix_pair_kunneth_isogeny K A hA 1 2 2 (-1) (by norm_num) hd L hL a b j h
  have t1 : tri 1 = 1 := by decide
  have t0 : tri (-1) = 0 := by decide
  have t2 : tri 2 = 3 := by decide
  have t2' : tri (-2) = 1 := by decide
  simp only [t1, t0, t2, t2', neg_neg] at h₁ h₂
  refine ⟨j₁, j₂, e, ?_, ?_⟩
  · convert h₁ using 2 <;> push_cast <;> ring
  · convert h₂ using 2 <;> push_cast <;> ring

theorem step {K : Type} [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] (hA : IsAbelianScheme A)
    (L : LB A.left) (hL : L.IsLB) (a b i : ℕ) (h : NV A (mix A L a b) i) :
    ∃ (i₁ i₂ a₁ b₁ a₂ b₂ : ℕ), i₁ + i₂ = 2 * i ∧ NV A (mix A L a₁ b₁) i₁ ∧ NV A (mix A L a₂ b₂) i₂ ∧
      a + b ≤ a₁ + b₁ ∧ 2 * (a + b) ≤ a₂ + b₂ ∧ ((a₂ : ℤ) - b₂ = (a : ℤ) - b ∨ (a₂ : ℤ) - b₂ = 0) := by
  by_cases h2 : (2 : K) = 0
  · have h5 : (5 : K) ≠ 0 := by
      have : (5 : K) = 2 * 2 + 1 := by norm_num
      rw [this, h2]; simp
    obtain ⟨i₁, i₂, e, h₁, h₂⟩ := stepFive A hA h5 L hL a b i h
    refine ⟨i₁, i₂, _, _, _, _, e, h₁, h₂, by omega, by omega, Or.inl (by push_cast; ring)⟩
  · obtain ⟨i₁, i₂, e, h₁, h₂⟩ := stepTwo A hA h2 L hL a b i h
    refine ⟨i₁, i₂, _, _, _, _, e, h₁, h₂, by omega, by omega, Or.inr (by push_cast; ring)⟩

theorem ampleVanishing : GlobalTheory.Published.AmpleVanishing := by
  intro K _ _ A _ hA L hL hamp
  refine GlobalTheory.T.relativelyAcyclic_of_cech_vanishing_all_covers K A L fun j hj => ?_
  have h0 := GlobalTheory.T.cechNonvanishing_lineBundleInvMix_one_zero K A L hL _ hj
  obtain ⟨c, hc⟩ := GlobalTheory.T.abelianVariety_cech_vanishing_above_degree K A hA
  have hLB : ∀ a b : ℤ, (mix A L a b).IsLB := fun a b => LB.isLB_linComb hL _ _

  let S : ℕ → Prop := fun i => 1 ≤ i ∧ ∃ a b : ℕ, 1 ≤ a + b ∧ NV A (mix A L a b) i
  have hS : ∀ i, S i → i ≤ c := fun i ⟨_, a, b, _, h⟩ =>
    le_of_lt (not_le.1 fun hi => hc _ (hLB a b) i hi h)
  have hj1 : S (j + 1) := ⟨by omega, 1, 0, by omega, by exact_mod_cast h0⟩
  classical
  let T := Nat.findGreatest S c
  have hT : S T := Nat.findGreatest_spec (hS _ hj1) hj1
  have hmax : ∀ i, S i → i ≤ T := fun i hi => Nat.le_findGreatest (hS i hi) hi
  obtain ⟨hT1, a, b, hab, hTab⟩ := hT

  have next : ∀ a' b' : ℕ, 1 ≤ a' + b' → NV A (mix A L a' b') T → ∃ a₂ b₂ : ℕ,
      NV A (mix A L a₂ b₂) T ∧ 2 * (a' + b') ≤ a₂ + b₂ ∧
        ((a₂ : ℤ) - b₂ = (a' : ℤ) - b' ∨ (a₂ : ℤ) - b₂ = 0) := by
    intro a' b' h1 h
    obtain ⟨i₁, i₂, a₁, b₁, a₂, b₂, e, h₁, h₂, l₁, l₂, hd⟩ := step A hA L hL a' b' T h
    have u₁ : i₁ ≤ T := by
      rcases Nat.eq_zero_or_pos i₁ with h0 | h0
      · omega
      · exact hmax _ ⟨h0, a₁, b₁, by omega, h₁⟩
    have u₂ : i₂ ≤ T := by
      rcases Nat.eq_zero_or_pos i₂ with h0 | h0
      · omega
      · exact hmax _ ⟨h0, a₂, b₂, by omega, h₂⟩
    exact ⟨a₂, b₂, by rwa [show i₂ = T by omega] at h₂, l₂, hd⟩
  have grow : ∀ n : ℕ, ∃ a' b' : ℕ, 1 ≤ a' + b' ∧ n ≤ a' + b' ∧ NV A (mix A L a' b') T ∧
      ((a' : ℤ) - b' = (a : ℤ) - b ∨ (a' : ℤ) - b' = 0) := by
    intro n
    induction n with
    | zero => exact ⟨a, b, hab, by omega, hTab, Or.inl rfl⟩
    | succ n ih =>
      obtain ⟨a', b', h1, hn, h, hd⟩ := ih
      obtain ⟨a₂, b₂, h₂, l, hd₂⟩ := next a' b' h1 h
      refine ⟨a₂, b₂, by omega, by omega, h₂, ?_⟩
      rcases hd₂ with e | e
      · rw [e]; exact hd
      · exact Or.inr e
  obtain ⟨N₁, hN₁⟩ := GlobalTheory.T.serre_vanishing_lineBundleInvMix_fixed_difference K A hA L hL hamp ((a : ℤ) - b)
  obtain ⟨N₂, hN₂⟩ := GlobalTheory.T.serre_vanishing_lineBundleInvMix_fixed_difference K A hA L hL hamp 0
  obtain ⟨a', b', -, hn, h, hd⟩ := grow (N₁ + N₂)
  obtain ⟨t, ht⟩ : ∃ t, T = t + 1 := ⟨T - 1, by omega⟩
  rw [ht] at h
  rcases hd with e | e
  · exact hN₁ a' b' (by omega) e t h
  · exact hN₂ a' b' (by omega) e t h

end GlobalTheory.AmpleGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BergmanFunctionTotalMassExtremalStatement
section
open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bergman_function_total_mass_extremal : ∀ (S : Type) (Y : S → Type) [∀ σ, MeasurableSpace (Y σ)] (ι : Type) [Fintype ι] [DecidableEq ι] (μ : ∀ σ, Measure (Y σ)) (v : ∀ σ, Y σ → ι → ℂ), IsFam μ v → (gram μ v).PosDef → (∀ σ, Integrable (bergmanDensity μ v σ) (μ σ)) ∧ ∑ᶠ σ, ∫ y, bergmanDensity μ v σ y ∂μ σ = Fintype.card ι ∧ (∀ σ y, 0 ≤ bergmanDensity μ v σ y) ∧ ∀ σ y (M : ℝ), 0 ≤ M → (∀ c : ι → ℂ, cmb v c σ y ≤ M * l2 μ v c) → bergmanDensity μ v σ y ≤ M := by
  first | exact @GlobalTheory.HSAmp.berg_mass_extremal | exact GlobalTheory.HSAmp.berg_mass_extremal | (intros; apply GlobalTheory.HSAmp.berg_mass_extremal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigLineBundleKodairaLemma
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KodairaLemma

theorem lineBundleGlobalSectionsDim_eq_zero_of_isEmpty (k : Type) [Field k] {Z : Scheme.{0}} [Algebra k Γ(Z, ⊤)] [IsEmpty Z]
    (L : LB Z) : lbH0 k L = 0 := by
  have e : (⊤ : Z.Opens) = ⊥ := Opens.ext (Set.eq_empty_of_isEmpty _)
  have : Subsingleton Γ(Z, ⊤) := by rw [e]; infer_instance
  have : Subsingleton L.Sec := Module.subsingleton Γ(Z, ⊤) _
  have : Subsingleton (coh (twist (structureModule Z) L) 0) := (cohZeroTwistEquiv L).toEquiv.subsingleton
  exact Module.finrank_zero_of_subsingleton

theorem isEmpty_zeroScheme {X : Scheme.{0}} [IsIntegral X] (hd : topologicalKrullDim X ≤ 0) {L : LB X}
    (hL : L.IsLB) (t : L.Sec) (ht : genericPoint X ∈ nonzeroLocus t) :
    IsEmpty (GlobalTheory.ThickeningDetermines.secIdeal hL t).subscheme := by
  refine ⟨fun z => ?_⟩
  have hx : (GlobalTheory.ThickeningDetermines.secIdeal hL t).subschemeι z ∈
      ((GlobalTheory.ThickeningDetermines.secIdeal hL t).support : Set X) := by
    rw [← (GlobalTheory.ThickeningDetermines.secIdeal hL t).range_subschemeι]; exact ⟨z, rfl⟩
  rw [coe_support_secIdeal] at hx
  set x := (GlobalTheory.ThickeningDetermines.secIdeal hL t).subschemeι z
  have hmax := Order.krullDim_nonpos_iff_forall_isMax.1
    (show Order.krullDim (IrreducibleCloseds X) ≤ 0 from hd)
  have hst : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
  let A : IrreducibleCloseds X := ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
  let B : IrreducibleCloseds X := ⟨closure {genericPoint X}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hAB : A ≤ B := specializes_iff_closure_subset.1 hst
  have hBA : B ≤ A := hmax A hAB
  have hts : x ⤳ genericPoint X := specializes_iff_closure_subset.2 hBA
  exact hx (hts.mem_open (nonzeroLocus t).isOpen ht)

open GlobalTheory.ThickeningDetermines (secIdeal)
open GlobalTheory.QuotSep

theorem exists_nsmul_cls_eq_add_toPic_of_isBig : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), IsProjOver p → ∀ (M A : LB X) (hM : letI := algebraΓOfHom p; IsBig k M) (hA : IsAmpleLB A), ∃ (a : ℕ) (D : CartierDiv X), 0 < a ∧ D.Eff ∧ a • cls M (letI := algebraΓOfHom p; hM.isLB) = cls A hA.isLB + toPic D := by
  intro k _ _ X _ p hp M A hM hA
  letI := algebraΓOfHom p
  have hp' : IsProjOver (strHom k X) := by rwa [strHom_eq (f := p) fun _ => rfl]
  have := isNoetherian_of_isProjOver hp'
  suffices h : ∃ a : ℕ, 0 < a ∧ ∃ (N : LB X) (hN : N.IsLB),
      cls N hN = a • cls M hM.isLB - cls A hA.isLB ∧ HasNonzeroSec N by
    obtain ⟨a, ha, N, hN, e, hs⟩ := h
    obtain ⟨s, hs⟩ := hasNonzeroSec_iff.1 hs
    refine ⟨a, divOfSec hN s hs, ha, GlobalTheory.PairStep.eff_divOfSec_of_sec hN s hs, ?_⟩
    rw [(presents_divOfRatSec hN (isRatSec_ratOfSec s hs)).toPic_eq, e]
    abel
  obtain ⟨q, hq, hq'⟩ := hA.exists_hasNonzeroSec (LB.isLB_triv X)
  have hAq : IsAmpleLB (lbPow A q) := (isAmpleLB_pow_iff hA.isLB hq).2 hA
  obtain ⟨r, -, hr'⟩ := hAq.exists_hasNonzeroSec (isLB_dual hA.isLB)
  have hP : (lbPow (lbPow A q) r).IsLB := isLB_lbPow hAq.isLB r
  have hPs : HasNonzeroSec (lbPow (lbPow A q) r) :=
    (hq' _ hAq.isLB (by rw [cls_triv, zero_add, cls_lbPow hA.isLB])).pow hAq.isLB r
  have hE := isLB_tens (isLB_dual hA.isLB) hP
  have hEs : HasNonzeroSec (tens (dual A) (lbPow (lbPow A q) r)) :=
    hr' _ hE (by rw [cls_tens (isLB_dual hA.isLB) hP, cls_lbPow hAq.isLB])
  obtain ⟨t, ht⟩ := hasNonzeroSec_iff.1 hPs
  have ht0 : t ≠ 0 := sec_ne_zero_of_mem ht
  letI := algebraΓAlong k (secIdeal hP t).subschemeι
  obtain ⟨m, hm, hlt⟩ : ∃ m : ℕ, 0 < m ∧
      lbH0 k ((lbPow M m).pull (secIdeal hP t).subschemeι) < lbH0 k (lbPow M m) := by
    obtain ⟨D, hD, c, hc, hfreq⟩ := hM.growth
    rcases D with _ | d
    · have hd0 : topologicalKrullDim X ≤ 0 := by rw [hD]; rfl
      haveI := isEmpty_zeroScheme hd0 hP t ht
      obtain ⟨m, hcm, hm⟩ := (hfreq.and_eventually (eventually_ge_atTop 1)).exists
      refine ⟨m, hm, ?_⟩
      rw [lineBundleGlobalSectionsDim_eq_zero_of_isEmpty]
      have h0 : (0 : ℝ) < lbH0 k (lbPow M m) := hc.trans_le (by simpa using hcm)
      exact_mod_cast h0
    · set ι := (secIdeal hP t).subschemeι
      have hMι := LB.isLB_pull hM.isLB ι
      obtain ⟨C, hC⟩ := GlobalTheory.exists_hdim_twist_lbPow_zero_le k _ (isProjOver_along hp' ι) d (M.pull ι) hMι
        (structureModule _) (by rw [QCoh.suppDim_structureModule]; exact dim_zeroScheme_le hP ht0 hD.le)
      have hev : ∀ᶠ m : ℕ in atTop, (C : ℝ) * 2 ^ d < c * m :=
        (tendsto_natCast_atTop_atTop.const_mul_atTop hc).eventually_gt_atTop _
      obtain ⟨m, h₁, h₂, h₃⟩ := (hfreq.and_eventually (hev.and (eventually_ge_atTop 1))).exists
      refine ⟨m, h₃, ?_⟩
      have e₂ : lbH0 k ((lbPow M m).pull ι) = lbH0 k (lbPow (M.pull ι) m) :=
        lineBundleGlobalSectionsDim_congr_picardClass (LB.isLB_pull (isLB_lbPow hM.isLB m) ι) (isLB_lbPow hMι m)
          ((cls_eq_iff _ _).2 (lbIso_lbPow_pull hM.isLB ι m)).symm
      rw [e₂]
      by_contra hle
      push_neg at hle
      have hb : (lbH0 k (lbPow (M.pull ι) m) : ℝ) ≤ C * ((m : ℝ) + 1) ^ d := by exact_mod_cast hC m
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast h₃
      have hm2 : ((m : ℝ) + 1) ^ d ≤ 2 ^ d * (m : ℝ) ^ d := by
        rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) d
      have hle' : (lbH0 k (lbPow M m) : ℝ) ≤ lbH0 k (lbPow (M.pull ι) m) := by exact_mod_cast hle
      have hmd : (0 : ℝ) < (m : ℝ) ^ d := pow_pos (by linarith) d
      have h₄ := mul_lt_mul_of_pos_right h₂ hmd
      have h₅ := mul_le_mul_of_nonneg_left hm2 (Nat.cast_nonneg C : (0 : ℝ) ≤ C)
      push_cast at h₁
      rw [pow_succ] at h₁
      nlinarith
  have hB := isLB_lbPow hM.isLB m
  have e₁ := globalSections_dim_le_div_add_restriction hp' hP hB ht0
  have hpos : 0 < lbH0 k (LB.div (lbPow M m) (lbPow (lbPow A q) r)) := by omega
  have hD := LB.isLB_div hB hP
  refine ⟨m, hm, _, isLB_tens hD hE, ?_, (lineBundleHasNonzeroSection_of_globalSectionsDim_pos hpos).tens hEs hD hE⟩
  rw [cls_tens hD hE, cls_div hB hP, cls_lbPow hM.isLB, cls_tens (isLB_dual hA.isLB) hP,
    cls_dual hA.isLB, cls_lbPow hAq.isLB, cls_lbPow hA.isLB]
  abel

end GlobalTheory.KodairaLemma
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigRouteKernelEqConstMulThetaStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.big_route_kernel_eq_const_mul_theta : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G)
    (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ')
    (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E)
    (om : Rep D.sp.cm.sig Γ.V Γ.W) (om' : Rep D.sp.cm.sig Γ.V' Γ.W) (h : IsTripleOf W M t i j e Bs Γ X), IsTriple Bs Γ X om om' → ∀ Φ, IsDatumA W e Γ Θ Φ → ∀ g g₁, ∃ ξ : ℂ, ξ ≠ 0 ∧
      ∀ u, kerBig W Θ g g₁ u = ξ * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om Φ (conjU _ 1 h.JW u) (blkU _ _ e h.JWW (g, g₁)) := by
  first | exact @GlobalTheory.BigKernel.kerBig_eq_theta | exact GlobalTheory.BigKernel.kerBig_eq_theta | (intros; apply GlobalTheory.BigKernel.kerBig_eq_theta <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlowupChartIdealSheafEqSpanMonomial
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SgZero

theorem exists_nat_evalZ (φ : InvFun ℤ) (g : ℕ) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (m : ℕ)
    (δ ga : Fin m → LinearMap.BilinForm ℤ X) (M d : ℕ) (hpf : IsPolFan id g φ) (hrk : Module.finrank ℤ X ≤ g)
    (hc : IsCone id φ ga) (hδ : ∀ k, δ k = (M : ℤ) • ga k) : ∃ b : Fin m → ℕ, ∀ k, (b k : ℝ) = d * φ.evalZ (δ k) := by
  have hP := hpf X hrk
  have key : ∀ k, ∃ n : ℕ, φ.evalZ (ga k) = n := by
    intro k
    obtain ⟨z, hz⟩ := hP.integral (ga k) (hc.mem k) (hc.nonneg k)
    by_cases h0 : ga k = 0
    · refine ⟨0, ?_⟩
      have := hc.evalZ_smul 0 k
      simp only [Nat.cast_zero, zero_smul, zero_mul] at this
      rw [h0]; simpa [h0] using this
    · have hp := hP.pos (ga k) (hc.mem k) (hc.nonneg k) h0
      refine ⟨z.toNat, ?_⟩
      rw [hz] at hp ⊢
      have : (0 : ℤ) ≤ z := by exact_mod_cast hp.le
      rw [show ((z.toNat : ℕ) : ℝ) = ((z.toNat : ℤ) : ℝ) by norm_cast, Int.toNat_of_nonneg this]
  choose n hn using key
  refine ⟨fun k => d * (M * n k), fun k => ?_⟩
  rw [hδ, hc.evalZ_smul, hn]
  push_cast; ring

theorem dvd_of_map_dvd_of_finite (A B : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [IsDomain B]
    (ρ : A →+* B) (hρ : Function.Injective ρ) (hf : ρ.Finite) (a c : A) (ha : a ≠ 0) (h : ρ a ∣ ρ c) : a ∣ c := by

  letI : Algebra A B := ρ.toAlgebra
  haveI : Module.Finite A B := hf
  obtain ⟨x, hx⟩ := h
  obtain ⟨p, hpm, hp⟩ := Algebra.IsIntegral.isIntegral (R := A) x
  let K := FractionRing A
  let L := FractionRing B
  let gL : A →+* L := (algebraMap B L).comp ρ
  have hgL : Function.Injective gL := (IsFractionRing.injective B L).comp hρ
  let iK : K →+* L := IsFractionRing.lift hgL
  have hιK : ∀ r : A, iK (algebraMap A K r) = gL r := IsFractionRing.lift_algebraMap hgL
  have hA : algebraMap A K a ≠ 0 := fun e => ha (IsFractionRing.injective A K (e.trans (map_zero _).symm))
  have hρa : algebraMap B L (ρ a) ≠ 0 := fun e => hA (by
    have := hgL (show gL a = gL 0 by simpa [gL] using e)
    rw [this, map_zero])
  set y : K := algebraMap A K c / algebraMap A K a with hy
  have hιKy : iK y = algebraMap B L x := by
    rw [hy, map_div₀, hιK, hιK]
    simp only [gL, RingHom.comp_apply, hx, map_mul]
    exact mul_div_cancel_left₀ _ hρa
  have hint : IsIntegral A y := by
    refine ⟨p, hpm, ?_⟩
    apply iK.injective
    rw [map_zero, Polynomial.hom_eval₂, hιKy]
    have e1 : iK.comp (algebraMap A K) = (algebraMap B L).comp (algebraMap A B) := by
      ext r; exact hιK r
    rw [e1, ← Polynomial.hom_eval₂, hp, map_zero]
  obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := K)).1 hint
  refine ⟨z, IsFractionRing.injective A K ?_⟩
  rw [map_mul, hz, hy, mul_div_cancel₀ _ hA]

theorem idlAlong_eq_span_monomial : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, ∀ (φ : InvFun ℤ) (d : ℕ) (J : Z.IdealSheafData) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S), (∀ x ∈ J.support, x ∉ Set.range i) → ValOn F i φ J d → IsNormBl π J → j ≫ π = i → IsPolFan id g φ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ Q.X), Module.finrank ℤ Q.X ≤ g → (∀ k, t k ∈ maximalIdeal V ∧ t k ≠ 0) → (∀ k a b, δ k a b = δ k b a) → (∀ k a, 0 ≤ δ k a a) → (∀ a, a ≠ 0 → ∃ k, 0 < δ k a a) → Q.IsMonomialTau t δ → ∀ (ga : Fin m → LinearMap.BilinForm ℤ Q.X) (M : ℕ), IsCone id φ ga → (∀ k, δ k = (M : ℤ) • ga k) → ∀ ξ : Sp V ⟶ S, UnifOver F j ξ Q → ∃ b : Fin m → ℕ, (∀ k, (b k : ℝ) = d * φ.evalZ (δ k)) ∧ idlAlong (J.comap π) ξ = Ideal.span {∏ k, t k ^ b k} := by
  intro g hg n hn hodd F Z z i _ hproj hnorm hiz hdense W φ d J S π j hJ hval hbl hji hpf V _ _ _ Q m t δ hrk ht hsym hnn hdef
    hmono ga M hcone hδ ξ hU
  obtain ⟨b, hb⟩ := exists_nat_evalZ φ g Q.X m δ ga M d hpf hrk hcone hδ
  refine ⟨b, hb, ?_⟩
  have hCN : IsCN V := hU.1
  obtain ⟨R', _, _, _, ρ, r, D, e, hCN', hρi, hρf, hρl, hr, hrefn, hmon⟩ :=
    GlobalTheory.T.refine_polarised_monomial_periods_monomial_data V Q m t δ hCN hmono (fun k => (ht k).1) (fun k => (ht k).2) hsym hnn hdef
  obtain ⟨g₀, hg₀⟩ := GlobalTheory.T.idealSheafAlongLocalSpec_normalisedBlowup_principal π J hbl V ξ
  rw [hg₀]
  have key : ∀ (Wr : Type) [CommRing Wr] [IsDomain Wr] [IsDiscreteValuationRing Wr], IsAdicComplete (maximalIdeal Wr) Wr →
      ∀ κ : R' →+* Wr, Function.Injective κ → IsLocalHom κ →
        Ideal.span {κ (ρ g₀)} = Ideal.span {κ (ρ (∏ k, t k ^ b k))} := by
    intro Wr _ _ _ hc κ hκi hκl
    obtain ⟨T, σ, c, e', hσ, hy, hc', hβ⟩ := GlobalTheory.T.exists_trait_period_form_valuation_sum_refined_chart F S j V Q ξ hU m t δ R' ρ r D e hCN' hρi hρf hρl hr
      (fun k => (ht k).2) hsym hrefn hmon Wr hc κ hκi hκl
    have hy' : jK T.V ≫ spMap σ ≫ (spMap κ ≫ spMap ρ ≫ ξ ≫ π) = T.y ≫ i := by
      rw [← hji]
      simpa only [Category.assoc] using congrArg (· ≫ π) hy
    have h1 := GlobalTheory.T.idealSheafAlongLocalSpec_monomial_of_cone_combination F Z i φ J d hval Q.X m ga δ M hcone hδ b hb T Wr σ c e' (spMap κ ≫ spMap ρ ≫ ξ ≫ π)
      (fun k => κ (ρ (t k))) hσ hy' hc' hβ
    have h2 : idlAlong J (spMap κ ≫ spMap ρ ≫ ξ ≫ π) = Ideal.span {κ (ρ g₀)} := by
      rw [GlobalTheory.TraitOrder.idlAlong_comp, GlobalTheory.TraitOrder.idlAlong_comp, ← GlobalTheory.PullAlong.idlAlong_comap_eq, hg₀,
        Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton]
    rw [← h2, h1, map_prod, map_prod]
    simp only [map_pow]
  obtain ⟨hN', hI', -, hZ'⟩ := hCN'
  obtain ⟨-, hIV, -, -⟩ := hCN
  set f := ∏ k, t k ^ b k with hfdef
  have hf0 : f ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (ht k).2
  have hρf0 : ρ f ≠ 0 := fun h => hf0 (hρi (h.trans (map_zero ρ).symm))
  have hκ0 : ∀ (Wr : Type) [CommRing Wr] (κ : R' →+* Wr), Function.Injective κ → κ (ρ f) ≠ 0 :=
    fun Wr _ κ hκ h => hρf0 (hκ (h.trans (map_zero κ).symm))
  have hg0 : g₀ ≠ 0 := by
    rintro rfl
    obtain ⟨Wr, _, _, _, κ, ⟨hdvr, hc, -⟩, hκi, hcm⟩ := GlobalTheory.PrimeUnif.exists_cdvr R' (maximalIdeal R')
    have hκl : IsLocalHom κ := ⟨fun a ha => by
      by_contra hna
      have : a ∈ (maximalIdeal Wr).comap κ := by rw [hcm]; exact hna
      exact (mem_maximalIdeal _).1 this ha⟩
    have := key Wr hc κ hκi hκl
    rw [map_zero, map_zero, Ideal.span_singleton_eq_bot.2 rfl, eq_comm, Ideal.span_singleton_eq_bot] at this
    exact hκ0 Wr κ hκi this
  have hρg0 : ρ g₀ ≠ 0 := fun h => hg0 (hρi (h.trans (map_zero ρ).symm))
  have d1 : ρ f ∣ ρ g₀ := GlobalTheory.Poinc.dvd_of_forall_complete_dvr R' (ρ g₀) (ρ f) hρf0
    fun Wr _ _ _ hc κ hκi hκl => (Ideal.span_singleton_eq_span_singleton.1 (key Wr hc κ hκi hκl)).symm.dvd
  have d2 : ρ g₀ ∣ ρ f := GlobalTheory.Poinc.dvd_of_forall_complete_dvr R' (ρ f) (ρ g₀) hρg0
    fun Wr _ _ _ hc κ hκi hκl => (Ideal.span_singleton_eq_span_singleton.1 (key Wr hc κ hκi hκl)).dvd
  exact Ideal.span_singleton_eq_span_singleton.2
    (associated_of_dvd_dvd (dvd_of_map_dvd_of_finite V R' ρ hρi hρf g₀ f hg0 d2) (dvd_of_map_dvd_of_finite V R' ρ hρi hρf f g₀ hf0 d1))

end GlobalTheory.SgZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleNonzeroConstantSecondStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bottom_triangle_nonzero_constant_second : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X → X.rW.β = 1 →
      ∃ Ω₂ : ℂ, Ω₂ ≠ 0 ∧ ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∃ u : ℂ, u ≠ 0 ∧ u ∈ Qbar ∧ (∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ GlobalTheory.SqTop.Qn G s → ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam u‖ = 1) ∧
          ∀ (ea : P'.a = A'.rank) (ed : P'.d = WW.rank) (h : GA D P'.d) (g : GA D WW), GlobalTheory.BotFormula.IsFinPt WW g h →
            ∀ (x : GA D P'.a) (g' : GA D A'), GlobalTheory.BotFormula.IsFinPt A' g' x → ∀ T' : Tup D P'.a P'.d P'.n,
              X.ker' W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T') g g' = Ω₂ * u * P'.term x h T' := by
  first | exact @GlobalTheory.BotSmallDict.kernel_eq_term | exact GlobalTheory.BotSmallDict.kernel_eq_term | (intros; apply GlobalTheory.BotSmallDict.kernel_eq_term <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalIsoHodgeFiltrationEqRangeInvariantFormsStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonical_iso_hodge_filtration_eq_range_invariant_forms : ∀ (p : ℕ) [Fact p.Prime]  (R : Type) [CommRing R] (N : ℕ), (p : R) ^ N = 0 → ∀ (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (G : PDivGroup p R) (t : G.TorsionTower A) (L : primDR A →ₗ[R] G.RigExt), Function.Surjective L → (∀ c, IsCan t c (L c)) → (PrimitiveSubmodule A).map L = LinearMap.range G.rigOfOmega := by
  first | exact @GlobalTheory.PtExt.map_F1prim_eq_range_rigOfOmega | exact GlobalTheory.PtExt.map_F1prim_eq_range_rigOfOmega | (intros; apply GlobalTheory.PtExt.map_F1prim_eq_range_rigOfOmega <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormTriangularConnectionEqEsymmGradedStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernForm_triangular_connection_eq_esymm_graded : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m : ι → ℕ) (E : Fr (ratOf X) m m) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → ∀ τ j p, chernFld (atlas X σ) (fun y z => ldPart (gramAt E H τ y z)) j p = aeval (fun i => grF E H ⟨τ, i⟩ p) (esymm (Fin (m τ)) ℂ j) := by
  first | exact @GlobalTheory.ChernCalc.chernFld_ldPart_eq_esymm_grF | exact GlobalTheory.ChernCalc.chernFld_ldPart_eq_esymm_grF | (intros; apply GlobalTheory.ChernCalc.chernFld_ldPart_eq_esymm_grF <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntegralLinearRelationZeroStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chern_integral_linear_relation_zero : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsProjOver p → ∀ (σ : k →+* ℂ) (D : ℕ) (J : Type) [Fintype J] (a : J → ℝ) (N : J → HermLB p), (∀ (c : AlgChart p σ D), ∀ y ∈ c.e.source, ∑ j, a j * c.chernDens ((N j).φ σ) y = 0) → ∀ (S : Set (CxPts p σ)) (g : CxPts p σ → ℝ), (∀ j, ((N j).φ σ).ChernIntegrableOn D S g) → ∑ j, a j * ((N j).φ σ).chernInt D S g = 0 := by
  first | exact @GlobalTheory.ChernLinRel.sum_chernInt_eq_zero | exact GlobalTheory.ChernLinRel.sum_chernInt_eq_zero | (intros; apply GlobalTheory.ChernLinRel.sum_chernInt_eq_zero <;> assumption)
end

