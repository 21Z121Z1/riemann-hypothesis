import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0655
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0768
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3287
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0702
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0801
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3614
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0847
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3576
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0895
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0720
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0705
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0669
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateSandwichOfPrismaticDieudonne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0714
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0697
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0824
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0832
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0721
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0716
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0938
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0829
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0708
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3615
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0026
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2181
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3268
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2631
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2475
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3613
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3151
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3616
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPeriodIntegral
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open GlobalTheory.QLog.Window

namespace GlobalTheory.QLog.WindowMat

section Frame

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] (hv : v.Integers O) {ε : PreTilt O p}
  (hε : IsPrimitiveSystem ε) (F : BFrame ε) {G : PDivGroup p O} {d : ℕ} (c : QLog.Chart G d)
  {μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B} (hL : IsLift F.θ μ')
  (hμ : ∀ i, map F.θ (μ' i) = c.μ i)
include hv hε hL hμ

theorem hasPeriod_add_smul (t : G.Tate) {f g : MvPowerSeries (Fin d) F.Q} {y y' : F.B} (b : F.B)
    (hg : DIn (⊤ : Ideal F.B) g) (h1 : c.HasPeriod F.θ t f y) (h2 : c.HasPeriod F.θ t g y') :
    c.HasPeriod F.θ t (f + algebraMap F.B F.Q b • g) (y + b * y') := by
  first
  | exact (GlobalTheory.T.formalChart_hasPeriod_linear_integral p C v O hv ε hε F G d c μ' hL hμ f g t y y' b hg h1 h2).1
  | exact (GlobalTheory.T.formalChart_hasPeriod_linear_integral p C v O hv ε hε F G d c μ' hL hμ f g t y y' b h1 h2).1

theorem hasPeriod_map_zero (t : G.Tate) (s : MvPowerSeries (Fin d) F.B) (hs : constantCoeff s = 0) :
    c.HasPeriod F.θ t (map (algebraMap F.B F.Q) s) 0 := by
  have hz := hasPeriod_zero c F.frame t
  have hd : DIn (⊤ : Ideal F.B) (0 : MvPowerSeries (Fin d) F.Q) := din_of_in (in_zero ⊤)
  first
  | exact (GlobalTheory.T.formalChart_hasPeriod_linear_integral p C v O hv ε hε F G d c μ' hL hμ 0 0 t 0 0 0 hd hz hz).2 s hs
  | exact (GlobalTheory.T.formalChart_hasPeriod_linear_integral p C v O hv ε hε F G d c μ' hL hμ 0 0 t 0 0 0 hz hz).2 s hs

theorem hasPeriod_comb (t : G.Tate) {ι : Type} [Fintype ι] (e : ι → MvPowerSeries (Fin d) F.Q)
    (hd : ∀ i, DIn (⊤ : Ideal F.B) (e i)) (y : ι → F.B) (hy : ∀ i, c.HasPeriod F.θ t (e i) (y i))
    (b : ι → F.B) : c.HasPeriod F.θ t (comb b e) (∑ i, b i * y i) := by
  classical
  unfold comb
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simpa using hasPeriod_zero c F.frame t
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, add_comm, add_comm (b a * y a)]
    exact hasPeriod_add_smul hv hε F c hL hμ t (b a) (hd a) ih (hy a)

theorem hasPeriod_integral (t : G.Tate) {D : MvPowerSeries (Fin d) F.Q}
    (hD : In (⊤ : Ideal F.B) D) (h0 : constantCoeff D = 0) : c.HasPeriod F.θ t D 0 := by
  obtain ⟨s, rfl⟩ := (in_top_iff D).1 hD
  have hs : constantCoeff s = 0 := by
    apply F.frame.inj
    rw [← constantCoeff_map, h0, map_zero]
  exact hasPeriod_map_zero hv hε F c hL hμ t s hs

theorem hasPeriod_unique (t : G.Tate) {f : MvPowerSeries (Fin d) F.Q} {y y' : F.B}
    (h1 : c.HasPeriod F.θ t f y) (h2 : c.HasPeriod F.θ t f y') : y = y' :=
  h1.unique F.frame h2

theorem hasPeriod_of_in (t : G.Tate) {f g : MvPowerSeries (Fin d) F.Q} {y : F.B}
    (hf : c.HasPeriod F.θ t f y) (hfg : In (⊤ : Ideal F.B) (f - g))
    (h0 : constantCoeff (f - g) = 0) : c.HasPeriod F.θ t g y := by
  have h := hasPeriod_add_smul hv hε F c hL hμ t (-1) (din_of_in hfg) hf
    (hasPeriod_integral hv hε F c hL hμ t hfg h0)
  rwa [map_neg, map_one, neg_one_smul, mul_zero, add_zero, neg_sub, add_sub_cancel] at h

end Frame

theorem window_matrices : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ G : PDivGroup p O, PDivLat.IsConn G → PDivLat.IsConn G.dual → ∀ F : BFrame ε, ∃ (d k : ℕ) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) (Y : Matrix (Fin d ⊕ Fin k) (Fin G.height) F.B) (Gm : Matrix (Fin G.height) (Fin d ⊕ Fin k) F.B) (tb : Module.Basis (Fin G.height) ℤ_[p] G.Tate) (χ : Fin G.height → G.dual.Tate) (w : Module.Basis (Fin d) O G.omega) (lb : Module.Basis (Fin k) O G.dual.Lie), d + k = G.height ∧ IsUnit U ∧ Y.map F.σ = blk d k (p : F.B) 1 * U.transpose * Y ∧ U * blk d k (p : F.B) 1 * (Gm.transpose.map F.σ) = (p : F.B) • Gm.transpose ∧ Gm * Y = F.a (Sandwich.mu ε) • (1 : Matrix (Fin G.height) (Fin G.height) F.B) ∧ (∀ i m, F.θ (Y (Sum.inl i) m) = 0) ∧ (∀ m j, F.θ (Gm m (Sum.inr j)) = 0) ∧ IsNil F.θ F.σ (U * blk d k (p : F.B) 1) ∧ IsNil F.θ F.σ (U.transpose⁻¹ * blk d k 1 (p : F.B)) ∧ (∀ m m', epsPairing hε G (tb m) (χ m') = if m = m' then 1 else 0) ∧ (∀ j m, F.θ (Y (Sum.inr j) m) = lb j (hodgeTate G (tb m))) ∧ ∀ m, dlog G (χ m) = ∑ i, F.θ (Gm m (Sum.inl i)) • w i := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε G hG hGd F
  obtain ⟨d, ⟨c⟩⟩ := GlobalTheory.T.exists_pDivGroupFormalChart_of_connected p C v O hv G hG
  have hdk := GlobalTheory.T.chartDim_add_finrank_dual_lie_eq_height p C v O hv G d c
  have hCf := GlobalTheory.T.isTorsionFreePDThickeningFrame_valuation_integers p C v O hv
  obtain ⟨k, e0, lb, hB0, hA0, hcob0, hLie0⟩ := GlobalTheory.T.exists_adapted_quasiLog_basis_pDivGroup_lieDual p C v O hv G d c C hCf
  obtain ⟨μ', hL, hμ⟩ := GlobalTheory.T.exists_formalGroupLawLift_of_surjective F.B O F.θ F.frame.surj d c.μ c.isLaw
  obtain ⟨Θ, hΘ⟩ := frame_fraction_map p F.B O F.Q F.θ F.frame C hCf
  obtain ⟨e, he0, hB, hA⟩ := GlobalTheory.T.exists_lift_adapted_basis_quasi_logarithms_frame p C v O hv ε hε F G d c μ' hL hμ Θ hΘ k e0 hB0 hA0
  obtain ⟨U, hU⟩ := GlobalTheory.T.exists_frobenius_matrix_quasiLogarithm_basis p C v O hv ε hε F G d c μ' hL hμ k e hB hA
  have hUu := GlobalTheory.T.frobenius_matrix_isUnit_adapted_basis p C v O hv ε hε F G d c μ' hL hμ k e hB hA U hU
  have hN1 := GlobalTheory.T.frobenius_nilpotent_mod_maximal_connected_pDivGroup p C v O hv ε hε F G d c μ' hL hμ k e hB hA U fun i => (hU i).1
  have hN2 := GlobalTheory.T.isNil_dual_frobenius_alt p C v O hv ε hε F G d c μ' hL hμ k e hB hA hGd U hUu hU
  haveI := integers_isIntegrallyClosedIn hv
  haveI := G.finite_tate C
  haveI := G.free_tate C
  let tb : Module.Basis (Fin G.height) ℤ_[p] G.Tate :=
    Module.finBasisOfFinrankEq ℤ_[p] G.Tate (G.finrank_tate C)
  obtain ⟨χ, hχ, -⟩ :=
    GlobalTheory.DieudonneSandwich.exists_dual_basis hε (G.pairing_flip_bijective C) tb.equivFun
  have hpair : ∀ m m', epsPairing hε G (tb m) (χ m') = if m = m' then 1 else 0 := by
    intro m m'
    have h1 := epsPairing_smul hε G (tb m) (χ m')
    rw [hχ m' (tb m)] at h1
    have h2 : epsPairing hε G (tb m) (χ m') = tb.equivFun (tb m) m' := (epsEquiv hε).injective h1
    rw [h2, Module.Basis.equivFun_self]
    all_goals
      by_cases h : m = m'
      · subst h; simp
      · simp [Pi.single_apply, h, Ne.symm h]
  have hQLe : ∀ l, QL μ' ⊤ (e l) := hB.1
  have hDe : ∀ l, DIn (⊤ : Ideal F.B) (e l) := fun l =>
    GlobalTheory.QLogDiff.dIn_of_QL p F.B O F.Q F.θ F.frame d μ' hL ⊤ (e l) (hQLe l)
  choose Y hY using fun l m =>
    (GlobalTheory.T.exists_unique_period_quasiLogarithm_pDivGroup p C v O hv ε hε F G d c μ' hL hμ (e l) (tb m) (hQLe l)).exists
  choose fχ wχ hfχ using fun m => GlobalTheory.T.exists_quasiLogarithm_of_dualCharacter p C v O hv ε hε F G d c μ' hL hμ (χ m)
  choose g hg using fun m => (hB.2 (fχ m) (hfχ m).1).exists
  obtain ⟨hbij, -⟩ := GlobalTheory.T.pdDivGroupChart_forms_basis_and_differential p C v O hv G d c
  let w : Module.Basis (Fin d) O G.omega :=
    Module.Basis.ofEquivFun (LinearEquiv.ofBijective (Fintype.linearCombination O c.form) hbij).symm
  have hw : ∀ i, w i = c.form i := by
    intro i
    simp [w, Module.Basis.ofEquivFun]
  have hcomb0 : ∀ m, constantCoeff (fχ m - comb (g m) e) = 0 := fun m => by
    rw [map_sub, (hfχ m).1.1, (ql_comb hL.const e hQLe (g m)).1, sub_zero]

  have hred : ∀ m, (∀ j, F.θ (g m (Sum.inr j)) = 0) ∧
      ∀ i, lin (map Θ (fχ m)) i = algebraMap O C (F.θ (g m (Sum.inl i))) := fun m => by
    refine GlobalTheory.T.logarithm_integers_adapted_basis_no_lie_components p C v O hv G d c k e0 lb hB0 hA0 hLie0 (map Θ (fχ m))
      (ql_map F.θ Θ hΘ hμ hL.const (hfχ m).1)
      (formalGroupLawCoboundaryOne_map_eq_zero F.θ Θ hΘ hμ hL.const (hfχ m).2.1) (fun l => F.θ (g m l)) ?_
    have := in_map_top F.θ Θ hΘ (hg m)
    rwa [map_sub, map_comb F.θ Θ hΘ, show (fun l => map Θ (e l)) = e0 from funext he0] at this

  have hperO : ∀ l m, c.HasPeriod (RingHom.id O) (tb m) (e0 l) (F.θ (Y l m)) := fun l m => by
    have h := GlobalTheory.T.hasPeriod_reduce_along_theta_to_integers p C v O hv ε hε F G d c μ' hL hμ C hCf Θ hΘ (e l) (tb m) (Y l m)
      (hQLe l) (hY l m)
    rwa [he0] at h
  refine ⟨d, k, U, Matrix.of Y, Matrix.of g, tb, χ, w, lb, ?_, hUu, ?_, ?_, ?_, ?_, ?_, hN1, hN2,
    hpair, ?_, ?_⟩
  · have := Module.finrank_eq_card_basis lb
    rw [Fintype.card_fin] at this
    omega
  ·
    ext i m
    have key : F.σ (Y i m) = ∑ l, (U * blk d k (p : F.B) 1) l i * Y l m := by
      have hc := hasPeriod_comb hv hε F c hL hμ (tb m) e hDe (fun l => Y l m) (fun l => hY l m)
        (fun l => (U * blk d k (p : F.B) 1) l i)
      have hf := GlobalTheory.T.quasiLogarithm_period_frobenius_twist p C v O hv ε hε F G d c μ' hL hμ (e i) (tb m) (Y i m) (hQLe i)
        (hY i m)
      refine hasPeriod_unique hv hε F c hL hμ (tb m)
        (hasPeriod_of_in hv hε F c hL hμ (tb m) hf (hU i).1 ?_) hc
      rw [map_sub, constantCoeff_frob p F.s (hQLe i).1, (ql_comb hL.const e hQLe _).1, sub_zero]
    rw [Matrix.map_apply, Matrix.of_apply, key, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [blk, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply,
      Matrix.of_apply]
    ring
  ·
    ext l m
    have key : (fun l => ∑ i, (U * blk d k (p : F.B) 1) l i * F.σ (g m i)) =
        fun l => (p : F.B) * g m l := by
      have hP : QL μ' ⊤ (algebraMap F.B F.Q (p : F.B) • fχ m) := by
        simpa using ql_add_smul hL.const (ql_zero (Q := F.Q) hL.const ⊤) (hfχ m).1 (p : F.B)
      refine (hB.2 _ hP).unique ?_ ?_
      · have e1 : algebraMap F.B F.Q (p : F.B) • fχ m -
            comb (fun l => ∑ i, (U * blk d k (p : F.B) 1) l i * F.σ (g m i)) e =
            -(frob p F.s (fχ m) - (p : F.Q) • fχ m) + frob p F.s (fχ m - comb (g m) e) +
              ∑ i, algebraMap F.B F.Q (F.σ (g m i)) •
                (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e) := by
          rw [comb_sum (fun l i => (U * blk d k (p : F.B) 1) l i) (fun i => F.σ (g m i)) e, frob_sub, frob_comb p F.s F.σ F.s_alg, map_natCast]
          simp only [comb, smul_sub, Finset.sum_sub_distrib]
          abel
        rw [e1]
        refine in_add (in_add (in_neg (hfχ m).2.2.1) (in_frob p F.s F.σ F.s_alg (hg m)))
          (in_sum _ _ fun i _ => in_smul (hU i).1 _)
      · have e2 : algebraMap F.B F.Q (p : F.B) • fχ m - comb (fun l => (p : F.B) * g m l) e =
            algebraMap F.B F.Q (p : F.B) • (fχ m - comb (g m) e) := by
          simp only [comb, map_mul, mul_smul, smul_sub, Finset.smul_sum]
        rw [e2]
        exact in_smul (hg m) _
    have := congrFun key l
    simp only [Matrix.smul_apply, Matrix.transpose_apply, Matrix.of_apply, smul_eq_mul, ← this,
      Matrix.mul_apply, Matrix.map_apply]
  ·
    ext m m'
    have key : ∑ l, g m l * Y l m' =
        F.a (Sandwich.mu ε * ofPadic p O (epsPairing hε G (tb m') (χ m))) := by
      refine hasPeriod_unique hv hε F c hL hμ (tb m')
        (hasPeriod_comb hv hε F c hL hμ (tb m') e hDe (fun l => Y l m') (fun l => hY l m') (g m)) ?_
      exact hasPeriod_of_in hv hε F c hL hμ (tb m') ((hfχ m).2.2.2.2.2 (tb m')) (hg m) (hcomb0 m)
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply]
    simp only [Matrix.of_apply]
    rw [key, hpair]
    by_cases h : m' = m
    · subst h; simp
    · simp [h, Ne.symm h]
  ·
    intro i m
    have hlie := GlobalTheory.T.tangent_eq_zero_of_formalGroupLawCoboundaryOne_eq_zero p C v O hv G d c (e0 (Sum.inl i)) (hB0.1 (Sum.inl i)).1 (hcob0 i)
    have h2 := GlobalTheory.T.quasiLogarithm_period_eq_tangent_hodgeTate p C v O hv G d c C hCf (e0 (Sum.inl i)) 0 (hB0.1 _) hlie (tb m)
    simpa using (hperO _ m).unique hCf h2
  · intro m j
    exact (hred m).1 j
  · intro j m
    exact (hperO _ m).unique hCf
      (GlobalTheory.T.quasiLogarithm_period_eq_tangent_hodgeTate p C v O hv G d c C hCf (e0 (Sum.inr j)) (lb j) (hB0.1 _) (hLie0 j) (tb m))
  · intro m
    rw [(hfχ m).2.2.2.2.1]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 := (hred m).2 i
    rw [lin_map F.θ Θ hΘ, (hfχ m).2.2.2.1 i, hΘ] at h1
    rw [hw, Matrix.of_apply, hCf.inj h1]

end GlobalTheory.QLog.WindowMat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDegreeLeWeightBoundStatement
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_degree_le_weight_bound : GlobalTheory.CovTop.HypothesesX → Hypotheses2 → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → DeepGood → Size → FlatDeg → Covers fun Fm x _ ι p i Y PP _ => ∀ Z, Real.log (Y.dg (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ Z) ≤ PP := by
  first | exact @GlobalTheory.CovTop.DgLog.log_dg_le_run | exact GlobalTheory.CovTop.DgLog.log_dg_le_run | (intros; apply GlobalTheory.CovTop.DgLog.log_dg_le_run <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefOnFiniteFieldFibresPowTensStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nefOnFiniteFieldFibres_pow_tens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L A : HermLB p) (n : ℕ), NefFib L → NefFib A → NefFib ((L.pow n).tens A) := by
  first | exact @GlobalTheory.NefFibTens.nefFib_pow_tens | exact GlobalTheory.NefFibTens.nefFib_pow_tens | (intros; apply GlobalTheory.NefFibTens.nefFib_pow_tens <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyLabelledCoverOfOddPrime
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.UCoverLab

theorem jK_mono (R : Type) [CommRing R] [IsDomain R] : Mono (jK R) := by
  haveI : Scheme.Spec.IsRightAdjoint := ΓSpec.adjunction.isRightAdjoint
  have : Mono (Scheme.Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))).op) := inferInstance
  exact this

theorem gp_mono {R : Type} [CommRing R] [IsDomain R] (M : Modif R) : Mono M.gp := by
  have : Mono (M.gp ≫ M.π) := by rw [M.gp_π]; exact jK_mono R
  exact mono_of_mono M.gp M.π

theorem mono_α {R : Type} [CommRing R] [IsDomain R] {M : Modif R} {X : Over M.S} [GrpObj X]
    {A : Over (Sp (FractionRing R))} [GrpObj A] {α : A.left ⟶ X.left} (h : IsGrpPullback A X M.gp α) : Mono α := by
  haveI := gp_mono M
  refine ⟨fun u v huv => h.1.hom_ext huv ?_⟩
  apply (cancel_mono M.gp).1
  rw [Category.assoc, Category.assoc, ← h.1.w, ← Category.assoc, huv, Category.assoc]

end GlobalTheory.Mum.UCoverLab

open GlobalTheory.Mum.UCoverLab GlobalTheory.Mum.CoverFin in

theorem GlobalTheory.Mum.UCover.labCover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : UCover R) (lab : Labels D.toPre C.A), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → OneTrait D.toPre C.A lab → GalEqN n lab → Nonempty (LabCover D) := by
  intro R _ _ _ hB D C lab n hn ho hu hone hgal
  refine ⟨{ toModif := C.toModif
            G := C.G
            semi := C.semi
            P := C.P
            A := C.A
            α := C.α
            α_cart := C.α_cart
            α_lb := C.α_lb
            n := n
            n_prime := hn
            n_odd := ho
            n_unit := hu
            lab := fun j => lab (n ^ j)
            trait := ?_ }⟩
  intro W _ _ _ hW φ ξ hφ hloc hξ
  obtain ⟨W', _, _, _, io, G', _, _, β, D', A', U', hW', hio, hfin, hcart, hlb⟩ := C.trait W hW φ ξ hφ hξ
  haveI : IsLocalHom io := hfin.to_isIntegral.isLocalHom hio
  have hsemi : IsSemiAbelian G' := semiAbelian_of_pull hcart C.semi
  have hγ : IsGrpPullback A'.A G' (jK W') (U'.gen.inv.left ≫ pullback.fst G'.hom (jK W')) :=
    GlobalTheory.ThetaBaseChange.grp_generic U'.toUnifPre
  have hinj : Function.Injective ((algebraMap W' (FractionRing W')).comp (io.comp φ)) :=
    (IsFractionRing.injective W' _).comp (hio.comp hφ)
  obtain ⟨ga, hga, hy⟩ := GlobalTheory.T.exists_factor_field_point_through_generic_point R C.toModif (FractionRing W') _ (jK W' ≫ spMap io ≫ ξ) hinj (by
    rw [Category.assoc, Category.assoc, hξ]
    simp only [jK, spMap, ← Spec.map_comp]
    rfl)
  have hcomp : IsGrpPullback A'.A C.G (spMap ga ≫ C.gp) ((U'.gen.inv.left ≫ pullback.fst G'.hom (jK W')) ≫ β) :=
    (hγ.comp hcart).congr hy rfl
  let a : A'.A.left ⟶ C.A.A.left := C.α_cart.1.lift ((U'.gen.inv.left ≫ pullback.fst G'.hom (jK W')) ≫ β)
    (A'.A.hom ≫ spMap ga) (by rw [hcomp.1.w, Category.assoc])
  have ha : a ≫ C.α = (U'.gen.inv.left ≫ pullback.fst G'.hom (jK W')) ≫ β := C.α_cart.1.lift_fst _ _ _
  have ha2 : a ≫ C.A.A.hom = A'.A.hom ≫ spMap ga := C.α_cart.1.lift_snd _ _ _
  have hcart' : IsGrpPullback A'.A C.A.A (spMap ga) a := IsGrpPullback.cancel C.α_cart (hcomp.congr rfl ha.symm) ha2
  have hgi : U'.gen.inv.left ≫ U'.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hA' : LBIso A'.L (U'.LG.L.pull (U'.gen.inv.left ≫ pullback.fst G'.hom (jK W'))) :=
    LBIso.chartPull (h := U'.gen.inv.left) (chartPullSec A'.L _ _ hgi)
      (chartPullSame U'.LG.L _ (fun _ => pullback.fst G'.hom (jK W')) _ _ fun _ => rfl) U'.ext
  have h2 : LBIso (U'.LG.L.pull (U'.gen.inv.left ≫ pullback.fst G'.hom (jK W')))
      (C.P.L.L.pull ((U'.gen.inv.left ≫ pullback.fst G'.hom (jK W')) ≫ β)) :=
    LBIso.chartPull (chartPullPull U'.LG.L _) (chartPullSame C.P.L.L _ _ _ _ fun _ => rfl) hlb
  have h3 : LBIso A'.L (C.P.L.L.pull ((U'.gen.inv.left ≫ pullback.fst G'.hom (jK W')) ≫ β)) :=
    LBIso.trans A'.isLB (pull_isLB U'.LG.isLB _) (pull_isLB C.P.L.isLB _) hA' h2
  have hfib : IsFib (io.comp φ) C.A A' a :=
    ⟨ga, fun r => hga r, hcart', lbIso_factor C.P.L.isLB C.A.isLB A'.isLB ha C.α_lb h3⟩
  obtain ⟨hD, hind⟩ := GlobalTheory.T.recognition_degData_labels_at_every_trait R hB D C.A lab n hn ho hu hone hgal W' hW' (io.comp φ) (hio.comp hφ)
    inferInstance G' D' A' U' a hsemi hfib
  refine ⟨W', inferInstance, inferInstance, inferInstance, io, G', inferInstance, inferInstance, β, D', A', U', hD, hW',
    hio, hfin, hcart, hlb, ?_⟩
  intro F _ _ _ _ em hF j p p₁ p' x' h₁ h₂ h₃ h₄
  refine hind j F em hF p p₁ p' x' h₁ h₂ h₃ ?_
  haveI := mono_α C.α_cart
  rw [← cancel_mono C.α, Category.assoc, ha]
  simpa only [Category.assoc] using h₄
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedAbelianPartFibreConjugateIsoMumford
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

theorem GlobalTheory.Poinc.Sep.conj_fibre_core : ∀ (g l : ℕ), l.Prime → Odd l → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (l : V₁) → ∀ (Q : Data V), Q.g ≤ g → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X), SharpRef W Q ρ D e → ∀ (C : Type) (u : (Fin 8 → Q.X) → C → V₁) (mo : (Fin 8 → Q.X) → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → IsThetaTerms D ((l ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → ∀ (σ : K ≃+* K), (∀ r ∈ k₀, σ r = r) → ∀ (a : Q.X) (p : Sp K ⟶ ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).left), p ≫ pullback.fst Q.B.hom (spMap (ev.comp ρ)) = spMap (ev.comp ρ) ≫ (Q.c a).left → p ≫ pullback.snd Q.B.hom (spMap (ev.comp ρ)) = 𝟙 _ → ∃ (f : ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B).left) (f₂ : (G2 ((Over.pullback (spMap (ev.comp ρ))).obj Q.B)).left ⟶ (G2 ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B)).left), IsGrpPullback ((Over.pullback (spMap (ev.comp ρ))).obj Q.B) ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B) (𝟙 _) f ∧ IsSquare f f₂ ∧ (∀ (ψ₀ : (G2 ((Over.pullback (spMap (ev.comp ρ))).obj Q.B)).left ⟶ (G2 Q.B).left) (ψσ : (G2 ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B)).left ⟶ (G2 Q.B).left), IsSquare (pullback.fst Q.B.hom (spMap (ev.comp ρ))) ψ₀ → IsSquare (pullback.fst Q.B.hom (spMap (σ.toRingHom.comp (ev.comp ρ)))) ψσ → LBIso ((abelian₂ Q.B Q.M.L).pull ψ₀) ((abelian₂ Q.B Q.M.L).pull (f₂ ≫ ψσ))) ∧ p ≫ f ≫ pullback.fst Q.B.hom (spMap (σ.toRingHom.comp (ev.comp ρ))) = spMap σ.toRingHom ≫ p ≫ pullback.fst Q.B.hom (spMap (ev.comp ρ)) := by
  intro g l hl hlo W hW
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.T.e8Power_fibre_conjugate_evaluation_iso g l hl hlo W hW
  refine ⟨max j₀ 1, ?_⟩
  intro j hj V V₁ _ _ _ _ _ hCN hlu Q hQg ρ hρ D e hSh C u mo hmo hTh K _ _ ev k₀ hk₀ hu σ hσ a p hpf hps
  obtain ⟨f, hf, hL, ht, hc⟩ :=
    hj₀ j (le_of_max_le_left hj) V V₁ hCN hlu Q hQg ρ hρ D e hSh C u mo hmo hTh K ev k₀ hk₀ hu σ hσ
  exact GlobalTheory.T.eighthPower_fibre_iso_sharp_torsion_gives_factor_iso l hl hlo W hW j (le_of_max_le_right hj) V V₁ hlu Q ρ hρ D e hSh
    K ev σ f hf hL ht hc a p hpf hps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperAmpleKTriv
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSObj

def chartPullComp {X X' Y' : Scheme.{0}} (L : LB X) (F : X' ⟶ X) (h : Y' ⟶ X') :
    ChartPull (L.pull (h ≫ F)) (L.pull F) h :=
  have hm : ∀ (y : Y') (J : PUnit → L.ι), y ∈ (L.pull (h ≫ F)).U J → h y ∈ (L.pull F).U J := fun y J hy =>
    (mem_pull (L := L) (F := F) (x := h y) (J := J)).2 ((mem_pull (L := L) (F := h ≫ F) (x := y) (J := J)).1 hy)
  { idx := fun J => J
    le := fun J y hy => hm y J hy
    g := fun y J J' hj hj' => (gm_pull_g L (h ≫ F) (𝟙 _) y J J' hj hj').trans
      (by rw [Category.id_comp]; exact (gm_pull_g L F h y J J' (hm y J hj) (hm y J' hj')).symm) }

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem relAmple_of_map {S X : Scheme.{0}} {t : SAB H X} {u : SAB H S} {f : X ⟶ S} (m : SABMap t u f)
    (hp : IsProper u.G.hom) (hA : Out.RelAmple u.G u.PP.L) : Out.RelAmple t.G t.PP.L := by
  have hpt : IsProper t.G.hom := MorphismProperty.of_isPullback m.cart.1 hp
  obtain ⟨w, hw, -⟩ := m.lin
  refine GlobalTheory.AmpleLocal.relAmple_of_locally X t.G t.PP.L t.PP.isLB inferInstance inferInstance fun x => ?_
  obtain ⟨V, hV, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤) (x := f x) trivial
  refine ⟨f ⁻¹ᵁ V, hx, ?_⟩
  have Hp : IsPullback ((t.G.hom ⁻¹ᵁ (f ⁻¹ᵁ V)).ι ≫ m.φ) (t.G.hom ∣_ (f ⁻¹ᵁ V)) u.G.hom ((f ⁻¹ᵁ V).ι ≫ f) :=
    (isPullback_morphismRestrict t.G.hom (f ⁻¹ᵁ V)).flip.paste_horiz m.cart.1
  obtain ⟨w', hw'⟩ : LBIso (t.PP.L.pull (t.G.hom ⁻¹ᵁ (f ⁻¹ᵁ V)).ι)
      (u.PP.L.pull ((t.G.hom ⁻¹ᵁ (f ⁻¹ᵁ V)).ι ≫ m.φ)) :=
    LBIso.chartPull (chartPullPull t.PP.L _) (chartPullComp u.PP.L m.φ _) ⟨w, hw⟩
  exact relAmple_pull (A' := Over.mk (t.G.hom ∣_ (f ⁻¹ᵁ V))) Hp u.PP.isLB (pull_isLB t.PP.isLB _)
    ((isGen_iff w').1 hw') V hV (fun y => y.2) hA

theorem proper_ample_kTriv {Dw : Datum H} {l : Geo.Tor.Level H} {B : Type} [CommRing B] {b : Base l B}
    {S : Scheme.{0}} {s : S ⟶ Sp B} (o : Obj Dw l b s) {X : Scheme.{0}} {t : SAB H X} {f : X ⟶ S}
    (m : SABMap t o.t f) :
    IsProper t.G.hom ∧ Out.RelAmple t.G t.PP.L ∧ Out.KTriv t.G t.PP.L := by
  obtain ⟨w, hw, -⟩ := m.lin
  exact ⟨MorphismProperty.of_isPullback m.cart.1 o.proper, relAmple_of_map m o.proper o.ample,
    kTriv_pull m.cart o.t.PP.isLB t.PP.isLB ((isGen_iff w).1 hw) o.ktriv⟩

end GlobalTheory.KSObj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankBoundOfDeepGoodStatement
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_bound_of_deep_good : GlobalTheory.CovTop.HypothesesX → Hypotheses2 → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → DeepGood → Size → FlatDeg → Deg → Share → Rk := by
  first | exact @GlobalTheory.CovTop.rk_of_steps | exact GlobalTheory.CovTop.rk_of_steps | (intros; apply GlobalTheory.CovTop.rk_of_steps <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoPointInductionKltPairSeparationStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twoPoint_induction_kltPair_separation : GlobalTheory.Published.Principalisation → GlobalTheory.Published.NadelVanishingPair → GlobalTheory.Published.NefNumerics → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → letI := algebraΓOfHom p; ∀ (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (N : LB X) (ε : ℚ) (h : ℕ → ℚ) (x₁ x₂ : X), IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < m → IsLogCanonicalMultiple p n Δ m G → IsAmpleLB N → IsClosed ({x₁} : Set X) → IsClosed ({x₂} : Set X) → x₁ ≠ x₂ → (∀ e, 0 < h e) → (∀ (z : X) (e : ℕ), z ⤳ x₁ ∨ z ⤳ x₂ → 1 ≤ e → topologicalKrullDim (closure ({z} : Set X)) = e → 2 * (e : ℚ) ^ e < h e ^ e * (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N : ℤ)) → 0 < ε → ∃ (D : X → ℚ) (d : ℚ), d ≤ ∑ e ∈ Finset.Icc 1 n, (h e + ε) ∧ QNum p N d D ∧ ((LcCut p n (Δ + D) x₁ 0 ∧ ¬ KltAt p n (Δ + D) x₂) ∨ (LcCut p n (Δ + D) x₂ 0 ∧ ¬ KltAt p n (Δ + D) x₁)) := by
  first | exact @GlobalTheory.PairStep.two_point_induction | exact GlobalTheory.PairStep.two_point_induction | (intros; apply GlobalTheory.PairStep.two_point_induction <;> assumption)
end

