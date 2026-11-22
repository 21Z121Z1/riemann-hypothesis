import Mathlib
import Formalism.HermitianCurvature.Bundle0007
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0136
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0137
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0103
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0099
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0105
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0016
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesMultiplicativeShiftCompAndSubst
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0057
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0042
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.GermEvalOneStandardPointSelf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LieEig
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0062
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0063
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0059
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0044
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0043
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0002
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0001
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0005
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0019
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0092

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselBigCellPointVectorEqBessel
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

namespace GlobalTheory

theorem vec_bigPt_eq_bessel : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (c : Fin (P.r + 1) → ℂ), (¬ ((∀ a, c a ≠ 0) ∧ TBB.TTp p < Complex.normSq (c (Fin.last P.r))) → p.V H (TBB.bigPt P.r c) = 0) ∧ (((∀ a, c a ≠ 0) ∧ TBB.TTp p < Complex.normSq (c (Fin.last P.r))) → 0 < TBB.Gp p (TBB.bigPt P.r c) ∧ ∀ γ ∈ B.GV P.k P.r, Zhat P.k P.r p.T.base.z p.T.base.z' γ = D.ptMatN (TBB.bigPt P.r c) (P.r + 1) → D.IsDFrame p.T.base p.ν' p.m₀ γ → γ ∈ B.GPos p.T.base ∧ p.V H (TBB.bigPt P.r c) = B.JF p.T.base H γ) := by
  intro Wp Wq _ _ _ _ _ _ P p H c
  refine ⟨fun hn => ?_, fun ⟨hd, hlt⟩ => ?_⟩
  · show D.vecV p.T.base p.ν' p.m₀ H (TBB.bigPt P.r c) = 0
    unfold D.vecV
    rw [dif_neg]
    rintro ⟨hl, hG⟩
    refine hn ⟨fun a => ?_, Formalism.FourierDecayAlt.P.PBM.zeta_big _ c hG⟩
    exact (hl.1 (1, c a) (List.mem_ofFn.2 ⟨a, rfl⟩)).2
  · have hc : ∀ a : Fin P.r, c a.castSucc ≠ 0 := fun a => hd _
    have hG : 0 < D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r
        (Formalism.FourierDecayAlt.P.PBJ.bigPt c) := by
      unfold D.ptG
      rw [Formalism.FourierDecayAlt.P.PBM.ptMatN_bigPt_head, Formalism.FourierDecayAlt.P.PBJ.Dens.ptMatN_bigPt, Formalism.FourierDecayAlt.P.PBM.hMat_one,
        Matrix.det_diagonal, Matrix.det_diagonal, Fin.prod_univ_castSucc, Complex.normSq_mul]
      have hp : 0 < Complex.normSq (∏ i : Fin P.r, c i.castSucc) :=
        Complex.normSq_pos.2 (Finset.prod_ne_zero_iff.2 fun a _ => hc a)
      have hlt' : Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' < Complex.normSq (c (Fin.last P.r)) := hlt
      nlinarith [mul_lt_mul_of_pos_left hlt' hp]
    have hl : D.IsLocPt (Formalism.FourierDecayAlt.P.PBJ.bigPt c) (P.r + 1) := Formalism.FourierDecayAlt.P.PBJ.Dens.isLocPt_bigPt c hd
    refine ⟨hG, fun γ hγ hZ hD => ?_⟩
    have hZ' : Zhat P.k P.r p.T.base.z p.T.base.z' γ = D.ptMatN (Formalism.FourierDecayAlt.P.PBJ.bigPt c) (P.r + 1) := hZ
    have hpos : 0 < Gf P.k P.r p.T.base.z p.T.base.z' γ := by
      rw [← Formalism.FourierDecayAlt.P.ptG_spec P.k P.r _ _ (Formalism.FourierDecayAlt.P.PBJ.bigPt c) _ hl hZ']; exact hG
    refine ⟨⟨hγ, hpos⟩, ?_⟩
    show D.vecV p.T.base p.ν' p.m₀ H (Formalism.FourierDecayAlt.P.PBJ.bigPt c) = _
    rw [Formalism.FourierDecayAlt.P.isotropic_vectors_linear_indep P.k P.r Wp Wq p.T.base p.ν' p.m₀ H _ hl γ p.hF hG hγ hZ' hD]
    have hw : (hl.2 ▸ D.ptPerm (Formalism.FourierDecayAlt.P.PBJ.bigPt c) : Equiv.Perm (Fin (P.r + 1))) = 1 :=
      Formalism.FourierDecayAlt.P.PBM.cast_perm_eq_one _ _ (Formalism.FourierDecayAlt.P.PBM.ptPerm_bigPt c hd)
    obtain ⟨hmono, hnz⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.ptMatN_monoP' (Formalism.FourierDecayAlt.P.PBJ.bigPt c) (P.r + 1) hl.2 hl.1
    rw [hw] at hmono
    rw [hw, Formalism.FourierDecayAlt.P.PBM.orbJ_one_eq p.T.base hγ hpos hnz (hZ'.trans hmono) H]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselGapExistsNonzeroStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_gap_exists_nonzero : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → (∃ w ∈ R.sm, ∃ v ∈ R.TK, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v ≠ 0) → ∃ (l₀ La : R.H → Wp), IsBes R z π l₀ ∧ NzOn R l₀ ∧ ∀ w ∈ R.sm, ∀ v ∈ R.TK, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v = (innerSL ℂ (La v)).smulRight (l₀ w) := by
  first | exact @GlobalTheory.BesselShape.bessel_shape | exact GlobalTheory.BesselShape.bessel_shape | (intros; apply GlobalTheory.BesselShape.bessel_shape <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BoxTupOfColumnsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boxTupSt_of_laws_of_twistBaseChange : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → BoxTupSt := by
  first | exact @GlobalTheory.boxTup_of_columns | exact GlobalTheory.boxTup_of_columns | (intros; apply GlobalTheory.boxTup_of_columns <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesCoeffBoundedTaylorEllipticOfPoles
section
noncomputable section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.EllBdd

variable {q : ℕ} [Fact q.Prime]

theorem bd_C (a : ℂ_[q]) : Bd ‖a‖ (C a : ℂ_[q]⟦X⟧) := by
  intro n
  rw [coeff_C]
  split_ifs <;> simp

theorem bd_mono {A B : ℝ} {f : ℂ_[q]⟦X⟧} (h : Bd A f) (hAB : A ≤ B) : Bd B f :=
  fun n => (h n).trans hAB

theorem bd_X_pow (k : ℕ) : Bd 1 (X ^ k : ℂ_[q]⟦X⟧) := by
  intro n
  rw [coeff_X_pow]
  split_ifs <;> simp

theorem bd_one_mul {f g : ℂ_[q]⟦X⟧} (hf : Bd 1 f) (hg : Bd 1 g) : Bd 1 (f * g) := by
  simpa using ((sup_norm_laws q).1 f g 1 1 hf hg).2

theorem bd_one_add {f g : ℂ_[q]⟦X⟧} (hf : Bd 1 f) (hg : Bd 1 g) : Bd 1 (f + g) := by
  simpa using ((sup_norm_laws q).1 f g 1 1 hf hg).1

theorem bd_one_pow {f : ℂ_[q]⟦X⟧} (hf : Bd 1 f) (k : ℕ) : Bd 1 (f ^ k) := by
  induction k with
  | zero => simpa using (bd_X_pow (q := q) 0)
  | succ k ih => rw [pow_succ]; exact bd_one_mul ih hf

theorem bd_one_sum {α : Type*} (s : Finset α) (f : α → ℂ_[q]⟦X⟧) (h : ∀ i ∈ s, Bd 1 (f i)) :
    Bd 1 (∑ i ∈ s, f i) :=
  Finset.sum_induction f (Bd 1) (fun _ _ => bd_one_add) (fun n => by simp) h

theorem bdd_mul {f g : ℂ_[q]⟦X⟧} (hf : Bdd f) (hg : Bdd g) : Bdd (f * g) := by
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  exact ⟨_, ((sup_norm_laws q).1 f g A B hA hB).2⟩

theorem bdd_add {f g : ℂ_[q]⟦X⟧} (hf : Bdd f) (hg : Bdd g) : Bdd (f + g) := by
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  exact ⟨_, ((sup_norm_laws q).1 f g A B hA hB).1⟩

theorem bdd_sum {α : Type*} (s : Finset α) (f : α → ℂ_[q]⟦X⟧) (h : ∀ i ∈ s, Bdd (f i)) :
    Bdd (∑ i ∈ s, f i) :=
  Finset.sum_induction f Bdd (fun _ _ => bdd_add) ⟨0, fun n => by simp⟩ h

theorem hat_one (ι : ℂ ≃+* ℂ_[q]) (ℓ : ℂ_[q]⟦X⟧) (hℓ : constantCoeff ℓ = 0) :
    hat ι ℓ (fun _ => 1) = 1 := by
  have h1 : tay (fun _ => 1) = 1 := by
    ext n
    rw [tay, coeff_mk, coeff_one, iteratedDeriv_const]
    split_ifs with h
    · simp [h]
    · simp
  have hs : HasSubst ℓ := HasSubst.of_constantCoeff_zero' hℓ
  rw [hat, h1, map_one, ← coe_substAlgHom hs, map_one]

theorem prod_coeff_le (ι : ℂ ≃+* ℂ_[q]) {m : ℕ} (a : Fin m → ℂ) (ha : ∀ i, ‖ι (a i)‖ ≤ 1) (n : ℕ) :
    ‖ι ((∏ i, (Polynomial.X - Polynomial.C (a i))).coeff n)‖ ≤ 1 := by
  revert n
  refine Finset.prod_induction _ (fun p : Polynomial ℂ => ∀ n, ‖ι (p.coeff n)‖ ≤ 1) ?_ ?_ ?_
  · intro p r hp hr n
    rw [Polynomial.coeff_mul, map_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one ?_
    intro x _
    rw [map_mul, norm_mul]
    exact mul_le_one₀ (hp _) (norm_nonneg _) (hr _)
  · intro n
    rw [Polynomial.coeff_one]
    split_ifs <;> simp
  · intro i _ n
    rcases n with _ | _ | n
    · simpa using ha i
    · simp
    · simp [Polynomial.coeff_X]

theorem bdd_hat_of_ell : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (ℓ : ℂ_[q]⟦X⟧) (φ : ℂ → ℂ), M.Chart ℓ → Ell M.L φ → AnalyticAt ℂ φ 0 → (∀ p, meromorphicOrderAt φ p < 0 → ¬ M.Small p) → Bdd (hat M.ι ℓ φ) := by
  intro q _ M ℓ φ hC hE hA hP
  obtain ⟨m, P, A, B, hPi, hz⟩ := GlobalTheory.EllipticModel.exists_mul_prod_eq_xy q M φ hC.1 hE
  obtain ⟨-, v, xs, ys, -, hxs, hys, -, hx0, -, -, -, -, hmain⟩ := GlobalTheory.MomOne.ChartXY.chart_xy q M ℓ hC
  set D : Polynomial ℂ := ∏ i, (Polynomial.X - Polynomial.C (M.x (P i))) with hD
  have hmon : D.Monic := Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _
  have hdeg : D.natDegree = m := by
    rw [hD, Polynomial.natDegree_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _]
    simp
  have hint : ∀ n, ‖M.ι (D.coeff n)‖ ≤ 1 := by
    refine prod_coeff_le M.ι (fun i => M.x (P i)) fun i => ?_
    by_contra h
    exact hP _ (hPi i).2 (Or.inr (not_le.mp h))
  have key := hmain φ A B (max A.natDegree B.natDegree) hA (le_max_left _ _) (le_max_right _ _)
    (fun _ => 1) analyticAt_const D m hdeg.le (by simpa using hz 0)
  set k := max A.natDegree B.natDegree
  set S := ∑ i ∈ Finset.range (m + 1), C (M.ι (D.coeff i)) * X ^ (2 * (m - i)) * xs ^ i with hS
  have hS1 : Bd 1 S := bd_one_sum _ _ fun i _ =>
    bd_one_mul (bd_one_mul (bd_mono (bd_C _) (hint i)) (bd_X_pow _)) (bd_one_pow hxs i)
  have hS0 : ‖constantCoeff S‖ = 1 := by
    rw [hS, Finset.sum_range_succ, map_add, map_sum, Finset.sum_eq_zero, zero_add]
    · have : D.coeff m = 1 := by rw [← hdeg]; exact hmon.coeff_natDegree
      simp [this, hx0]
    · intro i hi
      have : 2 * (m - i) ≠ 0 := by have := Finset.mem_range.mp hi; omega
      simp [this]
  have hR : Bdd (hat M.ι ℓ φ * X ^ (2 * k + 3) * S) := by
    rw [key, hat_one M.ι ℓ hC.2.1, one_mul]
    refine bdd_mul ⟨_, bd_X_pow _⟩ (bdd_sum _ _ fun i _ => bdd_add ?_ ?_)
    · exact bdd_mul (bdd_mul ⟨_, bd_C _⟩ ⟨_, bd_X_pow _⟩) ⟨_, bd_one_pow hxs i⟩
    · exact bdd_mul (bdd_mul (bdd_mul ⟨_, bd_C _⟩ ⟨_, bd_X_pow _⟩) ⟨_, bd_one_pow hxs i⟩) ⟨_, hys⟩
  obtain ⟨R, hR⟩ := hR
  refine ⟨R, (sup_norm_laws q).2.2.2.2.2 _ S (2 * k + 3) R hS1 hS0 ?_⟩
  rwa [show X ^ (2 * k + 3) * S * hat M.ι ℓ φ = hat M.ι ℓ φ * X ^ (2 * k + 3) * S by ring]

end GlobalTheory.MomOne.EllBdd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesMultiplicativeShiftCompAndSubstStatement
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cpSeriesMultiplicativeShift_comp_and_subst : ∀ (q : ℕ) [Fact q.Prime], (∀ (ζ ξ : ℂ_[q]) (f : ℂ_[q]⟦X⟧), ‖ζ - 1‖ < 1 → ‖ξ - 1‖ < 1 → Bdd f → shiftS ζ (shiftS ξ f) = shiftS (ζ * ξ) f) ∧ ∀ (ζ : ℂ_[q]) (n k : ℕ) (a : ℤ_[q]) (f : ℂ_[q]⟦X⟧), ζ ^ (q ^ n) = 1 → ‖a - (k : ℤ_[q])‖ ≤ (q : ℝ) ^ (-(n : ℤ)) → Bdd f → ‖ζ - 1‖ < 1 ∧ shiftS ζ (f.subst (mulS a : ℂ_[q]⟦X⟧)) = (shiftS (ζ ^ k) f).subst (mulS a : ℂ_[q]⟦X⟧) := by
  first | exact @GlobalTheory.MomOne.ShiftComp.main | exact GlobalTheory.MomOne.ShiftComp.main | (intros; apply GlobalTheory.MomOne.ShiftComp.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCharacterOnPoints
section
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionCharacter

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FamGerm GlobalTheory.HodgeTateStep GlobalTheory.KernelNoTorsion

theorem ringAct_natCast {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {Λ : Type} [Ring Λ]
    (ρ : RingAct A Λ) (n : ℕ) : ρ.act n = (𝟙 A) ^ n := by
  induction n with
  | zero =>
    have h : ρ.act 0 = ρ.act 0 * ρ.act 0 := by
      have := ρ.map_add 0 0
      rwa [add_zero] at this
    rw [Nat.cast_zero, pow_zero]
    exact left_eq_mul.mp h
  | succ n ih =>
    rw [Nat.cast_succ, ρ.map_add, ih, ρ.map_one, pow_succ]
    rfl

abbrev Admissible {V O : Type} [CommRing V] [IsLocalRing V] [CommRing O] (f : V →+* O) (A : Type) [CommRing A]
    [Algebra O A] : Prop :=
  (Module.Finite O A ∧ Module.Free O A) ∨ ∃ n : ℕ, ∀ a ∈ maximalIdeal V ^ n, algebraMap O A (f a) = 0

theorem dualBC_inr {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (s : O) :
    dualBC (Algebra.ofId O R) (TrivSqZeroExt.inr s) = TrivSqZeroExt.inr (algebraMap O R s) :=
  TrivSqZeroExt.lift_apply_inr _ _ _ _ _ s

theorem fst_comp_dualBC {O R : Type} [CommRing O] [CommRing R] [Algebra O R] :
    (TrivSqZeroExt.fstHom O R R).comp (dualBC (Algebra.ofId O R)) =
      (Algebra.ofId O R).comp (TrivSqZeroExt.fstHom O O O) := by
  apply DualNumber.algHom_ext
  show (dualBC (Algebra.ofId O R) (TrivSqZeroExt.inr 1)).fst =
    algebraMap O R (TrivSqZeroExt.inr 1 : DualNumber O).fst
  rw [dualBC_inr, TrivSqZeroExt.fst_inr, TrivSqZeroExt.fst_inr, map_zero]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type} [CommRing V] [IsDomain V]
  [IsDiscreteValuationRing V] {F : Type} [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (y : Pt1 E H V F)

theorem dAct_eq_map {R O F Λ : Type} [CommRing R] [CommRing O] [CommRing F] [CommRing Λ] [StarRing Λ] [Algebra R F]
    [Algebra O F] (f : R →+* O) (hf : ∀ r, algebraMap O F (f r) = algebraMap R F r) {d : ℕ}
    (B : Geo.Tor.Germ.FB R d Λ) (a : Λ) :
    TB.dAct F B a = ((TB.dLin (B.A.act a)).map f).map (algebraMap O F) := by
  ext i k
  simp [TB.dAct, TB.dLin, Geo.Tor.Germ.FB.actK, hf]

end GlobalTheory.TorsionCharacter
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFamThrough
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.UnitBallBox

theorem exists_secScal {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} (σ : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (φ' : K → (Y' ⟶ X))
    (e : φ' = fun a => h ≫ φ a) :
    ∃ s : LB.Sec (LB.LinComb L φ' ε), GeneratorPullback.SecScal L φ' ε s φ ε σ h 1 := by
  subst e
  exact ⟨DVR.pullSec L φ ε σ h, SectionScalarValuation.secScal_of_sval hL fun y J hJ => (SectionScalarValuation.sval_pullSec _ _ _ _ _ y hJ).symm⟩

section Fam

variable {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ}

theorem sum_f {D : DegPre R} {K : Type} (S : Finset K) (b : K → Fam D F k) (α : D.X) (jj) :
    ((∑ l ∈ S, b l).s α).f jj = ∑ l ∈ S, ((b l).s α).f jj := by
  classical
  induction S using Finset.induction_on with
  | empty => rfl
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_f, ih]

theorem eq_sum_of_classes (hG : GlobalFnsSt) {D : DegPre R} {N : Type} [Fintype N] (e : N → D.X)
    (he : ∀ χ : D.X, ∃! i, ∃ m : D.X, χ = e i + k • m) (S : Fam D F k) (T : N → Fam D F k)
    (h₁ : ∀ i jj, ((T i).s (e i)).f jj = (S.s (e i)).f jj)
    (h₀ : ∀ i β, (∀ mu, e i + k • mu ≠ β) → ∀ jj, ((T i).s β).f jj = 0) : S = ∑ i, T i := by
  refine fam_ext fun χ jj => ?_
  obtain ⟨i, ⟨m, rfl⟩, -⟩ := he χ
  refine fam_eq_on_class_of_eq hG R D F k _ _ (e i) (fun jj => ?_) m jj
  rw [sum_f, Finset.sum_eq_single i, h₁]
  · intro i' _ hi
    exact h₀ i' (e i) (fun m hm => hi ((he (e i)).unique ⟨m, hm.symm⟩ ⟨0, by rw [smul_zero, add_zero]⟩)) jj
  · intro h; exact absurd (Finset.mem_univ i) h

variable {j : ℕ} {D D' : DegPre R} (pD : IsPowDeg D' D j)

theorem box_zero {S : Fam D' F k} {s : Fin j → Fam D F k} (hS : IsBoxFam pD F k S s) (β : D'.X) (i : Fin j)
    (h : ∀ jj, ((s i).s (pD.xe β i)).f jj = 0) (jj) : (S.s β).f jj = 0 := by
  obtain ⟨hφ, H⟩ := hS β
  refine sec_ext_val D'.P.isLB (s' := SecOps.secZero) (fun y J' hJ' => ?_) jj
  choose J hJ using fun χ : (DegPre.BF D' F).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ y)
  have hJ : Good D.P.L y J := hJ
  have A := BoxFamScalar.box_sval pD.w hφ (S.s β) (fun i => (s i).s (pD.xe β i)) _ H (𝟙 _) y hJ hJ'
  rw [Finset.prod_eq_zero (Finset.mem_univ i) (UUA.sval_zero_of h _ y J (hJ.mem _ _))] at A
  rw [UUA.sval_zero_of (s := SecOps.secZero) (fun _ => rfl) _ y J' (hJ'.mem _ _)]
  exact (Units.mul_right_eq_zero _).1 A

theorem box_secScal {S : Fam D' F k} {s : Fin j → Fam D F k} (hS : IsBoxFam pD F k S s)
    {f' : ∀ α : D'.X, D'.SecB k α} {f : Fin j → ∀ α : D.X, D.SecB k α} (hf : IsBoxFamB pD k f' f) (α' : D'.X)
    (h : ∀ i, GeneratorPullback.SecScal D.P.L (DegPre.famφ D F (pD.xe α' i)) (DegPre.famε k) ((s i).s (pD.xe α' i))
      (D.famφB (pD.xe α' i)) (DegPre.famε k) (f i (pD.xe α' i)) (DegPre.prB D F).left 1) :
    GeneratorPullback.SecScal D'.P.L (DegPre.famφ D' F α') (DegPre.famε k) (S.s α')
      (D'.famφB α') (DegPre.famε k) (f' α') (DegPre.prB D' F).left 1 := by
  obtain ⟨hφ, H⟩ := hS α'
  obtain ⟨hψ, H'⟩ := hf α'
  have e₄ : ∀ i, (DegPre.prB D' F).left ≫ (pD.pw.pr i).left =
      prB pD F i ≫ (DegPre.prB D F).left := fun i => by
    rw [← Over.comp_left, ← Over.comp_left]; congr 1; exact (whiskerLeft_snd _ _).symm
  exact BoxFamScalar.secScal_box D.P.isLB D'.P.isLB pD.w (GC.famφ_eq D' F α') e₄
    (S.s α') (fun i => (s i).s (pD.xe α' i)) (f' α') (fun i => f i (pD.xe α' i))
    (fun y _ _ hJ hJ' => BoxFamScalar.box_sval pD.w hφ (S.s α') (fun i => (s i).s (pD.xe α' i)) _ H (𝟙 _) y hJ hJ')
    (fun y _ _ hJ hJ' => BoxFamScalar.box_sval pD.w hψ (f' α') (fun i => f i (pD.xe α' i)) _ H' _ y hJ hJ')
    (fun _ => 1) 1 (fun y => by simp only [NuBox.gs_one, Finset.prod_const_one]) h

theorem lin_pull {D : DegPre R} {α : D.X} {l : ℕ} (c : Fin l → R) (β : D.SecB k α) (f : Fin l → D.SecB k α)
    (hβ : ∀ jj, β.f jj = ∑ a, constFn D.P.A.hom _ (c a) * (f a).f jj)
    (βF : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k)))
    (fF : Fin l → LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k)))
    (h : GeneratorPullback.SecScal D.P.L (DegPre.famφ D F α) (DegPre.famε k) βF
      (D.famφB α) (DegPre.famε k) β (DegPre.prB D F).left 1)
    (hf : ∀ a, GeneratorPullback.SecScal D.P.L (DegPre.famφ D F α) (DegPre.famε k) (fF a)
      (D.famφB α) (DegPre.famε k) (f a) (DegPre.prB D F).left 1) (jj) :
    βF.f jj = ∑ a, DegPre.constBF D F (algebraMap (FractionRing R) F (algebraMap R (FractionRing R) (c a))) _ *
      (fF a).f jj := by
  refine NuBox.lin_of_sval D.P.isLB
    (fun a => gF D F (algebraMap (FractionRing R) F (algebraMap R (FractionRing R) (c a)))) fF (fun y J hJ => ?_) jj
  rw [← SectionScalarValuation.secScal_sval h (𝟙 _) y hJ, SectionScalarValuation.sval_lin (fun a => scal D.P.A.hom (c a)) f hβ _ y hJ]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [SectionScalarValuation.secScal_sval (hf a) (𝟙 _) y hJ]
  refine congrArg (· * _) ?_
  let g : R →+* F := (algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))
  have hTF : jFK (R := R) F ≫ jK R = Spec.map (CommRingCat.ofHom g) := by
    show Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) F)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have g₁ : (𝟙 _ ≫ (DegPre.prB D F).left) ≫ D.P.A.hom =
      (fst (TF (R := R) F) D.P.A).left ≫ Spec.map (CommRingCat.ofHom g) := by
    rw [Category.id_comp, Over.w, ← hTF]
    exact (Over.w (fst (TF (R := R) F) D.P.A)).symm
  refine (IntegralCoord.gs_appTop _ D.P.A.hom y _).trans ?_
  rw [g₁, ← IntegralCoord.gs_appTop, IntegralCoord.specMap_appTop, Iso.inv_hom_id_apply]
  exact ((IntegralCoord.gs_appTop (𝟙 _) (fst (TF (R := R) F) D.P.A).left y _).trans (by rw [Category.id_comp]; rfl)).symm

end Fam

theorem exists_fam_through (hG : GlobalFnsSt) {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {ϖ : V} (hϖ : Irreducible ϖ) (D : DegData V (maximalIdeal V)) {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q)
    (F : Type) [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)
    {k : ℕ} (hk : 1 ≤ k) (α : D.toPre.X) (σ : D.toPre.SecB k α) :
    ∃ s : Fam D.toPre F k, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) (s.s α)
      (D.toPre.famφB α) (DegPre.famε k) σ (DegPre.prB D.toPre F).left 1 ∧
      (∀ β, (∀ mu, α + k • mu ≠ β) → ∀ jj, (s.s β).f jj = 0) ∧
      ∀ t : F, ((((Q α : ℚ) / k : ℚ)) : WithTop ℚ) ≤ v t → NuGe D Q F v k (t • s) 0 := by
  classical
  obtain ⟨hinj, e, he⟩ := exists_representatives_mod_nsmul D.toPre.X k hk
  obtain ⟨σF, hσ⟩ := exists_secScal D.toPre.P.isLB σ (DegPre.prB D.toPre F).left (DegPre.famφ D.toPre F α)
    (funext fun i => GC.famφ_eq D.toPre F α i)
  obtain ⟨s, hs₁, hs₀⟩ := UUA.exists_fam_rep (F := F) hG D.tau_bimult k α
    (fun x y h => hinj x y (add_left_cancel h)) σF
  refine ⟨s, hs₁ ▸ hσ, hs₀, fun t ht => ?_⟩
  rw [n1a V ϖ hϖ D Q hQ F v hv k hk
    (insert α ((Finset.univ.image e).filter fun β => ∀ mu, α + k • mu ≠ β)) (fun χ => ?_) (t • s) 0]
  · intro β hβ
    rcases Finset.mem_insert.1 hβ with rfl | hβ
    · refine ⟨1, fun _ => t, fun _ => σ, fun _ => σF, fun _ => hσ, fun _ => by rwa [zero_add], fun jj => ?_⟩
      rw [Fin.sum_univ_one, smul_f, hs₁]
      rfl
    · refine ⟨0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun jj => ?_⟩
      rw [smul_f, hs₀ β (Finset.mem_filter.1 hβ).2 jj, mul_zero, Fin.sum_univ_zero]
  · obtain ⟨i, ⟨m, rfl⟩, -⟩ := he χ
    by_cases h : ∀ mu, α + k • mu ≠ e i
    · exact ⟨e i, Finset.mem_insert_of_mem
        (Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ (Finset.mem_univ i), h⟩), m, rfl⟩
    · push_neg at h
      obtain ⟨mu, hmu⟩ := h
      exact ⟨α, Finset.mem_insert_self _ _, mu + m, by rw [← hmu, smul_add, add_assoc]⟩

theorem exists_comp_off {R : Type} [CommRing R] [IsDomain R] {j : ℕ} {D D' : DegPre R} (pD : IsPowDeg D' D j)
    (k : ℕ) {α' β : D'.X} (h : ∀ mu, α' + k • mu ≠ β) : ∃ i, ∀ mu, pD.xe α' i + k • mu ≠ pD.xe β i := by
  by_contra hn
  push_neg at hn
  choose mu hmu using hn
  refine h (pD.xe.symm mu) (pD.xe.injective (funext fun i => ?_))
  rw [map_add, map_nsmul, AddEquiv.apply_symm_apply]
  exact hmu i

set_option maxHeartbeats 800000 in

theorem main : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (ϖ : V), Irreducible ϖ → ∀ (j : ℕ) (D D' : DegData V (maximalIdeal V)) (pD : IsPowDeg D'.toPre D.toPre j) (Q : D.toPre.X → ℤ), QForm.IsQ D.toPre ϖ Q → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] [IsAlgClosed F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ k : ℕ, 1 ≤ k → ∀ S : Fam D'.toPre F k, NuGe D' (fun x => ∑ i, Q (pD.xe x i)) F v k S 0 → ∃ (l : ℕ) (c : Fin l → F) (s : Fin l → Fin j → Fam D.toPre F k) (S' : Fin l → Fam D'.toPre F k), (∀ a, (0 : WithTop ℚ) ≤ v (c a)) ∧ (∀ a i, NuGe D Q F v k (s a i) 0) ∧ (∀ a, IsBoxFam pD F k (S' a) (s a)) ∧ S = ∑ a, c a • S' a := by
  intro hL hL₂ hL₄ hT V _ _ _ _ ϖ hϖ j D D' pD Q hQ F _ _ _ v hv k hk S hS
  classical
  have hG := hL.globalFns
  obtain ⟨bx, hbx⟩ := GlobalTheory.T.exists_boxFamily_multilinear_map hG V j D.toPre D'.toPre pD F k
  obtain ⟨-, e, he⟩ := exists_representatives_mod_nsmul D'.toPre.X k hk
  have hπ : v (algebraMap (FractionRing V) F (algebraMap V (FractionRing V) ϖ)) = ((1 : ℚ) : WithTop ℚ) := by
    have h1 : HasVal ϖ (algebraMap V (FractionRing V) ϖ) 1 := ⟨1, by simp⟩
    rw [hv _ _ h1]; simp
  choose t ht₀ ht using fun α : D.toPre.X => ValuedPrincipal.exists_val_eq_rat v hπ ((Q α : ℚ) / k)
  have hinv : ∀ α, ((-((Q α : ℚ) / k) : ℚ) : WithTop ℚ) ≤ v (t α)⁻¹ := fun α => by
    obtain ⟨r, hr, hr'⟩ := ValuedPrincipal.exists_val_eq v (ht₀ α)
    rw [ht, WithTop.coe_inj] at hr
    rw [hr', hr]
  choose g hg hg₀ hgν using fun α σ => exists_fam_through hG hϖ D hQ F hv hk α σ
  choose n a σ σF hσ ha hsum using fun x => hS (e x)
  choose l c f f' hf hlin using fun x m => GlobalTheory.T.exists_box_family_power_degree hL hL₂ hL₄ hT V j D.toPre D'.toPre pD k hk (e x) (σ x m)
  let N := Σ x, Σ m : Fin (n x), Fin (l x m)
  let G : N → Fin j → Fam D.toPre F k := fun p i => g (pD.xe (e p.1) i) (f p.1 p.2.1 p.2.2 i (pD.xe (e p.1) i))
  let b : N → F := fun p =>
    a p.1 p.2.1 * algebraMap (FractionRing V) F (algebraMap V (FractionRing V) (c p.1 p.2.1 p.2.2))
  let E := (Fintype.equivFin N).symm
  have hB : ∀ p, IsBoxFam pD F k (bx (G p)) (G p) := fun p => (hbx _ _).2 rfl
  refine ⟨_, fun u => b (E u) * ∏ i, (t (pD.xe (e (E u).1) i))⁻¹,
    fun u i => t (pD.xe (e (E u).1) i) • G (E u) i, fun u => bx fun i => t (pD.xe (e (E u).1) i) • G (E u) i,
    fun u => ?_, fun u i => hgν _ _ _ (ht _).ge, fun u => (hbx _ _).2 rfl, ?_⟩
  · beta_reduce
    generalize E u = p
    obtain ⟨x, m, u⟩ := p
    have h₁ := ha x m
    have h₂ := GC.v_alg_nonneg hϖ hv (c x m u)
    have h₃ := NuBox.le_val_prod v Finset.univ _ _ fun i => hinv (pD.xe (e x) i)
    rw [AddValuation.map_mul, AddValuation.map_mul]
    refine le_trans (le_of_eq ?_) (add_le_add (add_le_add h₁ h₂) h₃)
    rw [add_zero, ← WithTop.coe_add, Finset.sum_neg_distrib, ← Finset.sum_div]
    push_cast
    simp
  · have hE : ∑ u, (b (E u) * ∏ i, (t (pD.xe (e (E u).1) i))⁻¹) •
        (bx fun i => t (pD.xe (e (E u).1) i) • G (E u) i) = ∑ p, b p • bx (G p) := by
      rw [← E.sum_comp]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [bx.map_smul_univ, smul_smul, _root_.mul_assoc, ← Finset.prod_mul_distrib,
        Finset.prod_eq_one fun i _ => inv_mul_cancel₀ (ht₀ _), _root_.mul_one]
    rw [hE, Fintype.sum_sigma]
    refine eq_sum_of_classes hG e he S _ (fun x jj => ?_) (fun x β hβ jj => ?_)
    · rw [hsum x jj, Fintype.sum_sigma, sum_f]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [lin_pull (c x m) (σ x m) (fun u => f' x m u (e x)) (hlin x m) (σF x m)
        (fun u => (bx (G ⟨x, m, u⟩)).s (e x)) (hσ x m)
        (fun u => box_secScal pD (hB ⟨x, m, u⟩) (hf x m u) (e x) fun i => hg _ _) jj, sum_f, Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      simp only [smul_f, b, constBF_eq, resTop, map_mul, _root_.mul_assoc]
    · obtain ⟨i, hi⟩ := exists_comp_off pD k hβ
      rw [sum_f]
      refine Finset.sum_eq_zero fun p _ => ?_
      rw [smul_f, box_zero pD (hB ⟨x, p⟩) β i (hg₀ _ _ _ hi) jj, mul_zero]

end GlobalTheory.UnitBallBox
end
end

