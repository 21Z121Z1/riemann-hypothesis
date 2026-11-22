import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.EqZeroOfForallExistsLsumETwoPi
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0195
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0602
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodLinearAlgebraHodgeSequenceExact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0603
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0604
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHomBirationalModelsAmpleFrames
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NomePowerSeriesDvdOfSumBounded
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

namespace GlobalTheory

theorem powerSeries_dvd_of_sum_bounded : ∀ (G H : PowerSeries ℂ) (T C : ℝ) (g h : ℂ → ℂ), H ≠ 0 →
    (∀ w : ℂ, T < w.im → SumsAt G w (g w) ∧ SumsAt H w (h w) ∧ (h w ≠ 0 → ‖g w‖ ≤ C * ‖h w‖)) →
    H ∣ G := by
  intro G H T C g h hH hyp
  set m : ℕ := H.order.toNat with hm
  set T₀ : ℝ := max T 0 + 1 with hT₀
  have hT₀T : T < T₀ := by have := le_max_left T 0; linarith
  set w₁ : ℂ := Complex.I * (T₀ : ℂ) with hw₁
  have hw₁im : w₁.im = T₀ := by simp [hw₁]
  set q₁ := eTwoPi w₁ with hq₁
  set ρ₁ : ℝ := GlobalTheory.Conv.cuspRadius T₀ with hρ₁
  have hρ₁pos : 0 < ρ₁ := GlobalTheory.Conv.cuspRadius_pos T₀
  have hq₁n : ‖q₁‖ = ρ₁ := by rw [hq₁, GlobalTheory.Conv.norm_eTwoPi, hw₁im]
  have hH₁ : HasSum (fun j : ℕ => PowerSeries.coeff j H * q₁ ^ j) (h w₁) :=
    (hyp w₁ (by rw [hw₁im]; exact hT₀T)).2.1
  have hS₁ : Summable (fun j : ℕ => ‖PowerSeries.coeff j H * q₁ ^ j‖) := hH₁.summable.norm
  set S₁ := ∑' j : ℕ, ‖PowerSeries.coeff j H * q₁ ^ j‖ with hS₁def

  have hbnd : ∀ w : ℂ, T₀ ≤ w.im → ‖h w‖ ≤ (‖eTwoPi w‖ / ρ₁) ^ m * S₁ := by
    intro w hw
    have hHw : HasSum (fun j : ℕ => PowerSeries.coeff j H * eTwoPi w ^ j) (h w) :=
      (hyp w (lt_of_lt_of_le hT₀T hw)).2.1
    set ρ := ‖eTwoPi w‖ with hρ
    have hρ0 : 0 ≤ ρ := norm_nonneg _
    have hρle : ρ ≤ ρ₁ := by
      rw [hρ, GlobalTheory.Conv.norm_eTwoPi]; exact GlobalTheory.Conv.cuspRadius_strictAnti.antitone hw
    have hterm : ∀ j : ℕ, ‖PowerSeries.coeff j H * eTwoPi w ^ j‖ ≤
        (ρ / ρ₁) ^ m * ‖PowerSeries.coeff j H * q₁ ^ j‖ := by
      intro j
      by_cases hj : j < m
      · rw [PowerSeries.coeff_of_lt_order_toNat j hj]; simp
      · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 hj)
        rw [norm_mul, norm_mul, norm_pow, norm_pow, ← hρ, hq₁n, div_pow, pow_add, pow_add]
        have hc := norm_nonneg (PowerSeries.coeff (m + d) H)
        have hpow : ρ ^ d ≤ ρ₁ ^ d := pow_le_pow_left₀ hρ0 hρle d
        have hρ₁m : 0 < ρ₁ ^ m := pow_pos hρ₁pos m
        calc ‖PowerSeries.coeff (m + d) H‖ * (ρ ^ m * ρ ^ d)
            ≤ ‖PowerSeries.coeff (m + d) H‖ * (ρ ^ m * ρ₁ ^ d) := by gcongr
          _ = ρ ^ m / ρ₁ ^ m * (‖PowerSeries.coeff (m + d) H‖ * (ρ₁ ^ m * ρ₁ ^ d)) := by
            field_simp
    rw [← hHw.tsum_eq]
    exact tsum_of_norm_bounded (hS₁.hasSum.mul_left _) hterm

  have hconv : (H : ℂ⸨X⸩) ∈ GlobalTheory.Conv.convLaurent :=
    GlobalTheory.Conv.halfRing_le_convLaurent T (GlobalTheory.Conv.coe_mem_halfRing.2 fun w hw => ⟨_, (hyp w hw).2.1⟩)
  have hH' : (H : ℂ⸨X⸩) ≠ 0 := fun h0 => hH ((map_eq_zero_iff _ HahnSeries.ofPowerSeries_injective).1 h0)
  obtain ⟨T₂, hT₂⟩ := GlobalTheory.Conv.exists_lsum_eTwoPi_ne_zero hconv hH'
  have hne : ∀ w : ℂ, T < w.im → T₂ < w.im → h w ≠ 0 := by
    intro w hw hw2
    have := hT₂ w hw2
    rwa [GlobalTheory.Conv.lsum_coe, GlobalTheory.Conv.sum, (hyp w hw).2.1.tsum_eq] at this

  set F : ℂ⸨X⸩ := HahnSeries.single (-(m : ℤ)) (1 : ℂ) * (G : ℂ⸨X⸩) with hF
  have hFb := GlobalTheory.laurent_coeff_neg_eq_zero_of_bounded F (max T₀ T₂) (max C 0 * (S₁ / ρ₁ ^ m))
    (by
      intro w hw
      have hw0 : T₀ < w.im := lt_of_le_of_lt (le_max_left _ _) hw
      have hw2 : T₂ < w.im := lt_of_le_of_lt (le_max_right _ _) hw
      have hwT : T < w.im := hT₀T.trans hw0
      have hq0 : eTwoPi w ≠ 0 := GlobalTheory.Conv.eTwoPi_ne_zero w
      refine ⟨eTwoPi w ^ (-(m : ℤ)) * g w,
        GlobalTheory.Conv.hasSum_single_mul hq0 (-(m : ℤ)) (GlobalTheory.Conv.sumsAt_iff.1 (hyp w hwT).1), ?_⟩
      have hρpos : 0 < ‖eTwoPi w‖ := norm_pos_iff.2 hq0
      have hg := (hyp w hwT).2.2 (hne w hwT hw2)
      have hb := hbnd w hw0.le
      have hS₁0 : 0 ≤ S₁ := tsum_nonneg fun _ => norm_nonneg _
      have hρm : 0 < ‖eTwoPi w‖ ^ m := pow_pos hρpos m
      have hρ₁m : 0 < ρ₁ ^ m := pow_pos hρ₁pos m
      rw [norm_mul, norm_zpow, zpow_neg, zpow_natCast]
      have h1 : ‖g w‖ ≤ max C 0 * ((‖eTwoPi w‖ / ρ₁) ^ m * S₁) :=
        hg.trans ((mul_le_mul_of_nonneg_right (le_max_left C 0) (norm_nonneg _)).trans
          (mul_le_mul_of_nonneg_left hb (le_max_right C 0)))
      rw [div_pow] at h1
      rw [inv_mul_le_iff₀ hρm]
      calc ‖g w‖ ≤ max C 0 * (‖eTwoPi w‖ ^ m / ρ₁ ^ m * S₁) := h1
        _ = ‖eTwoPi w‖ ^ m * (max C 0 * (S₁ / ρ₁ ^ m)) := by ring)
  have hcoeff : ∀ i < m, PowerSeries.coeff i G = 0 := by
    intro i hi
    have := hFb ((i : ℤ) + -(m : ℤ)) (by omega)
    rw [hF, HahnSeries.coeff_single_mul_add, one_mul] at this
    simpa using this
  have hXG : (PowerSeries.X : PowerSeries ℂ) ^ m ∣ G := PowerSeries.X_pow_dvd_iff.2 hcoeff
  obtain ⟨u, hu⟩ := PowerSeries.isUnit_divided_by_X_pow_order hH
  have hHe : H = PowerSeries.X ^ m * (u : PowerSeries ℂ) := by
    rw [hu, hm, PowerSeries.X_pow_order_mul_divXPowOrder]
  have hHX : H ∣ (PowerSeries.X : PowerSeries ℂ) ^ m :=
    ⟨(u⁻¹ : (PowerSeries ℂ)ˣ), by rw [hHe, mul_assoc, Units.mul_inv, mul_one]⟩
  exact hHX.trans hXG

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PartsPositiveScalarsWithoutCongruenceLengthsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.positive_scalars_without_congruence_lengths : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : GlobalTheory.Mem.R3.Rw.RationalReadingWithoutCongruence R F X0 Y), Pins R F cG → Holds R F → HostHyp D → (Formalism.BasicNotions.Rows.IsotRank D.what₂ → Formalism.MainNotions.SumRepresentations.adm8 D) ∧ GlobalTheory.NRows.LamUsed D := by
  first | exact @GlobalTheory.NRows.L0.parts_positive_scalars_without_congruence_lengths | exact GlobalTheory.NRows.L0.parts_positive_scalars_without_congruence_lengths | (intros; apply GlobalTheory.NRows.L0.parts_positive_scalars_without_congruence_lengths <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodLinearAlgebraHodgeSequenceExactStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodLinearAlgebra_hodgeSequence_exact : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Letter Dw) (Fu : Fam Xo c σ e) (τ : E →+* ℂ) (a : CxFr Z σ) (i : Fin Fu.n) (Q : (Fu.Di i).La →+ (Letter Dw → ℂ)) (x : Idx Dw τ → (Fu.Di i).La) (hm : Matrix (Idx Dw τ) (Idx Dw τ) E), Per Fu a i Q → IsPerBasis (Fu.Di i) x hm → GoodPer c σ τ x hm Q := by
  first | exact @GlobalTheory.ShFam.Hor.goodPer_of_per | exact GlobalTheory.ShFam.Hor.goodPer_of_per | (intros; apply GlobalTheory.ShFam.Hor.goodPer_of_per <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodsChangeOfEigenFrameStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periods_change_of_eigenFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Letter Dw) (Fu : Fam Xo c σ e) (a a' : CxFr Z σ) (i : Fin Fu.n) (Q : (Fu.Di i).La →+ (Letter Dw → ℂ)), Per Fu a i Q → a.1 = a'.1 → ∃ Q', Per Fu a' i Q' ∧ ∀ ρ M, Chg a a' ρ M → ∀ v k, Q v ⟨ρ, k⟩ = ∑ j, Q' v ⟨ρ, j⟩ * M j k := by
  first | exact @GlobalTheory.ShFam.Hor.per_chg | exact GlobalTheory.ShFam.Hor.per_chg | (intros; apply GlobalTheory.ShFam.Hor.per_chg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PluckerVectorBlockTriangularFrameChange
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb

open AlgebraicGeometry CategoryTheory Limits NumberField in
private theorem wedgeForm_update_eq_zero_of_mem_span_others {S N : Type} [CommRing S]
    [AddCommGroup N] [Module S N] {k : ℕ} (F : N [⋀^Fin k]→ₗ[S] S) (v : Fin k → N) (i : Fin k)
    {x : N} (hx : x ∈ Submodule.span S (v '' {j | j ≠ i})) :
    F (Function.update v i x) = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, hj, rfl⟩ := hy
    have hj' : j ≠ i := hj
    exact F.map_eq_zero_of_eq (Function.update v i (v j)) (i := i) (j := j)
      (by simp [Function.update_of_ne hj']) (Ne.symm hj')
  | zero => exact F.map_update_zero v i
  | add y z _ _ hy hz => rw [F.map_update_add, hy, hz, add_zero]
  | smul a y _ hy => rw [F.map_update_smul, hy, smul_zero]

open AlgebraicGeometry CategoryTheory Limits NumberField in
private theorem wedgeForm_eq_prod_mul_of_triangular_change {T : Type} {m : T → ℕ} {S N : Type}
    [CommRing S] [AddCommGroup N] [Module S N] {k : ℕ} (F : N [⋀^Fin k]→ₗ[S] S)
    (c c' : _root_.GlobalTheory.FlagEmb.Let m → N) (d : _root_.GlobalTheory.FlagEmb.Let m → S)
    (ht : ∀ z : _root_.GlobalTheory.FlagEmb.Let m, c' z - d z • c z ∈
      Submodule.span S ((fun j => c ⟨z.fst, j⟩) '' {j | j < z.snd}))
    (e : Fin k → _root_.GlobalTheory.FlagEmb.Let m) (he : _root_.GlobalTheory.FlagEmb.Down e) :
    F (fun l => c' (e l)) = (∏ l, d (e l)) * F (fun l => c (e l)) := by
  classical
  obtain ⟨_, hdown⟩ := he
  let w : Finset (Fin k) → Fin k → N := fun s l => if l ∈ s then c' (e l) else c (e l)
  have key : ∀ s : Finset (Fin k), F (w s) = (∏ l ∈ s, d (e l)) * F (w ∅) := by
    intro s
    refine Finset.induction_on_min_value (fun l => ((e l).snd : ℕ)) s ?_ ?_
    · simp
    · intro a s ha hmin ih
      have hw : w (insert a s) = Function.update (w s) a
          (d (e a) • w s a + (c' (e a) - d (e a) • c (e a))) := by
        funext l
        by_cases hl : l = a
        · subst hl
          simp [w, ha]
        · simp [w, hl, Function.update_of_ne hl]
      have hzero : F (Function.update (w s) a (c' (e a) - d (e a) • c (e a))) = 0 := by
        refine wedgeForm_update_eq_zero_of_mem_span_others F (w s) a ?_
        refine Submodule.span_mono ?_ (ht (e a))
        rintro _ ⟨j, hj, rfl⟩
        have hj' : (j : ℕ) < ((e a).snd : ℕ) := hj
        obtain ⟨l', hl'⟩ := hdown a j hj
        have hsnd : ((e l').snd : ℕ) = j := by
          have := congrArg (fun z : _root_.GlobalTheory.FlagEmb.Let m => (z.snd : ℕ)) hl'
          simpa using this
        have hne : l' ≠ a := by
          rintro rfl
          omega
        have hns : l' ∉ s := by
          intro h
          have := hmin l' h
          omega
        refine ⟨l', hne, ?_⟩
        simp [w, hns, hl']
      rw [hw, F.map_update_add, F.map_update_smul, Function.update_eq_self, hzero,
        Finset.prod_insert ha, ih, smul_eq_mul, add_zero, mul_assoc]
  have h1 : w Finset.univ = fun l => c' (e l) := by
    funext l
    simp [w]
  have h2 : w ∅ = fun l => c (e l) := by
    funext l
    simp [w]
  have := key Finset.univ
  rwa [h1, h2] at this

open AlgebraicGeometry CategoryTheory Limits NumberField in

theorem _root_.GlobalTheory.FlagEmb.plk_tri (T : Type) (m : T → ℕ) (S : Type) [CommRing S]
    (M : ℕ) (c c' : _root_.GlobalTheory.FlagEmb.Let m → Fin (M + 1) → S)
    (d : _root_.GlobalTheory.FlagEmb.Let m → S) (k : ℕ) (e : Fin k → _root_.GlobalTheory.FlagEmb.Let m)
    (ht : _root_.GlobalTheory.FlagEmb.Tri c c' d) (he : _root_.GlobalTheory.FlagEmb.Down e) :
    _root_.GlobalTheory.FlagEmb.plk c' e = (∏ l, d (e l)) • _root_.GlobalTheory.FlagEmb.plk c e := by
  funext q
  have := wedgeForm_eq_prod_mul_of_triangular_change
    ((Matrix.detRowAlternating (n := Fin k) (R := S)).compLinearMap
      (LinearMap.funLeft S S (_root_.GlobalTheory.FlagEmb.plE M k q))) c c' d ht e he
  unfold _root_.GlobalTheory.FlagEmb.plk
  simp only [Pi.smul_apply, smul_eq_mul]
  exact this

end GlobalTheory.FlagEmb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointsOfClosureInProjectiveSpaceStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.points_of_closure_in_projective_space : ∀ (O : Type) [CommRing O] (Z Z' : Scheme.{0}) (s : Z ⟶ Sp O) (f : Z' ⟶ Z) (C : Coc Z) (N : ℕ) (Em : C.Emb N) (q : Z' ⟶ PSpace O N) (Ω : Set Z'), q ≫ PSpace.str O N = f ≫ s → IsReduced Z' → Dense Ω → (∀ (K : Type) [Field K] (w : Sp K ⟶ Z'), Set.range w ⊆ Ω → ∀ (α : C.A) (h : ⊤ ≤ (w ≫ f) ⁻¹ᵁ C.B α), ∃ (ξ : Fin (C.n α) → K) (g : O →+* K) (hv : _), w ≫ q = GlobalTheory.ProjSpace.pt g (((Em.A α).map (ev (w ≫ f) _ h)).mulVec ξ) hv) → ∃ L : C.Line f, ∀ (K : Type) [Field K] (w : Sp K ⟶ Z') (α : C.A) (h : ⊤ ≤ (w ≫ f) ⁻¹ᵁ C.B α) (ξ : Fin (C.n α) → K) (g : O →+* K), w ≫ f ≫ s = spMap g → (L.Carries w α h ξ ↔ ∃ hv, w ≫ q = GlobalTheory.ProjSpace.pt g (((Em.A α).map (ev (w ≫ f) _ h)).mulVec ξ) hv) := by
  first | exact @GlobalTheory.DRFlag.LineOfMap.exists_line | exact GlobalTheory.DRFlag.LineOfMap.exists_line | (intros; apply GlobalTheory.DRFlag.LineOfMap.exists_line <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationBaseChangeModels
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.PolFin

open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.FlagMod GlobalTheory.Reg
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem)

attribute [local instance] Over.cartesianMonoidalCategory

section Push

variable {X X' : Scheme.{0}} {G : Over X} {G' : Over X'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {π : X' ⟶ X} {F : G'.left ⟶ G.left} {S S' : Type} [CommRing S] [CommRing S']

def tanPush (h : IsGrpPullback G' G π F) (x : Sp S ⟶ X') : TanM x G' →ₗ[S] TanM (x ≫ π) G where
  toFun v := mkT (pushHom h (overAt x (DualNumber S)) (tv v)) (by
    have e : smT (x ≫ π) 0 (pushHom h (overAt x (DualNumber S)) (tv v)) =
        pushHom h (overAt x (DualNumber S)) (smT x 0 (tv v)) := Over.OverMorphism.ext (Category.assoc _ _ _).symm
    rw [e, tv_mem]
    exact map_one _)
  map_add' u v := tanM_ext (map_mul (pushHom h (overAt x (DualNumber S))) _ _)
  map_smul' a v := tanM_ext (Over.OverMorphism.ext (Category.assoc _ _ _))

theorem tanPush_left (h : IsGrpPullback G' G π F) (x : Sp S ⟶ X') (v : TanM x G') :
    (tv (tanPush h x v)).left = (tv v).left ≫ F := rfl

theorem tanPush_bijective (h : IsGrpPullback G' G π F) (x : Sp S ⟶ X') : Function.Bijective (tanPush h x) := by
  have inj : Function.Injective (pushHom h (overAt x (DualNumber S))) := fun p q hpq =>
    Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun V => V.left) hpq) ((Over.w p).trans (Over.w q).symm))
  refine ⟨fun u v e => tanM_ext (inj (congrArg tv e)), fun V => ?_⟩
  let p : overAt x (DualNumber S) ⟶ G' :=
    Over.homMk (h.1.lift (tv V).left (overAt x (DualNumber S)).hom (Over.w (tv V))) (h.1.lift_snd _ _ _)
  have hp : pushHom h (overAt x (DualNumber S)) p = tv V := Over.OverMorphism.ext (h.1.lift_fst _ _ _)
  refine ⟨mkT p (inj ?_), tanM_ext hp⟩
  have e : smT (x ≫ π) 0 (pushHom h (overAt x (DualNumber S)) p) =
      pushHom h (overAt x (DualNumber S)) (smT x 0 p) := Over.OverMorphism.ext (Category.assoc _ _ _).symm
  rw [← e, hp, map_one]
  exact tv_mem V

def tanEquiv (h : IsGrpPullback G' G π F) (x : Sp S ⟶ X') : TanM x G' ≃ₗ[S] TanM (x ≫ π) G :=
  LinearEquiv.ofBijective _ (tanPush_bijective h x)

theorem tanPull_tanEquiv (h : IsGrpPullback G' G π F) (φ : S →+* S') {x : Sp S ⟶ X'} {x' : Sp S' ⟶ X'}
    (e : spMap φ ≫ x = x') (e' : spMap φ ≫ x ≫ π = x' ≫ π) (v : TanM x G') :
    tanPull φ e' (tanEquiv h x v) = tanEquiv h x' (tanPull φ e v) :=
  tan_ext_left (Category.assoc _ _ _).symm

end Push

theorem isAffineOpen_inf_preimage {X X' T : Scheme.{0}} [IsAffine T] (s : X ⟶ T) [IsSeparated s] (π : X' ⟶ X)
    {U : X.Opens} {U' : X'.Opens} (hU : IsAffineOpen U) (hU' : IsAffineOpen U') : IsAffineOpen (U' ⊓ π ⁻¹ᵁ U) := by
  have : IsAffineHom ((hU'.fromSpec ≫ π) ≫ s) := isAffineHom_of_isAffine _
  have : IsAffineHom (hU'.fromSpec ≫ π) := IsAffineHom.of_comp _ s
  have h := (hU.preimage (hU'.fromSpec ≫ π)).image_of_isOpenImmersion hU'.fromSpec
  rwa [Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf, hU'.opensRange_fromSpec] at h

theorem ev_pull_g {X X' : Scheme.{0}} {S : Type} [CommRing S] (L : LB X) (π : X' ⟶ X) (z : Sp S ⟶ X')
    (J J' : PUnit → L.ι) (h : ⊤ ≤ z ⁻¹ᵁ ((L.pull π).U J ⊓ (L.pull π).U J'))
    (h' : ⊤ ≤ (z ≫ π) ⁻¹ᵁ (L.U (J PUnit.unit) ⊓ L.U (J' PUnit.unit))) :
    ev z _ h ((L.pull π).g J J').val = ev (z ≫ π) _ h' (L.g (J PUnit.unit) (J' PUnit.unit)).val := by
  have le : (L.pull π).U J ⊓ (L.pull π).U J' ≤ π ⁻¹ᵁ (L.U (J PUnit.unit) ⊓ L.U (J' PUnit.unit)) :=
    le_inf (inf_le_left.trans (LB.wchart_le L (fun _ : PUnit => π) J PUnit.unit))
      (inf_le_right.trans (LB.wchart_le L (fun _ : PUnit => π) J' PUnit.unit))
  have e : (L.pull π).g J J' = res le (pullU π _ (L.g (J PUnit.unit) (J' PUnit.unit))) := by
    show ∏ _k : PUnit, res le (pullU π _ (L.g (J _k) (J' _k))) ^ (1 : ℤ) = _
    rw [Fintype.prod_unique, zpow_one]
  rw [e, ← ev_appLE z π le h]
  rfl

section Det

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l l' : Level H}
  {Xo : Moduli D l} {Xo' : Moduli D l'} {c : Coeff l} {c' : Coeff l'} {O O' : Type} [CommRing O] [CommRing O']
  {β : O →+* c.F} {β' : O' →+* c'.F} {Z : Model Xo c β} {Z' : Model Xo' c' β'} {π : Z'.X ⟶ Z.X}
  {F : Z'.t.G.left ⟶ Z.t.G.left} (h : IsGrpPullback Z'.t.G Z.t.G π F) {S : Type} [CommRing S]

theorem isAffineOpen_mix (π : Z'.X ⟶ Z.X) (M' : MChart Z') (M : MChart Z) : IsAffineOpen (M'.U ⊓ π ⁻¹ᵁ M.U) := by
  have := GlobalTheory.ThetaDescent.isProper_of_isProjOver Z.proj
  exact isAffineOpen_inf_preimage Z.s π M.hU M'.hU

def mixChg (M' : MChart Z') (M : MChart Z) : Matrix (Fin M'.n) (Fin M.n) Γ(Z'.X, M'.U ⊓ π ⁻¹ᵁ M.U) :=
  ((lieBasis M' (tau (isAffineOpen_mix π M' M)) (tau_le _ inf_le_left)).map (tanEquiv h _)).toMatrix
    (lieBasis M (tau (isAffineOpen_mix π M' M) ≫ π) (le_preimage_map π inf_le_right (tau_le _ le_rfl)))

theorem mixChg_map (M' : MChart Z') (M : MChart Z) (x : Sp S ⟶ Z'.X) (h' : ⊤ ≤ x ⁻¹ᵁ M'.U)
    (h₀ : ⊤ ≤ (x ≫ π) ⁻¹ᵁ M.U) (hh : ⊤ ≤ x ⁻¹ᵁ (M'.U ⊓ π ⁻¹ᵁ M.U)) :
    (mixChg h M' M).map (ev x _ hh) = ((lieBasis M' x h').map (tanEquiv h x)).toMatrix (lieBasis M (x ≫ π) h₀) := by
  have e : spMap (ev x _ hh) ≫ tau (isAffineOpen_mix π M' M) = x := spMap_ev x _ hh
  have e' : spMap (ev x _ hh) ≫ tau (isAffineOpen_mix π M' M) ≫ π = x ≫ π := by rw [← Category.assoc, e]
  ext i j
  have h1 := ((lieBasis M' (tau (isAffineOpen_mix π M' M)) (tau_le _ inf_le_left)).map
    (tanEquiv h _)).sum_toMatrix_smul_self
    (lieBasis M (tau (isAffineOpen_mix π M' M) ≫ π) (le_preimage_map π inf_le_right (tau_le _ le_rfl))) j
  have h2 := congrArg (tanPull (G := Z.t.G) _ e') h1
  rw [map_sum, tanPull_lieBasis M _ e' _ h₀] at h2
  simp only [map_smulₛₗ, Module.Basis.map_apply, tanPull_tanEquiv h _ e e', tanPull_lieBasis M' _ e _ h'] at h2
  rw [Module.Basis.toMatrix_apply, ← h2]
  simp only [← Module.Basis.map_apply]
  rw [Module.Basis.repr_sum_self]
  rfl

def mixDet (M' : MChart Z') (M : MChart Z) : Γ(Z'.X, M'.U ⊓ π ⁻¹ᵁ M.U)ˣ :=
  (show IsUnit (rdet (mixChg h M' M)) from isUnit_rdet_toMatrix _ _).unit

theorem ev_mixDet (M' : MChart Z') (M : MChart Z) (x : Sp S ⟶ Z'.X) (h' : ⊤ ≤ x ⁻¹ᵁ M'.U)
    (h₀ : ⊤ ≤ (x ≫ π) ⁻¹ᵁ M.U) (hh : ⊤ ≤ x ⁻¹ᵁ (M'.U ⊓ π ⁻¹ᵁ M.U)) :
    ev x _ hh (mixDet h M' M).val =
      rdet (((lieBasis M' x h').map (tanEquiv h x)).toMatrix (lieBasis M (x ≫ π) h₀)) := by
  rw [← mixChg_map h M' M x h' h₀ hh, ← map_rdet]
  rfl

include h in

theorem lbIso_detLie : LBIso ((detLie Z).pull π) (detLie Z') := by
  have le : ∀ J : ((detLie Z).pull π).ι, ((detLie Z).pull π).U J ≤ π ⁻¹ᵁ (J PUnit.unit).U := fun J =>
    LB.wchart_le (detLie Z) (fun _ : PUnit => π) J PUnit.unit
  refine ⟨⟨fun p => res (inf_le_inf_left _ (le p.2)) (mixDet h p.1 (p.2 PUnit.unit))⟩, fun p q => ?_⟩
  refine Eq.trans ?_ (mul_right_comm _ _ _)
  refine eq_mul_inv_of_mul_eq (Units.ext (ext_ev fun S _ z hz => ?_))
  have hp := le_preimage_mono inf_le_left hz
  have hq := le_preimage_mono inf_le_right hz
  have hp1 : ⊤ ≤ z ⁻¹ᵁ (p.1 : MChart Z').U := le_preimage_mono inf_le_left hp
  have hq1 : ⊤ ≤ z ⁻¹ᵁ (q.1 : MChart Z').U := le_preimage_mono inf_le_left hq
  have hp2 : ⊤ ≤ z ⁻¹ᵁ ((detLie Z).pull π).U p.2 := le_preimage_mono inf_le_right hp
  have hq2 : ⊤ ≤ z ⁻¹ᵁ ((detLie Z).pull π).U q.2 := le_preimage_mono inf_le_right hq
  have hp3 := le_preimage_map π (le p.2) hp2
  have hq3 := le_preimage_map π (le q.2) hq2
  have hp4 := le_preimage_mono (inf_le_inf_left _ (le p.2)) hp
  have hq4 := le_preimage_mono (inf_le_inf_left _ (le q.2)) hq
  have g := ev_pull_g (detLie Z) π z p.2 q.2 (le_preimage_inf hp2 hq2) (le_preimage_inf hp3 hq3)
  refine (map_mul (ev z _ hz) _ _).trans (Eq.trans ?_ (map_mul (ev z _ hz) _ _).symm)
  refine (congrArg₂ (· * ·) ((ev_res z _ hz hp _).trans ((ev_res z _ hp hp4 _).trans (ev_mixDet h _ _ z hp1 hp3 hp4)))
    ((ev_res z _ hz _ _).trans (g.trans (ev_detChg _ _ _ hp3 hq3 _)))).trans (Eq.trans ?_
    (congrArg₂ (· * ·) ((ev_res z _ hz (le_preimage_inf hp1 hq1) _).trans (ev_detChg _ _ z hp1 hq1 _))
      ((ev_res z _ hz hq _).trans ((ev_res z _ hq hq4 _).trans (ev_mixDet h _ _ z hq1 hq3 hq4)))).symm)
  rw [rdet_toMatrix_mul, ← rdet_toMatrix_mul _ ((lieBasis q.1 z hq1).map (tanEquiv h z))]
  congr 2
  ext i j
  simp [Module.Basis.toMatrix_apply]

end Det

theorem isLB_detLie_of_polOf {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β} {m : ℕ}
    {BD : EffCartierData Z.X} (h : (polOf Z m BD).IsLB) : (detLie Z).IsLB := by
  refine isLB_of_ev _ (eq_top_iff.2 fun x _ => ?_) fun i j k _ _ z => ev_detChg_mul i j k z
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (h.cover.ge (Set.mem_univ x))
  exact Opens.mem_iSup.2 ⟨i.1 PUnit.unit, LB.wchart_le _ _ _ PUnit.unit hi.1⟩

theorem exists_H0_of_isAmpleLB {X : Scheme.{0}} {A : LB X} (h : GlobalTheory.IsAmpleLB A) (y : X) :
    ∃ (d : ℕ) (s : Out.H0 A d), 1 ≤ d ∧ y ∈ Out.nonzeroLocus s ∧ IsAffineOpen (Out.nonzeroLocus s) := by
  obtain ⟨n, hn, s, hy, hs⟩ := h.exists_affine y
  have e : LBIso (lbPow A n) (LB.LinComb A (K := Fin 1) (fun _ => 𝟙 X) (fun _ => (n : ℤ))) :=
    CechPic.iso_of_chart (LB.isLB_linComb h.isLB _ _) (AmpUniq.chartPullPowSingle A n)
  obtain ⟨t, ht⟩ := exists_sec_nonzeroLocus_eq_of_lbIso (LB.isLB_linComb h.isLB _ _) (isLB_lbPow h.isLB n) e.symm s
  exact ⟨n, t, hn, ht ▸ hy, ht ▸ hs⟩

theorem isFinite_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l' : Level H) (Xo : Moduli D l)
    (Xo' : Moduli D l') (c : Coeff l) (c' : Coeff l') (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F)
    (β' : O' →+* c'.F) (Z : Model Xo c β) (Z' : Model Xo' c' β') (BD : EffCartierData Z.X) (BD' : EffCartierData Z'.X)
    (m : ℕ) (b : O →+* O') (σ : 𝓞 E ≃+* 𝓞 E) (π : Z'.X ⟶ Z.X) (hπ : π ≫ Z.s = Z'.s ≫ spMap b)
    (mu : TwMap σ Z'.t Z.t π), GlobalTheory.IsAmpleLB (polOf Z m BD) → GlobalTheory.IsAmpleLB (polOf Z' m BD') →
    BD'.idealSheaf = BD.idealSheaf.comap π → IsFinite (pullback.lift π Z'.s hπ) := by
  intro E _ _ _ H D l l' Xo Xo' c c' O O' _ _ β β' Z Z' BD BD' m b σ π hπ mu hA hA' hI
  have hL := isLB_detLie_of_polOf hA.isLB
  have hL' := isLB_detLie_of_polOf hA'.isLB
  have e₁ : CechPic.pull π (CechPic.cls _ hL) = CechPic.cls _ hL' :=
    (CechPic.cls_eq_iff (pull_isLB hL π) hL').2 (lbIso_detLie mu.cart)
  have hk : BD.KeepsRegular π := (BD.keepsRegular_iff_effCartier π).2 (hI ▸ BD'.effCartier_idealSheaf)
  have e₂ : CechPic.pull π (CechPic.cls _ BD.isLB_lb) = CechPic.cls _ BD'.isLB_lb :=
    ((CechPic.cls_eq_iff (BD.pull π hk).isLB_lb (pull_isLB BD.isLB_lb π)).2 (BD.lbIso_pull π hk)).symm.trans
      ((CechPic.cls_eq_iff _ _).2 (EffCartierData.lbIso_of_idealSheaf_eq _ _
        ((BD.idealSheaf_pull π hk).trans hI.symm)))
  have cl : ∀ {X : Scheme.{0}} {L B : LB X} (hL : L.IsLB) (hB : B.IsLB)
      (h : (CechPic.tens (lbPow (CechPic.dual L) m) (CechPic.dual B)).IsLB),
      CechPic.cls _ h = m • -CechPic.cls L hL + -CechPic.cls B hB := fun hL hB h => by
    rw [CechPic.cls_tens (isLB_lbPow (CechPic.isLB_dual hL) m) (CechPic.isLB_dual hB),
      CechPic.cls_lbPow (CechPic.isLB_dual hL), CechPic.cls_dual hL, CechPic.cls_dual hB]
  have e : CechPic.pull π (CechPic.cls _ hA.isLB) = CechPic.cls _ hA'.isLB :=
    (congrArg _ (cl hL BD.isLB_lb hA.isLB)).trans (Eq.trans
      (by rw [map_add, map_nsmul, map_neg, map_neg, e₁, e₂]) (cl hL' BD'.isLB_lb hA'.isLB).symm)
  have := GlobalTheory.ThetaDescent.isProper_of_isProjOver Z.proj
  have := GlobalTheory.ThetaDescent.isProper_of_isProjOver Z'.proj
  let f := pullback.lift π Z'.s hπ
  let s₁ := pullback.snd Z.s (spMap b)
  have hf : f ≫ s₁ = 𝟙 _ ≫ Z'.s := (pullback.lift_snd _ _ _).trans (Category.id_comp _).symm
  let ν : Z'.X ⟶ pullback s₁ Z'.s := pullback.lift f (𝟙 _) hf
  have h₁ : ν ≫ pullback.fst s₁ Z'.s = f := pullback.lift_fst _ _ _
  have h₂ : ν ≫ pullback.snd s₁ Z'.s = 𝟙 _ := pullback.lift_snd _ _ _
  have : IsClosedImmersion (ν ≫ pullback.snd s₁ Z'.s) := h₂ ▸ inferInstance
  have : IsClosedImmersion ν := IsClosedImmersion.of_comp ν (pullback.snd s₁ Z'.s)
  have hB := pull_isLB hA.isLB (pullback.fst Z.s (spMap b))
  have key := AmpUniq.isFinite_fst s₁ Z'.s ν hB hA'.isLB (exists_H0_of_isAmpleLB hA') (by
    refine (CechPic.cls_eq_iff (pull_isLB hB _) (pull_isLB hA'.isLB _)).1 ?_
    rw [CechPic.cls_pull hB, CechPic.cls_pull hA.isLB, CechPic.cls_pull hA'.isLB, ← CechPic.pull_comp, h₁, h₂,
      CechPic.pull_id, pullback.lift_fst, e])
  rwa [h₁] at key

end GlobalTheory.PolFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PowFlatLocallyQuasiFiniteStatement
section
open AlgebraicGeometry CategoryTheory Limits MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_flat_locallyQuasiFinite : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ q : ℕ, q ≠ 0 → Flat ((𝟙 G) ^ q : G ⟶ G).left ∧ LocallyQuasiFinite ((𝟙 G) ^ q : G ⟶ G).left := by
  first | exact @GlobalTheory.SemiAbMulFlat.flat_and_locallyQuasiFinite_pow | exact GlobalTheory.SemiAbMulFlat.flat_and_locallyQuasiFinite_pow | (intros; apply GlobalTheory.SemiAbMulFlat.flat_and_locallyQuasiFinite_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RiemannRochNeBotOfHolomorphicSectionNeBotStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.H0_ne_bot_of_holSec_ne_bot : ∀ (F : Type) [Field F] (Y : GlobalTheory.ProjVar.Var F) (σ : F →+* ℂ) (R : AnRead Y.str σ Y.dim) (D : Y.Dv), R.holSec (Y.lb D) ≠ ⊥ → Y.H0 D ≠ ⊥ := by
  first | exact @GlobalTheory.ShFam.Hor.riemannRoch_ne_bot_of_holomorphicSection_ne_bot | exact GlobalTheory.ShFam.Hor.riemannRoch_ne_bot_of_holomorphicSection_ne_bot | (intros; apply GlobalTheory.ShFam.Hor.riemannRoch_ne_bot_of_holomorphicSection_ne_bot <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothBaseAndNormalCoordinateRing
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb

theorem smooth_cbase {X : Scheme.{0}} {T : Type} [Finite T] (m : T → ℕ) (U : X.affineOpens) : Smooth (cbase m U) := by
  have h : Smooth (spMap (MvPolynomial.C : Γ(X, U.1) →+* CR m U)) := by
    refine (HasRingHomProperty.Spec_iff (P := @Smooth)).2 ?_
    exact RingHom.smooth_algebraMap.2 (⟨inferInstance, inferInstance⟩ : Algebra.Smooth Γ(X, U.1) (MvPolynomial (CellVar m) Γ(X, U.1)))
  have h' : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
  have h'' : Smooth U.2.fromSpec := inferInstance
  exact MorphismProperty.comp_mem @Smooth _ _ h h''

theorem cell_smooth_normal : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (T : Type) [Finite T] (m : T → ℕ) (U : X.affineOpens), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → Smooth (cbase m U) ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp (CR m U)) := by
  intro X _ T _ m U hX
  have := smooth_cbase m U
  exact ⟨this, forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth (cbase m U) hX⟩

end GlobalTheory.FlagEmb
end

