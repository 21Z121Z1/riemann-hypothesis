import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3023
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HolomorphicMapModuliLiftsLocallyToPeriods
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0095
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2996
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0943
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3095
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0908
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3074
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0084
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2554
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2643
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3075
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2675
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0508
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0234
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0647
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0585
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3081
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedNullSetCharts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0946
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3080
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasPullbackEqChartExpressionStatement
section
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holAtlas_pullback_eq_chart_expression : ∀ (M M' : Type) [TopologicalSpace M] [TopologicalSpace M'] (n n' : ℕ) (A : HolAtlas M n) (A' : HolAtlas M' n')
    (f : M' → M) (α : A.Fld), A.IsHolo A' f → A.IsForm α →
    ∀ (x : A'.Pt) (i : A.ι) (h : f x.pt ∈ (A.e i).source),
      A.pullback A' f α x = pull (fderiv ℂ (A.e i ∘ f ∘ x.ch.symm) x.crd) (α ⟨(i, f x.pt), h⟩) := by
  first | exact @GlobalTheory.CxForm.pullback_eq_chart | exact GlobalTheory.CxForm.pullback_eq_chart | (intros; apply GlobalTheory.CxForm.pullback_eq_chart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicMapLiftsLocallyToPeriodFamilies
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open Filter Topology

namespace GlobalTheory.PELU.LocLiftU

theorem comp_pow_one {X : Scheme.{0}} {G : Over X} [GrpObj G] {T U : Over X} (f : T ⟶ U) (x : U ⟶ G) {n : ℕ}
    (h : x ^ n = 1) : (f ≫ x) ^ n = 1 := by
  have : ∀ k : ℕ, (f ≫ x) ^ k = f ≫ x ^ k := fun k => by
    induction k with
    | zero => simp only [pow_zero, MonObj.comp_one]
    | succ k ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]
  rw [this, h, MonObj.comp_one]

end GlobalTheory.PELU.LocLiftU

namespace GlobalTheory.PELU

open LocLiftU

set_option maxHeartbeats 1000000 in

theorem holomorphic_map_lifts_to_periods : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (Λ : Type) (F : Fam ℂ O Λ g) (N : ℕ) (D' : PLat O bar) (t : Λ → D'.La) (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ F.X)) (b₀ : Fin m → ℂ) P₀ e₀, 0 < N → (∀ a, F.eta a ^ N = 1) → LocallyOfFiniteType F.s → IsOpen B → b₀ ∈ B → (∀ b ∈ B, y b ≫ F.s = spMap (RingHom.id ℂ)) → IsHolTo B y → UnifAt F (RingHom.id ℂ) ρ N D' t P₀ (y b₀) e₀ → ∃ (B' : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → (D'.La →+ (Fin g → ℂ))) (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ F.A)), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ P b₀ = P₀ ∧ IsHolPeriods D' ρ B' P ∧ IsHolTo (B' ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left) ∧ ∀ b ∈ B', UnifAt F (RingHom.id ℂ) ρ N D' t (P b) (y b) (e b) := by
  intro O _ bar g ρ Λ F N D' t m B y b₀ P₀ e₀ hN heta hlft hB hb₀ hyσ hy hU
  obtain ⟨-, hper₀, hexp₀, hker₀, hact₀, hweil₀, heta₀⟩ := hU
  have hab : IsAbelianScheme F.A := F.ab
  haveI := hab.proper
  obtain ⟨B₁, e, r, hB₁, hb₁, hB₁B, rfl, hr, hol, he, hl⟩ :=
    GlobalTheory.RelExp.exists_relative_exp ℂ (RingHom.id ℂ) F.X F.s F.A g m B y b₀ e₀ hlft hab F.dim hB hb₀ hyσ hy hexp₀
  change GlobalTheory.LocLift.HasLifts B₁ y e at hl
  change ∀ b ∈ B₁, GlobalTheory.LocLift.IsExp (y b) (e b) ∧ _ at he
  have hy₁ := GlobalTheory.LocLift.isHolTo_mono hy hB₁ hB₁B
  obtain ⟨P, hP₀, hP⟩ := GlobalTheory.LocLift.exists_periods GlobalTheory.latContinuation hB₁ hb₁ hy₁ hr hol he hl P₀ hper₀.2.1
    hper₀.2.2.2.1 hker₀
  choose L hL1 hL2 using fun a : O =>
    haveI := F.hom a; GlobalTheory.LocLift.exists_hol_linear_lift hB₁ hr hol he hl (F.act a)
  have hL0 : ∀ a, L a b₀ = Matrix.toLin' (ρ a) := fun a =>
    GlobalTheory.LocLift.linear_lift_unique (he b₀ hb₁).1.1 hr (he b₀ hb₁).2 fun z => by
      rw [hL1 a b₀ hb₁, Matrix.toLin'_apply, hact₀]
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hP.and (hB₁.mem_nhds hb₁))
  set C := Metric.ball b₀ ε
  have hCo : IsOpen C := Metric.isOpen_ball
  have hCc : IsPreconnected C := (convex_ball b₀ ε).isPreconnected
  have hC₀ : b₀ ∈ C := Metric.mem_ball_self hε
  have hC₁ : C ⊆ B₁ := fun b hb => (hball b hb).2
  have hPd : ∀ x, DifferentiableOn ℂ (fun b => P b x) C := fun x b hb =>
    ((hball b hb).1.1 x).differentiableWithinAt
  have hmv : ∀ {M : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
      {W : Set V} {β : V → (Fin m → ℂ)} {v : V → (Fin g → ℂ)}, (∀ i j, DifferentiableOn ℂ (fun w => M (β w) i j) W) →
      DifferentiableOn ℂ v W → DifferentiableOn ℂ (fun w => (M (β w)) *ᵥ (v w)) W := fun hM hv =>
    differentiableOn_pi.2 fun i => by
      simp only [Matrix.mulVec, dotProduct]
      exact DifferentiableOn.fun_sum fun j _ => (hM i j).fun_mul (differentiableOn_pi.1 hv j)
  have hLm : ∀ a i j, DifferentiableOn ℂ (fun b => LinearMap.toMatrix' (L a b) i j) B₁ := fun a i j => by
    simp only [LinearMap.toMatrix'_apply]
    exact differentiableOn_pi.1 (hL2 a (Pi.single j 1)) i
  have hk1 : ∀ b ∈ C, ∀ x, e b (P b x) = 1 := fun b hb x => ((hball b hb).1.2.1 _).2 ⟨x, rfl⟩
  have hlin : ∀ (a : O) x, ∀ b ∈ C, P b (a • x) - L a b (P b x) = 0 := fun a x => by
    haveI := F.hom a
    have hd : ContinuousOn (fun b => P b (a • x) - L a b (P b x)) C := by
      refine ((hPd _).sub ((hmv (M := fun b => LinearMap.toMatrix' (L a b)) (β := id)
        (fun i j => (hLm a i j).mono hC₁) (hPd x)).congr fun b _ => ?_)).continuousOn
      exact (LinearMap.toMatrix'_mulVec (L a b) (P b x)).symm
    refine GlobalTheory.LocLift.eq_zero_of_small hCc hd hr (fun b hb hn => (he b (hC₁ hb)).2 _ hn ?_) hC₀ ?_
    · exact (GlobalTheory.LocLift.hom_sub_eq_one (he b (hC₁ hb)).1.1).2
        (by rw [hL1 a b (hC₁ hb), hk1 b hb, hk1 b hb, MonObj.one_comp])
    · simp only [hP₀, hL0, Matrix.toLin'_apply, hper₀.1, sub_self]
  have htor : ∀ (k : ℕ) x, IsHolTo C (fun b => (e b ((k : ℂ)⁻¹ • P b x)).left) := fun k x =>
    GlobalTheory.LocLift.isHolTo_comp (β := fun b => (b, (k : ℂ)⁻¹ • P b x)) hol hCo
      (differentiableOn_id.prodMk ((hPd x).fun_const_smul _)) fun b hb => ⟨hC₁ hb, trivial⟩
  have hpow : ∀ (k : ℕ), 0 < k → ∀ x, ∀ b ∈ C, e b ((k : ℂ)⁻¹ • P b x) ^ k = 1 := fun k hk x b hb => by
    rw [← GlobalTheory.LocLift.hom_nsmul (he b (hC₁ hb)).1.1, ← Nat.cast_smul_eq_nsmul ℂ,
      smul_inv_smul₀ (Nat.cast_ne_zero.2 hk.ne'), hk1 b hb]
  have hyC : ∀ b ∈ C, y b ≫ F.s = spMap (RingHom.id ℂ) := fun b hb => hyσ b (hB₁B (hC₁ hb))
  have hwe : ∀ b ∈ C, ∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) / k) →
      Out.WeilIs F.A F.L k (e b ((k : ℂ)⁻¹ • P b a)) (e b ((k : ℂ)⁻¹ • P b a₂)) (unitOn c) :=
    fun b hb k a a₂ c hk hc => (GlobalTheory.T.torsion_commutatorPairing_const_holomorphicFamily_anyLineBundle F.X F.s F.A F.L hlft hab F.isLB m k C y
      (fun b => e b ((k : ℂ)⁻¹ • P b a)) (fun b => e b ((k : ℂ)⁻¹ • P b a₂)) c b₀ hk hCo hCc hC₀ hyC
      (htor k a) (htor k a₂) fun b hb => ⟨hpow k hk a b hb, hpow k hk a₂ b hb⟩).2
      (by simp only [hP₀]; exact hweil₀ k a a₂ c hk hc) b hb
  have heC : ∀ a, ∀ b ∈ C, toUnit _ ≫ F.eta a = e b ((N : ℂ)⁻¹ • P b (t a)) := fun a =>
    (GlobalTheory.T.torsion_commutatorPairing_const_holomorphicFamily_anyLineBundle F.X F.s F.A F.L hlft hab F.isLB m N C y (fun b => toUnit _ ≫ F.eta a)
      (fun b => e b ((N : ℂ)⁻¹ • P b (t a))) 1 b₀ hN hCo hCc hC₀ hyC
      (GlobalTheory.LocLift.isHolTo_congr (GlobalTheory.LocLift.isHolTo_comp_hom (GlobalTheory.LocLift.isHolTo_mono hy₁ hCo hC₁)
        (F.eta a).left) fun b _ => by rw [Over.comp_left, Over.toUnit_left]; rfl) (htor N (t a))
      fun b hb => ⟨comp_pow_one _ _ (heta a), hpow N hN (t a) b hb⟩).1 (by rw [hP₀]; exact heta₀ a)
  obtain ⟨B₂, h, hB₂, hb₂, hB₂C, hh₀, hhd, hh⟩ := GlobalTheory.T.holomorphic_lattice_family_retype_periodType O bar g ρ D' m C b₀ P hCo hC₀ hPd
    (by rw [hP₀]; exact hper₀) fun b hb => ⟨(hball b hb).1.2.2.2.1, fun a => ⟨LinearMap.toMatrix' (L a b), fun x => by
      rw [LinearMap.toMatrix'_mulVec]; exact sub_eq_zero.1 (hlin a x b hb)⟩⟩
  have hdet : ∀ b ∈ B₂, IsUnit (h b).det := fun b hb => (Matrix.isUnit_iff_isUnit_det _).1 (hh b hb).1
  obtain ⟨P', hP'⟩ := GlobalTheory.LocLift.exists_mulVec_comp h P
  have hinv : ∀ b ∈ B₂, ∀ z, (h b)⁻¹ *ᵥ (h b *ᵥ z) = z := fun b hb z => by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (hdet b hb), Matrix.one_mulVec]
  have hinv' : ∀ b ∈ B₂, ∀ z, h b *ᵥ ((h b)⁻¹ *ᵥ z) = z := fun b hb z => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hdet b hb), Matrix.one_mulVec]
  have key : ∀ b ∈ B₂, UnifAt F (RingHom.id ℂ) ρ N D' t (P' b) (y b) (fun z => e b ((h b)⁻¹ *ᵥ z)) := by
    intro b hb
    have hbC := hB₂C hb
    have hb1 := hC₁ hbC
    obtain ⟨j, hj⟩ := GlobalTheory.LocLift.exists_equiv_mulVec (hdet b hb)
    have hjs : ∀ z, (h b)⁻¹ *ᵥ z = j.symm z := fun z => by
      conv_lhs => rw [← j.apply_symm_apply z, ← hj]
      exact hinv b hb _
    have hPj : ∀ x, P' b x = j (P b x) := fun x => by rw [hP', hj]
    have hsm : ∀ (s : ℂ) x, (h b)⁻¹ *ᵥ (s • P' b x) = s • P b x := fun s x => by
      rw [Matrix.mulVec_smul, hP', hinv b hb]
    have hex : IsExp (y b) (fun z => e b ((h b)⁻¹ *ᵥ z)) := by
      have e1 : (fun z => e b ((h b)⁻¹ *ᵥ z)) = fun z => e b (j.symm z) := funext fun z => by rw [hjs]
      rw [e1]
      exact GlobalTheory.LocLift.IsExp.comp (he b hb1).1 j.symm
    have hPinj : Function.Injective (P' b) := fun x x' hx =>
      (hball b hbC).1.2.2.1 (j.injective (by rw [← hPj, ← hPj, hx]))
    have hker : ∀ z, e b ((h b)⁻¹ *ᵥ z) = 1 ↔ z ∈ (P' b).range := fun z => by
      rw [hjs, (hball b hbC).1.2.1]
      constructor
      · rintro ⟨x, hx⟩
        exact ⟨x, by rw [hPj, hx, j.apply_symm_apply]⟩
      · rintro ⟨x, hx⟩
        exact ⟨x, by rw [← hx, hPj, j.symm_apply_apply]⟩
    have hweil' : ∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k →
        (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) / k) →
        Out.WeilIs F.A F.L k (e b ((h b)⁻¹ *ᵥ ((k : ℂ)⁻¹ • P' b a))) (e b ((h b)⁻¹ *ᵥ ((k : ℂ)⁻¹ • P' b a₂)))
          (unitOn c) := fun k a a₂ c hk hc => by
      rw [hsm, hsm]
      exact hwe b hbC k a a₂ c hk hc
    obtain ⟨Hm, EF', h1, h2, h3, h4⟩ :=
      GlobalTheory.T.exists_positiveRiemannForm_of_relAmple_exponential F.X F.A g hab F.dim F.L F.isLB F.ample (y b) _ D'.La (P' b) hex hPinj hker
    have hEF : ∀ x x', EF' x x' = D'.EF x x' := fun x x' => GlobalTheory.LocLift.int_eq_of_exp fun k hk => by
      have := congrArg Units.val (GlobalTheory.T.weilPairing_complex_value_unique F.X F.A g hab F.dim F.L F.isLB (y b) k _ _
        (Units.mk0 _ (Complex.exp_ne_zero _)) (Units.mk0 _ (Complex.exp_ne_zero _)) (h4 k x x' _ hk rfl)
        (hweil' k x x' _ hk rfl))
      exact this
    obtain ⟨sp, dc⟩ := GlobalTheory.LocLift.lattice_comp j.symm (P := P b) (P' := P' b)
      (fun x => by rw [hPj, j.symm_apply_apply]) (hball b hbC).1.2.2.2.1 (hball b hbC).1.2.2.2.2
    have hclaim : ∀ (a : O) w, (h b)⁻¹ *ᵥ (ρ a *ᵥ (h b *ᵥ w)) = L a b w := fun a w => by
      have hfg : ((Matrix.toLin' (h b)⁻¹ ∘ₗ Matrix.toLin' (ρ a) ∘ₗ Matrix.toLin' (h b)).restrictScalars ℝ) =
          (L a b).restrictScalars ℝ := LinearMap.ext_on (hball b hbC).1.2.2.2.1 (by
        rintro _ ⟨x, rfl⟩
        simp only [LinearMap.restrictScalars_apply, LinearMap.comp_apply, Matrix.toLin'_apply]
        rw [← (hh b hb).2 a x, hinv b hb]
        exact sub_eq_zero.1 (hlin a x b hbC))
      have := LinearMap.congr_fun hfg w
      simp only [LinearMap.restrictScalars_apply, LinearMap.comp_apply, Matrix.toLin'_apply] at this
      exact this
    refine ⟨hyσ b (hB₁B hb1), ⟨fun a x => ?_, hPinj, dc, sp, Hm, h1, h2, fun x x' => by rw [h3, hEF]⟩,
      hex, hker, fun a z => ?_, hweil', fun a => ?_⟩
    · simp only [hP']
      exact (hh b hb).2 a x
    · haveI := F.hom a
      have := hL1 a b hb1 ((h b)⁻¹ *ᵥ z)
      rw [← hclaim, hinv' b hb] at this
      exact this
    · beta_reduce
      rw [hsm]
      exact heC a b hbC
  refine ⟨B₂, P', fun b z => e b ((h b)⁻¹ *ᵥ z), hB₂, hb₂, hB₂C.trans (hC₁.trans hB₁B), ?_,
    ⟨fun b hb => (key b hb).2.1, fun x => ?_⟩, ?_, key⟩
  · ext1 x
    rw [hP', hh₀, Matrix.one_mulVec, hP₀]
  · exact (hmv (M := h) (β := id) hhd ((hPd x).mono hB₂C)).congr fun b _ => hP' b x
  · have hid : ∀ i j, DifferentiableOn ℂ (fun b => (h b)⁻¹ i j) B₂ :=
      GlobalTheory.RiemannRel.differentiableOn_left_inverse h (fun b => (h b)⁻¹) hhd fun b hb =>
        Matrix.nonsing_inv_mul _ (hdet b hb)
    exact GlobalTheory.LocLift.isHolTo_comp (β := fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (bz.1, (h bz.1)⁻¹ *ᵥ bz.2)) hol
      (hB₂.prod isOpen_univ) (differentiableOn_fst.prodMk (hmv (M := fun b => (h b)⁻¹) (β := Prod.fst)
        (fun i j => (hid i j).comp differentiableOn_fst fun _ hw => hw.1) differentiableOn_snd))
      fun _ hw => ⟨hC₁ (hB₂C hw.1), trivial⟩

end GlobalTheory.PELU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorPeriodsAtGeneratingPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotent_factor_periods_at_generating_point : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (θ : R →+* V) (Q : Data R) (D₀ : DegPre R) (F : PFactor Q D₀) (W : (Sp R).Opens) (ψW : PsiOn D₀ W) (g : (TK V).left ⟶ W.toScheme), g ≫ W.ι = jK V ≫ spMap θ → ∀ (a b : Q.X) (u : LB.Gen (LB.LinComb Q.M.L (lamPts (Q.c a) (Q.c b)) negε)) (x y : R) (k : (FractionRing R)ˣ) (k' : (FractionRing V)ˣ), u.IsGen → θ y ≠ 0 → (k : FractionRing R) * algebraMap R _ y = algebraMap R _ x → (k' : FractionRing V) * algebraMap V _ (θ y) = algebraMap V _ (θ x) → (∀ z J, Good Q.M.L z J → val (Q.tau a b) (𝟙 _) z J = gm (𝟙 (TK R).left) z ⊤ (unitOn k) * val u (toUnit (TK R)).left z J) → ∀ z J J', Good D₀.P.L z J → Good Q.M.L z J' → gm (𝟙 (TK V).left) z ⊤ (unitOn k') * val u ((TK V).hom ≫ spMap θ) z J' = lamVal F.w (((TK V).hom ≫ spMap θ) ≫ (lift (Q.c a) (Q.c b)).left) z J J' * val (ψW.tau (F.xi a) (F.f • F.xi b)) g z J := by
  first | exact @GlobalTheory.FactorPeriod.factor_period | exact GlobalTheory.FactorPeriod.factor_period | (intros; apply GlobalTheory.FactorPeriod.factor_period <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImHermFormAlternatingNondegenerateOnLatticeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.im_hermForm_alternating_nondegenerate_on_lattice : ∀ (La : Type) [AddCommGroup La] (g : ℕ) (P : La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (EF : LinearMap.BilinForm ℤ La), Function.Injective P → Submodule.span ℝ (Set.range P) = ⊤ → Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → (∀ x y, (hermForm Hm (P x) (P y)).im = EF x y) → (∀ x, EF x x = 0) ∧ ∀ x, (∀ y, EF x y = 0) → x = 0 := by
  first | exact @GlobalTheory.HermImNondeg.im_hermForm_alternating_nondegenerate | exact GlobalTheory.HermImNondeg.im_hermForm_alternating_nondegenerate | (intros; apply GlobalTheory.HermImNondeg.im_hermForm_alternating_nondegenerate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsLastLast
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

namespace GlobalTheory.ProdUnif

theorem even_box₂ : ∀ {B B₁ B₂ G G₁ G₂ T T₁ T₂ : Scheme.{0}} {M : LB B} {M₁ : LB B₁} {M₂ : LB B₂} {L : LB G} {L₁ : LB G₁} {L₂ : LB G₂} {b₁ : B ⟶ B₁} {b₂ : B ⟶ B₂} {g₁ : G ⟶ G₁} {g₂ : G ⟶ G₂} {p : T ⟶ B} {f : T ⟶ G} {p₁ : T₁ ⟶ B₁} {f₁ : T₁ ⟶ G₁} {p₂ : T₂ ⟶ B₂} {f₂ : T₂ ⟶ G₂} {h₁ : T ⟶ T₁} {h₂ : T ⟶ T₂} (wM : LB.Iso M (extLB M₁ M₂ b₁ b₂)) (wL : LB.Iso L (extLB L₁ L₂ g₁ g₂)) (we₁ : LB.Iso (L₁.pull f₁) (M₁.pull p₁)) (we₂ : LB.Iso (L₂.pull f₂) (M₂.pull p₂)), M.IsLB → M₁.IsLB → M₂.IsLB → L.IsLB → L₁.IsLB → L₂.IsLB → p ≫ b₁ = h₁ ≫ p₁ → p ≫ b₂ = h₂ ≫ p₂ → f ≫ g₁ = h₁ ≫ f₁ → f ≫ g₂ = h₂ ≫ f₂ → ∀ (we : LB.Iso (L.pull f) (M.pull p)), BoxSq wM wL we we₁ we₂ h₁ h₂ → ∀ (iT : T ⟶ T) (iT₁ : T₁ ⟶ T₁) (iT₂ : T₂ ⟶ T₂) {iG : G ⟶ G} {iG₁ : G₁ ⟶ G₁} {iG₂ : G₂ ⟶ G₂} {iB : B ⟶ B} {iB₁ : B₁ ⟶ B₁} {iB₂ : B₂ ⟶ B₂} (s : LB.Gen (LB.LinComb L (K := Fin 2) ![iG, 𝟙 G] ![1, -1])) (s₁ : LB.Gen (LB.LinComb L₁ (K := Fin 2) ![iG₁, 𝟙 G₁] ![1, -1])) (s₂ : LB.Gen (LB.LinComb L₂ (K := Fin 2) ![iG₂, 𝟙 G₂] ![1, -1])) (σ : LB.Gen (LB.LinComb M (K := Fin 2) ![iB, 𝟙 B] ![1, -1])) (σ₁ : LB.Gen (LB.LinComb M₁ (K := Fin 2) ![iB₁, 𝟙 B₁] ![1, -1])) (σ₂ : LB.Gen (LB.LinComb M₂ (K := Fin 2) ![iB₂, 𝟙 B₂] ![1, -1])), iT ≫ h₁ = h₁ ≫ iT₁ → iT ≫ h₂ = h₂ ≫ iT₂ → iT ≫ f = f ≫ iG → iT ≫ p = p ≫ iB → iT₁ ≫ f₁ = f₁ ≫ iG₁ → iT₁ ≫ p₁ = p₁ ≫ iB₁ → iT₂ ≫ f₂ = f₂ ≫ iG₂ → iT₂ ≫ p₂ = p₂ ≫ iB₂ → IsBoxGen wL g₁ g₂ s s₁ s₂ → IsBoxGen wM b₁ b₂ σ σ₁ σ₂ → GlobalTheory.PowUnif.EvenAlong we₁ iT₁ s₁ σ₁ → GlobalTheory.PowUnif.EvenAlong we₂ iT₂ s₂ σ₂ → GlobalTheory.PowUnif.EvenAlong we iT s σ := by
  intro B B₁ B₂ G G₁ G₂ T T₁ T₂ M M₁ M₂ L L₁ L₂ b₁ b₂ g₁ g₂ p f p₁ f₁ p₂ f₂ h₁ h₂ wM wL we₁ we₂
    hM hM₁ hM₂ hL hL₁ hL₂ e₁ e₂ e₃ e₄ we Q iT iT₁ iT₂ iG iG₁ iG₂ iB iB₁ iB₂ s s₁ s₂ σ σ₁ σ₂
    ih₁ ih₂ iF iP iF₁ iP₁ iF₂ iP₂ Hs Hσ ev₁ ev₂
  intro jS jT cS cT V k₁ k₂ k₃ k₄
  refine unit_ext fun z hz => ?_
  obtain ⟨n₁, n₂⟩ := GlobalTheory.EvenPull.even_stalk we s σ jS jT V k₁ k₂ k₃ k₄ (𝟙 T) z hz
  refine n₁.trans (Eq.trans ?_ n₂.symm)
  clear n₁ n₂
  obtain ⟨J, hJ, hJj⟩ := exists_good M hM z (fun k => p ≫ (![iB, 𝟙 B] : Fin 2 → _) k) jT cT
    (fun k => Set.mem_iInter.1 (k₁ hz) k)
  obtain ⟨N, hN, hNj⟩ := exists_good L hL z (fun k => f ≫ (![iG, 𝟙 G] : Fin 2 → _) k) jS cS
    (fun k => Set.mem_iInter.1 (k₄ hz) k)
  obtain ⟨J₁, hJ₁⟩ := GlobalTheory.BoxFamily.exists_good_at hM₁ z
  obtain ⟨J₂, hJ₂⟩ := GlobalTheory.BoxFamily.exists_good_at hM₂ z
  obtain ⟨N₁, hN₁⟩ := GlobalTheory.BoxFamily.exists_good_at hL₁ z
  obtain ⟨N₂, hN₂⟩ := GlobalTheory.BoxFamily.exists_good_at hL₂ z

  have hb₁ : (p ≫ iB) ≫ b₁ = (h₁ ≫ p₁) ≫ iB₁ := by
    rw [← iP, Category.assoc, e₁, ← Category.assoc, ih₁, Category.assoc, iP₁, Category.assoc]
  have hb₂ : (p ≫ iB) ≫ b₂ = (h₂ ≫ p₂) ≫ iB₂ := by
    rw [← iP, Category.assoc, e₂, ← Category.assoc, ih₂, Category.assoc, iP₂, Category.assoc]
  have hg₁ : (f ≫ iG) ≫ g₁ = (h₁ ≫ f₁) ≫ iG₁ := by
    rw [← iF, Category.assoc, e₃, ← Category.assoc, ih₁, Category.assoc, iF₁, Category.assoc]
  have hg₂ : (f ≫ iG) ≫ g₂ = (h₂ ≫ f₂) ≫ iG₂ := by
    rw [← iF, Category.assoc, e₄, ← Category.assoc, ih₂, Category.assoc, iF₂, Category.assoc]
  have QQ : ∀ k, om wM z J₁ J₂ J (p ≫ (![iB, 𝟙 B] : Fin 2 → _) k) *
        gw we ((![iT, 𝟙 T] : Fin 2 → _) k) z (J (p ≫ (![iB, 𝟙 B] : Fin 2 → _) k))
          (fun _ => N (f ≫ (![iG, 𝟙 G] : Fin 2 → _) k)) =
      gw we₁ ((![h₁ ≫ iT₁, h₁] : Fin 2 → _) k) z (J₁ ((h₁ ≫ p₁) ≫ (![iB₁, 𝟙 B₁] : Fin 2 → _) k))
          (fun _ => N₁ ((h₁ ≫ f₁) ≫ (![iG₁, 𝟙 G₁] : Fin 2 → _) k)) *
        gw we₂ ((![h₂ ≫ iT₂, h₂] : Fin 2 → _) k) z (J₂ ((h₂ ≫ p₂) ≫ (![iB₂, 𝟙 B₂] : Fin 2 → _) k))
          (fun _ => N₂ ((h₂ ≫ f₂) ≫ (![iG₂, 𝟙 G₂] : Fin 2 → _) k)) *
        om wL z N₁ N₂ N (f ≫ (![iG, 𝟙 G] : Fin 2 → _) k) := by
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · have q := Q T iT z J₁ J₂ J N₁ N₂ N hJ₁ hJ₂ hJ hN₁ hN₂ hN
      rw [iP, iF, ih₁, ih₂, hb₁, hb₂, hg₁, hg₂] at q
      simpa only [Matrix.cons_val_zero] using q
    · have q := Q T (𝟙 T) z J₁ J₂ J N₁ N₂ N hJ₁ hJ₂ hJ hN₁ hN₂ hN
      simp only [Category.id_comp] at q
      rw [e₁, e₂, e₃, e₄] at q
      simpa only [Matrix.cons_val_one, Matrix.cons_val_zero, Category.comp_id] using q
  have HM := Hσ T p z J₁ J₂ J hJ₁ hJ₂ hJ
  rw [e₁, e₂] at HM
  have HL := Hs T f z N₁ N₂ N hN₁ hN₂ hN
  rw [e₃, e₄] at HL
  have H₁ : val σ₁ (h₁ ≫ p₁) z J₁ = (∏ k, gw we₁ ((![h₁ ≫ iT₁, h₁] : Fin 2 → _) k) z
      (J₁ ((h₁ ≫ p₁) ≫ (![iB₁, 𝟙 B₁] : Fin 2 → _) k))
      (fun _ => N₁ ((h₁ ≫ f₁) ≫ (![iG₁, 𝟙 G₁] : Fin 2 → _) k)) ^ (![1, -1] : Fin 2 → ℤ) k) *
      val s₁ (h₁ ≫ f₁) z N₁ :=
    ev₁.stalk iF₁ iP₁ h₁ z _ _
      (fun a b e => congrArg N₁ ((Category.assoc _ _ _).trans ((congrArg (h₁ ≫ ·) e).trans
        (Category.assoc _ _ _).symm)))
      (fun a b e => congrArg J₁ ((Category.assoc _ _ _).trans ((congrArg (h₁ ≫ ·) e).trans
        (Category.assoc _ _ _).symm)))
      (fun k => hN₁ ((h₁ ≫ f₁) ≫ (![iG₁, 𝟙 G₁] : Fin 2 → _) k))
      (fun k => hJ₁ ((h₁ ≫ p₁) ≫ (![iB₁, 𝟙 B₁] : Fin 2 → _) k))
  have H₂ : val σ₂ (h₂ ≫ p₂) z J₂ = (∏ k, gw we₂ ((![h₂ ≫ iT₂, h₂] : Fin 2 → _) k) z
      (J₂ ((h₂ ≫ p₂) ≫ (![iB₂, 𝟙 B₂] : Fin 2 → _) k))
      (fun _ => N₂ ((h₂ ≫ f₂) ≫ (![iG₂, 𝟙 G₂] : Fin 2 → _) k)) ^ (![1, -1] : Fin 2 → ℤ) k) *
      val s₂ (h₂ ≫ f₂) z N₂ :=
    ev₂.stalk iF₂ iP₂ h₂ z _ _
      (fun a b e => congrArg N₂ ((Category.assoc _ _ _).trans ((congrArg (h₂ ≫ ·) e).trans
        (Category.assoc _ _ _).symm)))
      (fun a b e => congrArg J₂ ((Category.assoc _ _ _).trans ((congrArg (h₂ ≫ ·) e).trans
        (Category.assoc _ _ _).symm)))
      (fun k => hN₂ ((h₂ ≫ f₂) ≫ (![iG₂, 𝟙 G₂] : Fin 2 → _) k))
      (fun k => hJ₂ ((h₂ ≫ p₂) ≫ (![iB₂, 𝟙 B₂] : Fin 2 → _) k))
  have R := rel_alg (![1, -1] : Fin 2 → ℤ) _ _ _ _ _ QQ HM HL H₁ H₂
  rw [val_of σ p z J jT hJj, val_of s f z N jS hNj, Fin.prod_univ_two] at R
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_one, zpow_neg] at R
  have a₀ : J (p ≫ iB) = jT 0 := hJj 0
  have a₁ : J (p ≫ 𝟙 B) = jT 1 := hJj 1
  have c₀ : N (f ≫ iG) = jS 0 := hNj 0
  have c₁ : N (f ≫ 𝟙 G) = jS 1 := hNj 1
  rw [a₀, a₁, c₀, c₁] at R
  simp only [Category.id_comp]
  rw [R, mul_right_comm, inv_mul_cancel_right]

end GlobalTheory.ProdUnif
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsSideTer
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.WpFam

namespace GlobalTheory.HilbFam.SizeGL

theorem main : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) [NeZero N] (L : Lat F), 1 ≤ s → HasLevel N L → ∀ [IsGalois ℚ F] (z : ClassGroup (𝓞 F) → ℚ), ZetaVals (2 * s) z → ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (κ : Emb F → ℕ) (y : Fin 2 → ZMod N) (M M' b : ℕ) (e ρ₀ ρ : ℝ), 0 ≤ e → (∀ C, -(padicValRat l (z C / 2 ^ Module.finrank ℚ F) : ℝ) ≤ e) → ¬ l ∣ M → (∀ x ∈ stdLat F, ((M * l ^ b : ℕ) : 𝓞 F) • x ∈ L) → (∀ v ∈ L, ∀ (j : Fin 2) (i : Emb F), Sz l lam ρ₀ ((i (v j) : ℝ) : ℂ)) → Sz l lam ρ₀ (N : ℂ) → b + (padicValInt l (discr F) : ℝ) / Module.finrank ℚ F + ρ₀ ≤ ρ → 0 ≤ ρ → ¬ l ∣ M' → M' • y = 0 → y ≠ 0 → ∀ α : GL (Fin 2) (ZMod N), QAll (Sz l lam (e + s * (padicValInt l (discr F) : ℝ) + 2 * s * b * Module.finrank ℚ F + (∑ i, κ i : ℕ) * ρ)) N (hfun (2 * s) (twist N L ((α : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) κ (wB N (vmul y (α)))) := by
  intro hE F _ _ _ hf s N _ L hs hL _ z hz l _ lam κ y M M' b e ρ₀ ρ he hze hlM hML hLsz hNsz hρ hρ0 hlM' hMy hy α
  have hA := GlobalTheory.WpFam.Act.rightActions N
  have hS := GlobalTheory.QFam.SzSum.sz_ring l lam
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hTw : HasLevel N (twist N L ((α : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) :=
    GlobalTheory.HilbFam.hasLevel_twist_of_hasLevel F N L _ hL
  obtain ⟨hmem, hsz⟩ := GlobalTheory.T.twistedHilbertLattice_contains_and_coordinate_size l lam F N (M * l ^ b) L α ρ₀ hL.2 hML hLsz hNsz
  have hx : M' • vmul y α = 0 := by rw [← hA.2.2.2.2.2.1, hMy]; exact (hA.2.2.2.2.1 0 α).mpr rfl
  have hx0 : vmul y α ≠ 0 := fun h => hy ((hA.2.2.2.2.1 y α).mp h)
  obtain ⟨hQ, -⟩ := GlobalTheory.T.weierstrassTorsion_qExpansion_integral l lam N M' (vmul y α) hlM' hx hx0
  have hQρ : QAll (Sz l lam ρ) N (wB N (vmul y α)) := by
    obtain ⟨a, ha, hp⟩ := hQ
    exact ⟨a, ha, fun n => hS.2.2.2.1 0 ρ _ hρ0 (hp n)⟩
  exact GlobalTheory.T.hilbertEisenstein_coefficient_valuation_bound hE F hf s N _ hs hN hTw z hz l lam κ (wB N (vmul y α)) M b e ρ₀ ρ he hze hlM hmem hsz hρ hQρ

end GlobalTheory.HilbFam.SizeGL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InductiveArakelovFormulaRhsTensorAdditiveStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inductiveArakelovFormula_rhs_tensor_additive : ArchInteg → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → ∀ e : ℕ, topologicalKrullDim Y = (e + 1 : ℕ) → ∀ (h : Y → ℝ) (L : Fin e → HermLB q) (M A : HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r) (u : A.B.ι → Y.functionFieldˣ) (hu : IsRatSec A.B u) (t : (M.tens A).B.ι → Y.functionFieldˣ) (ht : IsRatSec (M.tens A).B t), (∀ (i : M.B.ι) (j : A.B.ι), genericPoint Y ∈ M.B.U i → genericPoint Y ∈ A.B.U j → t (i, j) = r i * u j) → recVal h L (M.tens A) ht = recVal h L M hr + recVal h L A hu := by
  first | exact @GlobalTheory.MixHt.recVal_tens | exact GlobalTheory.MixHt.recVal_tens | (intros; apply GlobalTheory.MixHt.recVal_tens <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableAgainstMixedChernFormIffPullIso
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
open scoped ENNReal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MixIso

theorem map_chartMeas {A B : Type} [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]
    [TopologicalSpace B] [MeasurableSpace B] [BorelSpace B] {n : ℕ} (Φ : A ≃ᵐ B)
    (e' : OpenPartialHomeomorph A (ReciprocityTheory.L2DbarEstimates.V n)) (e : OpenPartialHomeomorph B (ReciprocityTheory.L2DbarEstimates.V n))
    (ρ' : A → ℝ≥0∞) (ρ : B → ℝ≥0∞) (ht : e'.target = e.target)
    (hs : ∀ v ∈ e.target, Φ (e'.symm v) = e.symm v) (hρ : ∀ v ∈ e.target, ρ' (e'.symm v) = ρ (e.symm v)) :
    Measure.map Φ (chartMeas e' ρ') = chartMeas e ρ := by
  unfold chartMeas
  have hae : AEMeasurable e'.symm ((volume.restrict e'.target).withDensity (ρ' ∘ e'.symm)) :=
    (e'.continuousOn_symm.aemeasurable e'.open_target.measurableSet).mono_ac
      (withDensity_absolutelyContinuous _ _)
  rw [AEMeasurable.map_map_of_aemeasurable Φ.measurable.aemeasurable hae, ht]
  have h1 : (volume.restrict e.target).withDensity (ρ' ∘ e'.symm) =
      (volume.restrict e.target).withDensity (ρ ∘ e.symm) :=
    withDensity_congr_ae ((ae_restrict_iff' e.open_target.measurableSet).2
      (Eventually.of_forall fun v hv => hρ v hv))
  rw [h1]
  exact Measure.map_congr ((withDensity_absolutelyContinuous _ _).ae_le
    ((ae_restrict_iff' e.open_target.measurableSet).2 (Eventually.of_forall fun v hv => hs v hv)))

theorem le_map_symm_iff {A B : Type} [MeasurableSpace A] [MeasurableSpace B] (Φ : A ≃ᵐ B)
    (μ : Measure A) (ν : Measure B) : μ ≤ Measure.map Φ.symm ν ↔ Measure.map Φ μ ≤ ν := by
  constructor
  · intro h
    simpa only [MeasurableEquiv.map_map_symm] using Measure.map_mono h Φ.measurable
  · intro h
    simpa only [MeasurableEquiv.map_symm_map] using Measure.map_mono h Φ.symm.measurable

end GlobalTheory.MixIso

namespace GlobalTheory.MixIso

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k}

theorem inv_comp (π : Y ⟶ X) [IsIso π] (hπ : π ≫ p = q) : inv π ≫ q = p := by
  rw [IsIso.inv_comp_eq, hπ]

def ptH (π : Y ⟶ X) [IsIso π] (hπ : π ≫ p = q) (σ : k →+* ℂ) : CxPts q σ ≃ₜ CxPts p σ where
  toFun := ptMap π hπ σ
  invFun := ptMap (inv π) (inv_comp π hπ) σ
  left_inv y := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)
  continuous_toFun := CxPts.continuous_of_comp (f := π) fun _ => rfl
  continuous_invFun := CxPts.continuous_of_comp (f := inv π) fun _ => rfl

variable {σ : k →+* ℂ} {D : ℕ}

def pullChart (π : Y ⟶ X) [IsIso π] (hπ : π ≫ p = q) (c : AlgChart p σ D) : AlgChart q σ D where
  e := (ptH π hπ σ).transOpenPartialHomeomorph c.e
  U := π ⁻¹ᵁ c.U
  affine := c.affine.preimage_of_isIso π
  x a := π.app c.U (c.x a)
  etale := GlobalTheory.Mean4O.CoverExc.etale_app π hπ c.etale
    (RingHom.Etale.of_bijective (ConcreteCategory.bijective_of_isIso (π.app c.U)))
  source_subset y hy := (mem_ptsIn_preimage (m := ptMap π hπ σ) (fun _ => rfl)).2 (c.source_subset hy)
  apply_eq y hy a := (c.apply_eq _ hy a).trans (ev_of_comp (m := ptMap π hπ σ) (fun _ => rfl) _ _ _)
  holo W f := by
    refine ((c.holo (inv π ⁻¹ᵁ W) ((inv π).app W f)).mono fun v hv => ⟨hv.1,
      (mem_ptsIn_preimage (m := ptMap (inv π) (inv_comp π hπ) σ) (f := inv π) (fun _ => rfl)).2 hv.2⟩).congr
      fun v _ => ?_
    exact ev_of_comp (m := ptMap (inv π) (inv_comp π hπ) σ) (f := inv π) (fun _ => rfl) W f _

theorem pullChart_symm (π : Y ⟶ X) [IsIso π] (hπ : π ≫ p = q) (c : AlgChart p σ D) (v : ReciprocityTheory.L2DbarEstimates.V D) :
    (pullChart π hπ c).e.symm v = ptMap (inv π) (inv_comp π hπ) σ (c.e.symm v) := rfl

end GlobalTheory.MixIso

namespace GlobalTheory.MixIso

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

theorem map_chartMeas_dens (π : Y ⟶ X) [IsIso π] (hπ : π ≫ p = q) (L : Fin D → MLine p σ) (ε : ℤˣ)
    (c : AlgChart p σ D) (c' : AlgChart q σ D) (ht : c'.e.target = c.e.target)
    (hs : ∀ v, ptMap π hπ σ (c'.e.symm v) = c.e.symm v) :
    Measure.map (ptH π hπ σ).toMeasurableEquiv
      (chartMeas c'.e fun y => ENNReal.ofReal ((ε : ℤ) * dens (fun i => (L i).pull π hπ) c' y)) =
      chartMeas c.e fun y => ENNReal.ofReal ((ε : ℤ) * dens L c y) := by
  refine map_chartMeas _ _ _ _ _ ht (fun v _ => hs v) fun v hv => ?_
  rw [← hs v, GlobalTheory.MixPull.dens_pull k X Y p q σ D π hπ L c c' (fun w hw => ?_) _ (c'.e.map_target (ht ▸ hv))]
  have hw' : c'.e w ∈ c.e.target := ht ▸ c'.e.map_source hw
  have e : ptMap π hπ σ w = c.e.symm (c'.e w) := by rw [← hs, c'.e.left_inv hw]
  rw [e]
  exact ⟨c.e.map_target hw', (c.e.right_inv hw').symm⟩

theorem map_part (π : Y ⟶ X) [IsIso π] (hπ : π ≫ p = q) (L : Fin D → MLine p σ) (ε : ℤˣ) :
    Measure.map (ptH π hπ σ).toMeasurableEquiv (part (fun i => (L i).pull π hπ) ε) = part L ε := by
  unfold part glueMeas
  refine le_antisymm ((le_map_symm_iff _ _ _).1 (iSup_le fun c' => (le_map_symm_iff _ _ _).2 ?_))
    (iSup_le fun c => ?_)
  · rw [map_chartMeas_dens π hπ L ε (pullChart (inv π) (inv_comp π hπ) c') c' rfl fun v =>
      Subtype.ext (by simp [pullChart_symm])]
    exact le_iSup (fun c : AlgChart p σ D => chartMeas c.e fun y => ENNReal.ofReal ((ε : ℤ) * dens L c y)) _
  · rw [← map_chartMeas_dens π hπ L ε c (pullChart π hπ c) rfl fun v => (ptH π hπ σ).right_inv _]
    exact Measure.map_mono (le_iSup (fun c' : AlgChart q σ D => chartMeas c'.e fun y =>
      ENNReal.ofReal ((ε : ℤ) * dens (fun i => (L i).pull π hπ) c' y)) _) (MeasurableEquiv.measurable _)

theorem intg_int_pull : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ), IsProjOver p → ∀ (π : Y ⟶ X) [IsIso π] (hπ : π ≫ p = q) (D : ℕ) (L : Fin D → MLine p σ) (f : CxPts p σ → ℝ), (Intg (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y)) ↔ Intg L f) ∧ Mix.int (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y)) = Mix.int L f := by
  intro k _ X Y p q σ _ π _ hπ D L f
  simp only [Intg, Mix.int, ← map_part π hπ L, integrable_map_equiv, integral_map_equiv]
  exact ⟨Iff.rfl, rfl⟩

end GlobalTheory.MixIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinimiserCellFunctionMinFinitelyManyCombinationsStatement
section
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minimiser_cell_function_min_finitely_many_combinations : ∀ (g : ℕ) (φ : InvFun ℤ), IsPolFan id g φ → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), PosW W → ∀ (N : ℕ) [NeZero N], 3 ≤ N → (∃ ε : Fin 8 → ℤ, Nat.Coprime N (2 * (∑ u, ∑ v, W u v * ε u * ε v).natAbs)) → ∀ r : ℕ, r ≤ g → ∃ (ι : ℕ) (𝓛 : Finset (Finset ((Fin 8 → Fin r → ZMod N) → ℤ))), 1 ≤ ι ∧ ∀ (b : LinearMap.BilinForm ℤ (Fin r → ℤ)), (∀ x y, b x y = b y x) → (∀ x, x ≠ 0 → 0 < b x x) → ∀ μ : (Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ), (∀ c u i, ((μ c u i : ℤ) : ZMod N) = c u i) → (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W b (μ c) ≤ qW W b α) → ∃ L ∈ 𝓛, ∀ (b' : LinearMap.BilinForm ℤ (Fin r → ℤ)), (∀ x y, b' x y = b' y x) → (∀ x, 0 ≤ b' x x) → (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W b' (μ c) ≤ qW W b' α) → (∀ ν ∈ L, (ι * N : ℝ) * φ.evalZ b' ≤ ∑ c, (ν c : ℝ) * qW W b' (μ c)) ∧ ∃ ν ∈ L, (ι * N : ℝ) * φ.evalZ b' = ∑ c, (ν c : ℝ) * qW W b' (μ c) := by
  first | exact @GlobalTheory.Poinc.finite_types | exact GlobalTheory.Poinc.finite_types | (intros; apply GlobalTheory.Poinc.finite_types <;> assumption)
end

