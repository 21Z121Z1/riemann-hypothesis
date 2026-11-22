import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.ThetaBasic
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0034
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0345
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0330
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0320
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0344
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0346
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0326
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0289
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0017
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFinsetSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulEqZeroOfMem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0336
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0314
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0226
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0208
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0237
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0331
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusFactorisation.PullT

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumProdEqPow
section
noncomputable section

open scoped ENNReal

namespace GlobalTheory.CompanionTheory.LatticeSum

theorem tsum_prod_eq_pow (g : ℤ → ℝ≥0∞) (n : ℕ) :
    ∑' m : Fin n → ℤ, ∏ i, g (m i) = (∑' k, g k) ^ n :=
  _root_.UpperTheory.Reformulated.B.Yvb3.main g n

def wt (k : ℤ) : ℝ := ((1 + |(k : ℝ)|) ^ 2)⁻¹

theorem wt_nonneg (k : ℤ) : 0 ≤ wt k := by
  unfold wt; positivity

theorem summable_nat_wt : Summable fun k : ℕ => (((k : ℝ) + 1) ^ 2)⁻¹ := by
  have h : Summable fun k : ℕ => ((k : ℝ) ^ 2)⁻¹ := by
    simpa [one_div] using (Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num)
  have h1 := (summable_nat_add_iff 1).2 h
  simpa using h1

theorem summable_wt : Summable wt := by
  apply Summable.of_nat_of_neg
  · refine summable_nat_wt.congr fun k => ?_
    simp [wt, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) k), add_comm]
  · refine summable_nat_wt.congr fun k => ?_
    simp [wt, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) k), add_comm]

theorem pointwise_le (n M : ℕ) (h : 2 * n ≤ M) (m : Fin n → ℤ) :
    (1 + ‖fun i => (m i : ℝ)‖) ^ (-(M : ℤ)) ≤ ∏ i, wt (m i) := by
  set N : ℝ := 1 + ‖fun i => (m i : ℝ)‖ with hN
  have hN1 : 1 ≤ N := by
    have := norm_nonneg (fun i => (m i : ℝ))
    linarith
  have hN0 : 0 < N := by linarith
  have hle : ∏ i, (1 + |(m i : ℝ)|) ^ 2 ≤ N ^ M := by
    calc ∏ i, (1 + |(m i : ℝ)|) ^ 2 ≤ ∏ _i : Fin n, N ^ 2 := by
          apply Finset.prod_le_prod
          · intro i _; positivity
          · intro i _
            have h1 : |(m i : ℝ)| ≤ ‖fun i => (m i : ℝ)‖ := by
              simpa [Real.norm_eq_abs] using norm_le_pi_norm (fun i => (m i : ℝ)) i
            have h2 : 1 + |(m i : ℝ)| ≤ N := by rw [hN]; linarith
            exact pow_le_pow_left₀ (by positivity) h2 2
      _ = N ^ (2 * n) := by simp [Finset.prod_const, pow_mul]
      _ ≤ N ^ M := pow_le_pow_right₀ hN1 h
  have hpos : 0 < ∏ i, (1 + |(m i : ℝ)|) ^ 2 := Finset.prod_pos fun i _ => by positivity
  have hw : ∏ i, wt (m i) = (∏ i, (1 + |(m i : ℝ)|) ^ 2)⁻¹ := by
    simp only [wt, Finset.prod_inv_distrib]
  rw [hw, zpow_neg, zpow_natCast]
  exact inv_anti₀ hpos hle

theorem latSum : PositivityTheory.Rg.BcB.E1.LatSum := by
  intro n M h
  have hS : ∑' k, ENNReal.ofReal (wt k) ≠ ⊤ := summable_wt.tsum_ofReal_ne_top
  have hle : ∑' m : Fin n → ℤ, ENNReal.ofReal ((1 + ‖fun i => (m i : ℝ)‖) ^ (-(M : ℤ))) ≤
      ∑' m : Fin n → ℤ, ∏ i, ENNReal.ofReal (wt (m i)) := by
    refine ENNReal.tsum_le_tsum fun m => ?_
    rw [← ENNReal.ofReal_prod_of_nonneg fun i _ => wt_nonneg (m i)]
    exact ENNReal.ofReal_le_ofReal (pointwise_le n M h m)
  exact ne_top_of_le_ne_top (ENNReal.pow_ne_top hS)
    (hle.trans_eq (tsum_prod_eq_pow (fun k => ENNReal.ofReal (wt k)) n))

end GlobalTheory.CompanionTheory.LatticeSum

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwConjCentMul
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4

namespace GlobalTheory.CompanionTheory.ChiGamGlobal

theorem twConj_cent_mul {G : Type} [Group G] (θ : Monoid.End G) {t δ : G} (x : G) (ht : twConj θ t δ = δ) :
    twConj θ (t * x) δ = twConj θ x δ := by
  have h : t⁻¹ * δ * θ t = δ := ht
  calc twConj θ (t * x) δ = x⁻¹ * (t⁻¹ * δ * θ t) * θ x := by
        simp only [twConj, map_mul, _root_.mul_inv_rev, mul_assoc]
    _ = twConj θ x δ := by rw [h]; rfl

theorem logSize_nonneg {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ} (g : GA E n) :
    0 ≤ logSize g := by
  have h : ∀ A : Matrix (Fin n) (Fin n) (Ad E), 0 ≤ logSizeM A := fun A =>
    add_nonneg (Finset.sum_nonneg fun _ _ => Real.posLog_nonneg)
      (finsum_nonneg fun _ => Real.posLog_nonneg)
  exact add_nonneg (h _) (h _)

theorem chiGam_of (hI : OnlyIsotropic) (hP : PosY) (hC : ChainSum) : ChiGam := by
  classical
  intro E _ _ _ n
  obtain ⟨C₁, h₁⟩ := hI E n
  obtain ⟨C₂, h₂⟩ := hP E n
  refine ⟨max C₁ C₂, fun d m Wof a hiso huniq h0 hmeet hle hreg hdeg τ x hτ t ht => ?_⟩
  have hs : 0 ≤ 1 + logSize (twConj (thetaA E n) x (ratGL E n d)) := by
    have := logSize_nonneg (twConj (thetaA E n) x (ratGL E n d))
    linarith
  have b₁ := (mul_le_mul_of_nonneg_right (le_max_left C₁ C₂) hs).trans hτ
  have b₂ := (mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) hs).trans hτ
  have hconj : twConj (thetaA E n) (t * x) (ratGL E n d) = twConj (thetaA E n) x (ratGL E n d) :=
    twConj_cent_mul _ x ht
  have hind := (hC m).1 _ (a t) (h₂ d m Wof hiso huniq h0 hmeet hle hreg τ x b₂)
  have hiff : t * x ∈ cutSet E n τ ↔
      ∀ e, sdot e (a t) ≤ prof n τ (Module.finrank E (Wof e)) - deg x (Wof e) := by
    rw [h₁ τ (t * x) d (by rw [hconj]; exact b₁)]
    constructor
    · intro h e
      have := h (Wof e) (hiso e).1 (hiso e).2
      rw [hdeg t ht x e] at this
      linarith
    · intro h W hW₁ hW₂
      obtain ⟨e, rfl, _⟩ := huniq W ⟨hW₁, hW₂⟩
      have := h e
      rw [hdeg t ht x e]
      linarith
  rw [hind]
  by_cases hx : t * x ∈ cutSet E n τ
  · have ha : a t ∈ {b : Fin m → ℝ | ∀ e, sdot e b ≤ prof n τ (Module.finrank E (Wof e)) - deg x (Wof e)} :=
      hiff.1 hx
    rw [Set.indicator_of_mem ha, chiT, Set.indicator_of_mem hx]
    simp
  · have ha : a t ∉ {b : Fin m → ℝ | ∀ e, sdot e b ≤ prof n τ (Module.finrank E (Wof e)) - deg x (Wof e)} :=
      fun h => hx (hiff.2 h)
    rw [Set.indicator_of_notMem ha, chiT, Set.indicator_of_notMem hx]
    simp

end GlobalTheory.CompanionTheory.ChiGamGlobal

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedGradedGenerationGlobalSectionsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.Step
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_graded_generation_global_sections : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) {P : X.Modules} (S : ℕ → Subobject P) (hS : ClosedSys I P S) {k : ℕ} (g : Fin k → A), (∀ i, g i ∈ I) → ∀ (hr : ∀ i, MapsDown S (toFunctions (X := X) (A := A) ⊤ (g i))) (n : ℤ) (e : ℕ), Submodule.span Γ(X, ⊤) (⋃ i, Set.range ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (grT (anti hS) (hr i) e)).app ⊤)) = ⊤ → Lifts I H hS n e → Lifts I H hS n (e + 1) := by
  first | exact @GlobalTheory.CompanionTheory.GE.Step.lifts_succ | exact GlobalTheory.CompanionTheory.GE.Step.lifts_succ | (intros; apply GlobalTheory.CompanionTheory.GE.Step.lifts_succ <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedSectionsFiniteGenerators
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.TwLim

theorem twSecs_sub_mem {X : Scheme.{0}} (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) (n : ℤ) {P : X.Modules}
    (S : Subobject P) {x y : Γ(GlobalTheory.twistZ P H n, ⊤)} (hx : x ∈ twSecs H n S)
    (hy : y ∈ twSecs H n S) : x - y ∈ twSecs H n S := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a - b, map_sub _ a b⟩

theorem twSecs_mono {X : Scheme.{0}} (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) (n : ℤ) {P : X.Modules}
    {S T : Subobject P} (h : S ≤ T) : twSecs H n S ⊆ twSecs H n T := by
  rintro _ ⟨a, rfl⟩
  refine ⟨(GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (Subobject.ofLE S T h)).app ⊤ a, ?_⟩
  rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, ← GlobalTheory.Twist.map_comp,
    Subobject.ofLE_arrow]

theorem zero_mem_twPow {A : Type} [CommRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))]
    (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) (n : ℤ) (P : X.Modules) (m : ℕ) : (0 : Γ(GlobalTheory.twistZ P H n, ⊤)) ∈ twPow I H n P m :=
  Submodule.zero_mem _

end GlobalTheory.CompanionTheory.GE.TwLim

namespace GlobalTheory.CompanionTheory.GE.TwLim

theorem twPow_sub_twSecs : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H → ∀ {P : X.Modules}, IsCoherent P → ∀ (n : ℤ) (m : ℕ), twPow I H n P m ⊆ twSecs H n (powSub I P m) := GlobalTheory.T.twisted_ideal_power_le_sections

theorem twPow_complete : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A), IsAdicComplete I A → ∀ {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H → ∀ {P : X.Modules}, IsCoherent P → ∀ (n : ℤ) (f : ℕ → Γ(GlobalTheory.twistZ P H n, ⊤)), (∀ m, f m - f (m + 1) ∈ twPow I H n P m) → ∃ L : Γ(GlobalTheory.twistZ P H n, ⊤), ∀ m, f m - L ∈ twPow I H n P m := GlobalTheory.T.twisted_sections_cauchy_limit

theorem antitone_closedSys {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}}
    [X.Over (Spec (.of A))] {P : X.Modules} {S : ℕ → Subobject P} (hS : ClosedSys I P S) :
    Antitone S :=
  antitone_nat_of_succ_le fun m => (hS.succ m).symm ▸ le_sup_left

theorem exists_compat_limit : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A), IsAdicComplete I A → ∀ {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H → ∀ {P : X.Modules}, IsCoherent P → ∀ S : ℕ → Subobject P, ClosedSys I P S → ∀ n : ℤ, (∀ e, ∀ x ∈ twSecs H n (S e), ∃ y ∈ twSecs H n (S (e + 1)), x - y ∈ twPow I H n P (e + 1)) → ∃ W : Set Γ(GlobalTheory.twistZ P H n, ⊤), (∀ e, W ⊆ twSecs H n (S e)) ∧ ∀ e, ∀ x ∈ twSecs H n (S e), ∃ b ∈ W, x - b ∈ twPow I H n P (e + 1) := by
  intro A _ _ I hI X _ _ H hH P hP S hS n hstep
  refine ⟨⋂ e, twSecs H n (S e), fun e => Set.iInter_subset _ e, ?_⟩
  intro e x hx
  have hpow : ∀ m, twPow I H n P (m + 1) ⊆ twSecs H n (S m) := fun m =>
    (twPow_sub_twSecs I H hH hP n (m + 1)).trans (twSecs_mono H n (hS.pow_le m))
  let seq : ∀ k : ℕ, {y // y ∈ twSecs H n (S (e + k))} := fun k =>
    Nat.rec ⟨x, hx⟩ (fun k y => ⟨(hstep (e + k) y.1 y.2).choose, (hstep (e + k) y.1 y.2).choose_spec.1⟩) k
  have hseq : ∀ k, (seq k).1 - (seq (k + 1)).1 ∈ twPow I H n P (e + k + 1) := fun k =>
    (hstep (e + k) (seq k).1 (seq k).2).choose_spec.2
  have hcg : ∀ a b : ℕ, a = b → (seq a).1 = (seq b).1 := by rintro _ _ rfl; rfl
  have hs0 : (seq 0).1 = x := rfl
  let f : ℕ → Γ(GlobalTheory.twistZ P H n, ⊤) := fun j => (seq (j - (e + 1))).1
  have hf : ∀ j, f j - f (j + 1) ∈ twPow I H n P j := by
    intro j
    by_cases hj : j < e + 1
    · have h1 : f j = f (j + 1) := hcg _ _ (by omega)
      rw [h1, sub_self]
      exact zero_mem_twPow I H n P j
    · obtain ⟨k, rfl⟩ : ∃ k, j = e + 1 + k := ⟨j - (e + 1), by omega⟩
      have h1 : f (e + 1 + k) = (seq k).1 := hcg _ _ (by omega)
      have h2 : f (e + 1 + k + 1) = (seq (k + 1)).1 := hcg _ _ (by omega)
      rw [h1, h2]
      have := hseq k
      rwa [show e + k + 1 = e + 1 + k by omega] at this
  obtain ⟨L, hL⟩ := twPow_complete I hI H hH hP n f hf
  have hk : ∀ k, L ∈ twSecs H n (S (e + k)) := by
    intro k
    have h1 : f (e + k + 1) = (seq k).1 := hcg _ _ (by omega)
    have hd : (seq k).1 - L ∈ twSecs H n (S (e + k)) := h1 ▸ hpow (e + k) (hL (e + k + 1))
    have := twSecs_sub_mem H n _ (seq k).2 hd
    rwa [sub_sub_cancel] at this
  refine ⟨L, Set.mem_iInter.2 fun m => ?_, ?_⟩
  · rcases le_or_gt e m with hm | hm
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
      exact hk k
    · exact twSecs_mono H n (antitone_closedSys I hS hm.le) (by simpa using hk 0)
  · have h1 : f (e + 1) = x := (hcg (e + 1 - (e + 1)) 0 (by omega)).trans hs0
    simpa [h1] using hL (e + 1)

end GlobalTheory.CompanionTheory.GE.TwLim
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedVanishingSectionsSpanStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_vanishing_sections_span : ∀ {X : Scheme.{0}} (L : ReciprocityTheory.ChartRestriction.G.Semi.LB X), L.IsLB → ∀ {k : ℕ} {P : Fin k → X.Modules} {Q K : X.Modules} (f : ∀ i, P i ⟶ Q) (ι : K ⟶ ⨁ P) (w : ι ≫ biproduct.desc f = 0), (ShortComplex.mk ι (biproduct.desc f) w).ShortExact → Subsingleton (GlobalTheory.coh (GlobalTheory.twist K L) 1) → Submodule.span Γ(X, ⊤) (⋃ i, Set.range ((GlobalTheory.Twist.map L (f i)).app ⊤)) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.GE.span_range_twist_eq_top | exact GlobalTheory.CompanionTheory.GE.span_range_twist_eq_top | (intros; apply GlobalTheory.CompanionTheory.GE.span_range_twist_eq_top <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwoBasesComparisonStatement
section
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_bases_comparison : TwoBases := by
  first | exact @GlobalTheory.CompanionTheory.LinAlg.twoBases | exact GlobalTheory.CompanionTheory.LinAlg.twoBases | (intros; apply GlobalTheory.CompanionTheory.LinAlg.twoBases <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformFirstCohomologyKernelsExist
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

open TowerAx

section

variable {ι : Type} [LinearOrder ι] {R : Type} [CommRing R] {g : ℕ} {ρ : Fin g → R}
  {T : ℕ → ℤ → Finset ι → Type} [∀ e t S, AddCommGroup (T e t S)] [∀ e t S, Module R (T e t S)]
  {res : ∀ e t (S S' : Finset ι), S ⊆ S' → T e t S →ₗ[R] T e t S'}
  {p : ∀ e t S, T (e + 1) t S →ₗ[R] T e t S}
  {mm : ι → ∀ e t S, T e t S →ₗ[R] T e (t + 1) S}
  (H : TowerAx ρ res p mm)
  (hc : ∀ e S, OperatorsCommute (ι := ι) (R := R) (A := fun t => T e t S) fun j t => mm j e t S)

theorem resTot_self
    (h1 : ∀ e t S (h : S ⊆ S) a, res e t S S h a = a) (S : Finset ι) (h : S ⊆ S) (a : H.Tot hc S) :
    H.resTot hc S S h a = a := by
  induction a using (H.ops hc S).induction with
  | h0 => exact map_zero _
  | hof e t a =>
    rw [resTot_of]
    exact congrArg _ (Subtype.ext (h1 _ _ _ _ _))
  | hadd a b ha hb => rw [map_add, ha, hb]

theorem resTot_resTot
    (h2 : ∀ e t S S' S'' (h : S ⊆ S') (h' : S' ⊆ S'') a,
      res e t S' S'' h' (res e t S S' h a) = res e t S S'' (h.trans h') a)
    (S S' S'' : Finset ι) (h : S ⊆ S') (h' : S' ⊆ S'') (a : H.Tot hc S) :
    H.resTot hc S' S'' h' (H.resTot hc S S' h a) = H.resTot hc S S'' (h.trans h') a := by
  induction a using (H.ops hc S).induction with
  | h0 => simp only [map_zero]
  | hof e t a =>
    rw [resTot_of, resTot_of, resTot_of]
    exact congrArg _ (Subtype.ext (h2 _ _ _ _ _ _ _ _))
  | hadd a b ha hb => simp only [map_add, ha, hb]

theorem X_smul_bijective_tot
    (h9 : ∀ i e t S, i ∈ S → Function.Bijective (mm i e t S)) (i : ι) (S : Finset ι) (hi : i ∈ S) :
    Function.Bijective fun m : H.Tot hc S =>
      (MvPolynomial.X i : MvPolynomial ι (MvPolynomial (Fin g) R)) • m := by
  have hS : S.Nonempty := ⟨i, hi⟩
  refine (H.ops hc S).X_smul_bijective i fun e t => ⟨fun a b h => ?_, fun b => ?_⟩
  · exact Subtype.ext ((h9 i (e + 1) t S hi).1 (congrArg Subtype.val h))
  · obtain ⟨a, ha⟩ := (h9 i (e + 1) t S hi).2 (b : T (e + 1) (t + 1) S)
    refine ⟨⟨a, (mem_Ks hS).2 ((h9 i e t S hi).1 ?_)⟩, Subtype.ext ha⟩
    rw [← H.p_mm i e t S a hS, ha, (mem_Ks hS).1 b.2, map_zero]

end

theorem exists_uniform_h1_kernels : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] [IsNoetherianRing R] (g : ℕ) (ρ : Fin g → R) (T : ℕ → ℤ → Finset ι → Type) [∀ e t S, AddCommGroup (T e t S)] [∀ e t S, Module R (T e t S)] (res : ∀ e t (S S' : Finset ι), S ⊆ S' → T e t S →ₗ[R] T e t S') (p : ∀ e t S, T (e + 1) t S →ₗ[R] T e t S) (mm : ι → ∀ e t S, T e t S →ₗ[R] T e (t + 1) S) (one : ∀ e (i : ι), T e 0 {i}) (hc : ∀ e S, OperatorsCommute (ι := ι) (R := R) (A := fun t => T e t S) fun j t => mm j e t S), (∀ e t S (h : S ⊆ S) a, res e t S S h a = a) → (∀ e t S S' S'' (h : S ⊆ S') (h' : S' ⊆ S'') a, res e t S' S'' h' (res e t S S' h a) = res e t S S'' (h.trans h') a) → (∀ e t S S' (h : S ⊆ S') a, S.Nonempty → p e t S' (res (e + 1) t S S' h a) = res e t S S' h (p e t S a)) → (∀ j e t S a, S.Nonempty → p e (t + 1) S (mm j (e + 1) t S a) = mm j e t S (p e t S a)) → (∀ j e t S S' (h : S ⊆ S') a, S.Nonempty → res e (t + 1) S S' h (mm j e t S a) - mm j e t S' (res e t S S' h a) ∈ Ideal.span (Set.range ρ) • (⊤ : Submodule R (T e (t + 1) S'))) → (∀ e t S, S.Nonempty → Function.Surjective (p e t S)) → (∀ e t S, S.Nonempty → LinearMap.ker (p e t S) = Ideal.span (Set.range ρ) ^ (e + 1) • ⊤) → (∀ e t S, S.Nonempty → Ideal.span (Set.range ρ) ^ (e + 1) • (⊤ : Submodule R (T e t S)) = ⊥) → (∀ i e t S, i ∈ S → Function.Bijective (mm i e t S)) → (∀ e S j t (a : T e t S), S.Nonempty → res e t S (insert j S) (Finset.subset_insert j S) a = 0 → ∃ k : ℕ, (MvPolynomial.X j : MvPolynomial ι R) ^ k • GrSum.of (hc e S) t a = 0) → (∀ e S j t (b : T e t (insert j S)), S.Nonempty → ∃ (k : ℕ) (t' : ℤ) (a : T e t' S), GrSum.of (hc e (insert j S)) t' (res e t' S (insert j S) (Finset.subset_insert j S) a) = (MvPolynomial.X j : MvPolynomial ι R) ^ k • GrSum.of (hc e (insert j S)) t b) → (∀ e i, p e 0 {i} (one (e + 1) i) = one e i) → (∀ e i t (a : T e t {i}), ∃ (k : ℕ) (q : MvPolynomial ι R) (t' : ℤ) (w : T e t' {i}), w ∈ Ideal.span (Set.range ρ) • (⊤ : Submodule R (T e t' {i})) ∧ (MvPolynomial.X i : MvPolynomial ι R) ^ k • GrSum.of (hc e {i}) t a = q • GrSum.of (hc e {i}) 0 (one e i) + GrSum.of (hc e {i}) t' w) → ∃ t₀ : ℤ, ∀ t, t₀ ≤ t → ∀ e (c : ∀ i j : ι, T (e + 1) t {i, j}), (∀ i j, p e t {i, j} (c i j) = 0) → (∀ i j k, res (e + 1) t {i, j} {i, j, k} (sub_triple_ij i j k) (c i j) + res (e + 1) t {j, k} {i, j, k} (sub_triple_jk i j k) (c j k) = res (e + 1) t {i, k} {i, j, k} (sub_triple_ik i j k) (c i k)) → ∃ b : ∀ i, T (e + 1) t {i}, (∀ i, p e t {i} (b i) = 0) ∧ ∀ i j, c i j = res (e + 1) t {i} {i, j} (sub_pair_left i j) (b i) - res (e + 1) t {j} {i, j} (sub_pair_right i j) (b j) := by
  intro ι _ _ R _ _ g ρ T _ _ res p mm one hc h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  have H : TowerAx ρ res p mm := ⟨h3, h4, h5, h6, h7, h8⟩
  obtain ⟨t₀, ht⟩ := GlobalTheory.T.graded_module_system_restriction ι (MvPolynomial (Fin g) R) (H.Tot hc)
    (fun S => (H.ops hc S).grading) (H.resTot hc) (fun S S' h => H.isGradedMap_resTot hc h)
    (resTot_self H hc h1) (resTot_resTot H hc h2)
    (fun i S hi => X_smul_bijective_tot H hc h9 i S hi)
    (GlobalTheory.T.commuting_operators_uniform_kernel ι R g ρ T res p mm hc H h10) (GlobalTheory.T.commuting_operators_uniform_cokernel ι R g ρ T res p mm hc H h11)
    (GlobalTheory.T.commuting_operators_kernel_lift ι R g ρ T res p mm hc H one h12 h13)
  refine ⟨t₀, fun t htt e c hp hcoc => ?_⟩
  have hne (i j : ι) : ({i, j} : Finset ι).Nonempty := ⟨i, Finset.mem_insert_self _ _⟩
  let c' : ∀ i j : ι, H.Tot hc {i, j} := fun i j =>
    (H.ops hc {i, j}).of e t ⟨c i j, (mem_Ks (hne i j)).2 (hp i j)⟩
  obtain ⟨b', -, hcob⟩ := ht t htt c' (fun i j => (H.ops hc {i, j}).of_mem_grading e t _) (by
    intro i j k
    simp only [c', resTot_of, ← map_add]
    exact congrArg _ (Subtype.ext (hcoc i j k)))
  refine ⟨fun i => ((H.ops hc {i}).comp e t (b' i) : T (e + 1) t {i}), fun i =>
    (mem_Ks (Finset.singleton_nonempty i)).1 ((H.ops hc {i}).comp e t (b' i)).2, fun i j => ?_⟩
  have h := congrArg (fun m => (((H.ops hc {i, j}).comp e t m : Ks p e t {i, j}) : T (e + 1) t {i, j}))
    (hcob i j)
  simpa [c', comp_resTot] using h

end GlobalTheory.CompanionTheory.FormalAlg.Lift
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformLimitRightDerivatives
section
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

namespace GlobalTheory.CompanionTheory.PresSobA.LimSmooth

theorem tendstoLocallyUniformlyOn_frame {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {ι : Type} [Fintype ι] {A : ι → Mat n → CLof (Mat n) ℝ} (hA : ∀ p, ContinuousOn (A p) (GLs n))
    {u : ι → ℕ → Mat n → V} {U : ι → Mat n → V}
    (hu : ∀ p, TendstoUniformlyOn (u p) (U p) atTop (GLs n)) :
    TendstoLocallyUniformlyOn
      (fun (k : ℕ) (z : Mat n) => (∑ p, (A p z).smulRight (u p k z) : CLof (Mat n) V))
      (fun z => (∑ p, (A p z).smulRight (U p z) : CLof (Mat n) V)) atTop (GLs n) := by
  rw [Metric.tendstoLocallyUniformlyOn_iff]
  intro ε hε x hx
  set M : ℝ := ∑ p, (‖A p x‖ + 1) with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun p _ => by positivity
  have hnear : ∀ᶠ y in 𝓝[GLs n] x, ∀ p, ‖A p y‖ < ‖A p x‖ + 1 := by
    rw [Filter.eventually_all]
    intro p
    exact Filter.Tendsto.eventually_lt_const (lt_add_one _) (hA p x hx).norm
  have hpos : 0 < ε / (M + 1) := by positivity
  refine ⟨{y | ∀ p, ‖A p y‖ < ‖A p x‖ + 1} ∩ GLs n,
    Filter.inter_mem hnear self_mem_nhdsWithin, ?_⟩
  have hev : ∀ᶠ k in atTop, ∀ p, ∀ y ∈ GLs n, dist (U p y) (u p k y) < ε / (M + 1) := by
    rw [Filter.eventually_all]
    intro p
    exact Metric.tendstoUniformlyOn_iff.1 (hu p) _ hpos
  filter_upwards [hev] with k hk y hy
  rw [dist_eq_norm, ← Finset.sum_sub_distrib]
  have hterm : ∀ p, ‖(A p y).smulRight (U p y) - (A p y).smulRight (u p k y)‖
      ≤ (‖A p x‖ + 1) * (ε / (M + 1)) := by
    intro p
    have he : (A p y).smulRight (U p y) - (A p y).smulRight (u p k y)
        = (A p y).smulRight (U p y - u p k y) := by
      ext v
      simp [smul_sub]
    rw [he, ContinuousLinearMap.norm_smulRight_apply]
    have h1 := hk p y hy.2
    rw [dist_eq_norm] at h1
    exact mul_le_mul (hy.1 p).le h1.le (norm_nonneg _) (by positivity)
  calc _ ≤ ∑ p, ‖(A p y).smulRight (U p y) - (A p y).smulRight (u p k y)‖ := norm_sum_le _ _
    _ ≤ ∑ p, (‖A p x‖ + 1) * (ε / (M + 1)) := Finset.sum_le_sum fun p _ => hterm p
    _ = M * (ε / (M + 1)) := by rw [Finset.sum_mul]
    _ < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith

theorem sum_smulRight_apply {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {ι : Type} [Fintype ι] (B : ι → CLof (Mat n) ℝ) (c : ι → V) (v : Mat n) :
    (∑ q, (B q).smulRight (c q) : CLof (Mat n) V) v = ∑ q, B q v • c q := by
  simp

theorem limit_smooth : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (g : ℕ → Mat n → V), (∀ k, ContDiffOn ℝ ∞ (g k) (GLs n)) →
    (∀ w, UniformCauchySeqOn (fun k => Rw w (g k)) atTop (GLs n)) →
    ∃ Gf : List (Bool × Fin n × Fin n) → Mat n → V,
      (∀ w, TendstoUniformlyOn (fun k => Rw w (g k)) (Gf w) atTop (GLs n)) ∧
      ContDiffOn ℝ ∞ (Gf []) (GLs n) ∧ ∀ w, ∀ z ∈ GLs n, Rw w (Gf []) z = Gf w z := by
  intro n V _ _ _ g hg hc
  obtain ⟨A, hAc, hA⟩ := GlobalTheory.T.derivative_right_basis_expansion n
  have hopen : IsOpen (GLs n) := isOpen_GLs
  let Gf : List (Bool × Fin n × Fin n) → Mat n → V :=
    fun w z => limUnder atTop (fun k => Rw w (g k) z)
  have hpt : ∀ w, ∀ z ∈ GLs n, Tendsto (fun k => Rw w (g k) z) atTop (𝓝 (Gf w z)) := by
    intro w z hz
    have hcs : CauchySeq (fun k => Rw w (g k) z) := (hc w).cauchy_map hz
    obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcs
    have he : Gf w z = x := hx.limUnder_eq
    rwa [he]
  have hu : ∀ w, TendstoUniformlyOn (fun k => Rw w (g k)) (Gf w) atTop (GLs n) := fun w =>
    (hc w).tendstoUniformlyOn_of_tendsto (hpt w)
  have hsm : ∀ k w, ContDiffOn ℝ ∞ (Rw w (g k)) (GLs n) := fun k w =>
    GlobalTheory.CompanionTheory.SobGL.Smooth.Rw_contDiffOn' (hg k) w
  have hderiv : ∀ k w, ∀ z ∈ GLs n, fderiv ℝ (Rw w (g k)) z
      = (∑ p, (A p z).smulRight (Rw (p :: w) (g k) z) : CLof (Mat n) V) := by
    intro k w z hz
    exact hA V (fderiv ℝ (Rw w (g k)) z) z hz
  have hhas : ∀ w, ∀ z ∈ GLs n, HasFDerivAt (Gf w)
      (∑ p, (A p z).smulRight (Gf (p :: w) z) : CLof (Mat n) V) z := by
    intro w z hz
    refine hasFDerivAt_of_tendstoLocallyUniformlyOn (f := fun k => Rw w (g k))
      (f' := fun (k : ℕ) (y : Mat n) =>
        (∑ p, (A p y).smulRight (Rw (p :: w) (g k) y) : CLof (Mat n) V))
      (g' := fun y => (∑ p, (A p y).smulRight (Gf (p :: w) y) : CLof (Mat n) V))
      hopen (tendstoLocallyUniformlyOn_frame (u := fun p k => Rw (p :: w) (g k))
        (U := fun p => Gf (p :: w)) (fun p => hAc p |>.continuousOn) (fun p => hu (p :: w)))
      ?_ (hpt w) hz
    intro k y hy
    have hd : DifferentiableAt ℝ (Rw w (g k)) y :=
      ((hsm k w).contDiffAt (hopen.mem_nhds hy)).differentiableAt (by simp)
    have h2 := hd.hasFDerivAt
    rwa [hderiv k w y hy] at h2
  have hRd : ∀ w p, ∀ z ∈ GLs n, Rd (bs p) (Gf w) z = Gf (p :: w) z := by
    intro w p z hz
    have h1 : Rd (bs p) (Gf w) z
        = (∑ q, (A q z).smulRight (Gf (q :: w) z) : CLof (Mat n) V) (z * bs p) := by
      have h0 := (hhas w z hz).fderiv
      exact congrArg (fun L : CLof (Mat n) V => L (z * bs p)) h0
    have h2 : Tendsto (fun k => Rw (p :: w) (g k) z) atTop
        (𝓝 ((∑ q, (A q z).smulRight (Gf (q :: w) z) : CLof (Mat n) V) (z * bs p))) := by
      have h3 : ∀ k, Rw (p :: w) (g k) z
          = ∑ q, (A q z (z * bs p)) • Rw (q :: w) (g k) z := by
        intro k
        have h4 : Rw (p :: w) (g k) z
            = (∑ q, (A q z).smulRight (Rw (q :: w) (g k) z) : CLof (Mat n) V) (z * bs p) :=
          congrArg (fun L : CLof (Mat n) V => L (z * bs p)) (hderiv k w z hz)
        rw [h4, sum_smulRight_apply]
      rw [sum_smulRight_apply]
      simp only [h3]
      exact tendsto_finsetSum _ fun q _ => (hpt (q :: w) z hz).const_smul _
    rw [h1]
    exact tendsto_nhds_unique h2 (hpt (p :: w) z hz)
  have hfam : ∀ v, ContDiffOn ℝ ∞ (Gf v) (GLs n) :=
    GlobalTheory.T.closed_derivative_system_smooth n V (List (Bool × Fin n × Fin n)) Gf (fun p w => p :: w)
      (fun v z hz => (hhas v z hz).differentiableAt) (fun v p z hz => hRd v p z hz)
  refine ⟨Gf, hu, hfam [], ?_⟩
  intro w
  induction w with
  | nil => intro z _; rfl
  | cons p w ih =>
    intro z hz
    exact (Rd_congr ih (bs p) z hz).trans (hRd w p z hz)

end GlobalTheory.CompanionTheory.PresSobA.LimSmooth
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformSpanEventuallyStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniform_span_eventually : ∀ {X : Scheme.{0}} [CompactSpace X] {k : ℕ} {K : ℕ → X.Modules} (T : Fin k → ∀ e, K e ⟶ K (e + 1)), (∀ e, (K e).IsQuasicoherent) → (∀ U : X.affineOpens, ∃ dU : ℕ, ∀ e, dU ≤ e → Submodule.span Γ(X, U) (⋃ i, Set.range ((T i e).app U)) = ⊤) → ∃ d' : ℕ, ∀ e, d' ≤ e → ∀ U : X.affineOpens, Submodule.span Γ(X, U) (⋃ i, Set.range ((T i e).app U)) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.GE.Uniform.span_range_eq_top_uniform | exact GlobalTheory.CompanionTheory.GE.Uniform.span_range_eq_top_uniform | (intros; apply GlobalTheory.CompanionTheory.GE.Uniform.span_range_eq_top_uniform <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittAcrisFlatStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_acris_flat : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K), Module.Flat (WittVector l r.k) (CrystallineSemistableComparison.Pb.AW r) := by
  first | exact @GlobalTheory.CompanionTheory.FlatW.flat_AW | exact GlobalTheory.CompanionTheory.FlatW.flat_AW | (intros; apply GlobalTheory.CompanionTheory.FlatW.flat_AW <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittComparisonFrobeniusCompatStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_comparison_frobenius_compat : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) (M : Model l K) (n j : ℕ) (y : (HSW r M j).M n), phiM r M n j (bW r M n j y) = bW r M n j ((Wc.phiS l (B.schFn M.p) r.ρ j).f n y) := by
  first | exact @GlobalTheory.CompanionTheory.BaseChangeFrob.phiM_bW | exact GlobalTheory.CompanionTheory.BaseChangeFrob.phiM_bW | (intros; apply GlobalTheory.CompanionTheory.BaseChangeFrob.phiM_bW <;> assumption)
end

