import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0581
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0013
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
import Formalism.LocalRingCardinality.Bundle0004
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0014
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0036
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0184
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0182
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0183
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0257
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCorePb
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0586
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0580
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0028
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0003
import Formalism.SharpRestriction.GrowthBounds.TwistedLevelAgreement.StepInTwK
import Formalism.SharpRestriction.GrowthBounds.BaseLevels.LevelsGEmpty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelsTwG
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0572
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0568
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GradedLineBundleExists
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGeneratorMultiplierPower
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.LN GlobalTheory.TorRef GlobalTheory.IntegralCombination GlobalTheory.UU Formalism.L2.Pj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IntFam

noncomputable section

namespace GlobalTheory.IntFam

theorem intGen : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsIntegrallyClosed R → ∀ (D : DegPre R) (k : ℕ), 1 ≤ k →
    ∀ (α mu : D.X) (s : R),
    (∀ (ξ : Spec (CommRingCat.of (FractionRing R))) (J), Good D.P.L ξ J → GlobalTheory.IntFam.IntegralCharts D J →
      ∃ u : Rˣ, (val (GlobalTheory.UU.IntGen.multK D k mu α) (𝟙 _) ξ J).val ^ k = GlobalTheory.PeriodBalance.cst ξ (u * s)) →
    ∃ (u₀ : LB.Gen (LB.LinComb D.P.L (deltaφT D (α + k • mu) α (toUnit (𝟙_ _) ≫ D.c mu)) (DegPre.deltaε k))) (a : R),
      u₀.IsGen ∧ ∀ (u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D (FractionRing R) k α mu) (DegPre.deltaε k))), u.IsGen →
        LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D (FractionRing R)).left)
          (DegPre.famMult D (FractionRing R) k mu α) →
        ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D (FractionRing R)).left) (z : Z) (J), Good D.P.L z J →
          (val u r z J).val = gs r z ⊤ (scal (DegPre.BF D (FractionRing R)).hom a) *
            (val u₀ (r ≫ (toUnit (TF (R := R) (FractionRing R)) ▷ D.P.A).left) z J).val := by
  intro R _ _ _ hR D k hk α mu s hs
  obtain ⟨v, hv⟩ := exists_gen_of_local (V := R) D.P.L D.P.isLB (IntGen.basePts D (𝟙_ _) α mu) (IntGen.baseExp k)
  obtain ⟨u₀, hu₀, vu₀⟩ := IntGen.exists_genT D (𝟙_ _) (𝟙_ _) (toUnit _) k α mu v hv
  obtain ⟨r₁, r₂, h₁, h₂, hr⟩ := IntGen.multK_frac D k α mu v hv
  obtain ⟨a, ha⟩ : ∃ a : R, r₁ = r₂ * a := by
    have : IsProper D.P.A.hom := D.P.isAb.proper
    obtain ⟨ξ⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R))) := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
    obtain ⟨J, hJ, hJc⟩ := GlobalTheory.PeriodBalance.exists_good_integral ξ D.P.isLB D.P.A.hom
    obtain ⟨u, hu⟩ := hs ξ J hJ hJc
    have e := hr _ (𝟙 _) ξ J hJ
    have hσ : 𝟙 (TK R).left ≫ (toUnit (TK R)).left = jK R := by
      rw [Category.id_comp]; exact Over.w (toUnit (TK R))
    obtain ⟨w, hw⟩ : ∃ w : Rˣ, (val v (𝟙 _ ≫ (toUnit (TK R)).left) ξ J).val = GlobalTheory.PeriodBalance.cst ξ w := by
      rw [hσ]
      refine GlobalTheory.PeriodBalance.unit_gm ξ _ (Set.mem_iInter.2 fun i => ?_) _
      obtain ⟨q, hq⟩ : ∃ q : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A, IntGen.basePts D (𝟙_ _) α mu i = q.left := by
        fin_cases i <;> exact ⟨_, rfl⟩
      have := hJc (IntGen.basePts D (𝟙_ _) α mu i) (by rw [hq]; exact Over.w q)
      exact this
    have g : ∀ c : R, gs (𝟙 (TK R).left ≫ jK R) ξ ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) =
        GlobalTheory.PeriodBalance.cst ξ c := fun c => by
      rw [Category.id_comp, gs_eq (jK R) ξ ⊤ trivial, GlobalTheory.PeriodBalance.cst_eq]; rfl
    rw [g, g, hw] at e
    have e2 : GlobalTheory.PeriodBalance.cst ξ (r₂ ^ k * ((u : R) * s)) = GlobalTheory.PeriodBalance.cst ξ ((r₁ * w) ^ k) := by
      rw [map_mul, map_pow, ← hu, ← mul_pow, e, map_pow, map_mul]
    have e3 := GlobalTheory.PeriodBalance.cst_injective ξ e2
    have e5 : r₁ ^ k = r₂ ^ k * ((u : R) * s * ((w⁻¹ : Rˣ) : R) ^ k) := by
      have hwk : ((w : R) * ((w⁻¹ : Rˣ) : R)) ^ k = 1 := by rw [Units.mul_inv, one_pow]
      linear_combination (-(((w⁻¹ : Rˣ) : R)) ^ k) * e3 - r₁ ^ k * hwk
    have := hR
    have inj := IsFractionRing.injective R (FractionRing R)
    have hr₂ : algebraMap R (FractionRing R) r₂ ≠ 0 := (map_ne_zero_iff _ inj).2 h₂
    have hr₂k : algebraMap R (FractionRing R) (r₂ ^ k) ≠ 0 := (map_ne_zero_iff _ inj).2 (pow_ne_zero _ h₂)
    have hx : (algebraMap R (FractionRing R) r₁ / algebraMap R (FractionRing R) r₂) ^ k =
        algebraMap R (FractionRing R) ((u : R) * s * ((w⁻¹ : Rˣ) : R) ^ k) := by
      rw [div_pow, ← map_pow, ← map_pow, e5, map_mul, mul_div_cancel_left₀ _ hr₂k]
    have hint : IsIntegral R (algebraMap R (FractionRing R) r₁ / algebraMap R (FractionRing R) r₂) :=
      IsIntegral.of_pow (by omega) (hx ▸ isIntegral_algebraMap)
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    refine ⟨y, inj ?_⟩
    rw [map_mul, hy, mul_div_cancel₀ _ hr₂]
  refine ⟨u₀, a, hu₀, fun u hu hc Z r z J hJ => ?_⟩
  have key : gs r z ⊤ (scal (DegPre.BF D (FractionRing R)).hom r₂) * (val u r z J).val =
      gs r z ⊤ (scal (DegPre.BF D (FractionRing R)).hom r₁) *
        (val u₀ (r ≫ (toUnit (TF (R := R) (FractionRing R)) ▷ D.P.A).left) z J).val := by
    let T' : Over (Spec (CommRingCat.of R)) := Over.mk (r ≫ (DegPre.BF D (FractionRing R)).hom)
    let ρ : T' ⟶ DegPre.BF D (FractionRing R) := Over.homMk r rfl
    let κ : T' ⟶ TK R := Over.homMk ((ρ ≫ fst _ _).left ≫ jFK (R := R) (FractionRing R))
      ((Category.assoc _ _ _).trans (Over.w (ρ ≫ fst _ _)))
    have e₁ := (gen_fe (D := D) (F := FractionRing R) GlobalTheory.globalFns_holds k mu α).2 u hu hc T' ρ z J hJ
    have e₂ := vu₀ T' (ρ ≫ toUnit (TF (R := R) (FractionRing R)) ▷ D.P.A) z J hJ
    have e₃ : val (DegPre.famMult D (FractionRing R) k mu α) (ρ ≫ fst _ _).left z J =
        val (IntGen.multK D k mu α) κ.left z J :=
      val_pull hJ _ _ _
    have e₄ := hr _ κ.left z J hJ
    have e₅ : κ.left ≫ jK R = r ≫ (DegPre.BF D (FractionRing R)).hom := Over.w κ
    have e₆ : κ.left ≫ (toUnit (TK R)).left =
        ((ρ ≫ toUnit (TF (R := R) (FractionRing R)) ▷ D.P.A) ≫ toUnit _).left :=
      congrArg (fun q => q.left) (toUnit_unique (κ ≫ toUnit (TK R)) _)
    have e₇ : (ρ ≫ toUnit (TF (R := R) (FractionRing R)) ▷ D.P.A) ≫ snd _ _ = ρ ≫ DegPre.prB D (FractionRing R) := by
      rw [Category.assoc, whiskerRight_snd]
    have g : ∀ c : R, gs r z ⊤ (scal (DegPre.BF D (FractionRing R)).hom c) =
        gs (r ≫ (DegPre.BF D (FractionRing R)).hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) := fun c =>
      gs_pull r (DegPre.BF D (FractionRing R)).hom z ⊤ trivial _
    rw [e₅, e₆] at e₄
    rw [e₃, uVal, ← Category.assoc, comp_cP] at e₁
    rw [e₇] at e₂
    rw [g, g]
    exact IntGen.frac_mul e₁ e₂ e₄
  have sm : scal (DegPre.BF D (FractionRing R)).hom (r₂ * a) =
      scal (DegPre.BF D (FractionRing R)).hom r₂ * scal (DegPre.BF D (FractionRing R)).hom a := by
    simp only [Out.scal, map_mul]
  rw [ha, sm, gs_mul r z ⊤ trivial, mul_assoc] at key
  exact (GlobalTheory.FieldChange.isUnit_scal D h₂ r z).mul_left_cancel key

end GlobalTheory.IntFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicDescentPunctPolydiscLogCover
section
open GlobalTheory.ShFam.Hor

set_option autoImplicit false

namespace GlobalTheory.LogDescent

open Complex Topology

theorem continuous_logExp (n a : ℕ) : Continuous (logExp a : (Fin n → ℂ) → Fin n → ℂ) := by
  refine continuous_pi fun k => ?_
  simp only [logExp]
  split_ifs
  · exact Complex.continuous_exp.comp (continuous_apply k)
  · exact continuous_apply k

theorem mem_logDom_of_mem_ball {n a : ℕ} {ρ : ℝ} (hρ1 : ρ ≤ 1) (s : Fin n → ℂ)
    (hs : logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ) : s ∈ logDom n a := by
  intro k
  have hz := mem_ball_zero_iff.1 hs
  have hk' := (norm_le_pi_norm (logExp a s) k).trans_lt hz
  split_ifs with hk
  · simp only [logExp, hk, if_true, Complex.norm_exp] at hk'
    exact Real.exp_lt_one_iff.mp (lt_of_lt_of_le hk' hρ1)
  · simp only [logExp, hk, if_false] at hk'
    exact lt_of_lt_of_le hk' hρ1

theorem logExp_shift {n a : ℕ} (s : Fin n → ℂ) (k : Fin n) (hk : (k : ℕ) < a) (m : ℤ) :
    logExp a (s + Pi.single k ((m : ℂ) * (2 * Real.pi * Complex.I))) = logExp a s := by
  funext j
  by_cases hj : j = k
  · subst hj
    simp only [logExp, hk, if_true, Pi.add_apply, Pi.single_eq_same]
    rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  · simp [logExp, Pi.single_eq_of_ne hj]

variable {n a : ℕ} {ρ : ℝ} {h : (Fin n → ℂ) → ℂ}

theorem inv_int (hρ1 : ρ ≤ 1)
    (hinv : ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ → ∀ k : Fin n, (k : ℕ) < a →
      h (s + Pi.single k (2 * Real.pi * Complex.I)) = h s)
    (s : Fin n → ℂ) (hs : logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ) (k : Fin n) (hk : (k : ℕ) < a) (m : ℤ) :
    h (s + Pi.single k ((m : ℂ) * (2 * Real.pi * Complex.I))) = h s := by
  induction m using Int.induction_on with
  | zero => simp
  | succ m ih =>
    have ht : logExp a (s + Pi.single k (((m : ℤ) : ℂ) * (2 * Real.pi * Complex.I))) ∈ Metric.ball (0 : Fin n → ℂ) ρ := by
      rw [logExp_shift s k hk]; exact hs
    have := hinv _ (mem_logDom_of_mem_ball hρ1 _ ht) ht k hk
    have e : s + Pi.single k ((((m : ℤ) + 1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I)) =
        s + Pi.single k (((m : ℤ) : ℂ) * (2 * Real.pi * Complex.I)) + Pi.single k (2 * Real.pi * Complex.I) := by
      rw [add_assoc, ← Pi.single_add]; congr 2; push_cast; ring
    rw [e, this, ih]
  | pred m ih =>
    set t := s + Pi.single k ((((-(m : ℤ) - 1 : ℤ)) : ℂ) * (2 * Real.pi * Complex.I)) with htdef
    have ht : logExp a t ∈ Metric.ball (0 : Fin n → ℂ) ρ := by
      rw [htdef, logExp_shift s k hk]; exact hs
    have := hinv _ (mem_logDom_of_mem_ball hρ1 _ ht) ht k hk
    have e : t + Pi.single k (2 * Real.pi * Complex.I) =
        s + Pi.single k ((((-(m : ℤ)) : ℤ) : ℂ) * (2 * Real.pi * Complex.I)) := by
      rw [htdef, add_assoc, ← Pi.single_add]; congr 2; push_cast; ring
    rw [← this, e, ih]

theorem key (hρ1 : ρ ≤ 1)
    (hinv : ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ → ∀ k : Fin n, (k : ℕ) < a →
      h (s + Pi.single k (2 * Real.pi * Complex.I)) = h s)
    (s s' : Fin n → ℂ) (hs : logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ) (he : logExp a s = logExp a s') :
    h s = h s' := by
  suffices H : ∀ S : Finset (Fin n), ∀ s s' : Fin n → ℂ, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ →
      logExp a s = logExp a s' → (∀ k ∉ S, s k = s' k) → h s = h s' from
    H Finset.univ s s' hs he (fun k hk => absurd (Finset.mem_univ k) hk)
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro s s' _ _ hk
    congr 1; funext k; exact hk k (Finset.notMem_empty k)
  | insert j S hjS ih =>
    intro s s' hs he hk
    have hej := congrFun he j
    set s'' := Function.update s' j (s j) with hs''
    have he'' : logExp a s = logExp a s'' := by
      funext k
      by_cases hkj : k = j
      · subst hkj; simp [hs'', logExp]
      · have := congrFun he k
        simpa [hs'', logExp, Function.update_of_ne hkj] using this
    have h1 : h s = h s'' := ih s s'' hs he'' (fun k hk' => by
      by_cases hkj : k = j
      · subst hkj; simp [hs'']
      · rw [hs'', Function.update_of_ne hkj]
        exact hk k (by simp [hkj, hk']))
    rw [h1]
    have hs2 : logExp a s'' ∈ Metric.ball (0 : Fin n → ℂ) ρ := he'' ▸ hs
    by_cases hja : (j : ℕ) < a
    · simp only [logExp, hja, if_true] at hej
      obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.1 hej.symm
      have e : s' = s'' + Pi.single j ((m : ℂ) * (2 * Real.pi * Complex.I)) := by
        funext k
        by_cases hkj : k = j
        · subst hkj; simp [hs'', hm]
        · simp [hs'', Function.update_of_ne hkj, Pi.single_eq_of_ne hkj]
      rw [e, inv_int hρ1 hinv s'' hs2 j hja m]
    · simp only [logExp, hja, if_false] at hej
      congr 1
      rw [hs'', hej, Function.update_eq_self]

theorem dom_mem_nhds {ρ : ℝ} (hρ1 : ρ ≤ 1) (s₀ : Fin n → ℂ)
    (hs₀ : logExp a s₀ ∈ Metric.ball (0 : Fin n → ℂ) ρ) :
    {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ} ∈ 𝓝 s₀ := by
  have ho : IsOpen (logExp a ⁻¹' Metric.ball (0 : Fin n → ℂ) ρ) :=
    Metric.isOpen_ball.preimage (continuous_logExp n a)
  refine Filter.mem_of_superset (ho.mem_nhds hs₀) ?_
  intro s hs
  rw [Set.mem_preimage] at hs
  exact ⟨mem_logDom_of_mem_ball hρ1 s hs, hs⟩

noncomputable def logSec (a : ℕ) {n : ℕ} (z : Fin n → ℂ) : Fin n → ℂ := fun k => if (k : ℕ) < a then Complex.log (z k) else z k

noncomputable def logSecAt (a : ℕ) {n : ℕ} (z₀ z : Fin n → ℂ) : Fin n → ℂ :=
  fun k => if (k : ℕ) < a then Complex.log (z₀ k) + Complex.log (z k / z₀ k) else z k

theorem logExp_logSec (z : Fin n → ℂ) (hz : ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) : logExp a (logSec a z) = z := by
  funext k
  by_cases hk : (k : ℕ) < a
  · simp [logExp, logSec, hk, Complex.exp_log (hz k hk)]
  · simp [logExp, logSec, hk]

theorem logExp_logSecAt (z₀ z : Fin n → ℂ) (hz₀ : ∀ k : Fin n, (k : ℕ) < a → z₀ k ≠ 0)
    (hz : ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) : logExp a (logSecAt a z₀ z) = z := by
  funext k
  by_cases hk : (k : ℕ) < a
  · simp only [logExp, logSecAt, hk, if_true]
    rw [Complex.exp_add, Complex.exp_log (hz₀ k hk), Complex.exp_log (div_ne_zero (hz k hk) (hz₀ k hk))]
    field_simp [hz₀ k hk]
  · simp [logExp, logSecAt, hk]

theorem differentiableAt_logSecAt (z₀ : Fin n → ℂ) (hz₀ : ∀ k : Fin n, (k : ℕ) < a → z₀ k ≠ 0) :
    DifferentiableAt ℂ (logSecAt a z₀) z₀ := by
  rw [differentiableAt_pi]
  intro k
  have hpk : DifferentiableAt ℂ (fun z : Fin n → ℂ => z k) z₀ := differentiableAt_apply k z₀
  by_cases hk : (k : ℕ) < a
  · simp only [logSecAt, hk, if_true]
    refine (differentiableAt_const _).add ?_
    have hq : DifferentiableAt ℂ (fun z : Fin n → ℂ => z k / z₀ k) z₀ := by
      simpa [div_eq_mul_inv] using hpk.mul_const (z₀ k)⁻¹
    refine hq.clog ?_
    simp [div_self (hz₀ k hk), Complex.one_mem_slitPlane]
  · simpa [logSecAt, hk] using hpk

theorem descent : ∀ (n a : ℕ) (ρ : ℝ) (h : (Fin n → ℂ) → ℂ), 0 < ρ → ρ ≤ 1 →
    DifferentiableOn ℂ h {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ} →
    (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ → ∀ k : Fin n, (k : ℕ) < a →
      h (s + Pi.single k (2 * Real.pi * Complex.I)) = h s) →
    ∃ H : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ H
      {z | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} ∧
      ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ → h s = H (logExp a s) := by
  intro n a ρ h _ hρ1 hd hinv
  refine ⟨fun z => h (logSec a z), ?_, ?_⟩
  · intro z₀ hz₀
    obtain ⟨hb₀, hn₀⟩ := hz₀

    have hU : ∀ᶠ z in 𝓝 z₀, z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0 := by
      have h1 : ∀ᶠ z in 𝓝 z₀, z ∈ Metric.ball (0 : Fin n → ℂ) ρ := Metric.isOpen_ball.mem_nhds hb₀
      refine h1.and ?_
      rw [Filter.eventually_all]
      intro k
      by_cases hk : (k : ℕ) < a
      · exact ((continuous_apply k).continuousAt.eventually_ne (hn₀ k hk)).mono fun z hz _ => hz
      · exact Filter.Eventually.of_forall fun z hk' => absurd hk' hk
    have hEq : (fun z => h (logSec a z)) =ᶠ[𝓝 z₀] fun z => h (logSecAt a z₀ z) := by
      refine hU.mono fun z ⟨hb, hn⟩ => ?_
      refine key hρ1 hinv _ _ ?_ ?_
      · rw [logExp_logSec z hn]; exact hb
      · rw [logExp_logSec z hn, logExp_logSecAt z₀ z hn₀ hn]
    have hD : {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ} ∈ 𝓝 (logSecAt a z₀ z₀) := by
      refine dom_mem_nhds hρ1 _ ?_
      rw [logExp_logSecAt z₀ z₀ hn₀ hn₀]; exact hb₀
    have hh : DifferentiableAt ℂ h (logSecAt a z₀ z₀) := hd.differentiableAt hD
    have hcomp : DifferentiableAt ℂ (h ∘ logSecAt a z₀) z₀ :=
      DifferentiableAt.comp (𝕜 := ℂ) z₀ hh (differentiableAt_logSecAt z₀ hn₀)
    exact (hcomp.congr_of_eventuallyEq hEq).differentiableWithinAt
  · intro s _ hs
    have hn : ∀ k : Fin n, (k : ℕ) < a → logExp a s k ≠ 0 := fun k hk => by
      simp only [logExp, hk, if_true]; exact Complex.exp_ne_zero _
    refine key hρ1 hinv _ _ hs ?_
    rw [logExp_logSec _ hn]

end GlobalTheory.LogDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLawsAtStages
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealGeo

theorem exists_laws_at_stages : ∀ X : GlobalTheory.Mem.Stages, (∀ W, X.toD7.vol W = GlobalTheory.Mem.Vol.trueVol X.toD7.sp.cm (tauE X.toD7) X.toD7.cd W) → ∀ pb : Fin 2 → HeightOneSpectrum (𝓞 X.toD7.host.K), (∀ k, ((X.toD7.host.g k : ℕ) : 𝓞 X.toD7.host.K) ∈ (pb k).asIdeal) → VolTieG X.toD7 ∧ OKPsi X.toD7 ∧ ∃ (T : CoreJ X.toD7) (_ : Algebra T.Q.c.F X.toD7.what₂.LL), LawsJ T ∧ LawsCore T.toCore ∧ T.Q.Canon ∧ T.pb = pb ∧ AlgTie T ∧ ∀ x, X.toD7.embE x ∈ (algebraMap T.Q.c.F X.toD7.what₂.LL).range := by
  intro X hv pb hg
  have hV : VolTieG X.toD7 := GlobalTheory.Mem.Vol.volTieG_of_trueVol X.toD7 hv
  refine ⟨hV, GlobalTheory.Mem.TypeNormPin.hermitianCodeWordStages_typeNorms_principal X, ?_⟩
  obtain ⟨T, h₁, h₂, h₃, h₄⟩ := GlobalTheory.Member.CoreExist.exists_core_pb X.toD7 (GlobalTheory.Mem.hermitianCodeWordStages_ringOfIntegers_full X)
    (GlobalTheory.Mem.hermitianCodeWordStages_has_rootOfUnity X) hV pb hg
  have hp : T.Q.PinField := h₁.pins.2.2.1
  letI := algTop T hp
  have ha : AlgTie T := algTie_algTop T hp
  refine ⟨T, algTop T hp, h₁, h₂, h₃, h₄, ha, fun x => ⟨embF T.Q.c X.toD7.host.φ₀ x, ?_⟩⟩
  apply X.toD7.what₂.embLL.injective
  exact (RingHom.congr_fun (res_embLL T ha hp) (embF T.Q.c X.toD7.host.φ₀ x)).trans
    (RingHom.congr_fun X.toD7.embE_φ₀ x).symm

end GlobalTheory.RealGeo
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNatMulIsIntegralIwasawaDecomposition
section
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill

namespace GlobalTheory.UnipKill

theorem exists_nat_mul_isIntegral_iwasawa_decomposition (E : Type) [Field E] [NumberField E] (c : E) :
    ∃ a : ℕ, 0 < a ∧ IsIntegral ℤ ((a : E) * c) := by
  obtain ⟨y, hy, h⟩ := exists_integral_multiples ℤ ℚ (L := E) {c}
  have hc := h c (Finset.mem_singleton_self c)
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg y
  · refine ⟨n, Nat.pos_of_ne_zero (by rintro rfl; simp at hy), ?_⟩
    have : ((n : ℕ) : E) * c = ((n : ℤ)) • c := by rw [zsmul_eq_mul]; push_cast; rfl
    rw [this]; exact hc
  · refine ⟨n, Nat.pos_of_ne_zero (by rintro rfl; simp at hy), ?_⟩
    have : ((n : ℕ) : E) * c = -((-(n : ℤ)) • c) := by rw [zsmul_eq_mul]; push_cast; ring
    rw [this]; exact hc.neg

theorem exists_nat_smul_mem_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ)
    (X : Data E N) (v : Fin N → E), ∃ d : ℕ, 0 < d ∧ (d : E) • v ∈ X.Λ := by
  intro E _ _ _ N X v
  have hv : v ∈ Submodule.span E (X.Λ : Set (Fin N → E)) := by rw [X.Λ_span]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d1, hd1, h1⟩ := hx
    obtain ⟨d2, hd2, h2⟩ := hy
    refine ⟨d1 * d2, Nat.mul_pos hd1 hd2, ?_⟩
    have e : ((d1 * d2 : ℕ) : E) • (x + y) = d2 • ((d1 : E) • x) + d1 • ((d2 : E) • y) := by
      simp only [← Nat.cast_smul_eq_nsmul E, smul_smul, smul_add]
      push_cast; congr 1 <;> congr 1 <;> ring
    rw [e]
    exact X.Λ.add_mem (X.Λ.nsmul_mem h1 _) (X.Λ.nsmul_mem h2 _)
  | smul c x _ hx =>
    obtain ⟨d, hd, h⟩ := hx
    obtain ⟨a, ha, hi⟩ := exists_nat_mul_isIntegral_iwasawa_decomposition E c
    refine ⟨a * d, Nat.mul_pos ha hd, ?_⟩
    let k : 𝓞 E := ⟨(a : E) * c, hi⟩
    have e : ((a * d : ℕ) : E) • (c • x) = k • ((d : E) • x) := by
      rw [← algebraMap_smul E k ((d : E) • x), smul_smul, smul_smul]
      show _ = (((a : E) * c) * (d : E)) • x
      push_cast; congr 1; ring
    rw [e]
    exact X.Λ.smul_mem k h

end GlobalTheory.UnipKill
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOrthonormalStepBasisBaseLatticeChartsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.G Formalism.L2.G Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthonormal_step_basis_base_lattice_charts : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (n : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ (Fl : ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
        G.Fills ((w.D Z).gat u v hg)),
      ∀ (hfl : ∀ u v hg, (Fl u v hg).t = (w.D Z).R.t ∧ (Fl u v hg).mm = (w.D Z).R.m),
      (∀ u v hg (x : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' x)), ∀ j ∈ SizeData₂.lifts (w.D Z),
        ((Fl u v hg).w x j s : ℝ) = wj (w.D Z) j (t.Gt.gat_pos u v hg ⟨x, s⟩) - G.kaJ (w.D Z) j) →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∀ (hμ : (w.D Z).what₂.muAt v ≠ (w.D Z).what₂.mu0),
      ∀ (tt : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes n.tp t.C (w.tw Z)), TC.StdTw w.I w.l Z w.l0 tt →
      ∀ j (hj : j + 1 ≤ (w.D Z).R.m), ∃ B : GL (Fin ((w.D Z).sp.X (j + 1)).rank) (w.D Z).host.E,
        cT (sigD (w.D Z) : (w.D Z).host.E →+* (w.D Z).host.E)
          (reGL (rankN (w.D Z) (j + 1) hj) (w.D Z).host.E B).1 * gramN (w.D Z) (j + 1) hj *
          (reGL (rankN (w.D Z) (j + 1) hj) (w.D Z).host.E B).1 = 1 ∧
        ∀ (β : tt.ch.Ch u ((w.D Z).what₂.muAt v) (j + 1)) w' h (x : Fin ((w.D Z).sp.X (j + 1)).rank → w'.adicCompletion (w.D Z).host.F),
          (∃ y ∈ Formalism.L2.Herm.locL w' (tt.ch.lev u ((w.D Z).what₂.muAt v) (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj β).Lb,
            ∀ a, ((t.g.herm.g u v hg).spl w' h (y a)).1 = x a) ↔
          ∀ a, (((GlobalTheory.Mem.Top.KerTwLv.frOf t.g.herm u v hg B w' h)⁻¹ :
            GL (Fin ((w.D Z).sp.X (j + 1)).rank) (w'.adicCompletion (w.D Z).host.F)) :
              Matrix (Fin ((w.D Z).sp.X (j + 1)).rank) (Fin ((w.D Z).sp.X (j + 1)).rank) (w'.adicCompletion (w.D Z).host.F)).mulVec x a ∈
            w'.adicCompletionIntegers (w.D Z).host.F := by
  first | exact @GlobalTheory.Mem.Top.KerTwLv.stepBasis_std | exact GlobalTheory.Mem.Top.KerTwLv.stepBasis_std | (intros; apply GlobalTheory.Mem.Top.KerTwLv.stepBasis_std <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrincipalCMTripleExponentialOfPeriodStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.CuspFrom
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_principalCMTriple_exponential_of_period : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (DB : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (PB : DB.La →+ (Fin g → ℂ)), IsTypeFn H DB.p DB.q ty → IsPeriod DB ty PB → ∃ (B : GlobalTheory.CM.PAT H (Sp ℂ)) (ex : (Fin g → ℂ) → (Over.mk (spMap (RingHom.id ℂ)) ⟶ B.t.G)), GlobalTheory.CM.IsExp B (RingHom.id ℂ) DB ty PB ex := by
  first | exact @GlobalTheory.CuspFrom.exists_pat_isExp_of_isPeriod | exact GlobalTheory.CuspFrom.exists_pat_isExp_of_isPeriod | (intros; apply GlobalTheory.CuspFrom.exists_pat_isExp_of_isPeriod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRealUnitNotRootOfUnity
section
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill

namespace GlobalTheory.UnipKill

open NumberField.Units IsCMField in

theorem exists_real_unit_infinite_order (E : Type) [Field E] [NumberField E] [IsCMField E]
    (hE : 1 < Module.finrank ℚ E / 2) :
    ∃ u : (𝓞 E)ˣ, cc (u : E) = u ∧ ∀ n : ℕ, 0 < n → (u : E) ^ n ≠ 1 := by
  have hrank : 0 < rank E := by
    have h1 := IsTotallyComplex.finrank (K := E)
    have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := E)
    have h3 := IsTotallyComplex.nrRealPlaces_eq_zero (K := E)
    unfold rank
    omega
  let i : Fin (rank E) := ⟨0, hrank⟩
  refine ⟨realFundSystem E i, ?_, ?_⟩
  · simp only [realFundSystem, cc]
    exact complexConj_apply_eq_self E _
  · intro n hn hpow
    set v := fundSystem (maximalRealSubfield E) (finCongr (units_rank_eq_units_rank E).symm i)
    have hv : v ^ n = 1 := by
      have hinj : Function.Injective (algebraMap (𝓞 (maximalRealSubfield E)) E) :=
        (FaithfulSMul.algebraMap_injective (𝓞 (maximalRealSubfield E)) E)
      apply Units.ext
      apply hinj
      rw [Units.val_pow_eq_pow_val, map_pow, Units.val_one, map_one,
        IsScalarTower.algebraMap_apply (𝓞 (maximalRealSubfield E)) (𝓞 E) E]
      exact hpow
    have htor : v ∈ torsion (maximalRealSubfield E) := (CommGroup.mem_torsion _).mpr
      ((isOfFinOrder_iff_pow_eq_one).mpr ⟨n, hn, hv⟩)
    have hmk := fundSystem_mk (maximalRealSubfield E) (finCongr (units_rank_eq_units_rank E).symm i)
    rw [(QuotientGroup.eq_one_iff _).mpr htor] at hmk
    exact (basisModTorsion (maximalRealSubfield E)).ne_zero _ hmk.symm

end GlobalTheory.UnipKill
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemiAbelianExponentialAlongDiscStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
open scoped CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semi_abelian_exponential_along_disc : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (y : ℂ → (Sp ℂ ⟶ X)) (r : ℝ), IsSemiAbelian G → 0 < r → IsHolTo (Metric.ball (0 : ℂ) r) y → ∃ (g : ℕ) (ρ : ℝ) (e : ∀ u, (Fin g → ℂ) → (Over.mk (y u) ⟶ G)), 0 < ρ ∧ ρ ≤ r ∧ IsHolTo (Metric.ball (0 : ℂ) ρ ×ˢ Set.univ) (fun q : ℂ × (Fin g → ℂ) => (show Sp ℂ ⟶ G.left from (e q.1 q.2).left)) ∧ (∀ u ∈ Metric.ball (0 : ℂ) ρ, (∀ z w, e u (z + w) = e u z * e u w) ∧ Function.Surjective (e u) ∧ IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ G.left from (e u z).left)) ∧ (∀ w, ∃! v : epsPt (y u) ⟶ G, IsDerivAt0 (fun z => (e u z).left) w v.left) ∧ (∀ v : epsPt (y u) ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e u 0).left → ∃! w, IsDerivAt0 (fun z => (e u z).left) w v.left)) ∧ ∀ z₀, e 0 z₀ = 1 → ∃ ζ : ℂ → (Fin g → ℂ), ζ 0 = z₀ ∧ AnalyticAt ℂ ζ 0 ∧ ∀ᶠ u in 𝓝 (0 : ℂ), e u (ζ u) = 1 := by
  first | exact @GlobalTheory.RelExp.exists_exp_along_disc | exact GlobalTheory.RelExp.exists_exp_along_disc | (intros; apply GlobalTheory.RelExp.exists_exp_along_disc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniversalTripleFibreAtFramedPointStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_universalTripleFibre_at_framedPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (S : Type) [CommRing S] [Nontrivial S] [Algebra c.F S] (y : FrPt Xo c S), 1 ≤ Dw.p + Dw.q → ∃ Φ : FibKey Xo S y.x, Tied e y.s y.u Φ := by
  first | exact @GlobalTheory.KeyFourth.exists_tied | exact GlobalTheory.KeyFourth.exists_tied | (intros; apply GlobalTheory.KeyFourth.exists_tied <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GradedLineBundleExistsStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_line_bundle_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p), ∀ (Z : Mdl Y i₀), HasDR Z → ∀ e, ∃ L, IsGrLB Z e L := by
  first | exact @GlobalTheory.GradedPieces.exists_isGrLB | exact GlobalTheory.GradedPieces.exists_isGrLB | (intros; apply GlobalTheory.GradedPieces.exists_isGrLB <;> assumption)
end

