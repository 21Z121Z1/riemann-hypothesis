import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
import Formalism.LocalRingCardinality.SpanPowerMembership.Places
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Definitions.Divisors.DividedWeightUnique
import Formalism.MeanHeightDescent.CovolumeFullAssemblyWeighted
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0800
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0821
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0853
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0774
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0672
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0707
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0848
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0846
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0835
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0832
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentHaarRealSUOfMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0845
import Formalism.LocalToGlobal.InertKernelTheory.StatementAlg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0724
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0004

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceIdempotentComponentsConjValuation
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjVal

open GlobalTheory.IdemSupport

theorem valuation_cP {D : D7} (Q : HeightOneSpectrum (𝓞 D.host.E)) (x : D.host.E) :
    (cP Q).valuation D.host.E (star x) = Q.valuation D.host.E x := by
  have : cP Q = Formalism.BasicNotions.Examples₂.PlacesToy.conjW Q := by
    ext r
    have := Formalism.BasicNotions.Examples₂.PlacesToy.mem_conjW_pow Q r 1
    rw [pow_one, pow_one] at this
    rw [this, mem_cP]
    rfl
  rw [this, Formalism.BasicNotions.Examples₂.PlacesToy.valuation_conjW, star_star]

theorem eq_of_le_iff {a b : WithZero (Multiplicative ℤ)}
    (h : ∀ c, c ≠ 0 → (a ≤ c ↔ b ≤ c)) : a = b := by
  have key : ∀ {a b : WithZero (Multiplicative ℤ)}, (∀ c, c ≠ 0 → a ≤ c → b ≤ c) → b ≤ a := by
    intro a b h
    by_cases ha : a = 0
    · by_contra hb
      have hb0 : b ≠ 0 := fun e => hb (by rw [e]; exact zero_le)
      have h1 := h (WithZero.exp (WithZero.log b - 1)) WithZero.exp_ne_zero (by rw [ha]; exact zero_le)
      rw [← WithZero.exp_log hb0, WithZero.exp_le_exp, WithZero.log_exp] at h1
      omega
    · exact h a ha le_rfl
  exact le_antisymm (key fun c hc => (h c hc).2) (key fun c hc => (h c hc).1)

theorem int_iff {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {e : FiniteAdeleRing (𝓞 E) E}
    (h1 : e P = 1) (h0 : ∀ R, R ≠ P → e R = 0) (y : FiniteAdeleRing (𝓞 E) E) {k : E} (hk : k ≠ 0) :
    (∀ R : HeightOneSpectrum (𝓞 E), Valued.v ((e * (y * algebraMap E (FiniteAdeleRing (𝓞 E) E) k⁻¹)) R) ≤ 1) ↔
      Valued.v (y P) ≤ P.valuation E k := by
  have e1 : ∀ R, (e * (y * algebraMap E (FiniteAdeleRing (𝓞 E) E) k⁻¹)) R =
      e R * (y R * algebraMap E (R.adicCompletion E) k⁻¹) := fun R => rfl
  have hv : 0 < P.valuation E k := zero_lt_iff.2 (by simpa using hk)
  have e2 : Valued.v ((e * (y * algebraMap E (FiniteAdeleRing (𝓞 E) E) k⁻¹)) P) ≤ 1 ↔
      Valued.v (y P) ≤ P.valuation E k := by
    rw [e1, h1, one_mul, map_mul, Formalism.UG.P.levelaf_valued_algebraMap, map_inv₀, mul_inv_le_iff₀ hv, one_mul]
  rw [← e2]
  refine ⟨fun h => h P, fun h R => ?_⟩
  by_cases hR : R = P
  · rw [hR]; exact h
  · rw [e1, h0 R hR, zero_mul, map_zero]
    exact zero_le

theorem map_three {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B ≃+* C) (a b c : A) :
    g (f (a * (b * c))) = g (f a) * (g (f b) * g (f c)) := by
  simp only [map_mul]

theorem conj_mem_iff {D : D7} (e z : AE D) (k : D.host.E) :
    finPart D (cA D e * (cA D z * incA D (star k)⁻¹)) ∈ intAE D ↔ finPart D (e * (z * incA D k⁻¹)) ∈ intAE D := by
  rw [← star_inv₀, ← cA_incA, ← RingHom.map_mul, ← RingHom.map_mul]
  refine ⟨fun h => ?_, finPart_cA_mem⟩
  have := finPart_cA_mem h
  rwa [cA_cA] at this

set_option maxHeartbeats 800000 in

theorem components_and_conj_valuation : ∀ (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E), (∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x) → (∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1) → (∀ P : HeightOneSpectrum (𝓞 D.host.E), ∃ e : AE D, IsPlIdem D e P ∧ infPart D e = 0 ∧ ι (finPart D e) P = 1 ∧ ∀ P' : HeightOneSpectrum (𝓞 D.host.E), P' ≠ P → ι (finPart D e) P' = 0) → (∀ (e : AE D) (P : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt e P → infPart D e = 0 ∧ ι (finPart D e) P = 1 ∧ ∀ P' : HeightOneSpectrum (𝓞 D.host.E), P' ≠ P → ι (finPart D e) P' = 0) ∧ ∀ (z : AE D) (Q : HeightOneSpectrum (𝓞 D.host.E)), Valued.v (ι (finPart D (cA D z)) (GlobalTheory.IdemSupport.cP Q)) = Valued.v (ι (finPart D z) Q) := by
  intro D ι hinc hint hid
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  choose ε hε using hid
  have hd : ∀ P, IsDelta Φ P (ε P) := fun P => (tie_iff hΦ (hε P).1.1 (hε P).2.1 P).1 (hε P).1.2.2
  refine ⟨fun e P h => ?_, fun z Q => ?_⟩
  · rw [delta_unique hΦ (delta_of_isIdemAt hΦ h) (hd P)]
    exact (hε P).2
  have hc : cA D (ε Q) = ε (cP Q) := delta_unique hΦ (delta_conj hΦ (hd Q)) (hd _)
  have key : ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (y : AE D) (k : D.host.E), k ≠ 0 →
      (finPart D (ε P * (y * incA D k⁻¹)) ∈ intAE D ↔ Valued.v (ι (finPart D y) P) ≤ P.valuation D.host.E k) := by
    intro P y k hk
    have : ι (finPart D (incA D k⁻¹)) = algebraMap D.host.E _ k⁻¹ := hinc k⁻¹
    rw [hint, map_three, this]
    exact int_iff (hε P).2.2.1 (hε P).2.2.2 _ hk
  refine eq_of_le_iff fun c hc0 => ?_
  obtain ⟨k, rfl⟩ := Q.valuation_surjective D.host.E c
  have hk : k ≠ 0 := fun e => hc0 (by rw [e, Valuation.map_zero])
  have h1 := key (cP Q) (cA D z) (star k) (star_ne_zero.2 hk)
  rw [valuation_cP, ← hc, conj_mem_iff] at h1
  exact h1.symm.trans (key Q z k hk)

end GlobalTheory.ConjVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosDividedSlopeWeightsBaseHeight
section
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.L2.Indef.Tree NumberField GlobalTheory.MeanTop

namespace GlobalTheory.MeanTop.DividedSlope

theorem strictAnti_of_adj {N : ℕ} (v : Fin N → ℝ)
    (h : ∀ a b : Fin N, (b : ℕ) = a + 1 → v b < v a) : ∀ a b : Fin N, a < b → v b < v a := by
  intro a b hab
  obtain ⟨b, hb⟩ := b
  have hab' : (a : ℕ) < b := hab
  induction b, hab' using Nat.le_induction with
  | base => exact h a _ rfl
  | succ n hn ih =>
    have h1 := ih (by omega) (show (a : ℕ) < n from hn)
    have h2 := h ⟨n, by omega⟩ ⟨n + 1, hb⟩ rfl
    linarith

variable {ι : Type} [Fintype ι] {N : ℕ} (W : Wts ι N)

omit [Fintype ι] in
theorem T_pos (hW : W.Hyp) : (0 : ℝ) < W.T := by
  have := hW.h1
  have : 0 < W.T := by omega
  exact_mod_cast this

omit [Fintype ι] in
theorem pos_dividedSlopeWeights_baseHeight (hW : W.Hyp) : (0 : ℝ) < W.h0 := by
  have h1 := hW.h2.1
  have h2 := hW.weightConst_nonneg
  have : 0 < W.h0 := by omega
  exact_mod_cast this

omit [Fintype ι] in
theorem g_pos (hW : W.Hyp) : 0 < W.g := by
  have := T_pos W hW
  have := pos_dividedSlopeWeights_baseHeight W hW
  unfold Wts.g
  positivity

omit [Fintype ι] in
theorem g_le_of (hW : W.Hyp) {x : ℤ} (hx : W.h0 ≤ 4 * W.T * x) : W.g ≤ (x : ℝ) := by
  have hT := T_pos W hW
  have hx' : (W.h0 : ℝ) ≤ 4 * W.T * x := by exact_mod_cast hx
  unfold Wts.g
  rw [div_le_iff₀ (by positivity)]
  linarith

theorem adj_ge (hW : W.Hyp) (hD : W.IsDiv) (τ : ι) (a b : Fin N) (hab : (b : ℕ) = a + 1) (hb : W.p ≤ (b : ℕ)) :
    W.g ≤ reWt W.u' τ a - reWt W.u' τ b := by
  obtain ⟨-, h2, h3⟩ := GlobalTheory.T.dividedWeight_gaps_block_and_bar ι N W hW hD τ a b hab
  have hk := hW.kc_lt
  by_cases hp : (b : ℕ) = W.p
  · have := g_le_of W hW (h2 hp).2
    have ha : (a : ℕ) < W.p := by omega
    have hb' : ¬ (b : ℕ) < W.p := by omega
    simp only [reWt, Wts.u', ha, hb', if_true, if_false]
    push_cast at this ⊢
    linarith
  · have := g_le_of W hW (h3 hp (by omega))
    have ha : ¬ (a : ℕ) < W.p := by omega
    have hb' : ¬ (b : ℕ) < W.p := by omega
    simp only [reWt, Wts.u', ha, hb', if_false]
    push_cast at this ⊢
    linarith

theorem adj_lt (hW : W.Hyp) (hD : W.IsDiv) (τ : ι) (a b : Fin N) (hab : (b : ℕ) = a + 1) :
    reWt W.u' τ b < reWt W.u' τ a := by
  by_cases hb : W.p ≤ (b : ℕ)
  · have := adj_ge W hW hD τ a b hab hb
    have := g_pos W hW
    linarith
  · obtain ⟨h1, -, -⟩ := GlobalTheory.T.dividedWeight_gaps_block_and_bar ι N W hW hD τ a b hab
    have h := h1 (by omega)
    have h' : W.u1 τ b < W.u1 τ a := by omega
    have ha : (a : ℕ) < W.p := by omega
    have hb' : (b : ℕ) < W.p := by omega
    simp only [reWt, Wts.u', ha, hb', if_true]
    exact_mod_cast h'

theorem regular (hW : W.Hyp) (hD : W.IsDiv) (τ : ι) (a b : Fin N) (hab : a < b) :
    reWt W.u' τ b < reWt W.u' τ a :=
  strictAnti_of_adj _ (adj_lt W hW hD τ) a b hab

theorem anti (hW : W.Hyp) (hD : W.IsDiv) (τ : ι) (a b : Fin N) (hab : a ≤ b) :
    reWt W.u' τ b ≤ reWt W.u' τ a := by
  rcases hab.eq_or_lt with h | h
  · rw [h]
  · exact (regular W hW hD τ a b h).le

theorem far (hW : W.Hyp) (hD : W.IsDiv) (τ : ι) (a b : Fin N) (ha : W.p ≤ (a : ℕ)) (hab : a ≠ b) :
    W.g ≤ |reWt W.u' τ a - reWt W.u' τ b| := by
  have hk := hW.kc_lt
  rcases lt_or_gt_of_ne hab with h | h
  · have h' : (a : ℕ) < b := h
    have hb := b.2
    have h1 := adj_ge W hW hD τ a ⟨a + 1, by omega⟩ rfl (by simp only; omega)
    have h2 := anti W hW hD τ ⟨a + 1, by omega⟩ b (show (a : ℕ) + 1 ≤ b from h')
    exact le_trans (by linarith) (le_abs_self _)
  · have h' : (b : ℕ) < a := h
    have hb := a.2
    have h1 := adj_ge W hW hD τ ⟨a - 1, by omega⟩ a (by simp only; omega) ha
    have h2 := anti W hW hD τ b ⟨a - 1, by omega⟩ (show (b : ℕ) ≤ a - 1 by omega)
    exact le_trans (by linarith) (neg_le_abs _)

theorem entry_le (hW : W.Hyp) (hD : W.IsDiv) (τ : ι) (i : Fin N) :
    |reWt W.u' τ i| ≤ 2 * W.b / W.T := by
  have hT := T_pos W hW
  have h1 := (GlobalTheory.MeanTop.divided_entries ι N W hW hD τ i).1
  have h2 := (GlobalTheory.T.weight_division_l1_bound ι N W hW hD).2.2 τ i
  have h3 := hW.h5 τ i
  have h1' : ((W.T : ℝ) + W.Dd + 1) * |(W.u1 τ i : ℝ)| ≤ |(W.u τ i : ℝ)| + W.c0 + 4 * N := by exact_mod_cast h1
  have h2' : |(W.u' τ i : ℝ)| ≤ |(W.u1 τ i : ℝ)| := by exact_mod_cast h2
  have h4 : (0 : ℝ) ≤ W.Dd := Nat.cast_nonneg _
  have h5 := abs_nonneg (W.u1 τ i : ℝ)
  rw [le_div_iff₀ hT]
  show |(W.u' τ i : ℝ)| * W.T ≤ 2 * W.b
  nlinarith [mul_le_mul_of_nonneg_right h2' hT.le, mul_nonneg h4 h5]

end GlobalTheory.MeanTop.DividedSlope
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReductionMap
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

theorem Katz.reductionMap : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (h : IsLaw μ) (V : Type) [AddCommGroup V] [Module k V] (ρ : MvPowerSeries (Fin d ⊕ Fin d) k × (Fin d → k) →ₗ[k] V), IsRigOf μ ρ → ∃ r : Mod p h →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)] V, (∀ (f : quasiLog p h) c w, Red p (cob1 (fun i => Katz.lift p (μ i)) f.1) c → RedV p (lin f.1) w → r (Submodule.Quotient.mk f) = ρ (c, w)) ∧ Function.Surjective r ∧ ∀ m, r m = 0 ↔ ∃ n, m = p • n := by
  intro p _ k _ _ _ d μ h V _ _ ρ hρ
  have hμ' : ∀ i, constantCoeff (Katz.lift p (μ i)) = 0 := fun i => constantCoeff_lift p (h.const i)
  have hR1 := GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k (Fin d)
  have hR2 := GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k (Fin d ⊕ Fin d)
  have hC := GlobalTheory.T.reduction_commutes_formalGroupLawCoboundaries p k d μ h.const
  have hD := GlobalTheory.T.quasiLog_reduces_to_cocycle p k d μ h
  have hK := GlobalTheory.T.quasiLogarithm_eq_p_smul_add_integral p k d μ h
  have hS := GlobalTheory.T.exists_quasiLog_red_coboundary_and_linear p k d μ h
  have hVu : ∀ (v : Fin d → Fr p k) (w w' : Fin d → k), RedV p v w → RedV p v w' → w = w' := by
    intro v w w' h1 h2
    funext i
    obtain ⟨a, ha, ha'⟩ := h1 i
    obtain ⟨b, hb, hb'⟩ := h2 i
    rw [ha] at hb
    rw [← ha', ← hb', IsFractionRing.injective (WittVector p k) (Fr p k) hb]
  have hVa : ∀ (v v' : Fin d → Fr p k) (w w' : Fin d → k), RedV p v w → RedV p v' w' →
      RedV p (v + v') (w + w') := by
    intro v v' w w' h1 h2 i
    obtain ⟨a, ha, ha'⟩ := h1 i
    obtain ⟨b, hb, hb'⟩ := h2 i
    exact ⟨a + b, by rw [Pi.add_apply, ha, hb, map_add], by rw [map_add, ha', hb']; rfl⟩
  have hVs : ∀ (r : WittVector p k) (v : Fin d → Fr p k) (w : Fin d → k), RedV p v w →
      RedV p (fun i => algebraMap _ (Fr p k) r * v i) (WittVector.constantCoeff r • w) := by
    intro r v w h1 i
    obtain ⟨a, ha, ha'⟩ := h1 i
    exact ⟨r * a, by beta_reduce; rw [ha, ← map_mul], by rw [map_mul, ha']; rfl⟩
  have hlinadd : ∀ f g : MvPowerSeries (Fin d) (Fr p k), lin (f + g) = lin f + lin g := by
    intro f g; funext i; simp [lin]
  have hlinsmul : ∀ (r : WittVector p k) (f : MvPowerSeries (Fin d) (Fr p k)),
      lin (r • f) = fun i => algebraMap _ (Fr p k) r * lin f i := by
    intro r f; funext i
    simp only [lin, ← algebraMap_smul (Fr p k) r f, coeff_smul, smul_eq_mul]
  have hcobs : ∀ (r : WittVector p k) (f : MvPowerSeries (Fin d) (Fr p k)),
      cob1 (fun i => Katz.lift p (μ i)) (r • f) = r • cob1 (fun i => Katz.lift p (μ i)) f := by
    intro r f
    rw [← algebraMap_smul (Fr p k) r f, formalCoboundary_smul hμ', algebraMap_smul]
  choose c w hc hw using hD.1
  have key : ∀ f (hf : f ∈ quasiLog p h) c' w', Red p (cob1 (fun i => Katz.lift p (μ i)) f) c' →
      RedV p (lin f) w' → ρ (c f hf, w f hf) = ρ (c', w') := by
    intro f hf c' w' h1 h2
    rw [hR2.2.1 _ _ _ (hc f hf) h1, hVu _ _ _ (hw f hf) h2]
  let Φ : quasiLog p h →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)] V :=
    { toFun := fun f => ρ (c f.1 f.2, w f.1 f.2)
      map_add' := fun f g => by
        rw [key (f + g).1 (f + g).2 (c f.1 f.2 + c g.1 g.2) (w f.1 f.2 + w g.1 g.2), ← map_add,
          Prod.mk_add_mk]
        · rw [Submodule.coe_add, formalCoboundary_add hμ']
          exact (hR2.2.2.2.1 _ _ _ _ (hc _ _) (hc _ _)).1
        · rw [Submodule.coe_add, hlinadd]
          exact hVa _ _ _ _ (hw _ _) (hw _ _)
      map_smul' := fun r f => by
        rw [key (r • f).1 (r • f).2 (WittVector.constantCoeff r • c f.1 f.2)
          (WittVector.constantCoeff r • w f.1 f.2), ← map_smul, Prod.smul_mk]
        · rw [Submodule.coe_smul, hcobs]
          exact hR2.2.2.2.2.1 _ _ _ (hc _ _)
        · rw [Submodule.coe_smul, hlinsmul]
          exact hVs _ _ _ (hw _ _) }
  have hΦ : ∀ f : quasiLog p h, Φ f = ρ (c f.1 f.2, w f.1 f.2) := fun _ => rfl
  have hker : (intBy p k (Fin d) 1).submoduleOf (quasiLog p h) ≤ LinearMap.ker Φ := by
    intro f hf
    rw [LinearMap.mem_ker, hΦ]
    have hf' : (f : MvPowerSeries (Fin d) (Fr p k)) ∈ intBy p k (Fin d) 1 := hf
    obtain ⟨b, hb⟩ := (hR1.1 _).1 hf'
    obtain ⟨h1, h2⟩ := hC.2.1 _ _ hb
    rw [key _ _ _ _ h1 h2]
    exact ((hρ.ker _ _ (hD.2 _ f.2 _ h1)).2 ⟨b, rfl, rfl⟩)
  refine ⟨Submodule.liftQ _ Φ hker, ?_, ?_, ?_⟩
  · intro f c' w' h1 h2
    rw [Submodule.liftQ_apply, hΦ, key _ _ _ _ h1 h2]
  · intro v
    obtain ⟨c', w', hcoc, rfl⟩ := hρ.surj v
    obtain ⟨f, hf, h1, h2⟩ := hS c' hcoc w'
    exact ⟨Submodule.Quotient.mk ⟨f, hf⟩, by rw [Submodule.liftQ_apply, hΦ, key _ _ _ _ h1 h2]⟩
  · intro m
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    rw [Submodule.liftQ_apply, hΦ]
    constructor
    · intro h0
      obtain ⟨b, hb1, hb2⟩ := (hρ.ker _ _ (hD.2 _ f.2 _ (hc f.1 f.2))).1 h0
      have h1 := hc f.1 f.2
      have h2 := hw f.1 f.2
      rw [hb1] at h1
      rw [hb2] at h2
      obtain ⟨g, hg, hfg⟩ := hK f.1 f.2 b h1 h2
      refine ⟨Submodule.Quotient.mk ⟨g, hg⟩, ?_⟩
      rw [← Nat.cast_smul_eq_nsmul (WittVector p k), ← Submodule.Quotient.mk_smul,
        Submodule.Quotient.eq]
      exact hfg
    · rintro ⟨n, hn⟩
      have : Φ f = Submodule.liftQ _ Φ hker (p • n) := by
        rw [← hn, Submodule.liftQ_apply]
      rw [← hΦ, this, map_nsmul, ← Nat.cast_smul_eq_nsmul k, CharP.cast_eq_zero, zero_smul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShintaniFormula
section
open NumberField IsDedekindDomain Formalism.UG GlobalTheory.PRep GlobalTheory.LFun
open scoped Classical

open GlobalTheory.JSW

theorem GlobalTheory.JSW.shintani_formula : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ψ : AddChar (w.adicCompletion E) ℂ), (∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, ψ (x * y) = 1) ↔ x ∈ Ov E w) → ∀ (W : GL (Fin n) (w.adicCompletion E) → ℂ) (α : Fin n → ℂˣ), (∀ u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin n), ∀ g, W (u * g) = ψ (GlobalTheory.Whittaker.superDiag u) * W g) → (∀ g, ∀ k ∈ KGL w n, W (g * k) = W g) → (∀ ϖ, IsUnifV E w ϖ → ∀ j ≤ n, heckeVec (rightReg ℂ (GL (Fin n) (w.adicCompletion E)) ℂ) (KGL w n) (Tj ℂ n (Ov E w) ϖ j) W = satEig (qV E w) n (Finset.univ.val.map α) j • W) → ∀ (ϖ : (w.adicCompletion E)ˣ), IsUnifV E w (ϖ : w.adicCompletion E) → ∀ l : Fin n → ℕ, W (Units.map (Matrix.diagonalRingHom (Fin n) (w.adicCompletion E)).toMonoidHom (MulEquiv.piUnits.symm fun i => ϖ ^ l i)) = GlobalTheory.JSW.sphW (qV E w) (fun i => (α i : ℂ)) l * W 1 := by
  intro E _ _ w n ψ hψ W α hN hK hH ϖ hϖ l
  have hvan := GlobalTheory.T.whittaker_diagonal_eq_zero_of_not_antitone E w n ψ hψ W hN hK ϖ hϖ
  have hrec := GlobalTheory.T.sphericalWhittaker_torus_hecke_recursion E w n ψ hψ W α hN hK hH ϖ hϖ
  have hq : ((qV E w : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (GlobalTheory.LFun.qV_ne_zero w)
  have hes : ∀ j, MvPolynomial.eval₂ (Int.castRingHom ℂ) (fun i => (α i : ℂ)) (MvPolynomial.esymm (Fin n) ℤ j) =
      (Finset.univ.val.map fun i => (α i : ℂ)).esymm j := fun j => by
    rw [← MvPolynomial.aeval_esymm_eq_multiset_esymm (Fin n) ℤ]
    rfl
  let V : (Fin n → ℕ) → ℂ := fun m =>
    (qV E w : ℂ) ^ ((∑ k : Fin n, (((n : ℂ) - 1 - 2 * (k : ℕ)) * (((m) k : ℕ) : ℂ))) / 2) *
      W (Units.map (Matrix.diagonalRingHom (Fin n) (w.adicCompletion E)).toMonoidHom
        (MulEquiv.piUnits.symm fun i => ϖ ^ (m) i))
  let U : (Fin n → ℕ) → ℂ := fun m => if Antitone m then schurAt m (fun i => (α i : ℂ)) * W 1 else 0
  have hVU : V = U := by
    refine GlobalTheory.T.eq_of_pieri_recursion_of_eq_zero n (fun j => (Finset.univ.val.map fun i => (α i : ℂ)).esymm j) V U
      (fun m hm => by simp only [V, hvan m hm, mul_zero]) (fun m hm => by simp only [U, if_neg hm])
      (fun m hm j hj => hrec m hm j hj) (fun m hm j hj => ?_) ?_
    · have hp := congrArg (MvPolynomial.eval₂ (Int.castRingHom ℂ) (fun i => (α i : ℂ))) (GlobalTheory.T.esymm_mul_schurPolynomialJacobiTrudi n m hm j hj)
      rw [MvPolynomial.eval₂_mul, hes, MvPolynomial.eval₂_sum] at hp
      simp only [U, if_pos hm]
      rw [← Finset.sum_filter, Finset.filter_filter, ← Finset.sum_mul, ← mul_assoc]
      simp only [schurAt]
      rw [hp]
    · have h1 : (Units.map (Matrix.diagonalRingHom (Fin n) (w.adicCompletion E)).toMonoidHom
          (MulEquiv.piUnits.symm fun i => ϖ ^ (0 : Fin n → ℕ) i)) = 1 := by
        ext i j
        simp [Matrix.one_apply, Matrix.diagonal_apply]
      have h0 : (0 : Fin n → ℕ) = fun _ => 0 := rfl
      have ha0 : Antitone (0 : Fin n → ℕ) := antitone_const
      have hs : schurAt (0 : Fin n → ℕ) (fun i => (α i : ℂ)) = 1 := by
        rw [h0, schurAt, GlobalTheory.JSW.schur_zero, MvPolynomial.eval₂_one]
      have hU : U 0 = W 1 := by
        change (if Antitone (0 : Fin n → ℕ) then schurAt 0 (fun i => (α i : ℂ)) * W 1 else 0) = W 1
        rw [if_pos ha0, hs, one_mul]
      rw [hU]
      change _ * W _ = W 1
      rw [h1]
      simp
  have hl := congrFun hVU l
  simp only [V, U] at hl
  by_cases ha : Antitone l
  · rw [if_pos ha] at hl
    have hne : (qV E w : ℂ) ^ ((∑ k : Fin n, (((n : ℂ) - 1 - 2 * (k : ℕ)) * (((l) k : ℕ) : ℂ))) / 2) ≠ 0 := by
      rw [Complex.cpow_def_of_ne_zero hq]; exact Complex.exp_ne_zero _
    rw [sphW, if_pos ha, neg_div, Complex.cpow_neg, mul_assoc, ← hl, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  · rw [hvan l ha, GlobalTheory.JSW.sphW_of_not_antitone _ _ ha, zero_mul]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialUnitaryLieAlgebraEntriesOrthonormalFrameStatement
section
open NumberField MeasureTheory Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.specialUnitaryLieAlgebra_entries_orthonormal_frame : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (x : Frame X.Ψ r), IsOrth X x → ∀ (Y : EuclideanSpace ℂ (X.Ψ × Fin r × Fin r)), fromFrame x Y ∈ realLie X.Ψ X.Gm → (∀ τ a b, Y (τ, b, a) = -((sgn X.p0 a * sgn X.p0 b : ℝ) : ℂ) * conj (Y (τ, a, b))) ∧ ∀ τ, ∑ a, Y (τ, a, a) = 0 := by
  first | exact @GlobalTheory.SUVol.FrameSkew.entries_of_mem | exact GlobalTheory.SUVol.FrameSkew.entries_of_mem | (intros; apply GlobalTheory.SUVol.FrameSkew.entries_of_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaVacuumEqKappaPowMulBlockKernels
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.BaseVacuum
open Classical

namespace GlobalTheory.BaseVacuum

theorem thZero_eq_kappa_pow_mul_prod_kerB : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), B.StdOK →
    ∀ (n n' : ℕ) (z : TaylorLogMetric.VC D (n * 2) (n' * 2)),
      B.thZero (n * 2) (n' * 2) z = B.kappa ^ (n' * n) * ∏ k : Fin n' × Fin n, Formalism.L2.KerInert.kerB B (blk D k z) := by
  intro D cc δ B hS n n' z
  have h4 : tens4 B.thMM = B.kappa • Formalism.L2.KerInert.kerB B := (B.thMM_spec hS).2
  have hk : ∀ k : Fin n' × Fin n,
      B.kappa * Formalism.L2.KerInert.kerB B (blk D k z) =
        ∏ a : Fin 4, B.thMM (fun τ => z τ (posE n n' (k, a)).1 (posE n n' (k, a)).2) := by
    intro k
    have := congrFun h4 (blk D k z)
    rw [Pi.smul_apply, smul_eq_mul] at this
    rw [← this]
    rfl
  have hcard : B.kappa ^ (n' * n) = ∏ _k : Fin n' × Fin n, B.kappa := by
    simp [Finset.prod_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  rw [hcard, ← Finset.prod_mul_distrib]
  simp_rw [hk]
  rw [← Fintype.prod_prod_type' (f := fun k a => B.thMM (fun τ => z τ (posE n n' (k, a)).1 (posE n n' (k, a)).2))]
  rw [Fintype.prod_equiv (posE n n')
    (fun p => B.thMM (fun τ => z τ (posE n n' p).1 (posE n n' p).2))
    (fun q => B.thMM (fun τ => z τ q.1 q.2)) (fun _ => rfl)]
  show tensPow B.thMM (n * 2) (n' * 2) z = _
  unfold tensPow
  rw [← Fintype.prod_prod_type' (f := fun i j => B.thMM (fun τ => z τ i j))]

end GlobalTheory.BaseVacuum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointEqOfResidueEqInvertibleOrder
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PureLift
open scoped CategoryTheory.Obj

namespace GlobalTheory.TorsionReduction

theorem eq_of_residue_eq : ∀ (S : Type) [CommRing S] (P : Out.PolAV (Sp S)) (T : Type) [CommRing T] [IsLocalRing T] (b : S →+* T) (n : ℕ), IsUnit (n : T) → ∀ x y : Over.mk (spMap b) ⟶ P.A, x ^ n = 1 → y ^ n = 1 → spMap (IsLocalRing.residue T) ≫ x.left = spMap (IsLocalRing.residue T) ≫ y.left → x = y := by
  intro S _ P T _ _ b n hn x y hx hy hr
  letI := P.isAb.comm
  haveI : Smooth P.A.hom := P.isAb.smooth
  let j : Sp T ⟶ Sp S := spMap b
  let G : Over (Sp T) := (Over.pullback j).obj P.A
  have hn' : IsUnit (n : Γ(Sp T, ⊤)) := by
    simpa using hn.map (Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom
  let m : G.left ⟶ G.left := (Out.mulA G n).left
  have hw : m ≫ G.hom = G.hom := Over.w _
  have h₁ : FormallyUnramified m := formallyUnramified_mulA (Sp T) G n hn'
  have h₂ : LocallyOfFiniteType (m ≫ G.hom) := by
    rw [hw]; dsimp [G]; infer_instance
  have h₃ : LocallyOfFiniteType m := locallyOfFiniteType_of_comp _ G.hom
  have e : (Over.pullback j).map (Out.mulA P.A n) = Out.mulA G n :=
    (map_pow (Over.pullback j).homMonoidHom (𝟙 P.A) n).trans
      (congrArg (· ^ n) (CategoryTheory.Functor.map_id (Over.pullback j) P.A))
  have mf : m ≫ pullback.fst P.A.hom j = pullback.fst P.A.hom j ≫ (Out.mulA P.A n).left := by
    change (Out.mulA G n).left ≫ _ = _
    rw [← e]; exact pullback.lift_fst _ _ _
  have kx : ∀ z : Over.mk (spMap b) ⟶ P.A, z ^ n = 1 → z.left ≫ (Out.mulA P.A n).left = j ≫ (η[P.A]).left := by
    intro z hz
    rw [← Over.comp_left, Out.mulA, MonObj.comp_pow, Category.comp_id, hz, Hom.one_def]
    simp [j]
  let x' : Sp T ⟶ G.left := pullback.lift x.left (𝟙 _) (by simpa [j] using Over.w x)
  let y' : Sp T ⟶ G.left := pullback.lift y.left (𝟙 _) (by simpa [j] using Over.w y)
  have x₁ : x' ≫ pullback.fst P.A.hom j = x.left := pullback.lift_fst _ _ _
  have y₁ : y' ≫ pullback.fst P.A.hom j = y.left := pullback.lift_fst _ _ _
  have x₂ : x' ≫ pullback.snd P.A.hom j = 𝟙 _ := pullback.lift_snd _ _ _
  have y₂ : y' ≫ pullback.snd P.A.hom j = 𝟙 _ := pullback.lift_snd _ _ _
  have hab : x' ≫ m = y' ≫ m := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, mf, pullback.lift_fst_assoc, pullback.lift_fst_assoc, kx x hx, kx y hy]
    · rw [Category.assoc, Category.assoc]
      change x' ≫ m ≫ G.hom = y' ≫ m ≫ G.hom
      rw [hw]
      exact (pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm
  have hc : spMap (IsLocalRing.residue T) ≫ x' = spMap (IsLocalRing.residue T) ≫ y' := by
    apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) x₁).trans
        (hr.trans ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) y₁)).symm))
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (x₂.trans y₂.symm)).trans (Category.assoc _ _ _).symm)
  have hopen := isOpenImmersion_equalizer_ι_of_unramified m hab
  have hsub := range_subset_range_equalizer_ι _ hc
  have hcl : IsLocalRing.closedPoint T ∈ Set.range (equalizer.ι x' y') :=
    hsub ⟨IsLocalRing.closedPoint _, IsLocalRing.comap_closedPoint (IsLocalRing.residue T)⟩
  have hall : Set.range (equalizer.ι x' y') = Set.univ :=
    Set.eq_univ_of_forall fun p =>
      (IsLocalRing.specializes_closedPoint p).mem_open (equalizer.ι x' y').isOpenEmbedding.isOpen_range hcl
  have hxy : x' = y' := eq_of_range_equalizer_ι_eq_univ m hab hall
  apply Over.OverMorphism.ext
  exact x₁.symm.trans ((congrArg (· ≫ pullback.fst P.A.hom j) hxy).trans y₁)

end GlobalTheory.TorsionReduction
end

