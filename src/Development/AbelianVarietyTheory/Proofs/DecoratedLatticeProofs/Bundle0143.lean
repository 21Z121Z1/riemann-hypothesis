import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
import Formalism.LocalToGlobal.Columns.ChainTw
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResiduesOfCompletionAtPrimeWithUniformizer
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemZmuOfPowPred
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0105
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0102
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0023
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0125
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0120
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0132
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0119
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0121
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0133
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0199
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0299
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0134

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompletionTwistDataChainColumns
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

noncomputable section
namespace GlobalTheory.TwBridgeInhab

section Loc
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_eq_one_of_sub_one {x : k} (hx : valuation k (x - 1) < 1) : valuation k x = 1 := by
  have h := Valuation.map_add_eq_of_lt_right (valuation k) (x := x - 1) (y := 1) (by simpa using hx)
  simpa using h

def delta (μ₁ : kˣ →* ℂˣ) (ϖ : kˣ) : kˣ →* ℂˣ := μ₁ * GlobalTheory.SmGL.unrChar k (μ₁ ϖ)⁻¹

theorem delta_unit (μ₁ : kˣ →* ℂˣ) (ϖ : kˣ) {x : kˣ} (hx : valuation k (x : k) = 1) : delta μ₁ ϖ x = μ₁ x := by
  simp [delta, GlobalTheory.SmGL.isUnram_unrChar k _ x hx]

theorem delta_tame {μ₁ : kˣ →* ℂˣ} (h : IsTame μ₁) (ϖ : kˣ) : IsTame (delta μ₁ ϖ) := by
  intro x hx
  rw [delta_unit μ₁ ϖ (val_eq_one_of_sub_one hx)]
  exact h x hx

def eta (μ : ℕ → kˣ →* ℂˣ) (m : ℕ) (δ : kˣ →* ℂˣ) (j : ℕ) : kˣ →* ℂˣ :=
  if 1 ≤ j ∧ j ≤ m then μ j * δ⁻¹ else 1

theorem eta_mul (μ : ℕ → kˣ →* ℂˣ) (m : ℕ) (δ : kˣ →* ℂˣ) {i : ℕ} (hi : i < m) :
    eta μ m δ (i + 1) * δ = μ (i + 1) := by
  rw [eta, if_pos ⟨by omega, by omega⟩, inv_mul_cancel_right]

theorem eta_unram (μ : ℕ → kˣ →* ℂˣ) (m : ℕ) (δ : kˣ →* ℂˣ)
    (h : ∀ i, i < m → ∀ x : kˣ, valuation k (x : k) = 1 → μ (i + 1) x = δ x) (j : ℕ) : IsUnram (eta μ m δ j) := by
  intro x hx
  unfold eta
  split_ifs with hj
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, h i (by omega) x hx, mul_inv_cancel]
  · rfl

theorem exists_near {E : Type} [Field E] {ι : E →+* k} (hd : DenseRange ι) (x : k) :
    ∃ a : E, valuation k (ι a - x) < 1 := by
  have hU : {y | valuation k (y - x) < 1} ∈ nhds x := by
    rw [IsValuativeTopology.mem_nhds_iff]
    exact ⟨1, by rintro _ ⟨z, hz, rfl⟩; simpa using hz⟩
  obtain ⟨_, hy, a, rfl⟩ := mem_closure_iff_nhds.mp (hd x) _ hU
  exact ⟨a, hy⟩

theorem tame_near {μ : kˣ →* ℂˣ} (h : IsTame μ) {x u : kˣ} (hx : valuation k (x : k) = 1)
    (hu : valuation k ((u : k) - x) < 1) : μ u = μ x := by
  have hx0 : (x : k) ≠ 0 := x.ne_zero
  have hy : valuation k (((x⁻¹ * u : kˣ) : k) - 1) < 1 := by
    have e : ((x⁻¹ * u : kˣ) : k) - 1 = (x : k)⁻¹ * ((u : k) - x) := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val]; field_simp
    rw [e, map_mul, map_inv₀, hx, inv_one, one_mul]; exact hu
  have := h _ hy
  rw [map_mul, map_inv, inv_mul_eq_one] at this
  exact this.symm

end Loc

section Arith
variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K]

theorem unitV_inv {P : HeightOneSpectrum (𝓞 E)} (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (a : E) :
    LocE.unitV χ⁻¹ a = (LocE.unitV χ a)⁻¹ := by
  unfold LocE.unitV
  split_ifs <;> simp

theorem valuation_self (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (h0 : 0 < q) :
    LocE.vP P q (q : E) = 1 := by
  have hqE : (q : E) ≠ 0 := by exact_mod_cast h0.ne'
  have hnu : ¬ IsUnit (0 : 𝓞 E ⧸ P.asIdeal) := not_isUnit_zero
  have key : ∀ z : ℤ, IsUnit (redP P ((q : E) / (q : E) ^ z)) ↔ z = 1 := by
    intro z
    constructor
    · intro h
      by_contra hz
      rcases lt_or_gt_of_ne hz with hlt | hgt
      · obtain ⟨k, hk⟩ : ∃ k : ℕ, z = -(k : ℤ) := ⟨(-z).toNat, by omega⟩
        have e : (q : E) / (q : E) ^ z = algebraMap (𝓞 E) E (((q : ℕ) : 𝓞 E) ^ (k + 1)) := by
          rw [hk, _root_.zpow_neg, zpow_natCast, div_inv_eq_mul, map_pow, map_natCast, pow_succ']
        rw [e, reduction_coe] at h
        have h1 : Ideal.Quotient.mk P.asIdeal (((q : ℕ) : 𝓞 E) ^ (k + 1)) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_of_mem _ hq _ (Nat.succ_pos k))
        rw [h1] at h; exact hnu h
      · obtain ⟨k, hk⟩ : ∃ k : ℕ, z = (k : ℤ) + 2 := ⟨(z - 2).toNat, by omega⟩
        have e : (q : E) / (q : E) ^ z = ((q : E) ^ (k + 1))⁻¹ := by
          have e1 : (q : E) ^ z = (q : E) ^ (k + 1) * (q : E) := by
            rw [hk, ← pow_succ, ← zpow_natCast]; congr 1
          rw [e1, div_mul_eq_div_div_swap, div_self hqE, one_div]
        have hni : ¬ IntAt P ((q : E) / (q : E) ^ z) := by
          rintro ⟨r, s, hs, hrs⟩
          apply hs
          have h2 : algebraMap (𝓞 E) E s = algebraMap (𝓞 E) E (r * ((q : ℕ) : 𝓞 E) ^ (k + 1)) := by
            rw [map_mul, ← hrs, e, map_pow, map_natCast, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hqE), mul_one]
          rw [(FaithfulSMul.algebraMap_injective (𝓞 E) E) h2]
          exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hq _ (Nat.succ_pos k))
        rw [reduction_eq_zero_of_not_integral P hni] at h; exact hnu h
    · rintro rfl
      rw [zpow_one, div_self hqE]
      have h3 : (1 : E) = algebraMap (𝓞 E) E 1 := (map_one _).symm
      rw [h3, reduction_coe, map_one]; exact isUnit_one
  unfold LocE.vP
  have h4 : (fun z : ℤ => IsUnit (redP P ((q : E) / (q : E) ^ z))) = fun z => z = 1 := funext fun z => propext (key z)
  rw [h4]
  exact Classical.epsilon_spec (p := fun z : ℤ => z = 1) ⟨1, rfl⟩

theorem locChar_q {P : HeightOneSpectrum (𝓞 E)} (q : ℕ) (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (h0 : 0 < q) (cq : K)
    (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) : LocE.locChar q cq χ (q : E) = cq := by
  have hqE : (q : E) ≠ 0 := by exact_mod_cast h0.ne'
  have h1 : redP P (1 : E) = 1 := by
    have h3 : (1 : E) = algebraMap (𝓞 E) E 1 := (map_one _).symm
    rw [h3, reduction_coe, map_one]
  have hu : IsUnit (redP P (1 : E)) := by rw [h1]; exact isUnit_one
  unfold LocE.locChar
  rw [valuation_self P q hq h0, zpow_one, zpow_one, div_self hqE]
  unfold LocE.unitV
  rw [dif_pos hu]
  have h2 : hu.unit = 1 := Units.ext (by rw [IsUnit.unit_spec, h1]; rfl)
  rw [h2, map_one, Units.val_one, mul_one]

end Arith

section Chain
variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ}
  (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (P : rowSG Pr sel mu)

theorem muAt_unit (hP : P.1 ∉ Pr.vGs) (i : ℕ) {a : X.E} (ha : IsUnit (redP P.1 a)) :
    muAt Ch sel mu cst i P a = LocE.unitV (resChar (mu : Chr X.F X.E X.K) P.1)⁻¹ a := by
  unfold muAt
  rw [if_neg hP]
  exact GlobalTheory.LastSteps.locChar_unit _ _ ha

theorem muAt_q (hP : P.1 ∉ Pr.vGs) (i : ℕ) (hq : ((qOf P.1 : ℕ) : 𝓞 X.E) ∈ P.1.asIdeal) (h0 : 0 < qOf P.1) :
    muAt Ch sel mu cst i P ((qOf P.1 : ℕ) : X.E) = cst.muq (i + 1) P := by
  unfold muAt
  rw [if_neg hP]
  exact locChar_q _ hq h0 _ _

end Chain

theorem exists_twData : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (s : ℕ), L.Ok Ch sel mu cst G s → ∀ (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (ϖ : kˣ), GlobalTheory.SymBridge.IsCompl P.1 (qOf P.1) ι ϖ → GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ → ∀ ψ : AddChar k Circle, Continuous ψ → HasConductor ψ 1 → (∀ (a : X.E) (b : ℤ) (n : ℕ), IntAt P.1 (G.xi0 * a - (b : X.E) / (qOf P.1 : X.E) ^ n) → (ψ (ι a) : ℂ) = Complex.exp (2 * Real.pi * Complex.I * b / (qOf P.1 : ℂ) ^ n)) → ∀ μ : ℕ → kˣ →* ℂˣ, (∀ i, i < R.m → (∀ (a : X.E) (u : kˣ), (u : k) = ι a → (μ (i + 1) u : ℂ) = G.σ₀ (muAt Ch sel mu cst i P a)) ∧ IsTame (μ (i + 1))) → ∃ W : TwData k, AtTwist (R := R) sel mu cst G.σ₀ P ι s W ∧ W.ϖ = ϖ ∧ W.ψ = ψ ∧ (∀ i, i < R.m → W.η (i + 1) * W.δ = μ (i + 1)) ∧ (W.sg = 1 ∨ W.sg = -1) := by
  intro X Pr R Ch sel S₀ mu cst L G s hL P hP k _ _ _ _ ι ϖ hc hϖ ψ hψc hψ1 hψt μ hμ
  have hm : R.m = s + 2 := hL.hm
  have hm0 : 0 < R.m := by omega
  have hq0 : (qOf P.1 : X.E) ≠ 0 := GlobalTheory.SymBridge.ComplRes.q_ne_zero hc
  have hqpos : 0 < qOf P.1 := Nat.pos_of_ne_zero fun h => hq0 (by rw [h, Nat.cast_zero])
  have hqmem : ((qOf P.1 : ℕ) : 𝓞 X.E) ∈ P.1.asIdeal := GlobalTheory.SymBridge.ComplRes.q_mem hc
  have hμ1 : ∀ (a : X.E) (u : kˣ), (u : k) = ι a → (μ 1 u : ℂ) = G.σ₀ (muAt Ch sel mu cst 0 P a) :=
    fun a u h => (hμ 0 hm0).1 a u h
  have ht1 : IsTame (μ 1) := (hμ 0 hm0).2

  have hunit : ∀ i, i < R.m → ∀ x : kˣ, valuation k (x : k) = 1 → μ (i + 1) x = μ 1 x := by
    intro i hi x hx
    obtain ⟨a, ha⟩ := exists_near hc.dense (x : k)
    have hva : valuation k (ι a) = 1 := by
      have e : ι a = (ι a - x) + x := by ring
      rw [e, Valuation.map_add_eq_of_lt_right _ (by rw [hx]; exact ha), hx]
    have ha0 : ι a ≠ 0 := by
      intro h0; rw [h0, map_zero] at hva; exact zero_ne_one hva
    have hint : IntAt P.1 a := GlobalTheory.SymBridge.ComplRes.intAt_of_v hc (le_of_eq hva)
    have hred : IsUnit (redP P.1 a) := (GlobalTheory.SymBridge.ComplRes.v_eq_one_iff_red hc hϖ hint).mp hva
    have hn : valuation k (((Units.mk0 (ι a) ha0 : kˣ) : k) - x) < 1 := ha
    rw [← tame_near (hμ i hi).2 hx hn, ← tame_near ht1 hx hn]
    apply Units.ext
    rw [(hμ i hi).1 a _ rfl, hμ1 a _ rfl, muAt_unit Ch sel mu cst P hP i hred, muAt_unit Ch sel mu cst P hP 0 hred]
  have hδ : ∀ i, i < R.m → ∀ x : kˣ, valuation k (x : k) = 1 → μ (i + 1) x = delta (μ 1) ϖ x := by
    intro i hi x hx
    rw [delta_unit _ _ hx]; exact hunit i hi x hx

  have hsq : G.σ₀ (cst.sq P) ^ 2 = ((Real.sqrt (qOf P.1) : ℝ) : ℂ) ^ 2 := by
    rw [← map_pow, hL.cst_ok.sq_sq P, map_natCast, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _),
      Complex.ofReal_natCast]
  obtain ⟨sg, hsg1, hsg2⟩ : ∃ sg : ℂ, (sg = 1 ∨ sg = -1) ∧ G.σ₀ (cst.sq P) = sg * (Real.sqrt (qOf P.1) : ℂ) := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · exact ⟨1, Or.inl rfl, by rw [h, one_mul]⟩
    · exact ⟨-1, Or.inr rfl, by rw [h, neg_one_mul]⟩
  refine ⟨⟨ϖ, hϖ, ψ, hψc, hψ1, delta (μ 1) ϖ, delta_tame ht1 ϖ, eta μ R.m (delta (μ 1) ϖ),
    eta_unram μ R.m _ hδ, sg⟩, ⟨hP, hm, hc, ?_, ?_, ?_, hsg2⟩, rfl, rfl, fun i hi => eta_mul μ R.m _ hi, hsg1⟩
  ·
    intro a ha
    show (ψ (ι a) : ℂ) = G.σ₀ (cst.psi P a)
    have hxi : IntAt P.1 G.xi0 := (hL.xiUnitAtPrime P).1
    have hx : valuation k (ι (G.xi0 * ((qOf P.1 : X.E) ^ cst.D P * a))) ≤ 1 :=
      GlobalTheory.SymBridge.ComplRes.v_le_one hc (hxi.mul ha)
    obtain ⟨i, -, hi⟩ := GlobalTheory.SymBridge.ComplRes.exists_rep hc hϖ (cst.D P) _ hx
    have hqk : ((qOf P.1 : ℕ) : k) ≠ 0 := by
      rw [← GlobalTheory.SymBridge.ComplRes.unif_eq_cast hc]; exact ϖ.ne_zero
    have hint : IntAt P.1 (G.xi0 * a - ((i : ℤ) : X.E) / (qOf P.1 : X.E) ^ cst.D P) := by
      apply GlobalTheory.SymBridge.ComplRes.intAt_of_v hc
      have e : ι (G.xi0 * ((qOf P.1 : X.E) ^ cst.D P * a)) - (i : k) =
          ι (G.xi0 * a - ((i : ℤ) : X.E) / (qOf P.1 : X.E) ^ cst.D P) * (ϖ : k) ^ cst.D P := by
        rw [GlobalTheory.SymBridge.ComplRes.unif_eq_cast hc]
        simp only [map_mul, map_sub, map_div₀, map_pow, map_intCast, map_natCast]
        push_cast
        field_simp
      rw [e, map_mul, map_pow] at hi
      have h0 : (0 : ValueGroupWithZero k) < valuation k (ϖ : k) ^ cst.D P :=
        pow_pos (zero_lt_iff.mpr (by simp)) _
      exact le_of_mul_le_mul_right (by rwa [one_mul]) h0
    rw [hψt a (i : ℤ) (cst.D P) hint, hL.weil P a (i : ℤ) ha hint]
  ·
    intro a u ha hr hu
    show ((delta (μ 1) ϖ u : ℂˣ) : ℂ) = _
    have hva : valuation k (u : k) = 1 := by
      rw [hu]; exact (GlobalTheory.SymBridge.ComplRes.v_eq_one_iff_red hc hϖ ha).mpr hr
    rw [delta_unit _ _ hva, hμ1 a u hu, muAt_unit Ch sel mu cst P hP 0 hr, unitV_inv, map_inv₀]
  ·
    intro i hi
    show ((eta μ R.m (delta (μ 1) ϖ) (i + 1) * delta (μ 1) ϖ) ϖ : ℂ) = _
    rw [eta_mul μ R.m _ hi, (hμ i hi).1 ((qOf P.1 : ℕ) : X.E) ϖ hc.unif, muAt_q Ch sel mu cst P hP i hqmem hqpos]

end GlobalTheory.TwBridgeInhab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNormOfConjFixedUnitTamePlace
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace
open IsDedekindDomain NumberField GlobalTheory.FixedUnitNorm
open scoped TensorProduct

namespace GlobalTheory.FixedUnitNorm

set_option synthInstance.maxHeartbeats 200000 in
theorem compAt_cA (D : D7) (v : Pl D) (a : AE D) : compAt D v (cA D a) = sigV D v (compAt D v a) := by
  induction a using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero, map_zero]
  | add x y hx hy => rw [RingHom.map_add, RingHom.map_add, RingHom.map_add, map_add, hx, hy]
  | tmul a m => rfl

set_option synthInstance.maxHeartbeats 400000 in
theorem tmul_algebraMap (D : D7) (v : Pl D) (c : Fv D.host.F v) (f : D.host.F) :
    c ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E f) = (algebraMap D.host.F (Fv D.host.F v) f * c) ⊗ₜ[D.host.F] (1 : D.host.E) := by
  rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def]

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in

theorem fixed_unit_norm : ∀ (D : D7) (v : Pl D) (ε : AE D), Tame D v → ε * ε = ε → cA D ε = ε → ε ∈ intAt D (· = v) →
    (∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) → ∀ u ∈ intAt D (· = v), cA D u = u →
    (∃ y ∈ intAt D (· = v), u * y = ε) → ∃ x ∈ intAt D (· = v), x * cA D x = u := by
  intro D v ε hT _ _ _ hid u hu hcu ⟨y, hy, huy⟩
  obtain ⟨w, t, n, h1, h2, h3⟩ := GlobalTheory.UnramifiedDiscriminant.exists_discr_notMem D.host.F D.host.E D.sp.cm.sig
    (GlobalTheory.AdelicU.isCMExt_host D) v (fun P hP => @hT.1 P.asIdeal P.isPrime hP)
  have hw : ∀ f : D.host.F, algebraMap D.host.F D.host.E f ≠ w := by
    intro f hf
    apply h3
    have hs : D.sp.cm.sig w = w := by rw [← hf, AlgHom.commutes]
    have e : algebraMap D.host.F D.host.E ((t : D.host.F) ^ 2 - 4 * n) = 0 := by
      rw [map_sub, map_pow, map_mul, ← h1, ← h2, hs, map_ofNat]; ring
    have e2 : ((t ^ 2 - 4 * n : 𝓞 D.host.F) : D.host.F) = 0 := by
      have := (FaithfulSMul.algebraMap_injective D.host.F D.host.E) (e.trans (map_zero _).symm)
      push_cast; exact this
    have e3 : t ^ 2 - 4 * n = 0 := RingOfIntegers.coe_eq_zero_iff.1 e2
    rw [e3]; exact v.asIdeal.zero_mem
  obtain ⟨W, hW⟩ := GlobalTheory.T.exists_integer_of_relative_trace_norm_integral D w t n h1 h2

  have hone : (1 : Fv D.host.F v ⊗[D.host.F] D.host.E) ∈ intV D v :=
    AddSubgroup.subset_closure ⟨1, (v.adicCompletionIntegers D.host.F).one_mem, 1, by simp [Algebra.TensorProduct.one_def]⟩
  have hε1 : compAt D v ε = 1 := by
    obtain ⟨z, hz, hz1⟩ := GlobalTheory.T.exists_integralAdele_atPlace_with_component D v 1 hone
    have h := congrArg (compAt D v) ((hid z).1 hz.1)
    rwa [RingHom.map_mul, hz1, mul_one] at h

  obtain ⟨a, ha, b, hb, hU⟩ := GlobalTheory.T.localIntegers_tensor_coords_prime_to_discriminant D v w t n h1 h2 h3 _ (GlobalTheory.T.adeleComponentAtFinitePlace_integral_mem_localTensor D v u hu)
  have hsig : sigV D v (compAt D v u) = compAt D v u := by rw [← compAt_cA, hcu]
  have hsw : D.sp.cm.sig w = algebraMap D.host.F D.host.E t - w := by rw [← h1]; ring
  have hb0 : b = 0 := by
    have e : sigV D v (a ⊗ₜ[D.host.F] (1 : D.host.E) + b ⊗ₜ[D.host.F] w) -
        (a ⊗ₜ[D.host.F] (1 : D.host.E) + b ⊗ₜ[D.host.F] w) = 0 := by rw [← hU, hsig, sub_self]
    have e' : (algebraMap D.host.F (Fv D.host.F v) t * b) ⊗ₜ[D.host.F] (1 : D.host.E) + (-(2 * b)) ⊗ₜ[D.host.F] w = 0 := by
      rw [← e, sigV, map_add, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.id_apply,
        map_one, hsw, TensorProduct.tmul_sub, tmul_algebraMap, TensorProduct.neg_tmul]
      rw [show (2 : Fv D.host.F v) * b = b + b by ring, TensorProduct.add_tmul]
      abel
    have := (GlobalTheory.T.completion_tensor_relativeBasis_coords_unique D v w hw _ _ e').2
    have h2b : (2 : Fv D.host.F v) * b = 0 := neg_eq_zero.1 this
    have h2ne : (2 : Fv D.host.F v) ≠ 0 := by
      intro h
      apply two_ne_zero (α := D.host.F)
      apply (algebraMap D.host.F (Fv D.host.F v)).injective
      rw [map_ofNat, map_zero]; exact h
    exact (mul_eq_zero.1 h2b).resolve_left h2ne
  rw [hb0, TensorProduct.zero_tmul, add_zero] at hU
  obtain ⟨a', ha', b', hb', hY⟩ := GlobalTheory.T.localIntegers_tensor_coords_prime_to_discriminant D v w t n h1 h2 h3 _ (GlobalTheory.T.adeleComponentAtFinitePlace_integral_mem_localTensor D v y hy)
  have haa : a * a' = 1 := by
    have e : compAt D v u * compAt D v y = 1 := by rw [← RingHom.map_mul, huy, hε1]
    rw [hU, hY, mul_add, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul] at e
    have e' : (a * a' - 1) ⊗ₜ[D.host.F] (1 : D.host.E) + (a * b') ⊗ₜ[D.host.F] w = 0 := by
      rw [TensorProduct.sub_tmul, ← Algebra.TensorProduct.one_def, ← e]; abel
    exact sub_eq_zero.1 (GlobalTheory.T.completion_tensor_relativeBasis_coords_unique D v w hw _ _ e').1
  let A : v.adicCompletionIntegers D.host.F := ⟨a, ha⟩
  have hAu : IsUnit A := ⟨⟨A, ⟨a', ha'⟩, Subtype.ext haa, Subtype.ext (by rw [mul_comm]; exact haa)⟩, rfl⟩
  have hD : IsUnit (algebraMap (𝓞 D.host.F) (v.adicCompletionIntegers D.host.F) t ^ 2 -
      4 * algebraMap (𝓞 D.host.F) (v.adicCompletionIntegers D.host.F) n) := by
    have := (GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff v _).2 h3
    rwa [map_sub, map_pow, map_mul, map_ofNat] at this
  obtain ⟨r, s, hrs⟩ := GlobalTheory.T.exists_binary_quadratic_eq_unit_of_disc_isUnit D.host.F v _ _ A hD hAu

  set x' : Fv D.host.F v ⊗[D.host.F] D.host.E := (r : Fv D.host.F v) ⊗ₜ[D.host.F] (1 : D.host.E) + (s : Fv D.host.F v) ⊗ₜ[D.host.F] w
  have hx'i : x' ∈ intV D v := by
    refine AddSubgroup.add_mem _ (AddSubgroup.subset_closure ⟨r, r.2, 1, by simp⟩)
      (AddSubgroup.subset_closure ⟨s, s.2, W, by rw [hW]⟩)
  have hcoe : ∀ c : 𝓞 D.host.F, ((algebraMap (𝓞 D.host.F) (v.adicCompletionIntegers D.host.F) c : v.adicCompletionIntegers D.host.F) : Fv D.host.F v) =
      algebraMap D.host.F (Fv D.host.F v) c := fun c => rfl
  have hnorm : x' * sigV D v x' = compAt D v u := by
    have hrs' : (r : Fv D.host.F v) ^ 2 + algebraMap D.host.F (Fv D.host.F v) t * r * s +
        algebraMap D.host.F (Fv D.host.F v) n * (s : Fv D.host.F v) ^ 2 = a := by
      have := congrArg (fun q : v.adicCompletionIntegers D.host.F => (q : Fv D.host.F v)) hrs
      exact this
    have e1 : sigV D v x' = (r : Fv D.host.F v) ⊗ₜ[D.host.F] (1 : D.host.E) + (s : Fv D.host.F v) ⊗ₜ[D.host.F] D.sp.cm.sig w := by
      simp only [x', sigV, map_add, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]
    rw [e1, hU]
    simp only [x', add_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    have e2 : ((s : Fv D.host.F v) * r) ⊗ₜ[D.host.F] w = ((r : Fv D.host.F v) * s) ⊗ₜ[D.host.F] w := by rw [mul_comm]
    rw [e2, h2, tmul_algebraMap, hsw, TensorProduct.tmul_sub, tmul_algebraMap]
    have key : ∀ P Q R S : Fv D.host.F v ⊗[D.host.F] D.host.E, P + S + (Q - S + R) = P + Q + R := fun P Q R S => by abel
    rw [key, ← TensorProduct.add_tmul, ← TensorProduct.add_tmul]
    congr 1
    rw [← hrs']; ring
  obtain ⟨x, hxi, hxc⟩ := GlobalTheory.T.exists_integralAdele_atPlace_with_component D v x' hx'i
  refine ⟨x, hxi, ?_⟩
  have hx0 := (mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere D _ x).1 hxi.1
  have hu0 := (mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere D _ u).1 hu.1
  rw [← sub_eq_zero]
  apply CMAdele_eq_zero_of_infinite_and_finite_components_zero
  · rw [RingHom.map_sub, RingHom.map_mul, hx0.1, zero_mul, hu0.1, sub_zero]
  · intro w'
    by_cases hw' : w' = v
    · subst hw'; rw [RingHom.map_sub, RingHom.map_mul, compAt_cA, hxc, hnorm, sub_self]
    · rw [RingHom.map_sub, RingHom.map_mul, hx0.2 w' hw', zero_mul, hu0.2 w' hw', sub_zero]

end GlobalTheory.FixedUnitNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNsmulMemHomLatticeOfIntegralFrameCoordsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nsmul_mem_homLattice_of_integral_frameCoords : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (S T : HSp D) (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∃ N : ℕ, 0 < N ∧ ∀ t : WO S T, IsHalf p.e t → (∀ i j, rd α β t i j ∈ 𝒪[k]) → N • t ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v) := by
  first | exact @GlobalTheory.FinPl.exists_nsmul_mem_latO_of_rd_int | exact GlobalTheory.FinPl.exists_nsmul_mem_latO_of_rd_int | (intros; apply GlobalTheory.FinPl.exists_nsmul_mem_latO_of_rd_int <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRationalWittFlagCoordinatesOfMemUnipotent
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.RatCoord

set_option maxHeartbeats 1000000 in

theorem coords_rat {D : D7} {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (c' : skewA D ρ) (b' : Mx D ρ V₀.rank)
    (u : GL (Fin ρ) (AE D)) (hQ : d.nC c' * (d.nB b' * d.levi u) ∈ GQ V) :
    c'.1 ∈ ratMx D ρ ρ ∧ b' ∈ ratMx D ρ V₀.rank ∧ u.1 ∈ ratMx D ρ ρ ∧ (u⁻¹).1 ∈ ratMx D ρ ρ := by
  generalize hg : d.nC c' * (d.nB b' * d.levi u) = g at hQ
  have hM : mt V g ∈ ratMx D V.rank V.rank := (mem_GQ_iff V g).1 hQ
  have hM' : mt V g⁻¹ ∈ ratMx D V.rank V.rank := (mem_GQ_iff V g⁻¹).1 (inv_mem hQ)
  have hX : mt V g ⬝ d.jX = d.jX ⬝ u.1 := by
    rw [← hg]; simp only [mt_mul, Matrix.mul_assoc, d.levi_jX, cancel₂ (d.nB_jX _), cancel₂ (d.nC_jX _)]
  have hX' : mt V g⁻¹ ⬝ d.jX = d.jX ⬝ (u⁻¹).1 := by
    calc mt V g⁻¹ ⬝ d.jX = mt V g⁻¹ ⬝ (d.jX ⬝ u.1 ⬝ (u⁻¹).1) := by
          rw [Matrix.mul_assoc d.jX, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      _ = d.jX ⬝ (u⁻¹).1 := by rw [← hX, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul]
  have h0 : mt V g ⬝ d.j0 = d.j0 + d.jX ⬝ b' := by
    rw [← hg]; simp only [mt_mul, Matrix.mul_assoc, d.wittDecomp_levi_inclAnisotropic, d.nB_j0, Matrix.mul_add, cancel₂ (d.nC_jX _), d.nC_j0]
  have hY : d.pX ⬝ (mt V g ⬝ d.jY) = (c'.1 - half D • (b' ⬝ plus V₀ b')) ⬝ adj (u⁻¹).1 := by
    rw [← hg, mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, d.levi_jY, cancel₂ (d.nB_jY _)]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, cancel₂ (d.nC_jY _),
      cancel₂ (d.nC_j0 _), cancel₂ (d.nC_jX _), cancel₂ d.pX_jY, cancel₂ d.pX_jX, cancel₂ d.pX_j0, d.pX_jY, d.pX_jX,
      d.pX_j0, Matrix.one_mul, Matrix.zero_mul, zero_add, zero_sub, sub_zero]
  have hu1 : u.1 ∈ ratMx D ρ ρ := by
    have e : d.pX ⬝ (mt V g ⬝ d.jX) = u.1 := by rw [hX, cancel₂ d.pX_jX, Matrix.one_mul]
    rw [← e]; exact ratMx_mul (rat_mem _) (ratMx_mul hM (rat_mem _))
  have hu2 : (u⁻¹).1 ∈ ratMx D ρ ρ := by
    have e : d.pX ⬝ (mt V g⁻¹ ⬝ d.jX) = (u⁻¹).1 := by rw [hX', cancel₂ d.pX_jX, Matrix.one_mul]
    rw [← e]; exact ratMx_mul (rat_mem _) (ratMx_mul hM' (rat_mem _))
  have hb : b' ∈ ratMx D ρ V₀.rank := by
    have e : d.pX ⬝ (mt V g ⬝ d.j0) = b' := by
      rw [h0, Matrix.mul_add, d.pX_j0, zero_add, cancel₂ d.pX_jX, Matrix.one_mul]
    rw [← e]; exact ratMx_mul (rat_mem _) (ratMx_mul hM (rat_mem _))
  have hc : c'.1 = d.pX ⬝ (mt V g ⬝ d.jY) ⬝ adj u.1 + half D • (b' ⬝ plus V₀ b') := by
    have e : adj (u⁻¹).1 ⬝ adj u.1 = 1 := by rw [← adj_mul, Units.mul_inv, adj_one]
    rw [hY, Matrix.mul_assoc, e, Matrix.mul_one, sub_add_cancel]
  refine ⟨?_, hb, hu1, hu2⟩
  rw [hc]
  exact add_mem (ratMx_mul (ratMx_mul (rat_mem _) (ratMx_mul hM (rat_mem _))) (ratMx_adj hu1))
    (ratMx_smul _ (ratMx_mul hb (ratMx_mul (rat_mem _) (ratMx_adj hb))))

theorem rat_coords_of_mem_flagN : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (γ : GA D V), γ ∈ GQ V → γ ∈ flagN d → ∃ (c : skewA D ρ) (b : Mx D ρ V₀.rank) (u : UX D ρ), γ = d.nC c * (d.nB b * d.levi u.1) ∧ c.1 ∈ ratMx D ρ ρ ∧ b ∈ ratMx D ρ V₀.rank ∧ u ∈ UXQ D ρ := by
  intro D V V₀ ρ d γ hQ hN
  obtain ⟨u, hu, b, c, rfl⟩ := ((GlobalTheory.T.flag_unipotent_fourier_jacobi_group_structure D V V₀ ρ d).1 γ).1 hN
  have hγ : d.levi u * (d.nB b * d.nC c) = d.nC (skewConj u.1 c) * (d.nB (u.1 ⬝ b) * d.levi u) := by
    rw [← mul_assoc, d.levi_mul_nB, mul_assoc, d.levi_mul_nC, ← mul_assoc, ← d.nC_mul_nB, mul_assoc]
  rw [hγ] at hQ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := coords_rat d _ _ u hQ
  exact ⟨skewConj u.1 c, u.1 ⬝ b, ⟨u, hu⟩, rfl, h1, h2, h3, h4⟩

end GlobalTheory.RatCoord

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsScalarPreservesIntegralMatricesSubstStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.LocOm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_scalar_preservesIntegralMatricesSubst : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (gk : GL Y' k) (hk : GL Y k), ∃ c : kˣ, ∀ zk : GL Y k, (zk : Matrix Y Y k) = (c : k) • (1 : Matrix Y Y k) → Enl gk (hk * zk⁻¹) ∧ Enl (1 : GL Y' k) zk⁻¹ := by
  first | exact @GlobalTheory.LocOm.enl_scalar_denominator | exact GlobalTheory.LocOm.enl_scalar_denominator | (intros; apply GlobalTheory.LocOm.enl_scalar_denominator <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSchwartzVectorField
section
noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSch.CentreSchwartz

variable {D : D7} {θ : InfFam D} {V : HSp D} {n : ℕ} {τ : D.what₂.Tau}

def mulAt (τ : D.what₂.Tau) {m : ℕ} (n : ℕ) (Y : Matrix (Fin m) (Fin m) ℂ) :
    (D.what₂.Tau → Fin m → Fin n → ℂ) →ₗ[ℝ] (D.what₂.Tau → Fin m → Fin n → ℂ) where
  toFun z := fun τ' i j => if τ' = τ then ∑ k, Y i k * z τ' k j else 0
  map_add' z z' := by
    funext τ' i j
    by_cases h : τ' = τ <;> simp [h, mul_add, Finset.sum_add_distrib]
  map_smul' c z := by
    funext τ' i j
    by_cases h : τ' = τ <;> simp [h, Finset.mul_sum, mul_left_comm]

variable (θ V n) in

def Induced (T : (GA D V → ℂ) → GA D V → ℂ) : Prop :=
  ∀ Φ ∈ schwartzA θ V.rank n, ∃ Ψ ∈ schwartzA θ V.rank n,
    ∀ x : Mx D V.rank n, T (fun h => Φ (mt V h⁻¹ ⬝ x)) = fun h => Ψ (mt V h⁻¹ ⬝ x)

theorem Induced.sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (A : ι → (GA D V → ℂ) → GA D V → ℂ)
    (h : ∀ i, Induced θ V n (A i)) : Induced θ V n fun f => ∑ i ∈ s, c i • A i f := by
  intro Φ hΦ
  choose Ψ m e using fun i => h i Φ hΦ
  refine ⟨∑ i ∈ s, c i • Ψ i, Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (m i), fun x => ?_⟩
  funext g
  simp only [e, Finset.sum_apply, Pi.smul_apply]

end GlobalTheory.RegSch.CentreSchwartz

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSplitLocalSupportedScalarComponentStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.LocOm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_splitLocal_supported_scalar_component : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (V : HSp D) (Z : Type) [Fintype Z] [DecidableEq Z] (F : Frame k V.rank Z) (c : kˣ) (zk : GL Z k), (zk : Matrix Z Z k) = (c : k) • (1 : Matrix Z Z k) → ∃ z : GA D V, p.IsLoc F z zk := by
  first | exact @GlobalTheory.LocScalar.exists_isLoc_scalar | exact GlobalTheory.LocScalar.exists_isLoc_scalar | (intros; apply GlobalTheory.LocScalar.exists_isLoc_scalar <;> assumption)
end

