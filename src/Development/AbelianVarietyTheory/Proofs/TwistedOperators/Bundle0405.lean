import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0394
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0320
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0019
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0220
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0209
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0190
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0327
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0338
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0336
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0178
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0195
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0205
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0234
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0198
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0202
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0201
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0223
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0391
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0275
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0197
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0390
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1425
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0028
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumLocalSphericalZetaUnramified
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LocZeta

theorem hasSum_quot_of_equiv {G H : Type} [Group G] [Group H] (e : G ≃* H) {K : Subgroup G} {K' : Subgroup H}
    (hK : ∀ g, g ∈ K ↔ e g ∈ K') {f : G → ℂ} (hf : ∀ g, ∀ k ∈ K, f (g * k) = f g) {s : ℂ}
    (h : HasSum (fun b : H ⧸ K' => f (e.symm b.out)) s) : HasSum (fun a : G ⧸ K => f a.out) s :=
  GlobalTheory.T.hasSum_quotient_of_hasSum_mulEquiv_quotient G H e K K' hK f hf s h

theorem kerGL_mul_right {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {r N : ℕ} {z : ℂˣ}
    {φ : GL (Fin r) (w.adicCompletion E) → ℂ} (hφ : KerGL w N z φ) (g k : GL (Fin r) (w.adicCompletion E))
    (hk : k ∈ KGL w r) : φ (g * k) = φ g :=
  GlobalTheory.T.sphericalZetaKernelGL_right_invariant_integral E w r N z φ hφ g k hk

theorem kerU_mul_right {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)}
    {σ : w.adicCompletion E →+* w.adicCompletion E} {ϖ : w.adicCompletion E} {q r N : ℕ} (hU : IsUnramInv ϖ σ q)
    {z : ℂˣ} {φ : GU σ r → ℂ} (hφ : KerU ϖ q N z φ) (g k : GU σ r) (hk : k ∈ KU σ r) : φ (g * k) = φ g := by
  obtain ⟨d, t, -, ht, k₁, h₁, k₂, h₂, rfl⟩ := cartanU hU g
  rw [mul_assoc (k₁ * t), hφ d t ht k₁ h₁ _ (mul_mem h₂ hk), hφ d t ht k₁ h₁ k₂ h₂]

theorem conj_qpow (q : ℕ) (x : ℝ) : starRingEnd ℂ ((q : ℂ) ^ (x : ℂ)) = (q : ℂ) ^ (x : ℂ) := by
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.conj_ofReal]

theorem kerGL_conj {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {r N : ℕ} {z : ℂˣ}
    {φ : GL (Fin r) (w.adicCompletion E) → ℂ} (hφ : KerGL w N z φ) :
    KerGL w N (star z) (fun g => starRingEnd ℂ (φ g)) := by
  intro ϖ hϖ d t ht k₁ h₁ k₂ h₂
  show starRingEnd ℂ (φ (k₁ * t * k₂)) = _
  rw [hφ ϖ hϖ d t ht k₁ h₁ k₂ h₂, map_mul, map_zpow₀]
  have := conj_qpow (qV E w) (-((N : ℝ) / 2) * ((∑ i, |d i| : ℤ) : ℝ))
  simp only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_natCast,
    Complex.ofReal_intCast, Complex.ofReal_ofNat] at this
  rw [this]
  rfl

theorem kerU_conj {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {r : ℕ} {ϖ : L}
    {q N : ℕ} {z : ℂˣ} {φ : GU σ r → ℂ} (hφ : KerU ϖ q N z φ) :
    KerU ϖ q N (star z) (fun g => starRingEnd ℂ (φ g)) := by
  intro d t ht k₁ h₁ k₂ h₂
  show starRingEnd ℂ (φ (k₁ * t * k₂)) = _
  rw [hφ d t ht k₁ h₁ k₂ h₂]
  simp [map_zpow₀]

theorem quadSign_eq (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    (∀ w w' : HeightOneSpectrum (𝓞 D.host.E), w ≠ w' → (∀ u, u.under (𝓞 D.host.F) = v ↔ u = w ∨ u = w') →
      quadSign D v = 1) ∧
    (∀ w : HeightOneSpectrum (𝓞 D.host.E), (∀ u, u.under (𝓞 D.host.F) = v ↔ u = w) → quadSign D v = -1) :=
  GlobalTheory.T.unramifiedQuadraticCharSign_split_eq_one_inert_eq_neg D v

theorem value_split (D : D7) (B : Fam D.host.E) (m : HeightOneSpectrum (𝓞 D.host.E) → ℂˣ)
    (v : HeightOneSpectrum (𝓞 D.host.F)) (w w' : HeightOneSpectrum (𝓞 D.host.E)) (hne : w ≠ w')
    (hall : ∀ u, u.under (𝓞 D.host.F) = v ↔ u = w ∨ u = w') (hN : Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal)
    (hN' : Ideal.absNorm w'.asIdeal = Ideal.absNorm v.asIdeal) (hB' : B w' = (B w).map (·⁻¹))
    (hs : (B w).map star = (B w).map (·⁻¹)) (hm : m w * m w' = 1) (hm1 : ‖(m w : ℂ)‖ = 1) (hq : quadSign D v = 1) :
    starRingEnd ℂ (LvTw B m v ((1 + (D.R.t : ℂ)) / 2) / (dLoc D v : ℂ)) =
      eulerFac ((B w).map (star (m w) * ·)) (npow w (-((1 + (D.R.t : ℂ)) / 2))) *
        eulerFac ((B w).map fun β => (star (m w) * β)⁻¹) (npow w (-((1 + (D.R.t : ℂ)) / 2))) *
        ∏ i ∈ Finset.Ioc D.R.t (D.R.r + D.R.t), (1 - ((qV D.host.E w : ℂ) ^ i)⁻¹) :=
  GlobalTheory.T.conj_localTwistedLFactor_ratio_split_eq_zetaSum D B m v w w' hne hall hN hN' hB' hs hm hm1 hq

theorem value_inert (D : D7) (B : Fam D.host.E) (m : HeightOneSpectrum (𝓞 D.host.E) → ℂˣ)
    (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hall : ∀ u, u.under (𝓞 D.host.F) = v ↔ u = w) (hN : Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ^ 2)
    (hs : (B w).map star = B w) (hm : (m w : ℂ) = (-1) ^ D.R.nV) (hq : quadSign D v = -1) :
    starRingEnd ℂ (LvTw B m v ((1 + (D.R.t : ℂ)) / 2) / (dLoc D v : ℂ)) =
      eulerFac (B w) (((star (m w) : ℂˣ) : ℂ) * ((qV D.host.F v : ℂ) ^ (D.R.t + 1))⁻¹) *
        ∏ j ∈ Finset.range D.R.r,
          (1 - (-(qV D.host.F v : ℂ)) ^ j * (((star (m w) : ℂˣ) : ℂ) * ((qV D.host.F v : ℂ) ^ (D.R.r + D.R.t))⁻¹)) :=
  GlobalTheory.T.conj_localTwistedLFactor_ratio_inert_eq_zetaSum D B m v w hall hN hs hm hq

set_option maxHeartbeats 1000000 in

theorem hasSum_localZeta : GlobalTheory.Published.UnramifiedDoublingGL → ∀ (D : D7) (V : HSp D), V.rank = D.R.r → ∀ (χ : (AE D)ˣ →* Circle), Formalism.L2.Theta.ResEta D χ D.R.nV → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)), (∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → UnrAt χ w) → ∀ φ : Gv V v → ℂ, IsLocKer V D.R.nV (val χ) v φ → ∀ (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (Gv V v) X), IsUnitarisable ρ → ∀ (x : X) (B : Fam D.host.E), (∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsParamVec D.sp.cm.sig V.gram (frameLat V) h ρ x (B w) ∧ ∀ β ∈ B w, ‖(β : ℂ)‖ ≤ ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (((D.R.r : ℝ) - 1) / 2)) → ∀ ℓ : X →ₗ[ℂ] ℂ, (∃ C : ℝ, ∀ g, ‖ℓ (ρ g x)‖ ≤ C) → HasSum (fun a : Gv V v ⧸ Kv V v => φ a.out * starRingEnd ℂ (ℓ (ρ a.out x))) (LvTw B (val χ) v ((1 + (D.R.t : ℂ)) / 2) / (dLoc D v : ℂ) * starRingEnd ℂ (ℓ x)) := by
  intro hG D V hr χ hχ v hU φ hφ X _ _ ρ hρu x B hB ℓ hℓ
  classical
  have hc := isCMExt_host D
  have h2 : Module.finrank D.host.F D.host.E = 2 := hc.2.2.1
  have hχ' := (resEta_iff χ _).1 hχ
  have hJ := GlobalTheory.Mem.VolExists.isHermND D.sp.cm V
  have hd := SelfDual.isSelfDualAt_frameLat D V v
  have hrt : V.rank ≤ D.R.t := by
    have := D.R.rank_add_five_le
    rw [hr]
    unfold Ranks.r
    omega
  have hnV : D.R.nV = V.rank + D.R.t := by rw [hr]; rfl
  obtain ⟨w, h⟩ : ∃ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v := by
    have := v.isMaximal
    obtain ⟨Q, hQ, hl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal
    exact ⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hl.over.symm⟩
  obtain ⟨C, hC⟩ := hℓ
  have hfix : ∀ k ∈ Kv V v, ρ k x = x := GlobalTheory.LGrp.mem_fixed.1 (hB w h).1.mem_fixed
  have hnz : ‖(((star (val χ w) : ℂˣ)) : ℂ)‖ = 1 := by
    rw [Units.coe_star]
    simpa using norm_val χ w
  suffices H : HasSum (fun a : Gv V v ⧸ Kv V v => starRingEnd ℂ (φ a.out) * ℓ (ρ a.out x))
      (starRingEnd ℂ (LvTw B (val χ) v ((1 + (D.R.t : ℂ)) / 2) / (dLoc D v : ℂ)) * ℓ x) by
    have := H.map (starRingEnd ℂ) Complex.continuous_conj
    simpa [Function.comp_def] using this
  rcases (hB w h).1 with ⟨hv, e, he, hsat⟩ | ⟨hw, c, ϖ, e, α, hUI, he, hsat, hBw⟩
  · obtain ⟨w', hne, hall, hN, hN', -⟩ := SplitChart.exists_conj_place hc h hv
    have h' : w'.under (𝓞 D.host.F) = v := (hall w').2 (Or.inr rfl)
    have hB' : B w' = (B w).map (·⁻¹) :=
      ConjPlace.eq_map_inv_of_isParamVec hc hJ hd hne (hB w h).1 (hB w' h').1
    have hm : val χ w * val χ w' = 1 := ResEta.val_mul_val h2 hχ' hne h h' (hU w h) (hU w' h')
    have hs : (B w).map star = (B w).map (·⁻¹) :=
      GlobalTheory.T.satakeParameterGL_star_eq_inv_of_unitarisable _ w _ _ _ x (B w) (hρu.imp fun _ hb => ⟨hb.1, hb.2.1, fun g => hb.2.2 (e.symm g)⟩) hsat
    have hk := kerGL_conj ((hφ w h).1 hv e he)
    rw [hnV] at hk
    have hbd : ∀ β ∈ B w, ‖(β : ℂ)‖ ≤ (qV D.host.E w : ℝ) ^ (((V.rank : ℝ) - 1) / 2) ∧
        ‖((β⁻¹ : ℂˣ) : ℂ)‖ ≤ (qV D.host.E w : ℝ) ^ (((V.rank : ℝ) - 1) / 2) := by
      intro β hβ
      rw [hr]
      refine ⟨(hB w h).2 β hβ, ?_⟩
      have := (hB w' h').2 β⁻¹ (hB' ▸ Multiset.mem_map_of_mem _ hβ)
      have e2 : (qV D.host.E w : ℝ) = ((Ideal.absNorm w'.asIdeal : ℕ) : ℝ) := by
        rw [hN', ← hN]; rfl
      rw [e2]
      exact this
    have hsum := GlobalTheory.T.unramified_zeta_sum_GL_cosets hG D.host.E w V.rank D.R.t hrt (star (val χ w)) _ hnz hk X
      (ρ.comp e.symm.toMonoidHom) x (B w) hsat hbd ℓ ⟨C, fun g => hC _⟩
    rw [value_split D B (val χ) v w w' hne hall hN hN' hB' hs hm (norm_val χ w) ((quadSign_eq D v).1 w w' hne hall),
      ← hr]
    refine hasSum_quot_of_equiv e he.2 (f := fun g => starRingEnd ℂ (φ g) * ℓ (ρ g x)) ?_ hsum
    intro g k hk'
    have e1 : φ (g * k) = φ g := by
      have := kerGL_mul_right ((hφ w h).1 hv e he) (e g) (e k) ((he.2 k).1 hk')
      simpa using this
    show starRingEnd ℂ (φ (g * k)) * ℓ (ρ (g * k) x) = starRingEnd ℂ (φ g) * ℓ (ρ g x)
    rw [e1, map_mul, Module.End.mul_apply, hfix k hk']
  · have hall := InertChart.under_eq_iff hw
    have hNw := InertChart.absNorm_eq h2 hw
    have hval : val χ w = (-1) ^ D.R.nV := ResEta.val_of_isInertAt h2 hχ' hw (hU w h)
    have hk := kerU_conj ((hφ w h).2 hw c ϖ e hUI he)
    rw [hnV] at hk
    have hstarB : (B w).map star = B w := by
      rw [hBw]
      have := bcParam_eq_of_satU_eq (α := fun i => star (α i)) hUI
        (GlobalTheory.T.unitarySatakeTransform_star_parameter_eq_of_unitarisable _ ϖ c _ _ hUI _ _ x α (hρu.imp fun _ hb => ⟨hb.1, hb.2.1, fun g => hb.2.2 (e.symm g)⟩) hsat)
      conv_rhs => rw [← this]
      simp [bcParam, star_inv, Function.comp_def]
    have htb : GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.TrivialBound (qV D.host.F v) V.rank α := by
      have hq : ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) = (qV D.host.F v : ℝ) ^ 2 := by
        rw [hNw]; push_cast; rfl
      have hQ : (0 : ℝ) < (qV D.host.F v : ℝ) ^ 2 := by
        have := one_lt_absNorm v
        have : (0 : ℝ) < (qV D.host.F v : ℝ) := by
          show (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)
          exact_mod_cast (by omega : 0 < Ideal.absNorm v.asIdeal)
        positivity
      intro i
      have h1 := (hB w h).2 (α i) (by rw [hBw]; simp [bcParam])
      have h3 := (hB w h).2 (α i)⁻¹ (by rw [hBw]; simp [bcParam])
      rw [hq, ← hr] at h1 h3
      refine ⟨?_, h1⟩
      rw [Real.rpow_neg hQ.le]
      rw [Units.val_inv_eq_inv_val, norm_inv] at h3
      exact inv_le_of_inv_le₀ (norm_pos_iff.2 (α i).ne_zero) h3
    have hsum := GlobalTheory.T.hasSum_unramifiedZetaSum_unitary_inert _ ϖ c (qV D.host.F v) V.rank D.R.t hUI hrt (star (val χ w)) _ hnz hk X
      (ρ.comp e.symm.toMonoidHom) x α hsat htb ℓ ⟨C, fun g => hC _⟩
    rw [value_inert D B (val χ) v w hall hNw hstarB (by rw [hval]; push_cast; rfl) ((quadSign_eq D v).2 w hall), hBw, ← hr]
    refine hasSum_quot_of_equiv e he.2.2 (f := fun g => starRingEnd ℂ (φ g) * ℓ (ρ g x)) ?_ hsum
    intro g k hk'
    have e1 : φ (g * k) = φ g := by
      have := kerU_mul_right hUI ((hφ w h).2 hw c ϖ e hUI he) (e g) (e k) ((he.2.2 k).1 hk')
      simpa using this
    show starRingEnd ℂ (φ (g * k)) * ℓ (ρ (g * k) x) = starRingEnd ℂ (φ g) * ℓ (ρ g x)
    rw [e1, map_mul, Module.End.mul_apply, hfix k hk']

end GlobalTheory.LocZeta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianThetaLevelGroupStabilizesSelfDualLattic
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevKFrame

theorem levK_frame : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (Lv : GlobalTheory.SW.Level C.X) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ βT : GL (Fin T.rank) (Lev.EAf D), Formalism.L2.DIV.IsFrame βT ΛT → ∀ Pg : Finset (Formalism.L2.DIV.Pl D.host.E), (∀ PP ∈ Pg, Lv.𝔪 ≤ conjI PP.asIdeal) → (∀ κ ∈ Lv.J, ∀ κ' : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E), κ'.map (Ideal.Quotient.mk Lv.𝔪) = (κ : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E ⧸ Lv.𝔪)) → ∀ PP ∈ Pg, ∀ i j, κ' i j - (1 : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E)) i j ∈ conjI PP.asIdeal) → ∀ (k : GA D T) (κ : Lv.J), C.LevK Lv k κ → Lev.finE T k ∈ Formalism.L2.DIV.St βT ∧ ∀ PP ∈ Pg, Formalism.L2.DIV.redFn βT PP (Lev.finE T k) = 1 := by
  intro D S T C Lv ΛT hsd hAA βT hfr Pg hPg hJ k κ hk
  obtain ⟨-, hmov, κ', hκ', hc⟩ := hk
  have hmovT := GlobalTheory.T.latticeTransport_of_polarisationIdealTimesLattice D C.X.Λ ΛT (fmt T k) hAA hmov
  have hSt := GlobalTheory.T.finiteAdelic_mem_frameStabilizer_of_latticeTransport D T ΛT βT hfr k hmovT
  refine ⟨hSt, fun PP hPP => ?_⟩
  obtain ⟨PP', hPP', hcj⟩ := GlobalTheory.T.exists_conjugatePlace_cmField D PP
  have hI : ∀ i j, κ' i j - (1 : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E)) i j ∈ PP'.asIdeal := by
    rw [hPP']; exact hJ κ κ.2 κ' hκ' PP hPP
  have h1 := GlobalTheory.T.latticeTransport_congruence_of_frameVectors D C.X.Λ Lv.β Lv.𝔪 PP'.asIdeal Lv.β_mem Lv.β_span (hPP' ▸ hPg PP hPP) (fmt T k) κ' hI hmov hc
  have h2 := GlobalTheory.T.mulVec_sub_mem_latticeCompletion_of_lattice D C.X.Λ (PP'.asIdeal • C.X.Λ) (fmt T k) h1
  obtain ⟨b, hb, h3⟩ := GlobalTheory.T.congruenceModPrime_of_polarisationIdealTimesLattice D C.X.Λ ΛT PP'.asIdeal PP'.isPrime hAA (fmt T k) h2
  have h4 := GlobalTheory.T.lattice_reduction_eq_one_of_completion_congruence D T ΛT βT hfr k hSt PP' b hb h3
  exact GlobalTheory.T.reductionTrivial_of_conjugatePlace_selfDual D T ΛT hsd βT hfr k hSt PP PP' hcj h4

end GlobalTheory.LevKFrame

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfinitePartEqZeroOfIsHalfIdempotentSumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infinitePart_eq_zero_of_isHalf_idempotentSum : ∀ {D : D7} (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P → ∀ {m n : ℕ} (y : Mx D m n), (IsHalf e y ∨ IsHalf (cA D e) y) → y.map (infPart D) = 0 := by
  first | exact @GlobalTheory.IdemHalf.halfFin | exact GlobalTheory.IdemHalf.halfFin | (intros; apply GlobalTheory.IdemHalf.halfFin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralBlocksLeftInverseIsUnitDetSplitPlace
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

namespace GlobalTheory

theorem integralBlocks_leftInverse_isUnit_det : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d : ℕ} (v : Pl F) (π : AE F E →+* Fv F v) (b : GL (Fin d) (Fv F v))
  (g h : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)), h * g = 1 →
  (∀ i j, (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * ((g).toBlocks₁₁).map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) →
  (∀ i j, (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * ((g).toBlocks₁₂).map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) →
  (∀ i j, (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * ((g).toBlocks₂₁).map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) →
  (∀ i j, (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * ((g).toBlocks₂₂).map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) →
  (∀ i j, (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * ((h).toBlocks₁₁).map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) →
  (∀ i j, (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * ((h).toBlocks₁₂).map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) →
  (∀ i j, (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * ((h).toBlocks₂₁).map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) →
  (∀ i j, (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * ((h).toBlocks₂₂).map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) →
  ∃ G : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (v.adicCompletionIntegers F), G.map (fun x => (x : Fv F v)) = Matrix.fromBlocks (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (g).toBlocks₁₁.map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (g).toBlocks₁₂.map π * (b : Matrix (Fin d) (Fin d) (Fv F v)))
      (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (g).toBlocks₂₁.map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (g).toBlocks₂₂.map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) ∧ IsUnit G.det := by
  intro F E _ _ _ _ _ d v π b g h hhg g11 g12 g21 g22 h11 h12 h21 h22
  classical
  set Bi : Matrix (Fin d) (Fin d) (Fv F v) := ((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) with hBi
  set Bm : Matrix (Fin d) (Fin d) (Fv F v) := (b : Matrix (Fin d) (Fin d) (Fv F v)) with hBm
  have hbb : Bm * Bi = 1 := by
    simp only [hBi, hBm]
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hbb' : Bi * Bm = 1 := by
    simp only [hBi, hBm]
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have key : ∀ x : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E),
      Matrix.fromBlocks (Bi * x.toBlocks₁₁.map π * Bm) (Bi * x.toBlocks₁₂.map π * Bm)
        (Bi * x.toBlocks₂₁.map π * Bm) (Bi * x.toBlocks₂₂.map π * Bm)
      = Matrix.fromBlocks Bi 0 0 Bi * x.map π * Matrix.fromBlocks Bm 0 0 Bm := by
    intro x
    have hx : x.map π = Matrix.fromBlocks (x.toBlocks₁₁.map π) (x.toBlocks₁₂.map π)
        (x.toBlocks₂₁.map π) (x.toBlocks₂₂.map π) := by
      rw [← Matrix.fromBlocks_map, Matrix.fromBlocks_toBlocks]
    rw [hx, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp
  have hprod : (Matrix.fromBlocks Bi 0 0 Bi * h.map π * Matrix.fromBlocks Bm 0 0 Bm) *
      (Matrix.fromBlocks Bi 0 0 Bi * g.map π * Matrix.fromBlocks Bm 0 0 Bm) = 1 := by
    have hBB : Matrix.fromBlocks Bm 0 0 Bm * Matrix.fromBlocks Bi 0 0 Bi = (1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (Fv F v)) := by
      rw [Matrix.fromBlocks_multiply]; simp [hbb]
    have hBB' : Matrix.fromBlocks Bi 0 0 Bi * Matrix.fromBlocks Bm 0 0 Bm = (1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (Fv F v)) := by
      rw [Matrix.fromBlocks_multiply]; simp [hbb']
    have hhg' : h.map π * g.map π = 1 := by
      rw [← Matrix.map_mul, hhg, Matrix.map_one _ (map_zero π) (map_one π)]
    calc (Matrix.fromBlocks Bi 0 0 Bi * h.map π * Matrix.fromBlocks Bm 0 0 Bm) *
          (Matrix.fromBlocks Bi 0 0 Bi * g.map π * Matrix.fromBlocks Bm 0 0 Bm)
        = Matrix.fromBlocks Bi 0 0 Bi * h.map π * (Matrix.fromBlocks Bm 0 0 Bm *
          Matrix.fromBlocks Bi 0 0 Bi) * g.map π * Matrix.fromBlocks Bm 0 0 Bm := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hBB, Matrix.mul_one, Matrix.mul_assoc (Matrix.fromBlocks Bi 0 0 Bi), hhg', Matrix.mul_one, hBB']

  let G : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (v.adicCompletionIntegers F) := fun i j =>
    match i, j with
    | Sum.inl i, Sum.inl j => ⟨_, g11 i j⟩
    | Sum.inl i, Sum.inr j => ⟨_, g12 i j⟩
    | Sum.inr i, Sum.inl j => ⟨_, g21 i j⟩
    | Sum.inr i, Sum.inr j => ⟨_, g22 i j⟩
  let H : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (v.adicCompletionIntegers F) := fun i j =>
    match i, j with
    | Sum.inl i, Sum.inl j => ⟨_, h11 i j⟩
    | Sum.inl i, Sum.inr j => ⟨_, h12 i j⟩
    | Sum.inr i, Sum.inl j => ⟨_, h21 i j⟩
    | Sum.inr i, Sum.inr j => ⟨_, h22 i j⟩
  have hG : G.map (fun x => (x : Fv F v)) = Matrix.fromBlocks (Bi * g.toBlocks₁₁.map π * Bm) (Bi * g.toBlocks₁₂.map π * Bm)
        (Bi * g.toBlocks₂₁.map π * Bm) (Bi * g.toBlocks₂₂.map π * Bm) := by
    ext i j; rcases i with i | i <;> rcases j with j | j <;> rfl
  have hH : H.map (fun x => (x : Fv F v)) = Matrix.fromBlocks (Bi * h.toBlocks₁₁.map π * Bm) (Bi * h.toBlocks₁₂.map π * Bm)
        (Bi * h.toBlocks₂₁.map π * Bm) (Bi * h.toBlocks₂₂.map π * Bm) := by
    ext i j; rcases i with i | i <;> rcases j with j | j <;> rfl
  refine ⟨G, hG, ?_⟩
  apply Matrix.isUnit_det_of_left_inverse (B := H)
  have hmap : (H * G).map (v.adicCompletionIntegers F).subtype = 1 := by
    rw [Matrix.map_mul]
    change H.map (fun x => (x : Fv F v)) * G.map (fun x => (x : Fv F v)) = 1
    rw [hG, hH, key, key, hprod]
  refine Matrix.ext fun i j => Subtype.coe_injective ?_
  have := congrFun (congrFun hmap i) j
  rw [Matrix.map_apply] at this
  change (v.adicCompletionIntegers F).subtype ((H * G) i j) = (v.adicCompletionIntegers F).subtype ((1 : Matrix _ _ _) i j)
  rw [this, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralLocalBasisConjugatesOfKeepsLatticeAtPlac
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

namespace GlobalTheory.IntKeepConj

theorem mulVec_conj_col {R S : Type} [CommRing R] [CommRing S] {d : ℕ} (π : R →+* S)
    (b : GL (Fin d) S) (A : Matrix (Fin d) (Fin d) R) (z : Fin d → R) (k : Fin d)
    (hz : (fun j => π (z j)) = (b : Matrix (Fin d) (Fin d) S) *ᵥ Pi.single k 1) :
    (((b⁻¹ : GL (Fin d) S) : Matrix (Fin d) (Fin d) S) *ᵥ fun j => π ((A *ᵥ z) j)) =
      fun i => (((b⁻¹ : GL (Fin d) S) : Matrix (Fin d) (Fin d) S) * A.map π *
        (b : Matrix (Fin d) (Fin d) S)) i k := by
  have h1 : (fun j => π ((A *ᵥ z) j)) = A.map π *ᵥ (fun j => π (z j)) := by
    funext j; exact RingHom.map_mulVec π A z j
  rw [h1, hz, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  funext i
  simp [Matrix.mulVec_single]

theorem single_mem {F : Type} [Field F] [NumberField F] (v : Pl F) {d : ℕ} (k i : Fin d) :
    (Pi.single k (1 : Fv F v) : Fin d → Fv F v) i ∈ v.adicCompletionIntegers F := by
  by_cases h : i = k
  · subst h; simp only [Pi.single_eq_same]; exact (v.adicCompletionIntegers F).one_mem
  · rw [Pi.single_eq_of_ne h]; exact (v.adicCompletionIntegers F).zero_mem

end GlobalTheory.IntKeepConj

open GlobalTheory.IntKeepConj in
theorem GlobalTheory.IntKeepConj.conj_integral : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d : ℕ} (W : Spc F E d) (v : Pl F) (π₁ π₂ : AE F E →+* Fv F v) (b₁ b₂ : GL (Fin d) (Fv F v)),
  (∀ z : Fin d → AE F E, z ∈ GlobalTheory.InertSph.latAt W v ↔ At (evFin F v) z ∧
      (∀ i, (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₁ (z j)) i ∈
        v.adicCompletionIntegers F) ∧
      (∀ i, (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₂ (z j)) i ∈
        v.adicCompletionIntegers F)) → (∀ x₁ x₂ : Fv F v, ∃ z : AE F E, At (evFin F v) z ∧ π₁ z = x₁ ∧ π₂ z = x₂) →
  ∀ A : Matrix (Fin d) (Fin d) (AE F E), (∀ z ∈ GlobalTheory.InertSph.latAt W v, A *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) → (∀ i j, (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (A).map π₁ * (b₁ : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) ∧ (∀ i j, (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (A).map π₂ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) := by
  intro F E _ _ _ _ _ d W v π₁ π₂ b₁ b₂ hchar hsurj A hA
  constructor
  · intro i k
    choose z hzA hz1 hz2 using fun j => hsurj (((b₁ : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ Pi.single k 1) j) 0
    have hzL : z ∈ GlobalTheory.InertSph.latAt W v := by
      rw [hchar]
      refine ⟨?_, ?_, ?_⟩
      · intro u hu; funext j; exact hzA j u hu
      · intro i'
        have e : (fun j => π₁ (z j)) = (b₁ : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ Pi.single k 1 := funext hz1
        rw [e, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
        exact single_mem v k i'
      · intro i'
        have e : (fun j => π₂ (z j)) = 0 := funext hz2
        rw [e, Matrix.mulVec_zero]; exact (v.adicCompletionIntegers F).zero_mem
    have h := ((hchar _).1 (hA z hzL)).2.1 i
    rw [mulVec_conj_col π₁ b₁ A z k (funext hz1)] at h
    exact h
  · intro i k
    choose z hzA hz1 hz2 using fun j => hsurj 0 (((b₂ : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ Pi.single k 1) j)
    have hzL : z ∈ GlobalTheory.InertSph.latAt W v := by
      rw [hchar]
      refine ⟨?_, ?_, ?_⟩
      · intro u hu; funext j; exact hzA j u hu
      · intro i'
        have e : (fun j => π₁ (z j)) = 0 := funext hz1
        rw [e, Matrix.mulVec_zero]; exact (v.adicCompletionIntegers F).zero_mem
      · intro i'
        have e : (fun j => π₂ (z j)) = (b₂ : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ Pi.single k 1 := funext hz2
        rw [e, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
        exact single_mem v k i'
    have h := ((hchar _).1 (hA z hzL)).2.2 i
    rw [mulVec_conj_col π₂ b₂ A z k (funext hz2)] at h
    exact h
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IrreducibleUnitaryRepEqFiniteSmoothPartTensorDisStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducibleUnitaryRep_eq_finiteSmoothPart_tensor_discreteSeries : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : GA D V →* (H →L[ℂ] H)), IsIrrUnitary π → HasDSComp M π → ∀ hU : IsSubrep π ⊤, IsCopyFinDS (finPartDSSm M hU) M π ⊤ := by
  first | exact @GlobalTheory.TrCopy.isCopyFinDS_finPartDSSm | exact GlobalTheory.TrCopy.isCopyFinDS_finPartDSSm | (intros; apply GlobalTheory.TrCopy.isCopyFinDS_finPartDSSm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacuumAtFiniteHeisenbergCombinationStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFockVacuumAt_finiteHeisenbergCombination : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ) (τ : D.what₂.Tau) (g : WO S T → ℂ), IsThetaFunO ψ S T g → IsFockVacAt (heisO ψ S T) θ τ J g → ∀ {ι : Type} (R : Finset ι) (c : ι → ℂ) (t : ι → WO S T), (∀ z ∈ R, (t z).map (infPart D) = 0) → IsFockVacAt (heisO ψ S T) θ τ J (∑ z ∈ R, c z • heisO ψ S T (t z) g) := by
  first | exact @GlobalTheory.CombFockTranslate.isFockVacAt_comb | exact GlobalTheory.CombFockTranslate.isFockVacAt_comb | (intros; apply GlobalTheory.CombFockTranslate.isFockVacAt_comb <;> assumption)
end

