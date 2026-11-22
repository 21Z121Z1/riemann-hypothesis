import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0255
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MaxCompactIrreducibleHasHighestWeightAndIso
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0264
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0284
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0931
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0926
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0019
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSignatureFromBlocks
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0271
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0025

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdmissibleUnitaryKFinite
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate

namespace GlobalTheory.HCUnitary

variable {n : ℕ} {ε : Fin n → Bool}

theorem maxCpt_UJset (ε : Fin n → Bool) : GlobalTheory.LinRed.maxCpt (UJset ε) = Kset ε := by
  ext g
  refine ⟨fun hg => ⟨hg.2, ?_⟩, fun hg => ⟨mem_UJset_of_mem_Kset hg, hg.1⟩⟩
  have h1 : g * gᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hg.2
  have h2 : gᴴ * Jm ε * g = Jm ε := hg.1
  calc g * Jm ε = g * (gᴴ * Jm ε * g) := by rw [h2]
    _ = Jm ε * g := by rw [Matrix.mul_assoc, ← Matrix.mul_assoc g, h1, Matrix.one_mul]

theorem isLinRed_UJset (ε : Fin n → Bool) : GlobalTheory.LinRed.IsLinRed (UJset ε) := by
  have hW : IsIsoFlag ε (fun i : Fin 0 => i.elim0) (fun _ : Fin 1 => (⊥ : Submodule ℂ (Fin n → ℂ))) :=
    ⟨rfl, monotone_const, fun i => i.elim0, fun x hx y _ => by
      rw [(Submodule.mem_bot ℂ).1 hx]; simp⟩
  have h := (GlobalTheory.T.leviModulusOne_linearReductive_exp_mul_exp n ε 0 _ _ hW (fun i => i.elim0)).1
  rwa [leviOne_zero hW, mats_top] at h

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem isKStable_iff {S : Submodule ℂ H} : GlobalTheory.LinRed.IsKStable (UJset ε) π S ↔ IsKStableOn ε π S := by
  unfold GlobalTheory.LinRed.IsKStable IsKStableOn
  rw [maxCpt_UJset]

theorem isKTypeOf_map {Λ : Fin n → ℝ} {S : Submodule ℂ H} (hS : IsKTypeOf ε π Λ S) (T : H →ₗ[ℂ] H)
    (hT : ∀ k ∈ Kset ε, ∀ w ∈ S, T (π k w) = π k (T w)) : S.map T = ⊥ ∨ IsKTypeOf ε π Λ (S.map T) := by
  obtain ⟨hfin, hst, hirr, ⟨v, hvS, hv0, hv⟩, hdom⟩ := hS
  have hpre : ∀ S' : Submodule ℂ H, IsKStableOn ε π S' → IsKStableOn ε π (S ⊓ S'.comap T) :=
    fun S' h k hk w hw => ⟨hst k hk w hw.1, by
      have : T (π k w) ∈ S' := by rw [hT k hk w hw.1]; exact h k hk _ hw.2
      exact this⟩
  have hbot : IsKStableOn ε π ⊥ := fun k _ w hw => by
    rw [(Submodule.mem_bot ℂ).1 hw, map_zero]; exact Submodule.zero_mem _
  rcases hirr _ inf_le_left (hpre ⊥ hbot) with h0 | h1
  · right
    have hinj : ∀ w ∈ S, T w = 0 → w = 0 := fun w hw h => by
      have : w ∈ S ⊓ (⊥ : Submodule ℂ H).comap T := ⟨hw, h⟩
      rwa [h0, Submodule.mem_bot] at this
    refine ⟨inferInstance, ?_, fun S' hle hS' => ?_, ⟨T v, ⟨v, hvS, rfl⟩, fun h => hv0 (hinj v hvS h),
      fun θ hθ => ?_⟩, ?_⟩
    · rintro k hk _ ⟨w, hw, rfl⟩
      exact ⟨π k w, hst k hk w hw, hT k hk w hw⟩
    · rcases hirr _ inf_le_left (hpre S' hS') with h | h
      · left
        refine eq_bot_iff.2 fun x hx => ?_
        obtain ⟨w, hw, rfl⟩ := hle hx
        have : w ∈ S ⊓ S'.comap T := ⟨hw, hx⟩
        rw [h, Submodule.mem_bot] at this
        rw [this, map_zero]; exact Submodule.zero_mem _
      · exact Or.inr (le_antisymm hle (Submodule.map_le_iff_le_comap.2 (inf_eq_left.1 h)))
    · rw [← hT _ hθ v hvS, hv θ hθ, map_smul]
    · rintro μ _ ⟨w, hw, rfl⟩ hw0 hwt
      refine hdom μ w hw (fun h => hw0 (by rw [h, map_zero])) fun θ hθ => ?_
      refine sub_eq_zero.1 (hinj _ (S.sub_mem (hst _ hθ w hw) (S.smul_mem _ hw)) ?_)
      rw [map_sub, map_smul, hT _ hθ w hw, hwt θ hθ, sub_self]
  · exact Or.inl (eq_bot_iff.2 (Submodule.map_le_iff_le_comap.2 (inf_eq_left.1 h1)))

theorem isAdmOn_iff [CompleteSpace H] : GlobalTheory.LinRed.IsAdmOn (UJset ε) π ↔ IsAdmRep ε π := by
  unfold GlobalTheory.LinRed.IsAdmOn IsAdmRep
  simp only [isKStable_iff]
  rw [maxCpt_UJset]
  refine and_congr_right fun h1 => and_congr_right fun h2 => and_congr_right fun h3 => ?_
  obtain ⟨hA, hB⟩ := GlobalTheory.KTypeHighest.ktype_highest_weight n ε H π h1 h2 h3
  refine ⟨fun h Λ => ?_, fun h S hfin hst hirr => ?_⟩
  · by_cases he : ∃ S₀, IsKTypeOf ε π Λ S₀
    · obtain ⟨S₀, hS₀⟩ := he
      haveI := h S₀ hS₀.1 hS₀.2.1 hS₀.2.2.1
      refine Submodule.finiteDimensional_of_le (sSup_le_sSup (t := {S' | ∃ T : H →ₗ[ℂ] H, S' = S₀.map T ∧
        ∀ k ∈ Kset ε, ∀ w ∈ S₀, T (π k w) = π k (T w)}) fun S hS => ?_)
      obtain ⟨B, hB1, hB2⟩ := hB Λ S₀ S hS₀ hS.2
      exact ⟨B, hB2.symm, fun k hk w _ => hB1 k hk w⟩
    · exact Submodule.finiteDimensional_of_le (S₂ := ⊥) (sSup_le fun S hS => absurd ⟨S, hS.2⟩ he)
  · by_cases h0 : S = ⊥
    · refine Submodule.finiteDimensional_of_le (S₂ := ⊥) (sSup_le ?_)
      rintro _ ⟨T, rfl, -⟩
      rw [h0, Submodule.map_bot]
    · obtain ⟨Λ, hΛ⟩ := hA S hfin h0 hst hirr
      haveI := h Λ
      refine Submodule.finiteDimensional_of_le (S₂ := sSup {S | S ≤ ⊤ ∧ IsKTypeOf ε π Λ S}) (sSup_le ?_)
      rintro _ ⟨T, rfl, hT⟩
      rcases isKTypeOf_map hΛ T hT with hb | hk
      · rw [hb]; exact bot_le
      · exact le_sSup ⟨le_top, hk⟩

theorem admissible_and_analytic : (GlobalTheory.Published.IrreducibleUnitaryAdmissible → ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → IsAdmRep ε σ) ∧ (GlobalTheory.Published.KFiniteCoefficientsAnalytic → ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsAdmRep ε π → ∀ v w : H, IsKFin ε π v → AnalyticOnUJ ε fun g => ⟪w, π g v⟫_ℂ) := by
  refine ⟨fun h n ε H _ _ _ σ hU hI => isAdmOn_iff.1 (h n _ (isLinRed_UJset ε) H σ hU hI),
    fun h n ε H _ _ _ π hπ v w hv => h n _ (isLinRed_UJset ε) H π (isAdmOn_iff.2 hπ) v w ?_⟩
  obtain ⟨S, h1, h2, h3⟩ := hv
  exact ⟨S, h1, h2, isKStable_iff.2 h3⟩

end GlobalTheory.HCUnitary
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodAscentOfTowerRungsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselPeriod_ascent_of_tower_rungs : TowerEx → Rung0 → RungB → RungJ → Ascent := by
  first | exact @GlobalTheory.Asc.ascent_of_rungs | exact GlobalTheory.Asc.ascent_of_rungs | (intros; apply GlobalTheory.Asc.ascent_of_rungs <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepCoreComponentMemDepthLatticeGridCoreStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselStep_coreComponent_mem_depthLatticeGridCore : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ u ∈ (pcBF W F ρ h).Γ₀, ((F.oB ρ h).resS (G.V (.core (2 * ρ + 1))) u).1 ∈ latCore G (2 * ρ + 1) := by
  first | exact @GlobalTheory.AscFin.pcBF_core_mem_latCore | exact GlobalTheory.AscFin.pcBF_core_mem_latCore | (intros; apply GlobalTheory.AscFin.pcBF_core_mem_latCore <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepDiagonalCoordinatesMemComplementIdeal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.XCharBF

noncomputable section

namespace GlobalTheory.XCharBF.DiagCoord

variable {D : D7}

theorem auxiliaryCoordinate_mem_staircaseIdeal {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)
    {t : Fin B.rank → D.host.E} (ht : t ∈ d.lat Λ 𝔟) (r : Fin c) (hr : r.1 + r.1 + 1 ≠ c) :
    ((d.aᴴ * B.gram) *ᵥ t) r ∈ 𝔟 r.rev := by
  obtain ⟨y, -, v, hv, rfl⟩ := ht
  have hG : B.gramᴴ = B.gram := Matrix.ext fun i j => (B.herm.eq (B.frame j) (B.frame i) : star (B.gram j i) = B.gram i j)
  have hperp : d.aᴴ * B.gram * frameMat B A d.ι = 0 := by
    have h1 := congrArg Matrix.conjTranspose d.perp
    have e : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat B A d.ι) = (frameMat B A d.ι)ᴴ := rfl
    rw [e, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hG, conjTranspose_zero] at h1
    rw [← h1, Matrix.mul_assoc]
  have hgram : d.aᴴ * B.gram * d.a = antiDiagonalSignGramMatrix c ε := d.gram
  rw [mulVec_add, mulVec_mulVec, mulVec_mulVec, hperp, hgram, zero_mulVec, zero_add]
  rw [mulVec, dotProduct, Finset.sum_eq_single r.rev]
  · have : antiDiagonalSignGramMatrix c ε r r.rev = 1 := by
      have := r.2
      simp only [antiDiagonalSignGramMatrix, Fin.val_rev]
      rw [if_pos (by omega), if_neg (fun h => hr (by rw [Fin.ext_iff, Fin.val_rev] at h; omega))]
    rw [this, one_mul]; exact hv _
  · intro q _ hq
    have : antiDiagonalSignGramMatrix c ε r q = 0 := by
      have := r.2; have := q.2
      simp only [antiDiagonalSignGramMatrix]
      rw [if_neg (fun h => hq (by rw [Fin.ext_iff, Fin.val_rev]; omega))]
    rw [this, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem negPair_colsOf {n c k : ℕ} (G : Matrix (Fin n) (Fin n) D.host.E) (hG : ∀ i j, star (G j i) = G i j)
    (a : Matrix (Fin n) (Fin c) D.host.E) (f : Fin k → Fin c) (w : Fin k → D.host.E) (s : Fin n → D.host.E) (p : Fin k) :
    ∑ j, (∑ l, star (s l) * (-G) l j) * colsOf a f w j p = -(w p * star (((aᴴ * G) *ᵥ s) (f p))) := by
  simp only [colsOf, mulVec, dotProduct, Matrix.mul_apply, conjTranspose_apply, star_sum, star_mul', star_star, hG,
    Matrix.neg_apply, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

theorem entry_rankOne {m n k l : ℕ} (q : Matrix (Fin k) (Fin m) D.host.E) (e : Matrix (Fin n) (Fin l) D.host.E) (a : D.host.E)
    (t : Fin m → D.host.E) (g : Fin n → D.host.E) (p : Fin k) (p' : Fin l) :
    (q * Matrix.of (fun i j => a * t i * g j) * e) p p' = a * (q *ᵥ t) p * ∑ j, g j * e j p' := by
  simp only [Matrix.mul_apply, Matrix.of_apply, mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

theorem rat_tmul_entry {m n k l : ℕ} (q : Matrix (Fin k) (Fin m) D.host.E) (C : Matrix (Fin m) (Fin n) D.host.E)
    (e : Matrix (Fin n) (Fin l) D.host.E) (X : AF D.host.F) (p : Fin k) (p' : Fin l) :
    (rat q ⬝ (Matrix.of fun i j => X ⊗ₜ[D.host.F] C i j : Mx D m n) ⬝ rat e) p p' = X ⊗ₜ[D.host.F] (q * C * e) p p' := by
  have hinc : ∀ x, incA D x = (1 : AF D.host.F) ⊗ₜ[D.host.F] x := fun _ => rfl
  simp only [Matrix.mul_apply, rat, Matrix.map_apply, Matrix.of_apply, hinc, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    mul_one, ← TensorProduct.tmul_sum]

theorem stairId_mul_inv_succ (𝔞 𝔞' : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (h𝔞 : 𝔞 ≠ 0) (h𝔞' : 𝔞' ≠ 0) {c₁ c₂ : ℕ}
    (q₁ : Fin c₁) (q₂ : Fin c₂) (hc : c₂ = c₁ + 1) (hq : q₂.1 = q₁.1 + 1) :
    stairId 𝔞 𝔞' c₁ q₁ * (stairId 𝔞 𝔞' c₂ q₂)⁻¹ = 𝔞' := by
  unfold stairId
  rw [show c₂ - q₂.1 = c₁ - q₁.1 by omega, hq, pow_succ 𝔞' (q₁.1 + 1)]
  have h1 : 𝔞 ^ (c₁ - q₁.1) ≠ 0 := pow_ne_zero _ h𝔞
  have h2 : 𝔞' ^ (q₁.1 + 1) ≠ 0 := pow_ne_zero _ h𝔞'
  field_simp

theorem colsOf_gram {n c k : ℕ} (G : Matrix (Fin n) (Fin n) D.host.E) (a : Matrix (Fin n) (Fin c) D.host.E) (f g : Fin k → Fin c)
    (w w' : Fin k → D.host.E) (p q : Fin k) :
    ((colsOf a f w)ᴴ * G * colsOf a g w') p q = star (w p) * w' q * (aᴴ * G * a) (f p) (g q) := by
  simp only [colsOf, Matrix.mul_apply, conjTranspose_apply, star_mul', Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

set_option maxHeartbeats 1000000 in

theorem diag_mem_complId : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {F : Frames G}, Std F →
    ∀ (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m) (u : WO (negSp (G.V (.grid (2 * ρ + 2) 0))) (G.V (.grid (2 * ρ + 1) 0))),
    u ∈ latO _ _ (G.Λ (.grid (2 * ρ + 2) 0) : Set _) (G.Λ (.grid (2 * ρ + 1) 0) : Set _) (fun _ => True) →
    ∀ p : Fin ρ, ((F.dJ ρ h).pY ⬝ u ⬝ (F.dB ρ h).jY) p p ∈ complId (D.host.AA * G.pl.stAbar sc) := by
  intro D T L sc G F hF ρ h u hu p
  obtain ⟨hcJ, heJ, -⟩ := hF.hJ ρ h
  obtain ⟨hcB, heB, sB, he'B⟩ := hF.hB ρ h
  set aJ := G.colDec (2 * ρ + 1) (by omega) (by omega) with haJ
  set aB := G.colDec (2 * ρ + 2) (by omega) h with haB
  obtain ⟨hAA, -⟩ := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).1
  obtain ⟨hA, hconj⟩ := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).2 T L G.pl sc
  have hAb : G.pl.stAbar sc ≠ 0 := by
    intro h0
    apply hA
    rw [FractionalIdeal.eq_zero_iff] at h0 ⊢
    intro y hy
    have h1 : star y ∈ G.pl.stAbar sc := (hconj _).2 (by rwa [star_star])
    have h2 := h0 _ h1
    rwa [star_eq_zero] at h2

  have hJ : ∀ t ∈ G.Λ (.grid (2 * ρ + 1) 0), ((F.dJ ρ h).qY *ᵥ t) p =
      star ((-D.host.xi0) ^ (p.1 + 1)) * ((aJ.aᴴ * (G.V (.grid (2 * ρ + 1) 0)).gram) *ᵥ t) (Fin.castLE (by omega) p) := by
    intro t _
    simp only [HypDec.qY, heJ, mulVec, dotProduct, Matrix.mul_apply, conjTranspose_apply, colsOf, star_mul', Finset.mul_sum,
      Finset.sum_mul, mul_assoc]
  have hJmem : ∀ t ∈ G.Λ (.grid (2 * ρ + 1) 0), ((aJ.aᴴ * (G.V (.grid (2 * ρ + 1) 0)).gram) *ᵥ t) (Fin.castLE (by omega) p) ∈
      stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) (Fin.castLE (by omega) p).rev := by
    intro t ht
    have ht' : t ∈ aJ.lat (G.sp.P (2 * ρ + 1)).lat (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1)) := by
      rw [haJ, ← G.sp.colLat (2 * ρ + 1) (by omega) (by omega)]; exact ht
    exact auxiliaryCoordinate_mem_staircaseIdeal aJ _ _ ht' _ (by simp only [Fin.val_castLE]; omega)

  have hBmem : ∀ s ∈ G.Λ (.grid (2 * ρ + 2) 0),
      star (((aB.aᴴ * (G.V (.grid (2 * ρ + 2) 0)).gram) *ᵥ s) (Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev) ∈
      (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1) (Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev)⁻¹ := by
    intro s hs
    have hs' : s ∈ aB.lat (G.sp.P (2 * ρ + 2)).lat (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1)) := by
      rw [haB, ← G.sp.colLat (2 * ρ + 2) (by omega) h]; exact hs
    have h1 := auxiliaryCoordinate_mem_staircaseIdeal aB _ _ hs' (Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev
      (by simp only [Fin.val_rev, Fin.val_castLE]; omega)
    exact ((GlobalTheory.ChiGrid.stairId_ne_zero_and_mem_rev_iff D _ _ hA hconj _ _).2 _).1 h1

  have hsc : star ((-D.host.xi0) ^ (p.1 + 1)) * sB p = 1 := by
    have h1 := congrFun (congrFun (F.dB ρ h).e'e p) p
    rw [he'B, heB, colsOf_gram, Matrix.one_apply_eq] at h1
    have h2 : (aB.aᴴ * (G.V (.grid (2 * ρ + 2) 0)).gram * aB.a) (Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev
        (Fin.castLE (by omega) p) = 1 := by
      rw [show aB.aᴴ * (G.V (.grid (2 * ρ + 2) 0)).gram * aB.a = antiDiagonalSignGramMatrix (2 * ρ + 2 - 1) (-1) from aB.gram]
      simp only [antiDiagonalSignGramMatrix, Fin.val_rev, Fin.val_castLE]
      rw [if_pos (by omega), if_neg (fun e => by rw [Fin.ext_iff, Fin.val_rev, Fin.val_castLE] at e; omega)]
    rw [h2, mul_one] at h1
    have h3 := congrArg star h1
    rw [star_mul', star_star, star_one] at h3
    rw [mul_comm]; exact h3
  have hGB : ∀ i j, star ((G.V (.grid (2 * ρ + 2) 0)).gram j i) = (G.V (.grid (2 * ρ + 2) 0)).gram i j := fun i j =>
    (G.V (.grid (2 * ρ + 2) 0)).herm.eq ((G.V (.grid (2 * ρ + 2) 0)).frame j) ((G.V (.grid (2 * ρ + 2) 0)).frame i)

  have keyE : ∀ a ∈ D.host.AA, ∀ s ∈ G.Λ (.grid (2 * ρ + 2) 0), ∀ t ∈ G.Λ (.grid (2 * ρ + 1) 0),
      ((F.dJ ρ h).qY * Matrix.of (fun i j => a * t i * ∑ k, star (s k) * (negSp (G.V (.grid (2 * ρ + 2) 0))).gram k j) *
        (F.dB ρ h).e') p p ∈ D.host.AA * G.pl.stAbar sc := by
    intro a ha s hs t ht
    rw [entry_rankOne _ _ a t (fun j => ∑ k, star (s k) * (negSp (G.V (.grid (2 * ρ + 2) 0))).gram k j), hJ t ht, he'B,
      negSp_gram, negPair_colsOf _ hGB]
    have e : a * (star ((-D.host.xi0) ^ (p.1 + 1)) *
          ((aJ.aᴴ * (G.V (.grid (2 * ρ + 1) 0)).gram) *ᵥ t) (Fin.castLE (by omega) p)) *
        -(sB p * star (((aB.aᴴ * (G.V (.grid (2 * ρ + 2) 0)).gram) *ᵥ s) (Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev)) =
        -(a * (((aJ.aᴴ * (G.V (.grid (2 * ρ + 1) 0)).gram) *ᵥ t) (Fin.castLE (by omega) p) *
          star (((aB.aᴴ * (G.V (.grid (2 * ρ + 2) 0)).gram) *ᵥ s) (Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev))) := by
      linear_combination (-(a * ((aJ.aᴴ * (G.V (.grid (2 * ρ + 1) 0)).gram) *ᵥ t) (Fin.castLE (by omega) p) *
          star (((aB.aᴴ * (G.V (.grid (2 * ρ + 2) 0)).gram) *ᵥ s) (Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev))) * hsc
    rw [e]
    refine Submodule.neg_mem _ (FractionalIdeal.mul_mem_mul ha ?_)
    rw [← stairId_mul_inv_succ (G.pl.stA sc) (G.pl.stAbar sc) hA hAb (Fin.castLE (by omega) p : Fin (2 * ρ + 1 - 1)).rev
      (Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev (by omega) (by simp only [Fin.val_rev, Fin.val_castLE]; omega)]
    exact FractionalIdeal.mul_mem_mul (hJmem t ht) (hBmem s hs)
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hw
    have key : ((F.dJ ρ h).pY ⬝ (Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F]
        (a * t i * ∑ k, star (s k) * (negSp (G.V (.grid (2 * ρ + 2) 0))).gram k j)) ⬝ (F.dB ρ h).jY) p p =
        (pairA D.host.F 0 α) ⊗ₜ[D.host.F] ((F.dJ ρ h).qY * Matrix.of (fun i j => a * t i * ∑ k, star (s k) *
          (negSp (G.V (.grid (2 * ρ + 2) 0))).gram k j) * (F.dB ρ h).e') p p :=
      rat_tmul_entry _ _ _ _ _ _
    rw [key]
    exact tmul_mem_complId hα (keyE a ha s hs t ht)
  | zero => simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_apply]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_apply]; exact neg_mem hx

end GlobalTheory.XCharBF.DiagCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CardNegativeSignsDiagonalFrameEqSignature
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameSylvester

theorem neg_card_eq_sig : ∀ {D : D7} (V : HSp D), V.SigOK → ∀ (A : Fr V) (τ : D.what₂.Tau),
    (Finset.univ.filter fun a => A.ε τ a = false).card = (V.sig (tauE D τ)).2 := by
  intro D V hV A τ
  set ε := A.ε τ with hε
  set a := (Finset.univ.filter fun i => ε i = true).card with ha_def
  set b := (Finset.univ.filter fun i => ε i = false).card with hb_def
  have ha : Fintype.card {i // ε i = true} = a := by rw [Fintype.card_subtype]
  have hb : Fintype.card {i // ¬ ε i = true} = b := by
    rw [Fintype.card_subtype]; simp [b]
  let e0 : Fin V.rank ≃ Fin a ⊕ Fin b :=
    (Equiv.sumCompl (fun i => ε i = true)).symm.trans
      (Equiv.sumCongr (Fintype.equivFinOfCardEq ha) (Fintype.equivFinOfCardEq hb))
  have hl : ∀ k : Fin a, ε (e0.symm (Sum.inl k)) = true := fun k => by
    simp [e0]
    exact ((Fintype.equivFinOfCardEq ha).symm k).2
  have hr : ∀ k : Fin b, ε (e0.symm (Sum.inr k)) = false := fun k => by
    simp [e0]
    simpa using ((Fintype.equivFinOfCardEq hb).symm k).2
  have hcard : Fintype.card (Fin V.rank) = a + b := by simpa using Fintype.card_congr e0
  set F := A.fr τ with hF_def
  have hF : IsUnit F := A.fr_unit τ
  have hFi : F * F⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hF)
  have hJ : (F⁻¹)ᴴ * gramAt D V τ * F⁻¹ = Formalism.REAL.Jm ε := by
    rw [← A.fr_gram τ]
    calc (F⁻¹)ᴴ * (Fᴴ * Formalism.REAL.Jm ε * F) * F⁻¹ = (F * F⁻¹)ᴴ * Formalism.REAL.Jm ε * (F * F⁻¹) := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hFi]; simp
  let Q : Matrix (Fin V.rank) (Fin a ⊕ Fin b) ℂ := (F⁻¹).submatrix id e0.symm
  have hQ : Qᴴ * gramAt D V τ * Q = Formalism.UG.Jpq a b := by
    have h2 : Qᴴ * gramAt D V τ * Q = ((F⁻¹)ᴴ * gramAt D V τ * F⁻¹).submatrix e0.symm e0.symm := by
      ext r s; simp only [Q, Matrix.mul_apply, submatrix_apply, conjTranspose_apply, id]
    rw [h2, hJ]
    ext (r | r) (s | s) <;>
      simp [Formalism.REAL.Jm, Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply, hl, hr, e0.symm.injective.eq_iff] <;>
      split_ifs <;> simp
  have hsig1 : Formalism.UG.HasSignature (V.gram.map (tauE D τ)) a b :=
    GlobalTheory.FrameComplement.hasSignature_of_frame hcard Q hQ
  have hsig2 := hV (tauE D τ)
  have heq : a = (V.sig (tauE D τ)).1 := GlobalTheory.SylvesterInertia.hasSignature_fst_unique hsig1 hsig2
  obtain ⟨e2, _, _⟩ := hsig2
  have h2 : V.rank = (V.sig (tauE D τ)).1 + (V.sig (tauE D τ)).2 := by simpa using Fintype.card_congr e2
  have h3 : V.rank = a + b := by simpa using hcard
  omega

end GlobalTheory.FrameSylvester
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainIntertwinersRowZeroUnitVacua
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GridJoin.RowArrows

theorem vY_mem_span_core {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}
    (h : GlobalTheory.Hk3.Core R F) (t : T) {k : ℕ} (hk : k + 1 < D.R.m) : R.vY t k ∈ Submodule.span ℂ (Set.range
    fun a : {a : WO (Yc D k) (Yc D (k + 1)) // a.map (infPart D) = 0} => heisO R.ψ _ _ a (R.vac k)) :=
  GlobalTheory.Grid.stepVec_mem_span (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (h.lev.βY _ (by omega)))
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (h.lev.βY _ hk)) (h.chain.vY t k hk)

theorem vX_mem_span_core {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}
    (h : GlobalTheory.Hk3.Core R F) (t : T) : R.vX t ∈ Submodule.span ℂ (Set.range
    fun a : {a : WO (Yc D (D.R.m - 1)) D.sp.X' // a.map (infPart D) = 0} => heisO R.ψ _ _ a R.vacX) :=
  GlobalTheory.Grid.stepVec_mem_span (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (h.lev.βY _ (by have := D.R.two_le_m; omega)))
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ h.lev.βX) (h.chain.vX t)

theorem chainIntertwiners_rowZero_unitVacua : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ (t : T) j, j < D.R.m → IsItW R.θ (GlobalTheory.Grid.row0 R j).M (GlobalTheory.Grid.row0 R (j + 1)).M (GlobalTheory.Grid.th0 R t j).ω (GlobalTheory.Grid.fock R.ψ R.θ false (GlobalTheory.Grid.row0 R j) (GlobalTheory.Grid.row0 R (j + 1)) (GlobalTheory.Grid.th0 R t j).vac) (GlobalTheory.Grid.th0 R t j).It := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc _ _ _ F h _ G' W _ G _ _ _ _ t j hj
  unfold GlobalTheory.Grid.th0
  by_cases h1 : j + 1 < D.R.m
  · rw [dif_pos h1]
    have hc := (GlobalTheory.Grid.ArrS.is_cast (ψ := R.ψ) (θ := R.θ) (ε := false) (a := GlobalTheory.Grid.stepY R t j)
      (χS := GlobalTheory.Grid.GridPre.muAt R t (j + 1) (GlobalTheory.Grid.rkV D 0 j))
      (χT := GlobalTheory.Grid.GridPre.muAt R t (j + 1) (GlobalTheory.Grid.rkV D 0 (j + 1))) (GlobalTheory.Grid.nodeY_eq_chainVertexAtRowZero_of_lt R (by omega)) (GlobalTheory.Grid.nodeY_eq_chainVertexAtRowZero_of_lt R h1))
    have hω := h.chain.ωY t j h1
    rw [GlobalTheory.Grid.chrStep_eq_muAt] at hω
    exact (hc.2 ⟨hω, (h.chain.vY t j h1).1,
      GlobalTheory.Grid.isItW_of_mem_span hω h.models.inf (h.chain.vY t j h1).1.2.theta (vY_mem_span_core h t h1) (h.chain.ItY t j h1)⟩).intw
  · have h2 : j + 1 = D.R.m := by omega
    rw [dif_neg h1, dif_pos h2]
    have hc := (GlobalTheory.Grid.ArrS.is_cast (ψ := R.ψ) (θ := R.θ) (ε := false) (a := GlobalTheory.Grid.stepX R t)
      (χS := GlobalTheory.Grid.GridPre.muAt R t (j + 1) (GlobalTheory.Grid.rkV D 0 j))
      (χT := GlobalTheory.Grid.GridPre.muAt R t (j + 1) (GlobalTheory.Grid.rkV D 0 (j + 1))) (GlobalTheory.Grid.nodeY_pred_eq_chainVertexAtRowZero_last R h2) (GlobalTheory.Grid.nodeX_eq_chainVertexAtRowZero_of_ge R h1))
    have hω := h.chain.ωX t
    rw [(congrArg _ h2.symm).trans (GlobalTheory.Grid.chrStep_eq_muAt R t j)] at hω
    exact (hc.2 ⟨hω, (h.chain.vX t).1,
      GlobalTheory.Grid.isItW_of_mem_span hω h.models.inf (h.chain.vX t).1.2.theta (vX_mem_span_core h t) (h.chain.ItX t)⟩).intw

end GlobalTheory.GridJoin.RowArrows

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChamberCoefficientProductFormula
section
open MeasureTheory GlobalTheory.Chamber

namespace GlobalTheory.Chamber.SumSplit

open Finset in
theorem empty_mem_parF {k : ℕ} (𝔞 : Submodule ℝ (A0 k)) : (∅ : Finset (SV k)) ∈ parF 𝔞 ∅ := by
  refine mem_parF.2 ⟨⟨by simp, by simp⟩, ?_, subset_rfl⟩
  simp [aP]

theorem eL_zero {k : ℕ} (H : A0 k) : eL 0 H = 1 := by simp [eL]

theorem eL_add {k : ℕ} (l H H' : A0 k) : eL l (H + H') = eL l H * eL l H' := by
  simp only [eL, inner_add_right, Complex.ofReal_add, mul_add, Complex.exp_add]

theorem sum_isOrth {k : ℕ} {𝔞 : Submodule ℝ (A0 k)} {X Y W : Finset (SV k) → A0 k} (hX : IsOrth 𝔞 X)
    (hY : IsOrth 𝔞 Y) (hW : ∀ P ∈ parF 𝔞 ∅, W P = X P + Y P) : IsOrth 𝔞 W := by
  intro P hP Q e
  have hQ : Q ∈ parF 𝔞 ∅ := mem_parF.2 ⟨(mem_parF.1 hP).1.mono e, (vecSpan_mono e).trans (mem_parF.1 hP).2.1,
    Finset.empty_subset _⟩
  rw [hW P hP, hW Q hQ, map_add, ← hX P hP Q e, ← hY P hP Q e]

theorem cP_empty_empty {k : ℕ} (c : Finset (SV k) → A0 k → ℂ) (hc : Continuous (c ∅)) (l : A0 k) :
    cP ∅ ∅ c l = c ∅ l := by
  have hs : sumP ∅ ∅ c = c ∅ := by
    funext l
    have h : ∀ b : SV k → A0 k, epsOf (∅ \ ∅) b l = 1 := fun b => by
      have : IsEmpty ↥((∅ : Finset (SV k)) \ ∅) := ⟨fun x => by simpa using x.2⟩
      rw [epsOf, Matrix.det_isEmpty]; simp
    simp only [sumP, between, Finset.powerset_empty, Finset.filter_singleton, Finset.Subset.refl, if_true,
      Finset.sum_singleton, eps, epsHat, h]
    simp
  rw [cP, hs]
  refine extendFrom_eq (by rw [dense_generic.closure_eq]; trivial) ?_
  exact (hc.tendsto l).mono_left nhdsWithin_le_nhds

theorem volume_sum_split : ExpFamilyIntegral → FamilyProduct → ∀ (k : ℕ) (𝔞 : Submodule ℝ (A0 k)), IsLevi 𝔞 →
    ∀ X Y W : Finset (SV k) → A0 k, IsOrth 𝔞 X → IsOrth 𝔞 Y → (∀ P ∈ parF 𝔞 ∅, W P = X P + Y P) →
    ((∫ H : aMQ 𝔞 ∅, gamM 𝔞 ∅ W H : ℝ) : ℂ) = cM 𝔞 ∅ (expFam W) 0 ∧
    cM 𝔞 ∅ (expFam W) 0 = ∑ Q ∈ parF 𝔞 ∅, cM 𝔞 Q (expFam X) 0 * cP Q ∅ (expFam Y) 0 ∧
    cP ∅ ∅ (expFam Y) 0 = 1 := by
  intro hI hF k 𝔞 hL X Y W hX hY hW
  have hWo := sum_isOrth hX hY hW
  refine ⟨?_, ?_, ?_⟩
  · rw [(((hI k 𝔞 hL W hWo).2 ∅ (empty_mem_parF 𝔞)).1.2 0)]
    simp only [eL_zero, one_mul]
    exact (integral_ofReal).symm
  · rw [← hF k 𝔞 hL _ _ hX.isGMFam hY.isGMFam ∅ (empty_mem_parF 𝔞) 0]
    have hs : sumM 𝔞 ∅ (expFam W) = sumM 𝔞 ∅ (expFam X * expFam Y) := by
      funext l
      refine Finset.sum_congr rfl fun P hP => ?_
      have hPF : P ∈ parF 𝔞 ∅ := mem_parF.2 ⟨(mem_parP.1 hP).1, (mem_parP.1 hP).2.1.le, Finset.empty_subset _⟩
      simp only [expFam, Pi.mul_apply, hW P hPF, eL_add]
    simp only [cM, hs]
  · rw [cP_empty_empty _ (by
      simpa [expFam] using (((hY.isGMFam) ∅ (empty_mem_parF 𝔞)).1.continuous)) 0]
    exact eL_zero _

end GlobalTheory.Chamber.SumSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsOverVacuumIsometryOfSkeletonDatumStatement
section
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVectorsOverVacuumIsometry_of_skeletonDatum : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors.VacuumFock D := by
  first | exact @GlobalTheory.vacuumFock_all_records | exact GlobalTheory.vacuumFock_all_records | (intros; apply GlobalTheory.vacuumFock_all_records <;> assumption)
end

