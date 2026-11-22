import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0303
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0190
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0192
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0176
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0310
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0294
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0037
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0087
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0307
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0291
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0016
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianFrameExistence.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarFrameStabilizerLocalFixerSectionProduct
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.KapMulLast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0223
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0257
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0306
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0259
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0258
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
import Formalism.LocalToGlobal.HermitianForms.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0142
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0133
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0170
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0140
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0305
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0254
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0308
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFinEmb
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsUnimodularOfLocalStandardLatticeTranslates

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfandInvariantsScalarOnLowestKTypeCoefficients
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.CentreLow

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem smooth_comb {ε : Fin n → Bool} {f f' : Matrix (Fin n) (Fin n) ℂ → ℂ} (c : ℂ)
    (hf : SmoothOnG ε f) (hf' : SmoothOnG ε f') : SmoothOnG ε (fun h => f h + c * f' h) := by
  intro g hg
  obtain ⟨U, F, hU, hgU, hF, e⟩ := hf g hg
  obtain ⟨U', F', hU', hgU', hF', e'⟩ := hf' g hg
  refine ⟨U ∩ U', fun h => F h + c * F' h, hU.inter hU', ⟨hgU, hgU'⟩,
    (hF.mono Set.inter_subset_left).add (contDiffOn_const.mul (hF'.mono Set.inter_subset_right)), ?_⟩
  intro x hx hxJ
  simp only [e x hx.1 hxJ, e' x hx.2 hxJ]

theorem smooth_word {ε : Fin n → Bool} {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : SmoothOnG ε f)
    (w : List (Fin n × Fin n)) : SmoothOnG ε (Eword ε w f) := by
  induction w with
  | nil => exact hf
  | cons p w ih =>
    have hc := complex_parts_mem_lie_algebra_holds n ε (Matrix.single p.1 p.2 1)
    exact smooth_comb Complex.I (rdSmooth_of right_derivative_extends n ε _ _ ih hc.1)
      (rdSmooth_of right_derivative_extends n ε _ _ ih hc.2.1)

theorem word_comb {ε : Fin n → Bool} {f f' : Matrix (Fin n) (Fin n) ℂ → ℂ} (c : ℂ)
    (hf : SmoothOnG ε f) (hf' : SmoothOnG ε f') (w : List (Fin n × Fin n)) :
    ∀ g, inUJ ε g → Eword ε w (fun h => f h + c * f' h) g = Eword ε w f g + c * Eword ε w f' g := by
  induction w with
  | nil => intro g _; rfl
  | cons p w ih =>
    intro g hg
    have hc := complex_parts_mem_lie_algebra_holds n ε (Matrix.single p.1 p.2 1)
    have h1 := Eword_congr ε ih [p] g hg
    have h2 := fun X hX => (right_derivative_linear n ε _ _ X X 0 c g (smooth_word hf w) (smooth_word hf' w) hX hX hg).2.2
    refine Eq.trans h1 ?_
    simp only [Eword, Eab, Ec, id, h2 _ hc.1, h2 _ hc.2.1]
    ring

theorem gelf_comb {ε : Fin n → Bool} {f f' : Matrix (Fin n) (Fin n) ℂ → ℂ} (c : ℂ)
    (hf : SmoothOnG ε f) (hf' : SmoothOnG ε f') (m : ℕ) (g : Matrix (Fin n) (Fin n) ℂ) (hg : inUJ ε g) :
    gelf ε m (fun h => f h + c * f' h) g = gelf ε m f g + c * gelf ε m f' g := by
  simp only [gelf, word_comb c hf hf' _ g hg, Finset.sum_add_distrib, Finset.mul_sum]

theorem gelf_congr {ε : Fin n → Bool} {f f' : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (h : ∀ g, inUJ ε g → f g = f' g) (m : ℕ) (g : Matrix (Fin n) (Fin n) ℂ) (hg : inUJ ε g) :
    gelf ε m f g = gelf ε m f' g :=
  Finset.sum_congr rfl fun _ _ => Eword_congr ε h _ g hg

theorem centre_scalar_low : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsKTypeOf ε σ (lowK ε lam) (lowKSub ε lam σ) → ∃ c : ℕ → ℂ, ∀ s ∈ lowKSub ε lam σ, ∀ u : H, SmoothOnG ε (fun g => ⟪u, σ g s⟫_ℂ) ∧ ∀ m, ∀ g ∈ UJset ε, gelf ε m (fun x => ⟪u, σ x s⟫_ℂ) g = c m * ⟪u, σ g s⟫_ℂ := by
  intro n ε lam H _ _ _ σ hσ hK
  obtain ⟨α, hα, hαc, hfix⟩ := GlobalTheory.T.exists_smooth_compactSupport_fix_lowestKType n ε lam H σ hσ hK
  have hD := fun (s : lowKSub ε lam σ) => GlobalTheory.T.derivatives_coefficients_convolutionFixed_vector n ε H σ α s hσ hα hαc (hfix s s.2)
  have hsm : ∀ (s : lowKSub ε lam σ) (u : H), SmoothOnG ε (fun g => ⟪u, σ g s⟫_ℂ) := fun s => (hD s).1
  have h1 : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := by simp [UJset, inUJ]
  have hone : ∀ v, σ 1 v = v := fun v => by rw [hσ.1.1]; rfl
  have hmul : ∀ a ∈ UJset ε, ∀ b ∈ UJset ε, ∀ v, σ (a * b) v = σ a (σ b v) := fun a ha b hb v => by
    rw [hσ.1.2 a ha b hb]; rfl
  have hC : ∀ (m : ℕ) (s : lowKSub ε lam σ), ∃ s' : H, ∀ u, ∀ g ∈ UJset ε,
      gelf ε m (fun x => ⟪u, σ x s⟫_ℂ) g = ⟪u, σ g s'⟫_ℂ := by
    intro m s
    choose v hv using (hD s).2
    refine ⟨∑ a : Fin (m + 1) → Fin n, v (cycWord a), fun u g hg => ?_⟩
    simp only [gelf, hv _ u g hg, map_sum, inner_sum]
  choose C hC using hC
  have hC1 : ∀ (m : ℕ) (s : lowKSub ε lam σ) (u : H),
      ⟪u, C m s⟫_ℂ = gelf ε m (fun x => ⟪u, σ x s⟫_ℂ) 1 := fun m s u => by rw [hC m s u 1 h1, hone]
  have hlin : ∀ (m : ℕ) (c : ℂ) (s t : lowKSub ε lam σ), C m (s + c • t) = C m s + c • C m t := by
    intro m c s t
    refine ext_inner_left ℂ fun u => ?_
    rw [inner_add_right, inner_smul_right, hC1, hC1, hC1, ← gelf_comb c (hsm s u) (hsm t u) m 1 h1]
    simp [inner_add_right, inner_smul_right]
  have h0 : ∀ m, C m 0 = 0 := fun m => by simpa using hlin m 1 0 0
  have key : ∀ m, ∃ c : ℂ, ∀ s : lowKSub ε lam σ, C m s = c • (s : H) := by
    intro m
    refine GlobalTheory.T.kMap_lowestKTypeSubspace_eq_scalar n ε lam H σ hσ hK
      { toFun := C m
        map_add' := fun s t => by simpa using hlin m 1 s t
        map_smul' := fun c t => by simpa [h0] using hlin m c 0 t } ?_
    intro k hk s s' e
    have hkU : k ∈ UJset ε := (maximal_compact_facts n ε).1 k hk
    refine ext_inner_left ℂ fun u => ?_
    change ⟪u, C m s'⟫_ℂ = ⟪u, σ k (C m s)⟫_ℂ
    rw [hC1, ← hC m s u k hkU, ← Matrix.one_mul k,
      ← GlobalTheory.T.gelfandInvariant_comm_rightTranslation n ε m _ k 1 (hsm s u) hkU h1]
    refine gelf_congr (fun g hg => ?_) m 1 h1
    rw [e, hmul g hg k hkU]
  choose c hc using key
  refine ⟨c, fun s hs u => ⟨hsm ⟨s, hs⟩ u, fun m g hg => ?_⟩⟩
  rw [hC m ⟨s, hs⟩ u g hg, hc, map_smul, inner_smul_right]

end GlobalTheory.CentreLow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenusMassEqSumOverRationalGroupOrbits
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 4000000 in

theorem GlobalTheory.Unfold.massA_eq_sum_orbits : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (φ : ↥(FlagPairStabilizer F F') →* (∀ p, ↥(FP p).UW0)), (∀ (h : ↥(FlagPairStabilizer F F')) p, Ext p (h : GV D) ((φ h p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p)) → Function.Injective φ → ∀ [∀ p, MulAction ↥(FP p).UW0 (LocNG.Datum (FP p))], (∀ p (g : ↥(FP p).UW0) (d d' : LocNG.Datum (FP p)), LocNG.Datum.Moves g.1 d d' ↔ g • d = d') → ∀ d : Dat Z FP, massA F F' d = ∑' o : Quot (fun y y' : (∀ p, LocNG.Datum (FP p)) => ∃ h : ↥(FlagPairStabilizer F F'), (fun p => φ h p • y p) = y'), if (∀ p, ∃ g : ↥(FP p).UW0, g • d p = o.out p) ∧ {p | o.out p ≠ d p}.Finite then (({h : ↥(FlagPairStabilizer F F') | (fun p => φ h p • o.out p) = o.out}.encard : ℝ≥0∞))⁻¹ else 0 := by
  intro D X Y u u' F F' w hw hG Z FP hB hR φ hφ _hinj _inst hmov d

  have huniq := (GlobalTheory.T.rationalAutomorphism_local_extension_moves_lattices D X Y u u' F F' w hw hG Z FP hB hR).1

  have key : ∀ (h : ↥(FlagPairStabilizer F F')) (y y' : Dat Z FP),
      RMoves h.1 y y' ↔ (fun p => φ h p • y p) = y' := by
    intro h y y'
    constructor
    · intro hm
      funext p
      obtain ⟨g', hg', hmv⟩ := hm p
      have he : g' = ((φ h p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) :=
        (huniq h.1 p).unique hg' (hφ h p)
      subst he
      exact (hmov p (φ h p) (y p) (y' p)).1 hmv
    · intro he p
      exact ⟨_, hφ h p, (hmov p (φ h p) (y p) (y' p)).2 (congrFun he p)⟩

  have hrel : GRel (Z := Z) (FP := FP) F F' =
      (fun y y' : (∀ p, LocNG.Datum (FP p)) => ∃ h : ↥(FlagPairStabilizer F F'), (fun p => φ h p • y p) = y') := by
    funext y y'
    apply propext
    constructor
    · rintro ⟨h, hh, hm⟩
      exact ⟨⟨h, (mem_H0sub F F' h).2 hh⟩, (key ⟨h, (mem_H0sub F F' h).2 hh⟩ y y').1 hm⟩
    · rintro ⟨h, hh⟩
      exact ⟨h.1, (mem_H0sub F F' h.1).1 h.2, (key h y y').2 hh⟩

  have hstab : ∀ y : Dat Z FP, (stabY F F' y).encard =
      {h : ↥(FlagPairStabilizer F F') | (fun p => φ h p • y p) = y}.encard := by
    intro y
    have hs : stabY F F' y = Subtype.val '' {h : ↥(FlagPairStabilizer F F') | (fun p => φ h p • y p) = y} := by
      ext g
      constructor
      · rintro ⟨hg, hm⟩
        exact ⟨⟨g, (mem_H0sub F F' g).2 hg⟩, (key ⟨g, (mem_H0sub F F' g).2 hg⟩ y y).1 hm, rfl⟩
      · rintro ⟨h, hh, rfl⟩
        exact ⟨(mem_H0sub F F' h.1).1 h.2, (key h y y).2 hh⟩
    rw [hs, Subtype.val_injective.encard_image]
  rw [massA, hrel]
  refine tsum_congr fun o => ?_

  have hin : InGen d o.out ↔
      (∀ p, ∃ g : ↥(FP p).UW0, g • d p = o.out p) ∧ {p | o.out p ≠ d p}.Finite := by
    unfold InGen
    refine and_congr (forall_congr' fun p => ?_) Iff.rfl
    constructor
    · rintro ⟨g, hg, hm⟩
      exact ⟨⟨g, hg⟩, (hmov p ⟨g, hg⟩ (d p) (o.out p)).1 hm⟩
    · rintro ⟨g, hg⟩
      exact ⟨g.1, g.2, (hmov p g (d p) (o.out p)).2 hg⟩
  by_cases hc : (∀ p, ∃ g : ↥(FP p).UW0, g • d p = o.out p) ∧ {p | o.out p ≠ d p}.Finite
  · rw [if_pos (hin.2 hc), if_pos hc, hstab]
  · rw [if_neg (mt hin.1 hc), if_neg hc]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenusStableUnderRationalComplementGroup
section
noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GenusStab

theorem finrank_Vp_k (D : D7) (p : PlF D) :
    Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1 := by
  rw [finrank_Vp]
  have h2 := D.R.two_le_m
  obtain ⟨c, hc⟩ := D.R.m_even
  simp only [Ranks.r, Ranks.rS]
  omega

theorem inGen_of_gRel : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (Λ : LV D) (d y y' : Dat Z FP), LocOver Λ y → InGen d y → GRel F F' y y' → InGen d y' := by
  intro D X Y u u' F F' w hw hG Z FP hB hRel Λ d y y' hov hgen hgr
  obtain ⟨hext, hUW, -, hmove⟩ := GlobalTheory.T.rationalAutomorphism_local_extension_moves_lattices D X Y u u' F F' w hw hG Z FP hB hRel
  obtain ⟨h, hh, hmv⟩ := hgr
  obtain ⟨y'', hov'', hmv''⟩ := hmove h hh Λ y hov
  have hact := fun p => GlobalTheory.T.exists_complementUnitary_mulAction_localInnerDatum (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS D.R.k (FP p)
    (finrank_Vp_k D p) (hRel p)
  choose act hiff _ using hact
  have heq : ∀ p, y' p = y'' p := by
    intro p
    obtain ⟨g1, he1, hm1⟩ := hmv p
    obtain ⟨g2, he2, hm2⟩ := hmv'' p
    obtain rfl : g1 = g2 := (hext h p).unique he1 he2
    have hg : g1 ∈ (FP p).UW0 := hUW h hh p g1 he1
    have a1 := ((hiff p) ⟨g1, hg⟩ (y p) (y' p)).1 hm1
    have a2 := ((hiff p) ⟨g1, hg⟩ (y p) (y'' p)).1 hm2
    rw [← a1, ← a2]
  refine ⟨fun p => ?_, ?_⟩
  · obtain ⟨g0, hg0, hm0⟩ := hgen.1 p
    obtain ⟨g1, he1, hm1⟩ := hmv p
    have hg1 : g1 ∈ (FP p).UW0 := hUW h hh p g1 he1
    have a0 := ((hiff p) ⟨g0, hg0⟩ (d p) (y p)).1 hm0
    have a1 := ((hiff p) ⟨g1, hg1⟩ (y p) (y' p)).1 hm1
    refine ⟨g1 * g0, mul_mem hg1 hg0, ((hiff p) ⟨g1 * g0, mul_mem hg1 hg0⟩ (d p) (y' p)).2 ?_⟩
    letI := act p
    let a : (FP p).UW0 := ⟨g1, hg1⟩
    let b : (FP p).UW0 := ⟨g0, hg0⟩
    have hm : (a * b) • d p = a • (b • d p) := mul_smul a b (d p)
    change (a * b) • d p = y' p
    rw [hm]
    change a • (act p).smul b (d p) = y' p
    rw [a0]
    exact a1
  · have hfin := ((GlobalTheory.T.hermitianLattice_local_global_principle D Z).1 Λ (Formalism.HermitianLatticesTheory.gmap h Λ) hov.1 hov''.1).1
    refine (hfin.union hgen.2).subset fun p hp => ?_
    by_cases hyd : y p = d p
    · left
      intro hl
      apply hp
      rw [heq p, ← hyd]
      obtain ⟨τ, hτ, hL⟩ := hov.2 p
      obtain ⟨τ'', hτ'', hL''⟩ := hov''.2 p
      have hlam : τ''.abelian₂ = τ.abelian₂ := by rw [hL'', hL]; exact hl.symm
      have key := GlobalTheory.T.hermitianDatum_eq_of_same_lattice (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS D.R.k (FP p)
        (finrank_Vp_k D p) (hRel p) (y'' p) (y p) τ'' τ hτ'' hτ
      exact key hlam
    · right
      exact hyd

end GlobalTheory.GenusStab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GluedLatticesStableUnderVectorStabilizerStatement
section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gluedLattices_stable_under_vectorStabilizer : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (M₀ : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Ub X u)) (ψ : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Ub X u) → ℝ≥0∞), (∀ (s : Formalism.HermitianLatticesTheory.isom (GlobalTheory.RowsOrb.hU X u)) (M : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Ub X u)), ψ (s • M) = ψ M) → GlobalTheory.Mass.Stable (GlobalTheory.RowsOrb.Gz X u) {L : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Wb X) | Submodule.IsLattice D.host.E L ∧ Formalism.HermitianLatticesTheory.IsUnimodular (GlobalTheory.RowsOrb.hb X) L ∧ (∀ t : D.host.E, t • GlobalTheory.RowsOrb.zb X u ∈ L ↔ t ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)) ∧ GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) L ∈ Formalism.HermitianLatticesTheory.genus (GlobalTheory.RowsOrb.hU X u) M₀} ∧ ∀ (g : GlobalTheory.RowsOrb.Gz X u) (L : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Wb X)), ψ (GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) (g • L)) = ψ (GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) L) := by
  first | exact @GlobalTheory.RowsOrb.StabSet.main | exact GlobalTheory.RowsOrb.StabSet.main | (intros; apply GlobalTheory.RowsOrb.StabSet.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramUnitaryFirstHermitianSpaceIsUnit
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in

theorem GlobalTheory.St.gramN_unitary_isUnit : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V), WittX X u wt → ∀ y₀ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) X.B.I.E, (y₀.map (starRingEnd X.B.I.E))ᵀ * (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm * y₀ = (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm → ∃ g : GL (Fin (D.R.N 0)) D.host.E, (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) = y₀.map X.ιE := by
  intro D X u wt hW y₀ hy
  obtain ⟨Q, Qi, G', hQQi, hQiQ, -, -, -, -, -, hM⟩ := GlobalTheory.St.qFrame_basis_gram D X u wt hW
  set G := (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm with hG
  have hJ := X.B.I.J_det
  have hJJ : X.B.I.J * X.B.I.J⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hJ)
  have h1 : (Q.map (starRingEnd X.B.I.E))ᵀ * (Qi.map (starRingEnd X.B.I.E))ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Matrix.map_mul, hQiQ]; simp
  have hdetM : IsUnit (Matrix.fromBlocks G 0 0 G').det := by
    rw [← hM]
    apply Matrix.isUnit_det_of_right_inverse (B := Qi * X.B.I.J⁻¹ * (Qi.map (starRingEnd X.B.I.E))ᵀ)
    calc (Q.map (starRingEnd X.B.I.E))ᵀ * X.B.I.J * Q * (Qi * X.B.I.J⁻¹ * (Qi.map (starRingEnd X.B.I.E))ᵀ)
        = (Q.map (starRingEnd X.B.I.E))ᵀ * X.B.I.J * (Q * Qi) * X.B.I.J⁻¹ * (Qi.map (starRingEnd X.B.I.E))ᵀ := by
          simp only [Matrix.mul_assoc]
      _ = (Q.map (starRingEnd X.B.I.E))ᵀ * (X.B.I.J * X.B.I.J⁻¹) * (Qi.map (starRingEnd X.B.I.E))ᵀ := by
          rw [hQQi]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by rw [hJJ, Matrix.mul_one, h1]
  rw [Matrix.det_fromBlocks_zero₂₁] at hdetM
  have hGdet : G.det ≠ 0 := (isUnit_of_mul_isUnit_left hdetM).ne_zero
  have hy0 : y₀.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hy
    rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at this
    exact hGdet this.symm
  have hd : (y₀.map X.ιE).det = X.ιE y₀.det := by
    simpa using (RingHom.map_det X.ιE.toRingHom y₀).symm
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (y₀.map X.ιE) ?_, rfl⟩
  rw [hd]; exact (map_ne_zero X.ιE).mpr hy0
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarFrameStabilizerLocalFixerSectionProductStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_frameStabilizer_local_fixer_section_product : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → ∀ μ0 : Measure (S0 (Fv F v) σ J P), μ0.IsHaarMeasure → (∀ s ∈ Ssub (Fv F v) σ J P, ∀ f : HA (Fv F v) σ J → ℝ≥0∞, Measurable f → ∫⁻ h, f (s * (h : HA (Fv F v) σ J) * s⁻¹) ∂μ0 = ∫⁻ h, f (h : HA (Fv F v) σ J) ∂μ0) → ∀ μU : Measure ({p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E), μU.IsAddHaarMeasure → ∃ μS : Measure (Ssub (Fv F v) σ J P), μS.IsHaarMeasure ∧ ∀ h : HA (Fv F v) σ J → ℝ≥0∞, Measurable h → ∀ t : ({p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E) → HA (Fv F v) σ J, (∀ x b, lin (Fv F v) σ J (t x) (ratV (F := F) (Fv F v) (F0 P b)) = ∑ a : Fin (r + 1), (if a = b then 1 else if h : a < b then x ⟨(a, b), h⟩ else 0 : Fv F v ⊗[F] E) • ratV (F := F) (Fv F v) (F0 P a)) → ∫⁻ s, h s ∂(amb μS) = ∫⁻ x, ∫⁻ s0, h ((s0 : HA (Fv F v) σ J) * t x) ∂μ0 ∂μU := by
  first | exact @GlobalTheory.HaarSectionProd.haar_S_local | exact GlobalTheory.HaarSectionProd.haar_S_local | (intros; apply GlobalTheory.HaarSectionProd.haar_S_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarVolumeThinTubeUnitaryProductAsymptotic
section
noncomputable section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Tube

theorem unrealify_cont {m : ℕ} : Continuous (unrealify (m := m)) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have : (fun x : EuclideanSpace ℝ (Fin m × Fin m × Bool) => unrealify x i j) =
      fun x => (x (i, j, false) : ℂ) + (x (i, j, true) : ℂ) * Complex.I := by
    funext x; apply Complex.ext <;> simp [unrealify]
  rw [this]; fun_prop

theorem chart_zero (k : ℕ) (η : ℝ) : chart η (0 : Par k) = 1 := by
  have h1 : unrealify (m := k) (0 : EuclideanSpace ℝ _) = 0 := by
    ext i j; apply Complex.ext <;> simp [unrealify]
  have h2 : hv (0 : EuclideanSpace ℂ (Fin k)) = 0 := by funext j; simp [hv]
  simp [chart, h1, h2, kap_one, sec_zero]

theorem thin_tube : ∀ (k : ℕ) (η : ℝ), 1 ≤ k → (η = 1 ∨ η = -1) → ∀ (μ : Measure (PI.MtM (k + 1))) (μ₀ : Measure (PI.MtM k)) (c c₀ : ℝ), 0 < c → 0 < c₀ → PI.IsHaarOnM (UH (Matrix.diagonal fun j : Fin (k + 1) => if j = Fin.last k then (η : ℂ) else 1)) μ → HasDens (UH (Matrix.diagonal fun j : Fin (k + 1) => if j = Fin.last k then (η : ℂ) else 1)) μ (ENNReal.ofReal c) → PI.IsHaarOnM (UH (1 : Matrix (Fin k) (Fin k) ℂ)) μ₀ → μ₀ Set.univ = 1 → HasDens (UH (1 : Matrix (Fin k) (Fin k) ℂ)) μ₀ (ENNReal.ofReal c₀) → Tendsto (fun t : ℝ => μ {g | |‖g (Fin.last k) (Fin.last k)‖ ^ 2 - 1| ≤ t} / ENNReal.ofReal (t ^ k)) (𝓝[>] 0) (𝓝 (ENNReal.ofReal (c / c₀ * (2 * Real.pi) ^ (k + 1) / (k.factorial : ℝ)))) := by
  intro k η hk hη μ μ₀ c c₀ hc hc₀ hμ hd hμ₀ h1 hd₀
  change PI.IsHaarOnM (UH (Hd k η)) μ at hμ
  change HasDens (UH (Hd k η)) μ _ at hd
  have hexp : ∀ X : lieE (UH (1 : Matrix (Fin k) (Fin k) ℂ)),
      NormedSpace.exp (unrealify (X : EuclideanSpace ℝ _)) ∈ UH (1 : Matrix (Fin k) (Fin k) ℂ) := fun X =>
    CCRuleCW.exp_mem_UH _ _ ((GlobalTheory.T.mem_lieE_unitaryGroup_iff_of_involutive k 1 X.1 (Matrix.one_mul _)).1 X.2)
  obtain ⟨L, hL, hvol⟩ := GlobalTheory.T.exists_productChart_tangentEquiv_ballVolume k η hk hη
  have hmem : ∀ᶠ x in 𝓝 (0 : Par k), chart η x ∈ UH (Hd k η) := by
    filter_upwards [Metric.ball_mem_nhds (0 : Par k) one_pos] with x hx
    have hw : ‖x.2.2‖ < 1 := ((norm_snd_le x.2).trans (norm_snd_le x)).trans_lt (mem_ball_zero_iff.1 hx)
    refine (comp hη (hexp x.1) (Complex.norm_exp_ofReal_mul_I x.2.1) ?_).1
    rw [nsq_hv]; have := norm_nonneg x.2.2; nlinarith
  have hch := GlobalTheory.T.tendsto_measure_image_ball_div_volume (k + 1) (UH (Hd k η)) μ _ (GlobalTheory.GramExp.isMatGroup_UH _ (Hd_sq k hη)) hμ hd (Par k)
    (chart η) L (chart_zero k η) hmem (fun i j => by
      obtain ⟨D, h, h'⟩ := GlobalTheory.T.unitaryTubeProductChart_hasStrictFDerivAt_entry k η i j
      exact ⟨D, h, fun v => by rw [h', hL]⟩)
  refine GlobalTheory.T.thinUnitaryTube_volume_limit_arith k c c₀ (fun t => μ (tubeO k η t)) _
    (fun ρ => μ₀ (expSet (UH (1 : Matrix (Fin k) (Fin k) ℂ)) (Metric.ball 0 ρ)))
    (fun ρ => volume (Metric.ball (0 : lieE (UH (1 : Matrix (Fin k) (Fin k) ℂ))) ρ)) hc hc₀ (fun t s ht hs => ⟨?_, ?_⟩)
    (fun ρ hρ => ⟨Metric.measure_ball_pos _ _ hρ, measure_ball_lt_top⟩) hd₀ (hch.congr' ?_)
  · refine measure_mono fun g hg => ?_
    exact (abs_id hη hg.1).le.trans hg.2.le
  · refine measure_mono_ae ?_
    have : ∀ᵐ g ∂μ, Matrix.of g ∈ UH (Hd k η) := hμ.2.2.1
    filter_upwards [this] with g hg h
    exact ⟨hg, ((abs_id hη hg).ge.trans h).trans_lt hs⟩
  · filter_upwards [Ioo_mem_nhdsGT one_pos] with ρ hρ
    have hρ' : ρ ^ 2 / 2 ≤ 1 := by nlinarith [hρ.1, hρ.2]
    have hA0 : Continuous fun X : lieE (UH (1 : Matrix (Fin k) (Fin k) ℂ)) =>
        (Matrix.of.symm (NormedSpace.exp (unrealify (X : EuclideanSpace ℝ _))) : PI.MtM k) :=
      GlobalTheory.GramExp.exp_cont.comp (unrealify_cont.comp continuous_subtype_val)
    have hA : MeasurableSet (expSet (UH (1 : Matrix (Fin k) (Fin k) ℂ)) (Metric.ball 0 ρ)) :=
      GlobalTheory.GramExp.measurableSet_image_ball hA0 _ _
    have hB : MeasurableSet ((fun θ : ℝ => Complex.exp (θ * Complex.I)) '' Metric.ball 0 ρ) :=
      GlobalTheory.GramExp.measurableSet_image_ball (by fun_prop) _ _
    obtain ⟨τ, t1, t2, t3, t4⟩ := phase_law hη hμ hρ'
    rw [hvol ρ hρ.1, chart_image hη hexp hρ.1 hρ.2, prod_top hη hμ hμ₀ h1 hρ' hA hB, ← t1 _ hB,
      GlobalTheory.T.rotationInvariant_measure_unitCircle_arc τ ρ t2 t3 t4 hρ.1 (by linarith [hρ.2, Real.pi_gt_three]), t1 _ MeasurableSet.univ]
    simp

end GlobalTheory.Tube
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticesLevelOneGenus
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G

theorem tlat_one_genus : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f : ℕ) (L M : Submodule (𝓞 E) (Fin n → E)), T.Prime → SplitsIn E T → Module.finrank ℚ E = 2 * f → TLat cm.sig J T f L → TLat cm.sig J T f M → ∃ h : UPts cm.sig J (Ad F), ∀ x, (h⁻¹).1.1 *ᵥ x ∈ hat F L ↔ x ∈ hat F M := by
  intro F E _ _ _ _ _ _ cm n J hJ hdet T f L M hT hS hf hL hM
  classical
  have hLat : IsLat L := hL.1
  have hMat : IsLat M := hM.1

  have hloc : ∀ v : HeightOneSpectrum (𝓞 F), ∃ g ∈ UPts cm.sig J (v.adicCompletion F),
      ∀ x, x ∈ loc v L ↔ g.1 *ᵥ x ∈ loc v M := by
    intro v
    by_cases hv : (T : 𝓞 F) ∈ v.asIdeal
    · exact GlobalTheory.T.exists_localUnitary_lattices_of_level F E cm n J hJ hdet T f L M hT hS hf hL hM v hv
    · exact GlobalTheory.T.exists_localUnitary_of_selfDual_at_place F E cm n J hJ hdet L M hLat hMat v
        (GlobalTheory.T.isLocallySelfDual_of_hermitianLatticeOfLevel F E cm n J hJ hdet T f L hL v hv)
        (GlobalTheory.T.isLocallySelfDual_of_hermitianLatticeOfLevel F E cm n J hJ hdet T f M hM v hv)
  choose g hgU hg using hloc

  let k : ∀ v : HeightOneSpectrum (𝓞 F), GL (Fin n) (E ⊗[F] v.adicCompletion F) :=
    fun v => if loc v L = loc v M then 1 else g v
  have hkU : ∀ v, k v ∈ UPts cm.sig J (v.adicCompletion F) := by
    intro v
    by_cases hv : loc v L = loc v M
    · simp only [k, if_pos hv]; exact one_mem _
    · simp only [k, if_neg hv]; exact hgU v
  have hfin : {v | k v ≠ 1}.Finite := by
    refine (GlobalTheory.T.localSpanOfLatticeAtPlace_eq_for_almost_all_places F E n L M hLat hMat).subset ?_
    intro v hv heq
    exact hv (by simp only [k, if_pos heq])
  obtain ⟨y, hyU, hy⟩ := GlobalTheory.T.exists_adelic_unitary_of_finite_support F E n cm.sig J k hkU hfin
  have hglob : ∀ x, x ∈ hat F L ↔ y.1 *ᵥ x ∈ hat F M := by
    rw [GlobalTheory.T.adelicLattice_carry_iff_forall_place F E n L M hLat hMat y]
    intro v x
    rw [hy v]
    by_cases hv : loc v L = loc v M
    · simp only [k, if_pos hv, Units.val_one, Matrix.one_mulVec, hv]
    · simp only [k, if_neg hv]; exact hg v x
  refine ⟨⟨y, hyU⟩, fun x => ?_⟩
  rw [hglob, Matrix.mulVec_mulVec]
  have hinv : ((⟨y, hyU⟩ : UPts cm.sig J (Ad F))⁻¹).1 = y⁻¹ := rfl
  rw [hinv, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

end GlobalTheory.St.G
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InnerPreimageEqOfLocalInnerLatticeEqStatement
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.innerPreimage_eq_of_local_innerLattice_eq : ∀ (D : D7) (Z : LocDat D) {T : D.host.E} (G : LFlag (VS D) D.R.rS T) (Fr : ∀ p : PlF D, LocNG.FrameD (locH Z p) D.R.rS), (∀ p, (Fr p).f = (fun a => frFac Z.δ p a • baseChange₂ D p (frame G a))) → ∀ Λ₁ Λ₂ : LV D, Submodule.IsLattice D.host.E Λ₁ → Submodule.IsLattice D.host.E Λ₂ → (∀ p, (locH Z p).Lset (lattice₂ D Z.M p Λ₁) (Fr p).f = (locH Z p).Lset (lattice₂ D Z.M p Λ₂) (Fr p).f) → Lsub Λ₁ G = Lsub Λ₂ G := by
  first | exact @GlobalTheory.Unfold.LsubG.lsub_eq_of_local | exact GlobalTheory.Unfold.LsubG.lsub_eq_of_local | (intros; apply GlobalTheory.Unfold.LsubG.lsub_eq_of_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralExtensionFiniteAdelesBasicPropertiesStatement
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralExtensionFiniteAdeles_basic_properties : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], (∀ a : E ⊗[F] Ad F, a ∈ OAd F E ↔ ∀ v : HeightOneSpectrum (𝓞 F), prV (E := E) v a ∈ intV E v) ∧ (∀ a ∈ OAd F E, ∀ m : ℕ, 0 < m → ∃ x : 𝓞 E, ∃ t ∈ OAd F E, a = inclE (F := F) (Ad F) (x : E) + (m : E ⊗[F] Ad F) * t) ∧ (∀ a : E ⊗[F] Ad F, (∀ m : ℕ, 0 < m → ∃ t ∈ OAd F E, a = (m : E ⊗[F] Ad F) * t) → a = 0) ∧ (∀ a : E ⊗[F] Ad F, ∃ m : ℕ, 0 < m ∧ (m : E ⊗[F] Ad F) * a ∈ OAd F E) ∧ (∀ x : E, inclE (F := F) (Ad F) x ∈ OAd F E ↔ x ∈ intOE E) := by
  first | exact @GlobalTheory.St.G.IntAd.integral_adeles_properties | exact GlobalTheory.St.G.IntAd.integral_adeles_properties | (intros; apply GlobalTheory.St.G.IntAd.integral_adeles_properties <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsClosedEmbeddingOfCongruenceSubgroupsConjStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosedEmbedding_of_congruenceSubgroups_conj : ∀ (I I' : AutInst) (j : I'.Gf →* I.Gf) (xf : I.Gf), (∀ (N : ℕ) (g : I'.Gf), g ∈ I'.Kg N ↔ xf⁻¹ * j g * xf ∈ I.Kg N) → Topology.IsClosedEmbedding j := by
  first | exact @GlobalTheory.StabUnfold.isClosedEmbedding_of_conj_Kg | exact GlobalTheory.StabUnfold.isClosedEmbedding_of_conj_Kg | (intros; apply GlobalTheory.StabUnfold.isClosedEmbedding_of_conj_Kg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsUnimodularOfLocalStandardLatticeTranslatesStatement
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnimodular_of_local_standardLattice_translates : ∀ (D : D7) (Z : LocDat D) (A : ∀ p : PlF D, LocNG.FrameD (locH Z p) D.R.rS) (Λ : LV D), Submodule.IsLattice D.host.E Λ → (∀ p, ∃ n ∈ (A p).N, ∃ L, (A p).IsInner L ∧ lattice₂ D Z.M p Λ = LocNG.img n ((A p).LamStd L)) → Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ := by
  first | exact @GlobalTheory.Unfold.StdDual.unimodular_of_local | exact GlobalTheory.Unfold.StdDual.unimodular_of_local | (intros; apply GlobalTheory.Unfold.StdDual.unimodular_of_local <;> assumption)
end

