import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0350
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactHaarRightInvariantInst
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0006
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLintegralEqOfMeasurable
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0143
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0142
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaDecompositionUnitaryIsotropicFlag
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0349
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PerpendicularRankIdealBound
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
import Formalism.LocalToGlobal.Divisibility.DivisionCompatibleToSub2Indef2
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
import Formalism.LocalToGlobal.GroupLattices.JointServices.LevelOperatorFixesImage
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RadicalCoordinatesBoundedMajorantLengths
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RankOneUnitaryIntegrationFormulaExactConstant
import Formalism.PeriodIntegrals.Bundle0008
import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Formalism.LocalRingCardinality.DataCD
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0352
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.RealPlaceAnalysis.FinalF

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InnerDatumStableIffIdentificationsCompatible
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.GdatIota
open Formalism.L2.SG.Pf GlobalTheory.StabCnt

variable {D : D7} {T T' : D.host.E}

theorem mem_gmap' (φ : GV D) (M : LV D) (x : (VS D).V) : x ∈ Formalism.HermitianLatticesTheory.gmap φ M ↔ φ.symm x ∈ M := by
  rw [← gmap_apply_mem φ M, LinearEquiv.apply_symm_apply]

theorem xlam_adapt {A B : LFlag (VS D) D.R.rS T} {φ : GV D} (h : Adapt φ A B) (M : LV D) :
    XLam (Formalism.HermitianLatticesTheory.gmap φ M) B = Formalism.HermitianLatticesTheory.gmap φ (XLam M A) := by
  rw [XLam, XLam, gmap_inf', gmap_toO, adapt_xsp h]

theorem lrep_adapt {A B : LFlag (VS D) D.R.rS T} {φ : GV D} (h : Adapt φ A B) (M : LV D) :
    Lrep (Formalism.HermitianLatticesTheory.gmap φ M) B = Formalism.HermitianLatticesTheory.gmap φ (Lrep M A) := by
  rw [Lrep, Lrep, gmap_inf', gmap_toO, adapt_orth h]

theorem lsub_adapt {A B : LFlag (VS D) D.R.rS T} {φ : GV D} (h : Adapt φ A B) (M : LV D) :
    Lsub (Formalism.HermitianLatticesTheory.gmap φ M) B = Formalism.HermitianLatticesTheory.gmap φ (Lsub M A) := by
  rw [Lsub, Lsub, lrep_adapt h, gmap_inf', gmap_sup', gmap_toO, gmap_toO, adapt_xsp h, adapt_orth h]

theorem ngx_adapt {A B : LFlag (VS D) D.R.rS T} {A' B' : LFlag (VS D) D.R.rS T'} {φ : GV D} (h : Adapt φ A B)
    (h' : Adapt φ A' B') (M : LV D) (n : ℕ) :
    NgX (Formalism.HermitianLatticesTheory.gmap φ M) n B B' = Formalism.HermitianLatticesTheory.gmap φ (NgX M n A A') := by
  rw [NgX, NgX, gmap_sup', gmap_sup', gmap_ideal_smul, xlam_adapt h, xlam_adapt h']

theorem aut_lrep {F : LFlag (VS D) D.R.rS T} {M : LV D} {A : GV D} (hA : A ∈ Aut0 F M) (x : (VS D).V) :
    A x ∈ Lrep M F ↔ x ∈ Lrep M F := by
  have := lrep_adapt hA.1 M
  rw [hA.2] at this
  rw [← gmap_apply_mem A (Lrep M F) x, ← this]

theorem aut_lrep_symm {F : LFlag (VS D) D.R.rS T} {M : LV D} {A : GV D} (hA : A ∈ Aut0 F M) (x : (VS D).V) :
    A.symm x ∈ Lrep M F ↔ x ∈ Lrep M F := by
  rw [← aut_lrep hA (A.symm x), LinearEquiv.apply_symm_apply]

theorem lsub_eq {F : LFlag (VS D) D.R.rS T} {M : LV D} {A h : GV D} (hA : A ∈ Aut0 F M) (hh : Adapt h F F)
    (hc : ∀ x ∈ orth (VS D) (Xsp F), h x - A x ∈ Xsp F) : Lsub (Formalism.HermitianLatticesTheory.gmap h M) F = Lsub M F := by
  rw [lsub_adapt hh]
  ext y
  rw [mem_gmap']
  constructor
  · rintro ⟨hy, hy'⟩
    obtain ⟨l, hl, ξ, hξ, e⟩ := Submodule.mem_sup.1 hy
    have hy2 : y ∈ orth (VS D) (Xsp F) := by
      have := mem_of_map_eq (adapt_orth hh) hy'
      rwa [LinearEquiv.apply_symm_apply] at this
    refine ⟨?_, hy2⟩
    have e2 : y = A l + ((h l - A l) + h ξ) := by
      have : y = h (l + ξ) := by rw [e, LinearEquiv.apply_symm_apply]
      rw [this, map_add]; abel
    rw [e2]
    exact Submodule.add_mem_sup ((aut_lrep hA l).2 hl)
      (show _ ∈ Xsp F from add_mem (hc l hl.2) (mem_of_map_eq (adapt_xsp hh) hξ))
  · rintro ⟨hy, hy'⟩
    obtain ⟨l, hl, ξ, hξ, e⟩ := Submodule.mem_sup.1 hy
    refine ⟨?_, symm_mem_of_map_eq (adapt_orth hh) hy'⟩
    have hm := (aut_lrep_symm hA l).2 hl
    have h1 := hc _ hm.2
    rw [LinearEquiv.apply_symm_apply] at h1
    have e2 : h.symm y = A.symm l + h.symm (ξ - (h (A.symm l) - l)) := by
      rw [← e]; simp only [map_add, map_sub, LinearEquiv.symm_apply_apply]; abel
    rw [e2]
    exact Submodule.add_mem_sup hm
      (show _ ∈ Xsp F from symm_mem_of_map_eq (adapt_xsp hh) (sub_mem (show ξ ∈ Xsp F from hξ) h1))

theorem ngx_shift {F : LFlag (VS D) D.R.rS T} {F' : LFlag (VS D) D.R.rS T'} {M : LV D} {n : ℕ}
    {l m l' m' : (VS D).V} (hl : l ∈ Lrep M F) (hm : m ∈ Lrep M F) (hl' : l' ∈ Lrep M F') (hm' : m' ∈ Lrep M F')
    (h1 : l - m ∈ Xsp F) (h2 : l' - m' ∈ Xsp F') (h : m - m' ∈ NgX M n F F') : l - l' ∈ NgX M n F F' := by
  have e : l - l' = (m - m') + (l - m) - (l' - m') := by abel
  rw [e]
  refine sub_mem (add_mem h ?_) ?_
  · exact Submodule.mem_sup_left (Submodule.mem_sup_right ⟨M.sub_mem hl.1 hm.1, h1⟩)
  · exact Submodule.mem_sup_right ⟨M.sub_mem hl'.1 hm'.1, h2⟩

theorem gdat_iff {F : LFlag (VS D) D.R.rS T} {F' : LFlag (VS D) D.R.rS T'} {M : LV D} {A A' h : GV D}
    (hA : A ∈ Aut0 F M) (hA' : A' ∈ Aut0 F' M) (hh : Adapt h F F) (hh' : Adapt h F' F')
    (hc : ∀ x ∈ orth (VS D) (Xsp F), h x - A x ∈ Xsp F)
    (hc' : ∀ x ∈ orth (VS D) (Xsp F'), h x - A' x ∈ Xsp F') :
    gdat F F' (Formalism.HermitianLatticesTheory.gmap h M) = gdat F F' M ↔
      ∀ x' ∈ Lrep M F', ∀ l ∈ Lrep M F,
        (l - x' ∈ NgX M (gS D) F F' ↔ A l - A' x' ∈ NgX M (gS D) F F') := by
  have hG : ∀ p : (VS D).V × (VS D).V, p ∈ (gdat F F' (Formalism.HermitianLatticesTheory.gmap h M)).2.2 ↔
      ∃ l' ∈ Lrep M F', ∃ l ∈ Lrep M F, p.1 - A' l' ∈ Xsp F' ∧ p.2 - A l ∈ Xsp F ∧
        l - l' ∈ NgX M (gS D) F F' := by
    intro p
    show (∃ l' ∈ Lrep (Formalism.HermitianLatticesTheory.gmap h M) F', ∃ l ∈ Lrep (Formalism.HermitianLatticesTheory.gmap h M) F, p.1 - l' ∈ Xsp F' ∧
      p.2 - l ∈ Xsp F ∧ l - l' ∈ NgX (Formalism.HermitianLatticesTheory.gmap h M) (gS D) F F') ↔ _
    rw [lrep_adapt hh, lrep_adapt hh', ngx_adapt hh hh']
    constructor
    · rintro ⟨l', hl', l, hl, h1, h2, h3⟩
      obtain ⟨m', rfl⟩ := h.surjective l'
      obtain ⟨m, rfl⟩ := h.surjective l
      rw [gmap_apply_mem] at hl hl'
      rw [← map_sub, gmap_apply_mem] at h3
      refine ⟨m', hl', m, hl, ?_, ?_, h3⟩
      · simpa using add_mem h1 (hc' m' hl'.2)
      · simpa using add_mem h2 (hc m hl.2)
    · rintro ⟨m', hl', m, hl, h1, h2, h3⟩
      refine ⟨h m', (gmap_apply_mem _ _ _).2 hl', h m, (gmap_apply_mem _ _ _).2 hl, ?_, ?_, ?_⟩
      · simpa using sub_mem h1 (hc' m' hl'.2)
      · simpa using sub_mem h2 (hc m hl.2)
      · rw [← map_sub, gmap_apply_mem]; exact h3
  have hG0 : ∀ p : (VS D).V × (VS D).V, p ∈ (gdat F F' M).2.2 ↔
      ∃ l' ∈ Lrep M F', ∃ l ∈ Lrep M F, p.1 - l' ∈ Xsp F' ∧ p.2 - l ∈ Xsp F ∧
        l - l' ∈ NgX M (gS D) F F' := fun p => Iff.rfl
  constructor
  · intro he x' hx' l hl
    have hx2 := (aut_lrep hA' x').2 hx'
    have hl2 := (aut_lrep hA l).2 hl
    constructor
    · intro hN
      have : (A' x', A l) ∈ (gdat F F' M).2.2 := by
        rw [← he, hG]
        exact ⟨x', hx', l, hl, by simp, by simp, hN⟩
      obtain ⟨m', hm', m, hm, h1, h2, h3⟩ := (hG0 _).1 this
      exact ngx_shift hl2 hm hx2 hm' h2 h1 h3
    · intro hN
      have : (A' x', A l) ∈ (gdat F F' (Formalism.HermitianLatticesTheory.gmap h M)).2.2 := by
        rw [he, hG0]
        exact ⟨A' x', hx2, A l, hl2, by simp, by simp, hN⟩
      obtain ⟨m', hm', m, hm, h1, h2, h3⟩ := (hG _).1 this
      have h1' := symm_mem_of_map_eq (adapt_xsp hA'.1) h1
      have h2' := symm_mem_of_map_eq (adapt_xsp hA.1) h2
      simp only [map_sub, LinearEquiv.symm_apply_apply] at h1' h2'
      exact ngx_shift hl hm hx' hm' h2' h1' h3
  · intro hR
    refine Prod.ext (lsub_eq hA hh hc) (Prod.ext (lsub_eq hA' hh' hc') ?_)
    ext p
    rw [hG, hG0]
    constructor
    · rintro ⟨l', hl', l, hl, h1, h2, h3⟩
      exact ⟨A' l', (aut_lrep hA' l').2 hl', A l, (aut_lrep hA l).2 hl, h1, h2, (hR l' hl' l hl).1 h3⟩
    · rintro ⟨l', hl', l, hl, h1, h2, h3⟩
      obtain ⟨m', rfl⟩ := A'.surjective l'
      obtain ⟨m, rfl⟩ := A.surjective l
      rw [aut_lrep hA'] at hl'
      rw [aut_lrep hA] at hl
      exact ⟨m', hl', m, hl, h1, h2, (hR m' hl' m hl).2 h3⟩

theorem aut_conj {A B : LFlag (VS D) D.R.rS T} {M : LV D} {g b : GV D} (hg : Adapt g A B) (hb : b ∈ Aut0 A M) :
    g * b * g⁻¹ ∈ Aut0 B (Formalism.HermitianLatticesTheory.gmap g M) := by
  refine ⟨?_, (conj_gmap g b M).2 hb.2⟩
  rw [mul_assoc]
  exact adapt_mul (adapt_mul (adapt_inv hg) hb.1) hg

theorem gdat_iff_iotaCompat : ∀ (D : D7) (T T' : D.host.E) (F0 F : LFlag (VS D) D.R.rS T) (F0' F' : LFlag (VS D) D.R.rS T') (lam lam' Λ : LV D) (γ g h b₁ b₂ : GV D), γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → Formalism.HermitianLatticesTheory.gmap γ lam' = lam → Adapt g F0 F → Adapt g (mapLF γ F0') F' → Λ = Formalism.HermitianLatticesTheory.gmap g lam → b₁ ∈ Aut0 F0 lam → b₂ ∈ Aut0 F0' lam' → h ∈ H0 F F' → (∀ x ∈ orth (VS D) (Xsp F), h x - (g * b₁ * g⁻¹) x ∈ Xsp F) → (∀ x ∈ orth (VS D) (Xsp F'), h x - (g * γ * b₂ * γ⁻¹ * g⁻¹) x ∈ Xsp F') → (gdat F F' (Formalism.HermitianLatticesTheory.gmap h Λ) = gdat F F' Λ ↔ IotaCompat lam F0 (mapLF γ F0') (mapLF (b₁ * γ * b₂⁻¹) F0') (b₁ * γ * b₂⁻¹ * γ⁻¹) (gS D)) := by
  intro D T T' F0 F F0' F' lam lam' Λ γ g h b₁ b₂ hγ hlam hg hg' hΛ hb₁ hb₂ hh hc hc'
  have hγa : Adapt γ F0' (mapLF γ F0') := adapt_mapLF hγ
  have hc₂ : γ * b₂ * γ⁻¹ ∈ Aut0 (mapLF γ F0') lam := by
    have := aut_conj hγa hb₂
    rwa [hlam] at this
  have hA := aut_conj hg hb₁
  have hA' := aut_conj hg' hc₂
  have e1 : g * γ * b₂ * γ⁻¹ * g⁻¹ = g * (γ * b₂ * γ⁻¹) * g⁻¹ := by group
  rw [e1] at hc'
  subst hΛ
  rw [gdat_iff hA hA' (frameAdaptedIsometry_of_fixing_both_frames hh).1 (frameAdaptedIsometry_of_fixing_both_frames hh).2 hc hc', lrep_adapt hg, lrep_adapt hg', ngx_adapt hg hg']
  have hi : b₁ * γ * b₂⁻¹ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hb₁.1.1 hγ) (Subgroup.inv_mem _ hb₂.1.1)
  have hβ : Adapt (b₁ * γ * b₂⁻¹ * (b₂ * γ⁻¹)) (mapLF γ F0') (mapLF (b₁ * γ * b₂⁻¹) F0') :=
    adapt_mul (adapt_mul (adapt_inv hγa) hb₂.1) (adapt_mapLF hi)
  have e2 : b₁ * γ * b₂⁻¹ * (b₂ * γ⁻¹) = b₁ := by group
  rw [e2] at hβ
  have hN := ngx_adapt hb₁.1 hβ lam (gS D)
  rw [hb₁.2] at hN
  have e3 : b₁ * γ * b₂⁻¹ * γ⁻¹ = b₁ * (γ * b₂ * γ⁻¹)⁻¹ := by group
  unfold IotaCompat
  rw [hN, e3]
  generalize γ * b₂ * γ⁻¹ = c at hc₂ ⊢
  have e4 : ∀ x, (b₁ * c⁻¹) (c x) = b₁ x := fun x => by
    change b₁ (c.symm (c x)) = _
    rw [LinearEquiv.symm_apply_apply]
  constructor
  · intro H x' hx' l hl
    obtain ⟨y, rfl⟩ := c.surjective x'
    obtain ⟨m, rfl⟩ := b₁.surjective l
    rw [aut_lrep hc₂] at hx'
    rw [aut_lrep hb₁] at hl
    have := H (g y) ((gmap_apply_mem _ _ _).2 hx') (g m) ((gmap_apply_mem _ _ _).2 hl)
    simp only [conj_apply, LinearEquiv.symm_apply_apply, ← map_sub, gmap_apply_mem] at this
    rw [e4, ← map_sub, gmap_apply_mem]
    exact this.symm
  · intro H x' hx' l hl
    obtain ⟨y, rfl⟩ := g.surjective x'
    obtain ⟨m, rfl⟩ := g.surjective l
    rw [gmap_apply_mem] at hx' hl
    have := H (c y) ((aut_lrep hc₂ y).2 hx') (b₁ m) ((aut_lrep hb₁ m).2 hl)
    rw [e4, ← map_sub, gmap_apply_mem] at this
    simp only [conj_apply, LinearEquiv.symm_apply_apply, ← map_sub, gmap_apply_mem]
    exact this.symm

end GlobalTheory.GdatIota
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrableOfIntegrableProdOfContinuous
section
noncomputable section

open MeasureTheory NumberField Formalism.MainNotions.S
open scoped ENNReal InnerProductSpace

namespace GlobalTheory.ProdFactor

theorem integrable_of_integrable_prod {ι : Type} [Fintype ι] {E : ι → Type} {mE : ∀ i, MeasurableSpace (E i)}
    {μ : ∀ i, Measure (E i)} [∀ i, SigmaFinite (μ i)] {f : ∀ i, E i → ℂ}
    (hm : ∀ i, AEStronglyMeasurable (f i) (μ i)) (h0 : ∀ i, ¬ f i =ᵐ[μ i] 0)
    (h : Integrable (fun x : ∀ i, E i => ∏ i, f i (x i)) (Measure.pi μ)) (i : ι) :
    Integrable (f i) (μ i) := by

  by_contra hi
  have hn : ¬ Integrable (fun x => ‖f i x‖) (μ i) := fun h' => hi ((integrable_norm_iff (hm i)).1 h')
  have hprod : ∫ x : (∀ j, E j), ∏ j, ‖f j (x j)‖ ∂(Measure.pi μ) = 0 :=
    (integral_fintype_prod_eq_prod (μ := μ) (fun j (y : E j) => ‖f j y‖)).trans
      (Finset.prod_eq_zero (Finset.mem_univ i) (integral_undef hn))
  have hnorm : Integrable (fun x : ∀ j, E j => ∏ j, ‖f j (x j)‖) (Measure.pi μ) := by
    have h' := h.norm
    simp only [norm_prod] at h'
    exact h'
  have hae := (integral_eq_zero_iff_of_nonneg
    (fun x => Finset.prod_nonneg fun j _ => norm_nonneg (f j (x j))) hnorm).1 hprod
  have hbox : Measure.pi μ (Set.univ.pi fun j => {y | f j y ≠ 0}) = 0 := by
    refine measure_mono_null ?_ (ae_iff.1 hae)
    intro x hx
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_ofPred_eq] at hx
    simp only [Set.mem_ofPred_eq, Pi.zero_apply]
    exact Finset.prod_ne_zero_iff.2 fun j _ => norm_ne_zero_iff.2 (hx j)
  rw [Measure.pi_pi] at hbox
  refine (Finset.prod_ne_zero_iff.2 fun j _ => ?_) hbox
  intro hz
  exact h0 j (ae_iff.2 (by simpa using hz))

theorem integrable_of_integrable_prod_of_continuous {ι : Type} [Fintype ι] {E : ι → Type}
    [∀ i, TopologicalSpace (E i)] {mE : ∀ i, MeasurableSpace (E i)} [∀ i, OpensMeasurableSpace (E i)]
    {μ : ∀ i, Measure (E i)} [∀ i, SigmaFinite (μ i)] [∀ i, (μ i).IsOpenPosMeasure] {f : ∀ i, E i → ℂ}
    (hc : ∀ i, Continuous (f i)) (h0 : ∀ i, ∃ x, f i x ≠ 0)
    (h : Integrable (fun x : ∀ i, E i => ∏ i, f i (x i)) (Measure.pi μ)) (i : ι) :
    Integrable (f i) (μ i) := by

  refine integrable_of_integrable_prod (fun j => (hc j).aestronglyMeasurable) (fun j hj => ?_) h i
  obtain ⟨x, hx⟩ := h0 j
  exact hx (congrFun (((hc j).ae_eq_iff_eq (μ j) continuous_zero).1 hj) x)

section Local

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem continuous_coefOn (hU : IsURepOn (UJset ε) σ) (v w : H) : Continuous (coefOn (ε := ε) σ v w) := by
  obtain ⟨-, -, hcont⟩ := hU
  have hσ : Continuous fun g : Formalism.REAL.UJ ε => σ (umat g) v :=
    (hcont v).comp_continuous (Units.continuous_val.comp continuous_subtype_val) fun g => g.2
  exact continuous_const.inner hσ

theorem coefOn_one (hU : IsURepOn (UJset ε) σ) {w : H} (hw : ‖w‖ = 1) : coefOn (ε := ε) σ w w 1 = 1 := by
  obtain ⟨⟨h1, -⟩, -, -⟩ := hU
  have hu : umat (1 : Formalism.REAL.UJ ε) = 1 := rfl
  show ⟪w, σ (umat (1 : Formalism.REAL.UJ ε)) w⟫_ℂ = 1
  rw [hu, h1, one_apply_eq_self, inner_self_eq_norm_sq_to_K, hw]
  norm_num

theorem fdegOf_pos (hU : IsURepOn (UJset ε) σ) (hsq : IsSqIntOn ε σ) {w : H} (hw : ‖w‖ = 1) :
    0 < fdegOf (Formalism.REAL.muG ε) σ w := by

  show 0 < ‖w‖ ^ 4 / ∫ g, ‖coefOn (ε := ε) σ w w g‖ ^ 2 ∂(Formalism.REAL.muG ε)
  rw [hw, one_pow]
  refine div_pos one_pos ?_
  have hcont : Continuous fun g : Formalism.REAL.UJ ε => ‖coefOn (ε := ε) σ w w g‖ ^ 2 :=
    (continuous_coefOn hU w w).norm.pow 2
  have hint : Integrable (fun g => ‖coefOn (ε := ε) σ w w g‖ ^ 2) (Formalism.REAL.muG ε) :=
    (hsq w w).norm.integrable_sq
  rw [integral_pos_iff_support_of_nonneg (fun g => by positivity) hint]
  refine hcont.isOpen_support.measure_pos _ ⟨1, ?_⟩
  simp [Function.mem_support, coefOn_one hU hw]

end Local

theorem integrable_factor {ι : Type} [Fintype ι] {n : ℕ} (ε : ι → Fin n → Bool) {H : ι → Type}
    [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
    (σ : ∀ v, Matrix (Fin n) (Fin n) ℂ → (H v →L[ℂ] H v)) (w : ∀ v, H v) (d : ι → ℝ)
    (hU : ∀ v, IsURepOn (UJset (ε v)) (σ v)) (hw : ∀ v, ‖w v‖ = 1) (hd : ∀ v, d v ≠ 0)
    (h : Integrable (fun g : ∀ v, Formalism.REAL.UJ (ε v) =>
      ∏ v, (d v : ℂ) * star (coefOn (ε := ε v) (σ v) (w v) (w v) (g v))) (Measure.pi fun v => Formalism.REAL.muG (ε v)))
    (v : ι) :
    Integrable (fun g => (d v : ℂ) * star (coefOn (ε := ε v) (σ v) (w v) (w v) g)) (Formalism.REAL.muG (ε v)) := by

  exact integrable_of_integrable_prod_of_continuous (E := fun v => Formalism.REAL.UJ (ε v))
    (μ := fun v => Formalism.REAL.muG (ε v))
    (f := fun v g => (d v : ℂ) * star (coefOn (ε := ε v) (σ v) (w v) (w v) g))
    (fun v => continuous_const.mul (continuous_coefOn (hU v) (w v) (w v)).star)
    (fun v => ⟨1, by simp [coefOn_one (hU v) (hw v), hd v]⟩) h v

theorem integrable_factor' {ι : Type} [Fintype ι] {n : ℕ} (ε : ι → Fin n → Bool) {H : ι → Type}
    [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
    (σ : ∀ v, Matrix (Fin n) (Fin n) ℂ → (H v →L[ℂ] H v)) (w : ∀ v, H v) (d : ι → ℝ)
    (hU : ∀ v, IsURepOn (UJset (ε v)) (σ v)) (hw : ∀ v, ‖w v‖ = 1) (hd : ∀ v, d v ≠ 0)
    (h : Integrable (fun g : ∀ v, Formalism.REAL.UJ (ε v) =>
      ((∏ v, d v : ℝ) : ℂ) * star (∏ v, coefOn (ε := ε v) (σ v) (w v) (w v) (g v)))
      (Measure.pi fun v => Formalism.REAL.muG (ε v))) (v : ι) :
    Integrable (fun g => (d v : ℂ) * star (coefOn (ε := ε v) (σ v) (w v) (w v) g)) (Formalism.REAL.muG (ε v)) := by
  have hfun : (fun g : ∀ v, Formalism.REAL.UJ (ε v) =>
      ((∏ v, d v : ℝ) : ℂ) * star (∏ v, coefOn (ε := ε v) (σ v) (w v) (w v) (g v))) =
      fun g => ∏ v, (d v : ℂ) * star (coefOn (ε := ε v) (σ v) (w v) (w v) (g v)) := by
    funext g
    rw [Complex.ofReal_prod, star_prod, Finset.prod_mul_distrib]
  rw [hfun] at h
  exact integrable_factor ε σ w d hU hw hd h v

end GlobalTheory.ProdFactor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaIntegrationFormulaUpToConstant
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.IwasawaShape

theorem gauge_ne_zero_finite {n : ℕ} {ε : Fin n → Bool} (M : Subgroup (Formalism.REAL.UJ ε)) (d : ℕ)
    (μ : Measure (Formalism.REAL.UJ ε)) (hM : IsClosed (M : Set (Formalism.REAL.UJ ε)))
    (hμ : IsGaugeSub (M : Set (Formalism.REAL.UJ ε)) d μ) : μ ≠ 0 ∧ IsFiniteMeasureOnCompacts μ := by
  obtain ⟨h0, hinv, hlim⟩ := hμ
  have hL0 : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≠ 0 :=
    (Metric.measure_ball_pos volume _ one_pos).ne'
  have hLt : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≠ ⊤ := measure_ball_lt_top.ne
  have hpos : ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < r := self_mem_nhdsWithin
  obtain ⟨r, hr, hr0, hrt⟩ := (hpos.and ((hlim.eventually_ne hL0).and (hlim.eventually_ne hLt))).exists
  set B : Set (Formalism.REAL.UJ ε) := {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r} with hB
  have hden0 : ENNReal.ofReal (r ^ d) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact pow_pos hr d
  have hB0 : μ B ≠ 0 := by
    intro h; apply hr0; rw [h, ENNReal.zero_div]
  have hBt : μ B ≠ ⊤ := by
    intro h; apply hrt; rw [h]; exact ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top
  have hf : Continuous fun g : Formalism.REAL.UJ ε => Real.sqrt (Formalism.REAL.hs (uMat g - 1)) := by
    refine Real.continuous_sqrt.comp ?_
    unfold Formalism.REAL.hs
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun k _ => ?_
    refine (Continuous.norm ?_).pow 2
    exact (continuous_apply k).comp ((continuous_apply i).comp
      (GlobalTheory.FlagLeviGroup.continuous_uMat.sub continuous_const))
  have hBm : MeasurableSet B := (isClosed_le hf continuous_const).measurableSet
  have hBn : B ∈ nhds (1 : Formalism.REAL.UJ ε) := by
    have hO : IsOpen {g : Formalism.REAL.UJ ε | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) < r} :=
      isOpen_lt hf continuous_const
    refine Filter.mem_of_superset (hO.mem_nhds ?_) fun g hg => by
      rw [hB, Set.mem_ofPred_eq]; rw [Set.mem_ofPred_eq] at hg; exact hg.le
    show Real.sqrt (Formalism.REAL.hs (uMat (1 : Formalism.REAL.UJ ε) - 1)) < r
    rw [GlobalTheory.FlagLeviGroup.uMat_one, sub_self]
    unfold Formalism.REAL.hs
    simpa using hr
  refine ⟨fun h => hB0 (by rw [h]; rfl), ?_⟩
  exact finiteOnCompacts_of_nhds M μ h0 hM (fun s hs => hinv s hs) B hBm hBn hBt

theorem coe_KG {n : ℕ} (ε : Fin n → Bool) : (Formalism.REAL.KG ε : Set (Formalism.REAL.UJ ε)) = maxK ε := by
  ext g
  have hJ := GlobalTheory.RealIwasawa.uMat_form g
  change g ∈ Formalism.REAL.KG ε ↔ (uMat g)ᴴ * uMat g = 1
  rw [Formalism.REAL.mem_KG]
  change (uMat g ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ uMat g * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * uMat g) ↔ _
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  have h' : uMat g * (uMat g)ᴴ = 1 := mul_eq_one_comm.mp h
  calc uMat g * Formalism.REAL.Jm ε = uMat g * ((uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g) := by rw [hJ]
    _ = (uMat g * (uMat g)ᴴ) * Formalism.REAL.Jm ε * uMat g := by simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε * uMat g := by rw [h', Matrix.one_mul]

theorem iwasawa_shape : ∀ (n : ℕ) (ε : Fin n → Bool) (p q : ℕ), (univ.filter fun a => ε a = true).card = p → (univ.filter fun a => ε a = false).card = q → ∀ (a : ℕ) (j : Fin a → ℕ), (∀ i, 1 ≤ j i) → ∀ (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∀ (μN μM μK : Measure (Formalism.REAL.UJ ε)), IsGaugeSub (flagN ε W) (dimN n j) μN → IsGaugeSub (flagM ε W) ((n - 2 * ∑ i, j i) ^ 2 + 2 * ∑ i, j i ^ 2) μM → μK (maxK ε)ᶜ = 0 → μK Set.univ = 1 → (∀ k ∈ maxK ε, μK.map (fun g => k * g) = μK) → ∃ κ : ENNReal, κ ≠ 0 ∧ κ ≠ ⊤ ∧ ∀ φ : Formalism.REAL.UJ ε → ENNReal, Measurable φ → ∫⁻ g, φ g ∂(Formalism.REAL.muG ε) = κ * ∫⁻ u, ∫⁻ m, ENNReal.ofReal (layerProd n 1 j (locSize j W (uMat m)) id) * ∫⁻ k, φ (u * m * k) ∂μK ∂μM ∂μN := by
  intro n ε p q _ _ a j hj W hW μN μM μK hN hM hK0 hK1 hKi
  obtain ⟨⟨N, hNs⟩, hNc, -⟩ := GlobalTheory.FlagMeas.UnipRad.flagN_subgroup_closed_keeps n ε a j W hW
  obtain ⟨⟨M, hMs⟩, hMc, ⟨K, hKs⟩, -, hnorm⟩ := GlobalTheory.FlagLeviGroup.levi_compact_subgroups n ε a W
  obtain ⟨hdec, huniq⟩ := GlobalTheory.RealIwasawa.iwasawa n ε a j W hW
  have eN : ∀ x, x ∈ N ↔ x ∈ flagN ε W := fun x => by rw [← hNs]; rfl
  have eM : ∀ x, x ∈ M ↔ x ∈ flagM ε W := fun x => by rw [← hMs]; rfl
  have eK : ∀ x, x ∈ K ↔ x ∈ maxK ε := fun x => by rw [← hKs]; rfl
  have hKc : IsCompact (K : Set (Formalism.REAL.UJ ε)) := by
    rw [hKs, ← coe_KG]
    exact isCompact_iff_compactSpace.mpr (Formalism.REAL.instCompactKG n ε)
  have hN' : IsGaugeSub (N : Set (Formalism.REAL.UJ ε)) (dimN n j) μN := by rw [hNs]; exact hN
  have hM' : IsGaugeSub (M : Set (Formalism.REAL.UJ ε)) ((n - 2 * ∑ i, j i) ^ 2 + 2 * ∑ i, j i ^ 2) μM := by
    rw [hMs]; exact hM
  have hNc' : IsClosed (N : Set (Formalism.REAL.UJ ε)) := by rw [hNs]; exact hNc
  have hMc' : IsClosed (M : Set (Formalism.REAL.UJ ε)) := by rw [hMs]; exact hMc
  obtain ⟨hN0, hNf⟩ := gauge_ne_zero_finite N _ μN hNc' hN'
  obtain ⟨hM0, hMf⟩ := gauge_ne_zero_finite M _ μM hMc' hM'
  have := hNf
  have := hMf
  have : IsProbabilityMeasure μK := ⟨hK1⟩
  have : (Formalism.REAL.muG ε).IsMulRightInvariant := ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular n ε g⟩
  have hmod := GlobalTheory.T.isotropicFlag_levi_conj_haar_modulus n ε a j W hj hW μN hN
  obtain ⟨c, hc0, hct, hc⟩ := GlobalTheory.IwasawaShape.exists_lintegral_eq N M K hNc' hMc' hKc
    (fun m hm u hu => (eN _).2 (hnorm m ((eM m).1 hm) u ((eN u).1 hu)))
    (fun u hu m hm hk => huniq u ((eN u).1 hu) m ((eM m).1 hm) ((eK _).1 hk))
    (fun g => by
      obtain ⟨u, hu, m, hm, k, hk, rfl⟩ := hdec g
      exact ⟨u, (eN u).2 hu, m, (eM m).2 hm, k, (eK k).2 hk, rfl⟩)
    (Formalism.REAL.muG ε) μN μM μK (NeZero.ne _) hN0 hM0 hN'.1 hM'.1
    (fun s hs => hN'.2.1 s hs) (fun s hs => hM'.2.1 s hs) (fun s hs => hKi s ((eK s).1 hs))
    (fun m => ENNReal.ofReal (layerProd n 1 j (locSize j W (uMat m)) id))
    (fun m hm => hmod m ((eM m).1 hm))
  exact ⟨c, hc0, hct, hc⟩

end GlobalTheory.IwasawaShape
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NongenericRowStatementsOfFamilyStatementsStatement
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.SnFam
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nongeneric_row_statements_of_family_statements : FamNG → (FamilyWeightSumUnfoldingIdentity → Formalism.L2.SG.FamDefs.OrbitFamilyIdentityNonGeneric) ∧ (WeightsFam → Formalism.L2.SG.FamDefs.WeightsNG) ∧ (FamilyGroupSumFactorsWeightAmplitude → Formalism.L2.SG.FamDefs.ProductStructureNonGeneric) ∧ (ExistFam → Formalism.L2.SG.FamDefs.ExistNG) := by
  first | exact @GlobalTheory.SnFamNG.leaves_of_fam | exact GlobalTheory.SnFamNG.leaves_of_fam | (intros; apply GlobalTheory.SnFamNG.leaves_of_fam <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PerpendicularRankIdealBoundStatement
section
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.perpendicular_rank_ideal_bound : ∀ (D : D7) (u u' : D.what₂.Word) (F0 : Fb D u) (Λ : LatV D), Stand D u u' → IsBase D u F0 → IsRowLat D F0 Λ → ∀ (P : LatW D) (s : ℕ) (Q : ℝ), s ≤ D.R.k → SubOK D (L0X D Λ (lf D F0)) P s Q → rkW D (perpW D (L0X D Λ (lf D F0)) P) = s ∧ ∃ I : Ideal (𝓞 D.host.E), I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ Q ^ 2 * NT D u ^ 2 ∧ I • dualInH (D.sp.X 0).hT (perpW D (L0X D Λ (lf D F0)) P) ≤ perpW D (L0X D Λ (lf D F0)) P := by
  first | exact @GlobalTheory.LoopC.PerpDisc.main | exact GlobalTheory.LoopC.PerpDisc.main | (intros; apply GlobalTheory.LoopC.PerpDisc.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimitiveRowsMapBijectiveColumnLevel
section
open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Cx NumberField

namespace GlobalTheory

theorem prim_rows_surjective : ∀ (D : D7) [IsTotallyComplex D.what₂.LL] (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (s : ℕ), A3.fam3.Ok3 s → A3.fam3.TypesSep3 → R.WeakCharacterisation F → PrimRows3 R F → ∀ (Zs : DefSub A3.fam3.amb3) (S1 : IndefData (A3.side3 F.P1 F.ψ1 Zs)), (R.toCx3 F).zs = Zs → HEq ((R.toCx3 F).data F.cr true) S1 → Function.Surjective ((A3.side3 F.P1 F.ψ1 Zs).Pq A3.A.μ0).mulVec ∧ Function.Surjective (S1.ι A3.A.μ0).mulVec := by
  intro D _ G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hok hsep hW hP Zs S1 hz hS
  subst hz
  have hS' := eq_of_heq hS
  subst hS'
  have hR := complex_data_conditions_base_level_of_primitive_links hok hsep hW hP
  exact ⟨(hR.wf true).Pq_surj _, (CxData.rowMat_bij _ _ true (hR.what₂ true).1 (hR.ratMu true) _).2⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RadicalCoordinatesBoundedMajorantLengthsStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.radical_coordinates_bounded_majorant_lengths : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (g₀ : Mat k r) (β : Fin r → ℕ) (De R₀ : ℝ), TwoFl k r z z' g₀ → IsNormal k r β g₀ → DeOK k r z z' g₀ De → 1 ≤ R₀ → ∀ m ∈ UH (Hb k), ∀ (y : UToff β → ℂ) (q : PPar k r) (a : Fin r → ℝ), (∀ b, 0 < a b) → Sg k r z' (uEmb k r (upperOff β y) * pOf k r q * uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m) ≤ R₀ → Sg k r z (g₀ * (uEmb k r (upperOff β y) * pOf k r q * uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)) ≤ R₀ → (∀ b, eucl (m⁻¹ *ᵥ q.1 b) ≤ r * R₀ ^ (2 * r - 1) * De) ∧ (∀ p, ‖q.2.1 p‖ ≤ r * R₀ ^ (4 * r - 2) * De ^ 2) ∧ ∀ b, |q.2.2 b| ≤ r * R₀ ^ (4 * r - 2) * De ^ 2 := by
  first | exact @GlobalTheory.Amp.RadBound.radical_coords_le | exact GlobalTheory.Amp.RadBound.radical_coords_le | (intros; apply GlobalTheory.Amp.RadBound.radical_coords_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RankOneUnitaryIntegrationFormulaExactConstantStatement
section
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_one_unitary_integration_formula_exact_constant : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (μb μW μW' : Measure (Mt k r)) (cb : ℝ), 1 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → IsSection k r z z' μsec → 0 < cb → IsHaarOn (Formalism.FourierDecayAlt.B2.UWb k r) μb → HasDens (Formalism.FourierDecayAlt.B2.UWb k r) μb (ENNReal.ofReal cb) → IsHaarOn (UWset k r z) μW → μW Set.univ = 1 → IsHaarOn (UWset k r z') μW' → μW' Set.univ = 1 → ∀ f : Mt k r → ℝ≥0∞, Measurable f → ∫⁻ m, f m ∂μb = ENNReal.ofReal (cb * 2 * volUn k ^ 2 / volUn (k - 1) / (Tz k r z * Tz k r z') ^ k) * ∫⁻ ζ : ℂ, ENNReal.ofReal (Formalism.FourierDecayAlt.B2.zWeight k (Tz k r z) (Tz k r z') ζ) * ∫⁻ p : Mt k r × Mt k r, f ((Matrix.of p.1)⁻¹ * Formalism.FourierDecayAlt.B2.embWb k r (μsec ζ) * Matrix.of p.2) ∂(μW.prod μW') := by
  first | exact @GlobalTheory.RankOneExact.rankOne_exact | exact GlobalTheory.RankOneExact.rankOne_exact | (intros; apply GlobalTheory.RankOneExact.rankOne_exact <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ReproducingFormulaFixedVectorModerateGrowthStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reproducing_formula_fixedVector_moderateGrowth : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → 1 ≤ B.I.n → LocDec B h → HBig B 40 h → ∀ T, B.I.IsRConv B.μf B.fund B.R (phe B d) T → ∀ (y : B.I.L2 B.μf B.fund) (f : B.I.GA → ℂ) (C : ℝ), T y = y → IsContRep B y f → (∀ x, ‖f x‖ ≤ C * (tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f)) → (∃ Φ : B.I.GA → ℝ, Integrable Φ (B.I.muA B.μf) ∧ ∀ x g, ‖phe B d g * f (x * g)‖ ≤ (tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) * Φ g) ∧ ∀ x, f x = ∫ g, phe B d g * f (x * g) ∂(B.I.muA B.μf) := by
  first | exact @GlobalTheory.ReproducingFixed.reproducing_fixed | exact GlobalTheory.ReproducingFixed.reproducing_fixed | (intros; apply GlobalTheory.ReproducingFixed.reproducing_fixed <;> assumption)
end

