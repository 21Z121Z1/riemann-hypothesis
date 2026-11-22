import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0011
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0269
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0254
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0255
import Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.Imports
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0079
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0176
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0259
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemRangeSrcForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0119
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSplittingCharacterSelf
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0071
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0070
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SIsoReD
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2 Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.ConcreteSettingExists GlobalTheory.Mem GlobalTheory.Mem.SRe

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SRe.IsoRe

variable {D : D7} (Z : New D) {X : HidaSetting D} {Y : Full X} (h : FinX Y) (h' : FinX (reY Z Y))

def eP (u u' : D.what₂.Word) : RP Y u u' ≃ RP (reY Z Y) (wd Z u) (wd Z u') :=
  (rp_iso_pair D Z X Y h h' u u').choose

set_option maxHeartbeats 4000000 in

def sIsoRe : SIso (sOf h) ((@sOf (reD D Z) (@reX D Z X) (@reY D Z X Y) h')) where
  cd := (by with_unfolding_all exact ((Eq.refl (Formalism.L2.SG.PairVal.cdScaleOf D)) :))
  del := (by with_unfolding_all exact ((Eq.refl D.s.Del) :))
  letter := (by with_unfolding_all exact ((Eq.refl D.s.letter) :))
  eHH := (by with_unfolding_all exact ((eHHre Z X) :))
  eCu := (by with_unfolding_all exact ((eCure Z h h') :))
  Pu_eq := (by with_unfolding_all exact ((keep_pu_vol_aR D Z X Y h h').1 :))
  volN := (by with_unfolding_all exact ((Eq.refl Y.volN) :))
  volH := (by with_unfolding_all exact ((Eq.refl Y.volH) :))
  eT := (by with_unfolding_all exact ((eRT Z Y) :))
  aTerm_eq := (by with_unfolding_all exact ((keep_pu_vol_aR D Z X Y h h').2.2 :))
  isId := fun {u u'} t => (by with_unfolding_all exact (((GlobalTheory.T.spectralRedivisionTermEquiv_keeps_term_data D Z X Y u u').1 t).1 :))
  inS := fun {u u'} t => (by with_unfolding_all exact (((GlobalTheory.T.spectralRedivisionTermEquiv_keeps_term_data D Z X Y u u').1 t).2.1 :))
  relevant := fun {u u'} t => (by with_unfolding_all exact (((GlobalTheory.T.spectralRedivisionTermEquiv_keeps_term_data D Z X Y u u').1 t).2.2.1 :))
  FeqF := fun {u u'} t => (by with_unfolding_all exact (((GlobalTheory.T.spectralRedivisionTermEquiv_keeps_term_data D Z X Y u u').1 t).2.2.2.1 :))
  Gterm := fun {u u'} t => Subtype.ext (a1 := (sOf h).Gterm t) (a2 := (by with_unfolding_all exact (((sOf h').Gterm (eRT Z Y u u' t)) :))) ((by with_unfolding_all exact (((GlobalTheory.T.spectralRedivisionTermEquiv_keeps_term_data D Z X Y u u').1 t).2.2.2.2.2.1 :)))
  atP := fun p => (by with_unfolding_all exact ((Formalism.L2.S.LocIso.refl (Formalism.L2.S.locC D p)) :))
  ePl := (by with_unfolding_all exact ((Equiv.refl (Formalism.MainNotions.S.LocalSplitGroups.PlF D)) :))
  BBne := fun {u u'} t q => (by with_unfolding_all exact ((((GlobalTheory.T.spectralRedivisionTermEquiv_keeps_term_data D Z X Y u u').1 t).2.2.2.2.2.2.1 q) :))
  generic := fun {u u'} t => (by with_unfolding_all exact (((GlobalTheory.T.spectralRedivisionTermEquiv_keeps_term_data D Z X Y u u').1 t).2.2.2.2.1 :))
  eP := (by with_unfolding_all exact ((eP Z h h') :))
  pfst := fun {u u'} p => (by with_unfolding_all exact ((((rp_iso_pair D Z X Y h h' u u').choose_spec p).1) :))
  psnd := fun {u u'} p => (by with_unfolding_all exact ((((rp_iso_pair D Z X Y h h' u u').choose_spec p).2.1) :))
  s0 := fun {u u'} p => (by with_unfolding_all exact ((((rp_iso_pair D Z X Y h h' u u').choose_spec p).2.2.1) :))
  scalarPair := fun {u u'} p => (by with_unfolding_all exact ((((rp_iso_pair D Z X Y h h' u u').choose_spec p).2.2.2.1) :))
  pval := fun {u u'} p => (by with_unfolding_all exact ((((rp_iso_pair D Z X Y h h' u u').choose_spec p).2.2.2.2) :))
  ptOf := fun {u u'} t => (by with_unfolding_all exact (((GlobalTheory.T.spectralRedivisionTermEquiv_keeps_term_data D Z X Y u u').1 t).2.2.2.2.2.2.2.1 :))
  cTerm := fun {u u'} t => (by with_unfolding_all exact (((GlobalTheory.T.spectralRedivisionTermEquiv_keeps_term_data D Z X Y u u').1 t).2.2.2.2.2.2.2.2.2 :))
  massPair := fun {u u'} p => (by with_unfolding_all exact (((((GlobalTheory.T.spectralRedivisionTermEquiv_keeps_term_data D Z X Y u u').1 ((p.1.1) : RT Y u u')).2.2.2.2.2.2.2.2.1).trans
      (congrArg Formalism.L2.SG.PairVal.massTerm ((rp_iso_pair D Z X Y h h' u u').choose_spec ((p) : RP Y u u')).1)) : _))
  meanCount := (by with_unfolding_all exact ((funext fun u => funext fun u' => funext fun w => (GlobalTheory.T.spectralRedivisionTermEquiv_keeps_term_data D Z X Y u u').2 w :
      (fun (u u' : D.what₂.Word) w => Formalism.L2.SG.PairVal.meanCount D u u' (X.Fu u) (Y.what₂ u) w) =
        fun (u u' : D.what₂.Word) w => Formalism.L2.SG.PairVal.meanCount (reD D Z) (wd Z u) (wd Z u') ((reX Z X).Fu (wd Z u)) ((reY Z Y).what₂ (wd Z u)) w) :))

end GlobalTheory.Mem.SRe.IsoRe

namespace GlobalTheory.Mem.SRe

set_option maxHeartbeats 4000000 in

theorem sIso_reD : ∀ (D : D7) (Z : New D) (X : HidaSetting D) (Y : Full X) (h : FinX Y) (h' : FinX (reY Z Y)),
    ∃ e : SIso (sOf h) ((@sOf (reD D Z) (@reX D Z X) (@reY D Z X Y) h')), HEq e.eHH (eHHre Z X) ∧ ∀ u, HEq (e.eCu u) (eCure Z h h' u) :=
  fun _ Z X _ h h' => ⟨IsoRe.sIsoRe Z h h', (by with_unfolding_all exact ((HEq.refl (eHHre Z X)) :)),
    fun u => (by with_unfolding_all exact ((HEq.refl (eCure Z h h' u)) :))⟩

end GlobalTheory.Mem.SRe
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothVectorWordActionContinuous
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmVec.WordCont

theorem continuous_apply_family {Y L E : Type} [TopologicalSpace Y] [AddCommGroup L] [Module ℝ L]
    [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L] [FiniteDimensional ℝ L]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (W : Y → L →ₗ[ℝ] E) (hW : ∀ x, Continuous fun y => W y x)
    {f : Y → L} (hf : Continuous f) : Continuous fun y => W y (f y) := by
  let b := Module.finBasis ℝ L
  have e : (fun y => W y (f y)) = fun y => ∑ i, b.coord i (f y) • W y (b i) := by
    funext y
    conv_lhs => rw [← b.sum_repr (f y), map_sum]
    simp only [map_smul, Module.Basis.coord_apply]
  rw [e]
  exact continuous_finset_sum _ fun i _ =>
    ((b.coord i).continuous_of_finiteDimensional.comp hf).smul (hW _)

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def lieSub (G : Matrix (Fin n) (Fin n) ℂ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) := GlobalTheory.UnitaryLieAlgebra.unitaryLie G

variable {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {P G : Matrix (Fin n) (Fin n) ℂ}

theorem continuous_word [CompleteSpace H] (hP : IsUnit P) (h : Pᴴ * Formalism.REAL.Jm ε * P = G)
    (hσ : IsURepOn (UJset ε) σ) {Y : Type} [TopologicalSpace Y] (l : List (Y → Matrix (Fin n) (Fin n) ℂ))
    (hc : ∀ f ∈ l, Continuous f) (hm : ∀ f ∈ l, ∀ y, f y ∈ lieG G) :
    ∀ w ∈ smSub G (trRep σ P), Continuous fun y => word (trRep σ P) (l.map fun f => f y) w := by
  have hG := gram_unit hP h
  have hπ := isURepOn_trRep hP h hσ
  induction l using List.reverseRecOn with
  | nil => intro w _; exact continuous_const
  | append_singleton l f ih =>
    intro w hw
    have hc' : ∀ f ∈ l, Continuous f := fun g hg => hc g (by simp [hg])
    have hm' : ∀ f ∈ l, ∀ y, f y ∈ lieG G := fun g hg => hm g (by simp [hg])
    have hl : ∀ y, ∀ X ∈ l.map (fun f => f y), X ∈ lieG G := fun y X hX => by
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hX
      exact hm' g hg y
    obtain ⟨hadd, hsm⟩ := GlobalTheory.T.derived_action_smooth_vector_real_linear n ε H σ P G hP h hσ w hw
    let W : Y → lieSub G →ₗ[ℝ] H := fun y =>
      { toFun := fun X => word (trRep σ P) (l.map fun f => f y) (dRep (trRep σ P) X w)
        map_add' := fun X Z => by
          rw [Submodule.coe_add, hadd _ X.2 _ Z.2,
            word_add hG hπ (hl y) (dRep_mem hG hπ hw X.2) (dRep_mem hG hπ hw Z.2)]
        map_smul' := fun a X => by
          rw [Submodule.coe_smul, hsm a _ X.2, word_smul hG hπ (hl y) _ (dRep_mem hG hπ hw X.2)]
          simp }
    have hf : Continuous fun y => (⟨f y, hm f (by simp) y⟩ : lieSub G) :=
      (hc f (by simp)).subtype_mk _
    have := continuous_apply_family W (fun X => ih hc' hm' _ (dRep_mem hG hπ hw X.2)) hf
    simp only [List.map_append, word_append, List.map_cons, List.map_nil, word_cons, word_nil]
    exact this

theorem word_rep {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsUnit G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π)
    {w : H} (hw : w ∈ smSub G π) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH G)
    {l : List (Matrix (Fin n) (Fin n) ℂ)} (hl : ∀ X ∈ l, X ∈ lieG G) :
    word π l (π g w) = π g (word π (l.map fun X => g⁻¹ * X * g) w) := by
  induction l with
  | nil => rfl
  | cons X l ih =>
    have hl' : ∀ Y ∈ l, Y ∈ lieG G := fun Y hY => hl Y (by simp [hY])
    have hm : ∀ Y ∈ l.map (fun X => g⁻¹ * X * g), Y ∈ lieG G := fun Y hY => by
      obtain ⟨Z, hZ, rfl⟩ := List.mem_map.1 hY
      exact conj_mem_lieG hG hg (hl' Z hZ)
    rw [word_cons, ih hl', dRep_rep hG hπ (word_mem hG hπ hm hw) hg (hl X (by simp))]
    rfl

theorem continuous_sigma (hσ : IsURepOn (UJset ε) σ) {u : Formalism.REAL.UJ ε → H} (hu : Continuous u) :
    Continuous fun g : Formalism.REAL.UJ ε => σ (umat g) (u g) := by
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  have h1 : Tendsto (fun g => σ (umat g) (u g) - σ (umat g) (u g₀)) (𝓝 g₀) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have e : (fun g : Formalism.REAL.UJ ε => ‖σ (umat g) (u g) - σ (umat g) (u g₀)‖) = fun g => ‖u g - u g₀‖ := by
      funext g
      rw [← map_sub, hσ.2.1 _ g.2]
    rw [e]
    exact tendsto_iff_norm_sub_tendsto_zero.1 hu.continuousAt
  have h2 := h1.add (continuous_orbit hσ (u g₀)).continuousAt
  simpa [ContinuousAt] using h2

theorem continuous_word_translate : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ l, X ∈ lieG G) → ∀ w ∈ smSub G (trRep σ P), Continuous fun g : Formalism.REAL.UJ ε => word (trRep σ P) l (σ (umat g) w) := by
  intro n ε H _ _ _ σ P G hP h hσ l hl w hw
  have hG := gram_unit hP h
  have hπ := isURepOn_trRep hP h hσ
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have hmem : ∀ g : Formalism.REAL.UJ ε, P⁻¹ * umat g * P ∈ Formalism.QuantumDeterminants.UH G := fun g => conj_mem_UH hP h g.2
  have hinv : ∀ g : Formalism.REAL.UJ ε, (P⁻¹ * umat g * P)⁻¹ = P⁻¹ * umat g⁻¹ * P := fun g => by
    apply Matrix.inv_eq_right_inv
    have e : umat g * umat g⁻¹ = 1 := Units.mul_inv g.1
    calc P⁻¹ * umat g * P * (P⁻¹ * umat g⁻¹ * P) = P⁻¹ * (umat g * (P * P⁻¹) * umat g⁻¹) * P := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [mul_nonsing_inv _ hd, Matrix.mul_one, e, Matrix.mul_one, nonsing_inv_mul _ hd]
  have c1 : Continuous fun g : Formalism.REAL.UJ ε => P⁻¹ * umat g * P :=
    (continuous_const.matrix_mul continuous_umat).matrix_mul continuous_const
  have c2 : Continuous fun g : Formalism.REAL.UJ ε => (P⁻¹ * umat g * P)⁻¹ := by
    simp only [hinv]
    exact c1.comp continuous_inv
  have hc := continuous_word hP h hσ
    (l.map fun X (g : Formalism.REAL.UJ ε) => (P⁻¹ * umat g * P)⁻¹ * X * (P⁻¹ * umat g * P))
    (fun f hf => by
      obtain ⟨X, _, rfl⟩ := List.mem_map.1 hf
      exact (c2.matrix_mul continuous_const).matrix_mul c1)
    (fun f hf g => by
      obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hf
      exact conj_mem_lieG hG (hmem g) (hl X hX)) w hw
  convert continuous_sigma hσ hc using 2 with g
  have := word_rep hG hπ hw (hmem g) hl
  rw [trRep_conj hP] at this
  rw [this, List.map_map]
  rfl

end GlobalTheory.SmVec.WordCont
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanEigenformsAdelicFormsIffClassPresentation
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.LiftSpanEig

theorem eigen_span_iff : ∀ {G Γ W K G0 : Type} [Group G] [Group Γ] (ι : Γ →* G) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K] [NumberField K] [StarRing K] (S : CSD K) (σ : K →+* ℂ) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) [Group G0] [Fintype G0] (Q : Subgroup G) (ch : Q →* ℂˣ) (act : Representation K G0 S.Forms) (P : Bridge.ClassPres ι S σ ρ J χ) (Tt : Bridge.ActTie ι P Q ch act), P.ExtBij → ∀ (U : Subgroup G0) (ψ : U →* Kˣ) (Φ : G → W), Φ ∈ Submodule.span ℂ (P.extL '' {f | ∀ u : U, act (u : G0) f = ((ψ u : Kˣ) : K) • f}) ↔ (Φ ∈ Bridge.AdForms ι ρ J χ ∧ ∀ (κ : Q) (hu : Tt.red κ ∈ U) (h : G), Φ (h * κ) = ((ch κ : ℂˣ) : ℂ) • σ ((ψ ⟨_, hu⟩ : Kˣ) : K) • Φ h) := by
  classical
  intro G Γ W K G0 _ _ ι _ _ _ _ _ S σ ρ J χ _ _ Q ch act P Tt hB U ψ Φ

  let gA : Q → (G → W) →ₗ[ℂ] (G → W) := fun κ =>
    { toFun := Bridge.g0Act ch κ
      map_add' := fun F F' => by
        funext h
        simp only [Bridge.g0Act, Pi.add_apply, smul_add]
      map_smul' := fun a F => by
        funext h
        simp only [Bridge.g0Act, Pi.smul_apply, RingHom.id_apply]
        rw [smul_comm] }
  have gA_apply : ∀ κ F h, gA κ F h = (((ch κ)⁻¹ : ℂˣ) : ℂ) • F (h * (κ : G)) := fun _ _ _ => rfl
  have hsemi : ∀ (a : K) (f : S.Forms), P.extL (a • f) = σ a • P.extL f := fun a f => map_smulₛₗ P.extL a f
  have hact : ∀ (g : G0) (κ : Q), Tt.red κ = g → ∀ f : S.Forms, P.extL (act g f) = gA κ (P.extL f) :=
    fun g κ hk f => Tt.act_eq g κ hk f

  let N : Submodule ℂ (G → W) :=
    { carrier := {Φ | Φ ∈ Bridge.AdForms ι ρ J χ ∧ ∀ (κ : Q) (hu : Tt.red κ ∈ U) (h : G),
        Φ (h * κ) = ((ch κ : ℂˣ) : ℂ) • σ ((ψ ⟨_, hu⟩ : Kˣ) : K) • Φ h}
      add_mem' := fun {a b} ha hb => ⟨add_mem ha.1 hb.1, fun κ hu h => by
        simp only [Pi.add_apply, ha.2 κ hu h, hb.2 κ hu h, smul_add]⟩
      zero_mem' := ⟨zero_mem _, fun κ hu h => by simp⟩
      smul_mem' := fun c a ha => ⟨Submodule.smul_mem _ c ha.1, fun κ hu h => by
        simp only [Pi.smul_apply, ha.2 κ hu h]
        rw [smul_comm c, smul_comm c]⟩ }
  constructor
  · intro hΦ
    have : Submodule.span ℂ (P.extL '' {f | ∀ u : U, act (u : G0) f = ((ψ u : Kˣ) : K) • f}) ≤ N := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨f, hf, rfl⟩
      refine ⟨hB.2 ▸ Submodule.subset_span ⟨f, rfl⟩, fun κ hu h => ?_⟩
      have e := congrFun (hact (Tt.red κ) κ rfl f) h
      have e2 : act (Tt.red κ) f = ((ψ ⟨_, hu⟩ : Kˣ) : K) • f := hf ⟨_, hu⟩
      rw [e2, hsemi, gA_apply] at e
      rw [Pi.smul_apply] at e
      rw [e, smul_smul, Units.mul_inv, one_smul]
    exact this hΦ
  · rintro ⟨hA, hc⟩
    choose κ hκ using Tt.red_surj
    let L : (G → W) →ₗ[ℂ] (G → W) := ∑ g : G0, σ (GlobalTheory.TraceIncl.invChar U ψ g) • gA (κ g)
    have L_apply : ∀ F, L F = ∑ g : G0, σ (GlobalTheory.TraceIncl.invChar U ψ g) • gA (κ g) F := fun F => by
      simp [L, LinearMap.sum_apply]
    have hLext : ∀ f : S.Forms, L (P.extL f) = P.extL (GlobalTheory.TraceIncl.trU act U ψ f) := fun f => by
      rw [L_apply, GlobalTheory.TraceIncl.trU_apply, map_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [hsemi, hact g (κ g) (hκ g)]
    let E := P.extL '' {f | ∀ u : U, act (u : G0) f = ((ψ u : Kˣ) : K) • f}
    have hspan : Submodule.span ℂ (Set.range P.extL) ≤ (Submodule.span ℂ E).comap L := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨f, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, hLext]
      exact Submodule.subset_span ⟨_, fun u => GlobalTheory.TraceIncl.trU_eigen act U ψ f u, rfl⟩
    have hLΦ : L Φ = (Nat.card U : ℂ) • Φ := by
      have term : ∀ g : G0, σ (GlobalTheory.TraceIncl.invChar U ψ g) • gA (κ g) Φ = if g ∈ U then Φ else 0 := fun g => by
        unfold GlobalTheory.TraceIncl.invChar
        split_ifs with hg
        · have hs : ψ ⟨Tt.red (κ g), (hκ g).symm ▸ hg⟩ = ψ ⟨g, hg⟩ := congrArg ψ (Subtype.ext (hκ g))
          funext h
          rw [Pi.smul_apply, gA_apply, hc (κ g) ((hκ g).symm ▸ hg) h, hs, smul_smul, smul_smul, smul_smul]
          convert one_smul ℂ (Φ h) using 2
          rw [mul_assoc (σ _), Units.inv_mul, mul_one, ← map_mul, Units.inv_mul, map_one]
        · rw [map_zero, zero_smul]
      rw [L_apply, Finset.sum_congr rfl fun g _ => term g, ← Finset.sum_filter, Finset.sum_const,
        ← Nat.cast_smul_eq_nsmul ℂ, Nat.card_eq_fintype_card, Fintype.card_subtype]
    have hmem : L Φ ∈ Submodule.span ℂ E := hspan (hB.2.symm ▸ hA)
    rw [hLΦ] at hmem
    have hne : (Nat.card U : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
    exact (Submodule.smul_mem_iff _ hne).1 hmem

end GlobalTheory.LiftSpanEig
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardAddCharPlaceIdempotentDivPrime
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdCharDegOne

variable {K : Type} [Field K] [NumberField K]

theorem intTrace_modEq (p : ℕ) (hp : p.Prime) (v : HeightOneSpectrum (𝓞 K)) (I : Ideal (𝓞 K))
    (hvI : IsCoprime v.asIdeal I) (hpI : Ideal.span {(p : 𝓞 K)} = v.asIdeal * I)
    (hnorm : Ideal.absNorm v.asIdeal = p) (x : 𝓞 K) (b : ℤ) (hxv : x - (b : 𝓞 K) ∈ v.asIdeal) (hxI : x ∈ I) :
    ∃ m : ℤ, Algebra.intTrace ℤ (𝓞 K) x = b + p * m := by
  classical
  set P : Ideal ℤ := Ideal.span {(p : ℤ)} with hPdef
  haveI hPm : P.IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  letI := Ideal.Quotient.field P
  have hmap : Ideal.map (algebraMap ℤ (𝓞 K)) P = v.asIdeal * I := by
    rw [hPdef, Ideal.map_span, Set.image_singleton, map_natCast]; exact hpI
  have hPv : P ≤ v.asIdeal.comap (algebraMap ℤ (𝓞 K)) := by
    rw [← Ideal.map_le_iff_le_comap, hmap]; exact Ideal.mul_le_left (I := v.asIdeal) (J := I)
  have hPI : P ≤ I.comap (algebraMap ℤ (𝓞 K)) := by
    rw [← Ideal.map_le_iff_le_comap, hmap]; exact Ideal.mul_le_right (I := v.asIdeal) (J := I)
  letI : Algebra (ℤ ⧸ P) (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.algebraQuotientOfLEComap hPv
  letI : Algebra (ℤ ⧸ P) (𝓞 K ⧸ I) := Ideal.Quotient.algebraQuotientOfLEComap hPI
  haveI : IsScalarTower ℤ (ℤ ⧸ P) (𝓞 K ⧸ v.asIdeal) := .of_algebraMap_eq' rfl
  haveI : IsScalarTower ℤ (ℤ ⧸ P) (𝓞 K ⧸ I) := .of_algebraMap_eq' rfl
  haveI : Module.Finite (ℤ ⧸ P) (𝓞 K ⧸ v.asIdeal) := Module.Finite.of_restrictScalars_finite ℤ _ _
  haveI : Module.Finite (ℤ ⧸ P) (𝓞 K ⧸ I) := Module.Finite.of_restrictScalars_finite ℤ _ _
  let e : (𝓞 K ⧸ Ideal.map (algebraMap ℤ (𝓞 K)) P) ≃ₐ[ℤ ⧸ P] ((𝓞 K ⧸ v.asIdeal) × (𝓞 K ⧸ I)) :=
    { __ := (Ideal.quotEquivOfEq hmap).trans (Ideal.quotientMulEquivQuotientProd v.asIdeal I hvI),
      commutes' := Quotient.ind fun _ ↦ rfl }
  have he : e (Ideal.Quotient.mk _ x) = (Ideal.Quotient.mk v.asIdeal x, Ideal.Quotient.mk I x) := rfl
  have hx2 : Ideal.Quotient.mk I x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hxI
  have hx1 : Ideal.Quotient.mk v.asIdeal x = algebraMap (ℤ ⧸ P) (𝓞 K ⧸ v.asIdeal) (Ideal.Quotient.mk P b) := by
    rw [Ideal.Quotient.eq.mpr hxv]
    show _ = Ideal.Quotient.mk v.asIdeal (algebraMap ℤ (𝓞 K) b)
    rw [algebraMap_int_eq, eq_intCast]
  have hcardP : Nat.card (ℤ ⧸ P) = p := by
    rw [Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]
  have hcardv : Nat.card (𝓞 K ⧸ v.asIdeal) = p := by
    rw [← hnorm, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hfr : Module.finrank (ℤ ⧸ P) (𝓞 K ⧸ v.asIdeal) = 1 := by
    have h := Module.natCard_eq_pow_finrank (K := ℤ ⧸ P) (V := 𝓞 K ⧸ v.asIdeal)
    rw [hcardP, hcardv] at h
    exact (Nat.pow_right_injective hp.two_le (h.symm.trans (pow_one p).symm))
  have key : Ideal.Quotient.mk P (Algebra.intTrace ℤ (𝓞 K) x) = Ideal.Quotient.mk P b := by
    rw [← Algebra.trace_quotient_eq_of_isDedekindDomain, ← Algebra.trace_eq_of_algEquiv e, he,
      Algebra.trace_prod_apply, hx2, map_zero, add_zero, hx1, Algebra.trace_algebraMap, hfr, one_smul]
  rw [Ideal.Quotient.eq, hPdef, Ideal.mem_span_singleton] at key
  obtain ⟨m, hm⟩ := key
  exact ⟨m, by linear_combination hm⟩

end GlobalTheory.StdCharDegOne

namespace GlobalTheory.StdCharDegOne

variable {K : Type} [Field K] [NumberField K]

theorem integral_of_mul (w : HeightOneSpectrum (𝓞 K)) (n z s y : 𝓞 K) (hn : n ≠ 0) (hs : s ∉ w.asIdeal)
    (h : z * s = n * y) :
    algebraMap K (Af K) ((z : K) / (n : K)) w ∈ w.adicCompletionIntegers K := by
  have hs0 : (s : K) ≠ 0 := by
    intro h0; apply hs; rw [show s = 0 from by exact_mod_cast h0]; exact zero_mem _
  have hn0 : (n : K) ≠ 0 := by exact_mod_cast hn
  have hq : (z : K) / (n : K) = (y : K) / (s : K) := by
    rw [div_eq_div_iff hn0 hs0]
    have := congrArg (fun t : 𝓞 K => (t : K)) h
    simp only [map_mul] at this
    push_cast at this
    linear_combination this
  rw [hq, HeightOneSpectrum.mem_adicCompletionIntegers]
  have e := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w ((y : K) / (s : K))
  erw [e]
  rw [map_div₀, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_eq_one_iff.mpr hs, div_one]
  exact HeightOneSpectrum.intValuation_le_one w y

theorem exists_cofactor (p : ℕ) (v : HeightOneSpectrum (𝓞 K))
    (hnorm : Ideal.absNorm v.asIdeal = p) (hsq : (p : 𝓞 K) ∉ v.asIdeal ^ 2) :
    ∃ I : Ideal (𝓞 K), IsCoprime v.asIdeal I ∧ Ideal.span {(p : 𝓞 K)} = v.asIdeal * I := by
  have hpv : (p : 𝓞 K) ∈ v.asIdeal := by
    have := Ideal.absNorm_mem v.asIdeal
    rwa [hnorm] at this
  obtain ⟨I, hI⟩ : v.asIdeal ∣ Ideal.span {(p : 𝓞 K)} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hpv)
  refine ⟨I, ?_, hI⟩
  have hpr := (Ideal.prime_iff_isPrime v.ne_bot).mpr v.isPrime
  rw [Ideal.isCoprime_iff_gcd, hpr.irreducible.gcd_eq_one_iff]
  rintro ⟨J, rfl⟩
  apply hsq
  have : Ideal.span {(p : 𝓞 K)} ≤ v.asIdeal ^ 2 := by
    rw [hI, pow_two, ← mul_assoc]; exact Ideal.mul_le_left (I := v.asIdeal * v.asIdeal) (J := J)
  exact this (Ideal.mem_span_singleton_self _)

end GlobalTheory.StdCharDegOne

namespace GlobalTheory.StdCharDegOne

variable {K : Type} [Field K] [NumberField K]

theorem fin_part (p : ℕ) (hp : p.Prime) (v : HeightOneSpectrum (𝓞 K))
    (hnorm : Ideal.absNorm v.asIdeal = p) (hsq : (p : 𝓞 K) ∉ v.asIdeal ^ 2) (α : Af K)
    (hα1 : evalV K v α = 1) (hα0 : ∀ w, w ≠ v → evalV K w α = 0) (a : 𝓞 K) (b : ℤ)
    (hab : a - (b : 𝓞 K) ∈ v.asIdeal) :
    ∃ x : 𝓞 K, (∃ m : ℤ, Algebra.intTrace ℤ (𝓞 K) x = b + p * m) ∧
      ∀ w : HeightOneSpectrum (𝓞 K), (α * algebraMap K (Af K) ((a : K) / (p : K)) -
        algebraMap K (Af K) ((x : K) / (p : K))) w ∈ w.adicCompletionIntegers K := by
  obtain ⟨I, hvI, hpI⟩ := exists_cofactor p v hnorm hsq
  obtain ⟨u, hu, t, ht, hut⟩ := Ideal.isCoprime_iff_exists.mp hvI
  have htv : t ∉ v.asIdeal := fun h =>
    v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr (hut ▸ add_mem hu h))
  have hp0 : (p : 𝓞 K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hmemp : ∀ z ∈ v.asIdeal * I, ∃ y, z = (p : 𝓞 K) * y := fun z hz => by
    rw [← hpI, Ideal.mem_span_singleton'] at hz
    obtain ⟨y, hy⟩ := hz
    exact ⟨y, by rw [← hy, mul_comm]⟩
  have hxv : (b : 𝓞 K) * t - b ∈ v.asIdeal := by
    have e : (b : 𝓞 K) * t - b = -((b : 𝓞 K) * u) := by linear_combination (b : 𝓞 K) * hut
    rw [e]; exact neg_mem (Ideal.mul_mem_left _ _ hu)
  refine ⟨b * t, intTrace_modEq p hp v I hvI hpI hnorm _ b hxv (Ideal.mul_mem_left _ _ ht), fun w => ?_⟩
  have hcomp : (α * algebraMap K (Af K) ((a : K) / (p : K)) - algebraMap K (Af K) ((((b : 𝓞 K) * t : 𝓞 K) : K) / (p : K))) w =
      α w * algebraMap K (Af K) ((a : K) / (p : K)) w - algebraMap K (Af K) ((((b : 𝓞 K) * t : 𝓞 K) : K) / (p : K)) w := rfl
  rw [hcomp]
  by_cases hw : w = v
  · subst hw
    have h1 : α w = 1 := hα1
    have hsub : algebraMap K (Af K) ((a : K) / (p : K)) w - algebraMap K (Af K) ((((b : 𝓞 K) * t : 𝓞 K) : K) / (p : K)) w =
        algebraMap K (Af K) (((a - (b : 𝓞 K) * t : 𝓞 K) : K) / ((p : 𝓞 K) : K)) w := by
      rw [show (((a - (b : 𝓞 K) * t : 𝓞 K) : K) / ((p : 𝓞 K) : K)) =
        (a : K) / (p : K) - ((((b : 𝓞 K) * t : 𝓞 K) : K) / (p : K)) by push_cast; ring, map_sub]
      rfl
    rw [h1, one_mul, hsub]
    have hmem : (a - (b : 𝓞 K) * t) * t ∈ w.asIdeal * I := by
      refine Ideal.mul_mem_mul ?_ ht
      have e : a - (b : 𝓞 K) * t = (a - b) - ((b : 𝓞 K) * t - b) := by ring
      rw [e]; exact sub_mem hab hxv
    obtain ⟨y, hy⟩ := hmemp _ hmem
    exact integral_of_mul w _ _ t y hp0 htv hy
  · have h0 : α w = 0 := hα0 w hw
    rw [h0, zero_mul, zero_sub]
    refine neg_mem ?_
    obtain ⟨s, hsv, hsw⟩ : ∃ s ∈ v.asIdeal, s ∉ w.asIdeal := by
      by_contra hc
      push_neg at hc
      exact hw (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top hc).symm)
    obtain ⟨y, hy⟩ := hmemp _ (Ideal.mul_mem_mul hsv (Ideal.mul_mem_left _ (b : 𝓞 K) ht))
    have := integral_of_mul w (p : 𝓞 K) ((b : 𝓞 K) * t) s y hp0 hsw (by rw [mul_comm]; exact hy)
    simpa using this

end GlobalTheory.StdCharDegOne

namespace GlobalTheory.StdCharDegOne

theorem stdChar_placeIdem_div : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (p : ℕ), p.Prime → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)), Ideal.absNorm v.asIdeal = p → (p : 𝓞 D.host.F) ∉ v.asIdeal ^ 2 → ∀ ε, IsPlaceIdem D v ε → ∀ (a : 𝓞 D.host.F) (b : ℤ), a - (b : 𝓞 D.host.F) ∈ v.asIdeal → ψ (ε * algebraMap D.host.F (AF D.host.F) ((a : D.host.F) / (p : D.host.F))) = Complex.exp (2 * Real.pi * Complex.I * b / (p : ℂ)) := by
  intro D ψ hψ p hp v hnorm hsq ε hε a b hab
  obtain ⟨α, rfl, hα1, hα0⟩ := hε
  obtain ⟨x, ⟨m, hm⟩, hint⟩ := fin_part p hp v hnorm hsq α hα1 hα0 a b hab
  have hsplit : pairA D.host.F 0 α * algebraMap D.host.F (AF D.host.F) ((a : D.host.F) / (p : D.host.F)) =
      pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) ((x : D.host.F) / (p : D.host.F))) +
      pairA D.host.F 0 (α * algebraMap D.host.F (Af D.host.F) ((a : D.host.F) / (p : D.host.F)) -
        algebraMap D.host.F (Af D.host.F) ((x : D.host.F) / (p : D.host.F))) := by
    refine Prod.ext ?_ ?_
    · show (0 : Ainf D.host.F) * _ = 0 + 0
      rw [zero_mul, add_zero]
    · show α * algebraMap D.host.F (Af D.host.F) ((a : D.host.F) / (p : D.host.F)) =
        algebraMap D.host.F (Af D.host.F) ((x : D.host.F) / (p : D.host.F)) +
        (α * algebraMap D.host.F (Af D.host.F) ((a : D.host.F) / (p : D.host.F)) -
          algebraMap D.host.F (Af D.host.F) ((x : D.host.F) / (p : D.host.F)))
      rw [add_sub_cancel]
  have htr : ∀ r : 𝓞 D.host.F, Algebra.trace ℚ D.host.F (r : D.host.F) = ((Algebra.intTrace ℤ (𝓞 D.host.F) r : ℤ) : ℚ) :=
    fun r => (Algebra.algebraMap_intTrace (A := ℤ) (K := ℚ) (L := D.host.F) r).symm
  have h1 : ψ (pairA D.host.F 0 (α * algebraMap D.host.F (Af D.host.F) ((a : D.host.F) / (p : D.host.F)) -
        algebraMap D.host.F (Af D.host.F) ((x : D.host.F) / (p : D.host.F)))) = 1 := by
    refine GlobalTheory.IntDense.mem_of_isClosed D.host.F (C := {y | ψ (pairA D.host.F 0 y) = 1})
      (isClosed_eq (hψ.1.1.comp (Continuous.prodMk continuous_const continuous_id)) continuous_const)
      (fun r => ?_) _ hint
    show ψ (pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) (r : D.host.F))) = 1
    rw [GlobalTheory.StdRat.stdChar_fin_rat D ψ hψ, htr, mul_comm]
    push_cast
    exact Complex.exp_int_mul_two_pi_mul_I _
  rw [hsplit, AddChar.map_add_eq_mul, h1, mul_one, GlobalTheory.StdRat.stdChar_fin_rat D ψ hψ]
  have hq : Algebra.trace ℚ D.host.F ((x : D.host.F) / (p : D.host.F)) = ((b : ℚ) + p * m) / p := by
    have e : (x : D.host.F) / (p : D.host.F) = ((p : ℚ)⁻¹) • (x : D.host.F) := by
      rw [Algebra.smul_def, map_inv₀, map_natCast, div_eq_inv_mul]
    rw [e, map_smul, htr, hm, smul_eq_mul]
    push_cast
    ring
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [hq, show 2 * ↑Real.pi * Complex.I * ((((b : ℚ) + p * m) / p : ℚ) : ℂ) =
      2 * Real.pi * Complex.I * b / (p : ℂ) + m * (2 * Real.pi * Complex.I) by
    push_cast; field_simp, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

end GlobalTheory.StdCharDegOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroClassEquivReferenceTupleEqSelf
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC.MuZeroCls

theorem stepZeroClassEquiv_referenceTuple_eq_self : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (u : B.Word)
    (c : (I.stp u I.mu0 0).Cl), I.eCls0 l u I.mu0 c = c := by
  intro B X I h l u c
  show (I.stp u I.mu0 0).cl _ (I.pt0 u I.mu0 I.mu0 ((I.stp u I.mu0 0).rep c)) = c
  refine Eq.trans ?_ (GlobalTheory.Mem.Col2.ClsZero.cl_rep _ c)
  refine (GlobalTheory.Mem.Col2.ClsZero.cl_eq_iff h u I.mu0 _ _ _ _).2 ?_
  rfl

end GlobalTheory.Mem.Col2.TC.MuZeroCls
end

