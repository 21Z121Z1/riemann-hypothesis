import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0215
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0210
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0187
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionStar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0269
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0138
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0176
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0208
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0216
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0154
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0214
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
import Formalism.LocalToGlobal.Columns.ChainTw
import Formalism.LocalToGlobal.Columns.ChainTwAn
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsGLExistsUnique
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0156
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0057
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0067
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0197

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageFiniteLevelEqProductLocalLevels
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ChainTw.LevLoc

variable {D : D7}

def LocOK {n : ℕ} (L : Formalism.L2.DIV.LevDat D.host.E ℂ n) (PP : Pl D.host.E) (y : GL (Fin n) (Formalism.L2.DIV.kP PP)) : Prop :=
  (PP ∈ L.Pg → y ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf L.r L.t) ∧ Formalism.L2.DIV.upperLeftBlock L.hr y = 1) ∧
    (PP ∈ L.Q → y ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 L.r))

theorem locOK_one {n : ℕ} (L : Formalism.L2.DIV.LevDat D.host.E ℂ n) (PP : Pl D.host.E) : LocOK L PP 1 :=
  ⟨fun _ => ⟨one_mem _, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _⟩, fun _ => one_mem _⟩

theorem mem_lev_iff {n : ℕ} (J : Matrix (Fin n) (Fin n) D.host.E) (β : GL (Fin n) (Lev.EAf D))
    (L : Formalism.L2.DIV.LevDat D.host.E ℂ n) (hP : L.P.H = ⊥) (x : GL (Fin n) (Lev.EAf D)) :
    x ∈ Formalism.L2.DIV.lev D.sp.cm J β L ↔ x ∈ Formalism.L2.DIV.UA D.sp.cm J ∧ x ∈ Formalism.L2.DIV.St β ∧
      ∀ PP, LocOK L PP (Formalism.L2.DIV.redFn β PP x) := by
  rw [Formalism.L2.DIV.mem_lev, Formalism.L2.DIV.mem_parLev, hP, Subgroup.mem_bot]
  constructor
  · rintro ⟨⟨hU, hS, hg, hq⟩, hr⟩
    exact ⟨hU, hS, fun PP => ⟨fun h => ⟨hg PP h, congrFun hr ⟨PP, h⟩⟩, fun h => hq PP h⟩⟩
  · rintro ⟨hU, hS, h⟩
    exact ⟨⟨hU, hS, fun PP hP => ((h PP).1 hP).1, fun PP hP => (h PP).2 hP⟩, funext fun PP => ((h PP.1).1 PP.2).2⟩

theorem finE_gAt_mem_St {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hfr : Formalism.L2.DIV.IsFrame β Λ) (g : GA D V) (v : HeightOneSpectrum (𝓞 D.host.F))
    (hv : GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram Λ v) :
    Lev.finE V (gAt V (.inl v) g) ∈ Formalism.L2.DIV.St β := by
  refine (GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer D V β Λ hfr _).2 fun w => ?_
  show GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram w
    (GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g)) ∈ _
  by_cases e : w = v
  · subst e
    rw [GlobalTheory.AdelicU.proj_emb_self]
    exact hv
  · rw [GlobalTheory.AdelicU.proj_emb_ne _ _ e]
    exact one_mem _

theorem red_local {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hfr : Formalism.L2.DIV.IsFrame β Λ) (g : GA D V) (hg : Lev.finE V g ∈ Formalism.L2.DIV.St β) (PP : Pl D.host.E) :
    Formalism.L2.DIV.redFn β PP (Lev.finE V g) =
      Formalism.L2.DIV.redFn β PP (Lev.finE V (gAt V (.inl (PP.under (𝓞 D.host.F))) g)) := by
  set v := PP.under (𝓞 D.host.F)
  set k := gAt V (.inl v) g with hkdef
  have hk : Lev.finE V k ∈ Formalism.L2.DIV.St β := finE_gAt_mem_St hfr g v ((GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer D V β Λ hfr g).1 hg v)
  have hpk : GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v k = GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g := by
    show GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v
      (GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g)) = _
    rw [GlobalTheory.AdelicU.proj_emb_self]
  have h2 : Lev.finE V (k⁻¹ * g) ∈ Formalism.L2.DIV.St β := by
    rw [map_mul, map_inv]; exact mul_mem (inv_mem hk) hg
  have h3 : Formalism.L2.DIV.redFn β PP (Lev.finE V (k⁻¹ * g)) = 1 :=
    GlobalTheory.T.latticeReduction_eq_one_of_local_component_one D V β _ PP h2 (by rw [map_mul, map_inv, hpk, inv_mul_cancel])
  have e : g = k * (k⁻¹ * g) := by group
  conv_lhs => rw [e]
  rw [map_mul, Formalism.L2.DIV.redFn_mul hk h2, h3, mul_one]

end GlobalTheory.ChainTw.LevLoc

namespace GlobalTheory.ChainTw.LevLoc

open Classical in

theorem levLoc : ∀ D : D7, ForStageQ D fun c w _ s => MeasurableSet (levSet s) ∧ MeasurableSet (intOff c s) ∧ (∀ g, g ∈ levSet s ↔ g ∈ intOff c s ∧ ∀ v ∈ c.S, gAt s.V (.inl v) g ∈ Lev.levG s.V s.β s.L) ∧ (∀ g ∈ levSet s, ∃ b : GinfC s.V, ∃ κ ∈ Lev.levG s.V s.β s.L, g = (b : GA D s.V) * κ) ∧ (∀ κ ∈ Lev.levG s.V s.β s.L, ‖Lev.levChi s.V s.β s.L κ‖ = 1 ∧ ∀ v, GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v κ ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v) ∧ ∃ mR, IsLevMeas s mR := by
  intro D c w hw j _ s hs
  obtain ⟨hr, hL, hfl⟩ := hs
  have hfr : Formalism.L2.DIV.IsFrame s.β s.Λ := hfl.frame
  haveI : s.ν.IsHaarMeasure := hfl.haar
  have hsd : IsSelfDualC s.V s.Λ := hfl.selfDual
  have hP : s.L.P.H = ⊥ := by rw [hL]; rfl
  have hPl : ∀ PP, PP ∈ s.L.Pg ∨ PP ∈ s.L.Q → PP.under (𝓞 D.host.F) ∈ c.S := by
    intro PP hPP
    have h1 : PP ∈ c.Pg := by
      rw [hw.union, Finset.mem_union]
      rw [hL] at hPP
      exact hPP
    unfold Com.S
    exact Finset.mem_image_of_mem _ h1
  set V := s.V
  set K := Lev.levG s.V s.β s.L

  have h3 : ∀ k ∈ K, ∀ v, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram s.Λ v :=
    fun k hk v => (GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer D V s.β s.Λ hfr k).1 (GlobalTheory.ChainOnto.LevelFacts.finE_mem_St hk) v

  have h1 : ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ k ∈ U, k ∈ GfC V → k ∈ K := by
    obtain ⟨U, hU, hUk⟩ := GlobalTheory.T.exists_open_principal_congruence_finitely_many_primes D V s.β (s.L.Pg ∪ s.L.Q)
    refine ⟨U, hU, fun k hk hkf => ⟨hkf, ?_⟩⟩
    exact GlobalTheory.LevSplit.mem_lev_of_red D.sp.cm V.gram s.β s.L _ (GlobalTheory.LevSplit.finE_mem_UA V k) (hUk k hk).1
      fun PP hPP => (hUk k hk).2 PP (Finset.mem_union.2 hPP)

  have hloc : ∀ g, g ∈ levSet s ↔ g ∈ intOff c s ∧ ∀ v ∈ c.S, gAt s.V (.inl v) g ∈ K := by
    intro g
    constructor
    · intro hg
      obtain ⟨-, hS, hl⟩ := (mem_lev_iff V.gram s.β s.L hP _).1 hg
      refine ⟨fun v _ => (GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer D V s.β s.Λ hfr g).1 hS v, fun v _ => ?_⟩
      have hkS := finE_gAt_mem_St hfr g v ((GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer D V s.β s.Λ hfr g).1 hS v)
      refine ⟨GlobalTheory.ChainOnto.LevelFacts.emb_mem_GfC V v _, ?_⟩
      refine (mem_lev_iff V.gram s.β s.L hP _).2 ⟨GlobalTheory.LevSplit.finE_mem_UA V _, hkS, fun PP => ?_⟩
      by_cases e : PP.under (𝓞 D.host.F) = v
      · subst e
        rw [← red_local hfr g hS PP]
        exact hl PP
      · rw [GlobalTheory.T.latticeReduction_eq_one_of_local_component_one D V s.β _ PP hkS (GlobalTheory.AdelicU.proj_emb_ne _ _ e _)]
        exact locOK_one _ _
    · rintro ⟨hI, hK⟩
      have hS : Lev.finE V g ∈ Formalism.L2.DIV.St s.β := by
        refine (GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer D V s.β s.Λ hfr g).2 fun v => ?_
        by_cases hv : v ∈ c.S
        · have := h3 _ (hK v hv) v
          have e : GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v (gAt s.V (.inl v) g) = GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g := by
            show GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v
              (GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g)) = _
            rw [GlobalTheory.AdelicU.proj_emb_self]
          rw [e] at this
          exact this
        · exact hI v hv
      refine (mem_lev_iff V.gram s.β s.L hP _).2 ⟨GlobalTheory.LevSplit.finE_mem_UA V g, hS, fun PP => ?_⟩
      by_cases hPP : PP ∈ s.L.Pg ∨ PP ∈ s.L.Q
      · rw [red_local hfr g hS PP]
        exact ((mem_lev_iff V.gram s.β s.L hP _).1 (hK _ (hPl PP hPP)).2).2.2 PP
      · exact ⟨fun h => absurd (Or.inl h) hPP, fun h => absurd (Or.inr h) hPP⟩
  let A : Subgroup (GA D V) := (Formalism.L2.DIV.lev D.sp.cm V.gram s.β s.L).comap (Lev.finE V)
  have hAset : (A : Set (GA D V)) = levSet s := rfl
  have hfinK : ∀ g ∈ A, (GlobalTheory.AutMult.toFin V g : GA D V) ∈ K := fun g hg =>
    ⟨(GlobalTheory.AutMult.toFin V g).2, Subgroup.mem_comap.2 (by rw [GlobalTheory.ChainOnto.HaarInf.finE_toFin]; exact Subgroup.mem_comap.1 hg)⟩
  have hAopen : IsOpen (A : Set (GA D V)) := by
    obtain ⟨U, hU, hUK⟩ := h1
    let Lf : Subgroup (GfC V) := K.subgroupOf (GfC V)
    have hLf : IsOpen (Lf : Set (GfC V)) := by
      refine Subgroup.isOpen_mono (H₁ := U.subgroupOf (GfC V)) (fun k hk => ?_) (hU.preimage continuous_subtype_val)
      exact hUK k hk k.2
    have e : (A : Set (GA D V)) = GlobalTheory.AutMult.toFin V ⁻¹' (Lf : Set (GfC V)) := by
      ext g
      refine ⟨fun hg => hfinK g hg, fun hg => ?_⟩
      have := Subgroup.mem_comap.1 hg.2
      refine Subgroup.mem_comap.2 ?_
      rw [← GlobalTheory.ChainOnto.HaarInf.finE_toFin]; exact this
    rw [e]; exact hLf.preimage (GlobalTheory.AutMult.continuous_toFin V)
  have hAint : (A : Set (GA D V)) ⊆ intOff c s := fun g hg => ((hloc g).1 hg).1
  let I : Subgroup (GA D V) :=
    { carrier := intOff c s
      mul_mem' := fun {a b} ha hb v hv => by rw [map_mul]; exact mul_mem (ha v hv) (hb v hv)
      one_mem' := fun v _ => by rw [map_one]; exact one_mem _
      inv_mem' := fun {a} ha v hv => by rw [map_inv]; exact inv_mem (ha v hv) }
  have hIopen : IsOpen (I : Set (GA D V)) := Subgroup.isOpen_mono (H₁ := A) hAint hAopen
  have hker : {g : GA D V | g ∈ A ∧ GlobalTheory.AutMult.toInf V g = 1} = (K : Set (GA D V)) := by
    ext g
    simp only [Set.mem_setOf_eq, GlobalTheory.ChainOnto.HaarInf.toInf_eq_one_iff]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  have hKc : IsCompact (K : Set (GA D V)) :=
    GlobalTheory.T.isCompact_finite_adelic_subgroup_integral_open D V s.Λ hsd K inf_le_left h3 h1
  have hpi : ∀ b : GinfC V, GlobalTheory.AutMult.toInf V ((GinfC V).subtype b) = b := fun b => GlobalTheory.AutMult.toInf_coe b
  have hiA : ∀ b : GinfC V, (GinfC V).subtype b ∈ A := fun b => by
    refine Subgroup.mem_comap.2 ?_
    rw [Subgroup.subtype_apply, GlobalTheory.ChainOnto.HaarInf.finE_of_mem_ginfC V b.2]; exact one_mem _
  have hHaar : (Measure.map (GlobalTheory.AutMult.toInf V) (s.ν.restrict (A : Set (GA D V)))).IsHaarMeasure :=
    GlobalTheory.T.map_restrict_isHaar_of_open_product_compact (GA D V) (GinfC V) s.ν A (GinfC V).subtype (GlobalTheory.AutMult.toInf V) hAopen
      continuous_subtype_val (GlobalTheory.AutMult.continuous_toInf V) hpi hiA (hker ▸ hKc)
  refine ⟨hAopen.measurableSet, hIopen.measurableSet, hloc, fun g hg => ?_, fun κ hκ =>
    ⟨GlobalTheory.ChainOnto.LevelFacts.levChi_norm s.β s.L κ, h3 κ hκ⟩, ?_⟩
  · exact ⟨GlobalTheory.AutMult.toInf V g, GlobalTheory.AutMult.toFin V g, hfinK g hg, (GlobalTheory.AutMult.toInf_mul_toFin g).symm⟩
  refine ⟨_, hHaar, fun f F hf hF => ?_⟩
  have hmeas : AEMeasurable (GlobalTheory.AutMult.toInf V) (s.ν.restrict (A : Set (GA D V))) :=
    (GlobalTheory.AutMult.continuous_toInf V).measurable.aemeasurable
  have hFA : ∀ g ∈ (A : Set (GA D V)), F g = f (GlobalTheory.AutMult.toInf V g) := fun g hg => by
    conv_lhs => rw [← GlobalTheory.AutMult.toInf_mul_toFin g]
    exact hF _ _ (hfinK g hg)
  have hint : IntegrableOn (fun g => f (GlobalTheory.AutMult.toInf V g)) (A : Set (GA D V)) s.ν :=
    (integrable_map_measure hf.aestronglyMeasurable hmeas).1 hf
  refine ⟨hint.congr_fun (fun g hg => (hFA g hg).symm) hAopen.measurableSet, ?_⟩
  rw [← hAset, setIntegral_congr_fun hAopen.measurableSet hFA, integral_map hmeas hf.aestronglyMeasurable]

end GlobalTheory.ChainTw.LevLoc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageRealDataConjValueMemCuspForms
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto.RealData

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

section Frame

variable {n p q : ℕ} (e : Fin n ≃ Fin p ⊕ Fin q)

theorem submatrix_symm_mul (X Y : Matrix (Fin n) (Fin n) ℂ) : X.submatrix e.symm id * Y = (X * Y).submatrix e.symm id := by
  ext i j
  simp [Matrix.mul_apply]

theorem mul_submatrix_symm (B : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    B * X.submatrix e.symm id = (B.submatrix e e * X).submatrix e.symm id := by
  have hB : B = (B.submatrix e e).submatrix e.symm e.symm := by ext; simp
  conv_lhs => rw [hB]
  rw [show X.submatrix e.symm id = X.submatrix e.symm (Equiv.refl _) from rfl, submatrix_mul_equiv]
  rfl

theorem conj_submatrix_symm (B : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    (X.submatrix e.symm id)ᴴ * B * X.submatrix e.symm id = Xᴴ * B.submatrix e e * X := by
  rw [Matrix.mul_assoc, mul_submatrix_symm, conjTranspose_submatrix, submatrix_mul_equiv, submatrix_id_id, Matrix.mul_assoc]

end Frame

theorem fr_det (M : DSModel V S) (τ : D.what₂.Tau) : IsUnit (M.fr τ).det :=
  (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)

theorem sortedFrame_gram (M : DSModel V S) (hV : V.SigOK) (τ : D.what₂.Tau) :
    (sortedFrame M hV τ)ᴴ * Formalism.UG.Jpq (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2 * sortedFrame M hV τ = gramAt D V τ := by
  rw [sortedFrame, conj_submatrix_symm, Jpq_submatrix, M.fr_gram τ]

theorem isCartanFrame_sortedFrame (M : DSModel V S) (hV : V.SigOK) : GlobalTheory.Cusp.IsCartanFrame V (sortedFrame M hV) :=
  sortedFrame_gram M hV

theorem sortedFrame_cart (M : DSModel V S) (hV : V.SigOK) (τ : D.what₂.Tau) :
    sortedFrame M hV τ * cart M τ = Formalism.UG.Jpq (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2 * sortedFrame M hV τ := by
  rw [sortedFrame, submatrix_symm_mul, mul_submatrix_symm, Jpq_submatrix, cart, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (fr_det M τ), Matrix.one_mul]

theorem isCartanInv_cart (M : DSModel V S) (τ : D.what₂.Tau) : IsCartanInv (gramAt D V τ) (cart M τ) := by
  have hd := fr_det M τ
  have h1 : ((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ = 1 := by
    rw [← conjTranspose_mul, Matrix.mul_nonsing_inv _ hd, conjTranspose_one]
  have hJ : (Formalism.REAL.Jm (M.ε τ)) * Formalism.REAL.Jm (M.ε τ) = 1 := by
    ext i j; by_cases h : i = j <;> simp [Formalism.REAL.Jm, diagonal_apply, h, Matrix.one_apply] <;> split_ifs <;> simp
  have hJh : (Formalism.REAL.Jm (M.ε τ))ᴴ = Formalism.REAL.Jm (M.ε τ) := by
    ext i j
    by_cases h : i = j
    · subst h; simp [Formalism.REAL.Jm, diagonal_apply]; split_ifs <;> simp
    · simp [Formalism.REAL.Jm, diagonal_apply, h, Ne.symm h]
  have hg : ((M.fr τ)⁻¹)ᴴ * gramAt D V τ * (M.fr τ)⁻¹ = Formalism.REAL.Jm (M.ε τ) := by
    rw [← M.fr_gram τ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
  have e : cart M τ = (M.fr τ)⁻¹ * ((M.fr τ)⁻¹)ᴴ * gramAt D V τ := by
    rw [cart, ← M.fr_gram τ]
    simp only [← Matrix.mul_assoc]
    rw [Matrix.mul_assoc (M.fr τ)⁻¹ ((M.fr τ)⁻¹)ᴴ (M.fr τ)ᴴ, h1, Matrix.mul_one]
  rw [e]
  exact GlobalTheory.Doubling.isCartanInv_of_frame (Matrix.nonsing_inv_mul _ hd) hg hJ hJh

theorem exists_maj_cart (θ : InfFam D) (hθ : IsInfFam θ) (M : DSModel V S) :
    ∃ a : GL (Fin V.rank) (AE D), GlobalTheory.Doubling.IsMaj V a ∧
      ∀ τ, (compAt θ τ a.1)ᴴ * (gramAt D V τ * cart M τ) * compAt θ τ a.1 = 1 := by
  obtain ⟨a, ha, -, hs⟩ := GlobalTheory.Doubling.exists_isMaj_frameInv_eq hθ (fun τ => isCartanInv_cart M τ)
  refine ⟨a, ha, fun τ => ?_⟩
  obtain ⟨ε, hε⟩ := (GlobalTheory.Doubling.isMaj_iff hθ).1 ha τ
  rw [← hs τ, GlobalTheory.Doubling.frameInv]
  have : (compAt θ τ a.1)ᴴ * (gramAt D V τ * (compAt θ τ a.1 * (compAt θ τ a.1)ᴴ * gramAt D V τ)) * compAt θ τ a.1 =
      ((compAt θ τ a.1)ᴴ * gramAt D V τ * compAt θ τ a.1) * ((compAt θ τ a.1)ᴴ * gramAt D V τ * compAt θ τ a.1) := by
    simp only [Matrix.mul_assoc]
  rw [this, hε, diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j <;> simp [diagonal_apply, h, Matrix.one_apply] <;> split_ifs <;> simp

theorem exists_kStable (M : DSModel V S) (τ : D.what₂.Tau) {w : M.H τ} (hw : w ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) :
    ∃ W : Submodule ℂ (M.H τ), FiniteDimensional ℂ W ∧ w ∈ W ∧ Formalism.MainNotions.S.IsKStableOn (M.ε τ) (M.σ τ) W := by
  induction hw using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨⊥, inferInstance, zero_mem _, fun g _ v hv => by rw [(Submodule.mem_bot ℂ).1 hv, map_zero]; exact zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨W, h1, h2, h3⟩ := hx
    obtain ⟨W', h1', h2', h3'⟩ := hy
    refine ⟨W ⊔ W', inferInstance, Submodule.add_mem_sup h2 h2', fun g hg v hv => ?_⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add]
    exact Submodule.add_mem_sup (h3 g hg y hy) (h3' g hg z hz)
  | smul a x _ hx =>
    obtain ⟨W, h1, h2, h3⟩ := hx
    exact ⟨W, h1, W.smul_mem a h2, h3⟩

theorem isKFinite_value (θ : InfFam D) (hθ : IsInfFam θ) (M : DSModel V S) (hV : V.SigOK) {J : Set (GA D V)}
    {χ : GA D V → ℂ} {T : MMap M} (hT : IsMultMap θ M J χ T) (v : M.Vec)
    (hv : ∀ τ, (v τ : M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) :
    GlobalTheory.Doubling.IsKFinite (GlobalTheory.Cusp.Kinf θ V (sortedFrame M hV)) (T v) := by
  choose W hWf hvW hWK using fun τ => exists_kStable M τ (hv τ)
  let W' : ∀ τ, Submodule ℂ (M.sm τ) := fun τ => (W τ).comap (M.sm τ).subtype
  have hW' : ∀ τ, FiniteDimensional ℂ (W' τ) := fun τ => by
    haveI := hWf τ
    refine Module.Finite.of_injective (LinearMap.codRestrict (W τ) ((M.sm τ).subtype.comp (W' τ).subtype)
      fun x => x.2) fun x y h => ?_
    exact Subtype.ext (Subtype.ext (congrArg (fun z : W τ => (z : M.H τ)) h))
  have hfd := GlobalTheory.T.finiteDimensional_span_multilinear_values' (fun τ => M.sm τ) (GA D V → ℂ) T W' hW'
  refine GlobalTheory.Doubling.isKFinite_iff.2 ⟨_, hfd, fun k hk => ?_⟩
  obtain ⟨v', hv', hx⟩ := GlobalTheory.T.multiplicity_map_right_translate_real_point D θ hθ V S M J χ T hT k (GlobalTheory.Cusp.Kinf_le hk) v
  have e : (fun g => T v (g * k)) = T v' := funext hx
  rw [e]
  refine Submodule.subset_span ⟨v', fun τ => ?_, rfl⟩
  show ((v' τ : M.sm τ) : M.H τ) ∈ W τ
  rw [hv' τ]
  exact hWK τ _ (GlobalTheory.T.maximal_compact_sorted_frame_acts_through_model_compact D θ V S M hV k hθ hk τ) _ (hvW τ)

theorem conj_multiplicityValue_mem_cuspFormsArchimedeanKFinite (θ : InfFam D) (hθ : IsInfFam θ) (M : DSModel V S) (hV : V.SigOK) {J : Set (GA D V)}
    {χ : GA D V → ℂ} (F : SmT M →ₗ[ℂ] (GA D V → ℂ)) (hF : F ∈ MultT θ M J χ) (w : SmT M)
    (hw : w ∈ Submodule.span ℂ {w | ∃ v : M.Vec, (∀ τ, (v τ : M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) ∧
      w = PiTensorProduct.tprod ℂ v}) :
    (fun g => conj (F w g)) ∈ GlobalTheory.Cusp.A0 θ V (sortedFrame M hV) := by
  have hT : IsMultMap θ M J χ (PiTensorProduct.lift.symm F) :=
    (GlobalTheory.MultMem.mem_mult_iff ..).1 ((mem_multT ..).1 hF)
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    have e : F (PiTensorProduct.tprod ℂ v) = PiTensorProduct.lift.symm F v := by
      rw [PiTensorProduct.lift_symm]; rfl
    rw [e]
    have ha := hT.aut v
    refine GlobalTheory.Cusp.mem_cuspForms.2 ⟨⟨GlobalTheory.Mem.AutConj.isAutFunSm_star D θ hθ V _ ha,
      (GlobalTheory.Cusp.conj_mem_cuspCont ⟨ha.cont, ha.left, hT.cusp v⟩).2.2⟩, ?_⟩
    exact GlobalTheory.Mem.AutConj.finiteDimensional_span_star (isKFinite_value θ hθ M hV hT v hv)
      (by rintro f ⟨k, hk, rfl⟩; exact ⟨k, hk, funext fun g => by simp⟩)
  | zero =>
    convert zero_mem (GlobalTheory.Cusp.A0 θ V (sortedFrame M hV)) using 1
    funext g; simp
  | add x y _ _ hx hy =>
    convert add_mem hx hy using 1
    funext g; simp
  | smul a x _ hx =>
    convert (GlobalTheory.Cusp.A0 θ V (sortedFrame M hV)).smul_mem (conj a) hx using 1
    funext g; simp

end GlobalTheory.ChainOnto.RealData

open GlobalTheory.ChainOnto

theorem GlobalTheory.ChainOnto.conj_stage_val_mem_A0_and_cartan_frame : ∀ (D : D7) (c : Com D), c.Is → ∀ j ≤ D.R.m, ∀ s : PiLocalization₂ D, s.Is c j → ∃ (cA : GlobalTheory.Mem.Th.CptF s.V) (a : GL (Fin s.V.rank) (AE D)), GlobalTheory.Cusp.IsCartanFrame s.V cA ∧ (∀ τ, IsCartanInv (gramAt D s.V τ) (cart s.M τ)) ∧ (∀ τ, cA τ * cart s.M τ = Formalism.UG.Jpq (s.V.sig (tauE D τ)).1 (s.V.sig (tauE D τ)).2 * cA τ) ∧ GlobalTheory.Doubling.IsMaj s.V a ∧ (∀ τ, (compAt c.θ τ a.1)ᴴ * (gramAt D s.V τ * cart s.M τ) * compAt c.θ τ a.1 = 1) ∧ ∀ (u : s.CC c), ∀ v ∈ s.KF, (fun g => conj (PiLocalization₂.val u v g)) ∈ GlobalTheory.Cusp.A0 c.θ s.V cA := by
  intro D c hc j _ s hs
  obtain ⟨a, ha, hmaj⟩ := RealData.exists_maj_cart c.θ hc.inf s.M
  exact ⟨RealData.sortedFrame s.M hs.sigOK, a, RealData.isCartanFrame_sortedFrame _ _, fun τ => RealData.isCartanInv_cart _ τ,
    fun τ => RealData.sortedFrame_cart _ _ τ, ha, hmaj, fun u v hv => RealData.conj_multiplicityValue_mem_cuspFormsArchimedeanKFinite c.θ hc.inf s.M hs.sigOK u.1 u.2 v hv⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaContractionIsLocalModelSecondVariableStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaContraction_isLocalModel_secondVariable : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (vL : VolM D B'.L.rank S.rank) (s : k), s ≠ 0 → ∀ (n n'' : Type) [Fintype n] [DecidableEq n] [Fintype n''] [DecidableEq n''] (FS : Frame k S.rank n) (FA' : Frame k B'.A.rank n'') (F₀' : Frame k B'.V₀.rank (n'' ⊕ Unit)), p.IsCoreFrame B' s FA' F₀' → ∀ (T₂ : SB (Matrix (n'' ⊕ Unit) n k) →ₗ[ℂ] (WO S B'.V₀ → ℂ)), p.IsModel ψ FS F₀' T₂ → ∀ (φ₀ : SB (n → k)) (Ξ₁ : WO B.V₀ S → ℂ), IsThetaFunO ψ B.V₀ S Ξ₁ → ∀ (u : WO B.A S) (T : SB (Matrix n'' n k) →ₗ[ℂ] (WO S B'.A → ℂ)), (∀ Ξ₂ v, T Ξ₂ v = GlobalTheory.Unf.contr l S vL Ξ₁ (T₂ (GlobalTheory.ContractionLocal.rowTens φ₀ Ξ₂)) u v) → p.IsModel ψ FS FA' T := by
  first | exact @GlobalTheory.ContrModR.contr_isModel | exact GlobalTheory.ContrModR.contr_isModel | (intros; apply GlobalTheory.ContrModR.contr_isModel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelModerateGrowthBothVariablesStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_kernel_moderate_growth_both_variables : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : WRep S T), IsWeilDatumO ψ S T χS χT om → ∀ f, IsThetaFunO ψ S T f → GlobalTheory.Grow.ModGrowth₂ S T fun g h => thetaKO om g h f := by
  first | exact @GlobalTheory.Core.Rk.ThetaGrowthBoth.thetaKO_modGrowth₂ | exact GlobalTheory.Core.Rk.ThetaGrowthBoth.thetaKO_modGrowth₂ | (intros; apply GlobalTheory.Core.Rk.ThetaGrowthBoth.thetaKO_modGrowth₂ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainSurjectiveOfAdjointNonvanishingStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLiftChain_surjective_of_adjoint_nonvanishing : ∀ D : D7, FinDim D → MetEx D → EigSpan D → ParIndep D → ChainUp D → OntoAll D := by
  first | exact @GlobalTheory.ChainOnto.ontoAll_of_chainUp | exact GlobalTheory.ChainOnto.ontoAll_of_chainUp | (intros; apply GlobalTheory.ChainOnto.ontoAll_of_chainUp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftUpwardsAdjointOfRapidDecayStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLiftUpwardsAdjoint_of_rapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, UpAdj D := by
  first | exact @GlobalTheory.ChainOnto.upAdj_of_cuspRapidDecay | exact GlobalTheory.ChainOnto.upAdj_of_cuspRapidDecay | (intros; apply GlobalTheory.ChainOnto.upAdj_of_cuspRapidDecay <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedChainStepWeilExponentsFockVacuumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_chain_step_weil_exponents_fock_vacuum : ∀ D : D7, ForStepQ D fun c _ k s s' p => ∀ hk : k < D.R.m, IsWeilExp c.ψ s.V s'.V (GlobalTheory.Chain.expS D ⟨k, hk⟩) (GlobalTheory.Chain.expT D ⟨k, hk⟩) p.ω ∧ GlobalTheory.Chain.IsVacVec c.ψ c.θ s.M s'.M p.f := by
  first | exact @GlobalTheory.ChainTw.StepExpTw.twStepExpVac | exact GlobalTheory.ChainTw.StepExpTw.twStepExpVac | (intros; apply GlobalTheory.ChainTw.StepExpTw.twStepExpVac <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingIntegralTwistPrimeEqDeepFiniteSum
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

noncomputable section
namespace GlobalTheory.TwSumAgree

theorem sumAgree : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → SumAgree Ch sel mu cst σ₀ P ι s W ν := by
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W _ _ ν hν hok hAt
  have hPA := GlobalTheory.T.parahoric_test_functions_agree_rational_points X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hν hok hAt
  have hiL := GlobalTheory.Proof.TwistSupportPeriodicLevels.ofTwist_support_periodic_levels k s (Fin R.k ⊕ Fin (s + 1)) (Fin R.t)
    (Ix (Fin R.k ⊕ Fin (s + 1)) (Fin R.t) (s + 2)) (XIx (Fin R.k) (Fin R.t)) W.δ W.tame W.η
    (fun j c h => GlobalTheory.StepData.plainFrame (stdOrd (Fin R.k) (Fin R.t) j c h)) (LatFrame.refl k _) (fun _ _ _ => rfl)
  intro j c h a b g g' hag hbg' ha hb hD
  have hm := hAt.steps
  refine ⟨j + 1, j + 1, fun A' B' hA hB e' e hoe' hoe x => ?_⟩
  obtain ⟨E', hE', hg⟩ := id hag
  obtain ⟨E, hE, hg'⟩ := id hbg'
  have hj : j < R.m := by omega
  have hom := GlobalTheory.TwBridge.Model.om_agree Ch sel mu cst σ₀ P ι s W hAt hok j (c + 1) (c + 1 + 1) hj E' E a b g g' hg hg'
    ((W.T s R).Phi j (c + 1) (by omega)) (PhiAt Ch mu cst.sharp j P.1)
    (fun y => hPA.1 j (c + 1) (by omega) E' E hE' hE y)
  obtain ⟨h1, h2⟩ := GlobalTheory.T.completionMatrix_boundedRationalAut_integral ι W.ϖ P.1 hAt.nmem hAt.compl j (c + 1 + 1) a g hag ha
  obtain ⟨h1', h2'⟩ := GlobalTheory.T.completionMatrix_boundedRationalAut_integral ι W.ϖ P.1 hAt.nmem hAt.compl (j + 1) (c + 1) b g' hbg' hb
  have hSP := GlobalTheory.T.linearWeilAction_support_and_period_integral W.ϖ ((W.unif W.ϖ).2 le_rfl) j ((W.T s R).mu (j + 1)) ((W.T s R).Phi j (c + 1) (by omega))
    (hiL.1 j (c + 1) (by omega)) (hiL.2.1 j (c + 1) (by omega)) g g' h1 h2 h1' h2'
  have hpsi : ∀ z, IntAt P.1 ((qOf P.1 : X.E) ^ (j + 1) * z) → (W.ψ (ι z) : ℂ) = σ₀ (cst.psi P z) :=
    fun z hz => hAt.psi z (twAn_qpow_mul (by omega) hz)
  have o1 : GlobalTheory.SymBridge.IsOrd (GlobalTheory.SymBridge.yPos (fun z => (e' z).val) (R.N j)) E' := by
    rintro (z | z)
    · exact (hE' _).trans (hoe' z).symm
    · exact hE' _
  have o2 : GlobalTheory.SymBridge.IsOrd (GlobalTheory.SymBridge.yPos (fun z => (e z).val) (R.N (j + 1))) E := by
    rintro (z | z)
    · exact (hE _).trans (hoe z).symm
    · exact hE _
  exact GlobalTheory.T.unfoldingIntegral_positionOne_eq_finite_sum X.E X.K k P.1 (qOf P.1) ι W.ϖ σ₀ W.ψ ν (cst.psi P) (j + 1) hAt.compl W.unif W.cond hν hpsi
    (XIx (Fin R.k) (Fin R.t) j) (XIx (Fin R.k) (Fin R.t) (j + 1)) (c + 1) (R.N j) (cOf R j) (R.N (j + 1)) (cOf R (j + 1))
    A' B' (by omega) (by unfold cOf; omega) (by unfold cOf; omega) hA hB e' e E' E o1 o2 _ _ _ hom hSP.1 hSP.2 x

end GlobalTheory.TwSumAgree
end
end

