import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
import Formalism.LocalToGlobal.Columns.ChainTw
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0062
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentHaarAndModulus
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0156
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0067
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0066
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0004
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0333
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0289
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0152
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0153
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0158
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumTransportSourceRationalIsometry

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalVolumeAgreesRowSubgroupUnitary
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

noncomputable section
namespace GlobalTheory.VolBridge

theorem index_comap_of_dense_image {A B : Type} [Group A] [Group B] (f : A →* B) (H : Subgroup B)
    (hf : ∀ b, ∃ a, (f a)⁻¹ * b ∈ H) : (H.comap f).index = H.index := by
  first
  | exact @_root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit
  | exact _root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit
  | (apply _root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit <;> assumption)
  | (intros; apply _root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit ..)

theorem relIndex_comap_of_dense_image {Γ G : Type} [Group Γ] [Group G] (φ : Γ →* G)
    (K U : Subgroup G) (h : ∀ g ∈ U, ∃ γ, (φ γ)⁻¹ * g ∈ K ⊓ U) :
    (K.comap φ).relIndex (U.comap φ) = K.relIndex U := by
  let f : U.comap φ →* U := φ.subgroupComap U
  have hc : (K.comap φ).subgroupOf (U.comap φ) = (K.subgroupOf U).comap f := by
    ext x
    exact Iff.rfl
  have key := index_comap_of_dense_image f (K.subgroupOf U) (by
    rintro ⟨b, hb⟩
    obtain ⟨γ, hγK, hγU⟩ := h b hb
    have hγ : φ γ ∈ U := by
      have := U.mul_mem hb (U.inv_mem hγU)
      simpa using this
    refine ⟨⟨γ, hγ⟩, ?_⟩
    exact hγK)
  simp only [Subgroup.relIndex]
  rw [hc, key]

theorem vol_agree : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → VolAgree (R := R) sel mu cst σ₀ P ι s W ν := by
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W _ _ ν hν hok hat
  have hLev := GlobalTheory.T.parahoricLevels_characters_doubleCosets_agree_rational X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hν hok hat
  haveI : ν.IsAddHaarMeasure := hν.1
  intro j c h γ g hg
  obtain ⟨e, he, hge⟩ := hg
  have hcc : cOf R j = c + 1 := by unfold cOf; have := hat.steps; omega
  have heR : ∀ i : Fin (c + 1), (e (Sum.inr i)).val = R.N j + i.val := fun i => he (Sum.inr i)
  have hgφ : g = GlobalTheory.VolBridge.locHom ι e γ := Units.ext hge
  have hreg : (W.T s R).Regular := Chain.ofTwist_regular _ _ _ _ _
  obtain ⟨hJo, hJc, -⟩ := hreg.2.2 j (c + 1) h
  set J := ((W.T s R).lev j (c + 1) h).J with hJdef
  set φ := GlobalTheory.VolBridge.locHom ι e with hφ
  have hcompl := hat.compl

  have hIsGL : ∀ x : AutY X R j, IsGL ι (γ⁻¹ * x * γ) (g⁻¹ * φ x * g) := by
    intro x
    refine ⟨e, he, ?_⟩
    rw [hgφ, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hC : ∀ x : AutY X R j, x ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) γ ↔ φ x ∈ Cgrp J g := by
    intro x
    rw [mem_Cgrp, ← GlobalTheory.T.mem_R1_iff_local_hom ι e hcc heR x, (hLev j (c + 1) h _ _ (hIsGL x)).1]
    simp [Loc.Cbe, Subgroup.mem_comap, MulAut.conj_apply]
  have hN1 := GlobalTheory.T.mem_N1_iff_locHom_mem_N_one ι e hcc heR
  have hlam : lamYat (Pr := Pr) (R := R) j P.1 = stdAt X.E _ P.1 := by
    ext v
    simp only [lamYat, if_neg hat.nmem, LocE.lamY, LocE.sclLat, Submodule.mem_comap]
    congr! 1
    funext l
    simp [LocE.scE]
  have hKO : ∀ x : AutY X R j, x ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) j P.1) ↔ φ x ∈ KO k _ := by
    intro x
    rw [hlam]
    exact GlobalTheory.T.mem_stabLocalizedStdLattice_iff_integralGL P.1 ι hcompl.int e x
  have hdN := GlobalTheory.T.exists_N1_locHom_mem_open ι hcompl.dense e hcc heR
  refine ⟨?_, ?_⟩
  ·
    have hH := GlobalTheory.RootEx.VolN.volN_haar_and_modulus k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1 le_rfl (by omega) ν
    haveI := hH.2.2.1
    obtain ⟨ho, hAc, hBc⟩ := GlobalTheory.T.isOpen_mirabolicConj_inf_integralGL_unipotent J g hJo hJc
    have hst : stabLat (1 : GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) k) = KO k _ := by
      ext z; simp [stabLat, Subgroup.mem_comap]
    have hvol : volNat ν 1 (Cgrp J g) =
        (volN ν _ (c + 1) 1 ((Cgrp J g).subgroupOf (N k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1) :
          Set (N k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1))).toReal /
        (volN ν _ (c + 1) 1 ((KO k (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1))).subgroupOf (N k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1) :
          Set (N k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1))).toReal := by
      rw [volNat, hst]
    rw [hvol, GlobalTheory.T.haar_volume_ratio_compact_eq_relIndex_ratio _ _ _ ho hAc hBc]
    set K := Cgrp J g ⊓ N k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1 with hKdef
    set U := KO k (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) ⊓ N k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1 with hUdef
    have hA : (Cgrp J g).subgroupOf (N k _ (c + 1) 1) = K.subgroupOf (N k _ (c + 1) 1) :=
      (Subgroup.inf_subgroupOf_right _ _).symm
    have hB : (KO k _).subgroupOf (N k _ (c + 1) 1) = U.subgroupOf (N k _ (c + 1) 1) :=
      (Subgroup.inf_subgroupOf_right _ _).symm
    rw [hA, hB, Subgroup.relIndex_subgroupOf inf_le_right, Subgroup.relIndex_subgroupOf inf_le_right]
    have hKc : K.comap φ = Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) γ ⊓ Loc.N1 X.E (R.N j) (cOf R j) := by
      ext x
      show φ x ∈ Cgrp J g ⊓ N k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1 ↔ _
      rw [Subgroup.mem_inf, Subgroup.mem_inf, hC, hN1]
    have hUc : U.comap φ = Loc.N1 X.E (R.N j) (cOf R j) ⊓ stabL X.E _ (lamYat (Pr := Pr) (R := R) j P.1) := by
      ext x
      show φ x ∈ KO k (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) ⊓ N k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1 ↔ _
      rw [Subgroup.mem_inf, Subgroup.mem_inf, hKO, hN1]; exact And.comm
    have hden : ∀ z, z ∈ K ∨ z ∈ U → ∃ x, (φ x)⁻¹ * z ∈ K ⊓ U := by
      intro z hz
      have hzN : z ∈ N k _ (c + 1) 1 := by rcases hz with hz | hz; exacts [hz.2, hz.2]
      have hO1 : IsOpen {w : GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) k | g⁻¹ * w * g ∈ J} :=
        hJo.preimage (by fun_prop)
      have hO' := hO1.inter (GlobalTheory.SplitFlip.isOpen_KO (k := k) (n := XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)))
      have hV : IsOpen {v : GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) k | v⁻¹ * z ∈ ({w | g⁻¹ * w * g ∈ J} ∩
          (KO k (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) : Set (GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) k)))} :=
        hO'.preimage (by fun_prop)
      obtain ⟨x, hx, hxV⟩ := hdN z hzN _ hV (by simp [J.one_mem, one_mem])
      refine ⟨x, ?_⟩
      have hxN := (hN1 x).1 hx
      have hm : (φ x)⁻¹ * z ∈ N k _ (c + 1) 1 := mul_mem (inv_mem hxN) hzN
      have hmR : (φ x)⁻¹ * z ∈ GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1 := by unfold GlobalTheory.RootEx.R; exact Subgroup.mem_sup_right hm
      exact ⟨⟨mem_Cgrp.2 ⟨hmR, hxV.1⟩, hm⟩, hxV.2, hm⟩
    have h1 := GlobalTheory.VolBridge.relIndex_comap_of_dense_image φ K U (fun z hz => hden z (Or.inr hz))
    have h2 := GlobalTheory.VolBridge.relIndex_comap_of_dense_image φ U K (fun z hz => by
      obtain ⟨x, hx⟩ := hden z (Or.inl hz); exact ⟨x, by rwa [inf_comm]⟩)
    rw [hKc, hUc] at h1 h2
    rw [← h1, ← h2]
    simp [Loc.volN, map_div₀, map_natCast]
  · intro hle m hm hm1
    haveI := hm
    set e' := GlobalTheory.VolBridge.eX e hcc heR with he'
    set φ' := GlobalTheory.VolBridge.locHom ι e' with hφ'
    have hOo : IsOpen {w : GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) k | g⁻¹ * w * g ∈ J} :=
      hJo.preimage (by fun_prop)
    have hOR : ∀ z ∈ GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1, z ∈ Cgrp J g ↔ z ∈ {w | g⁻¹ * w * g ∈ J} := fun z hz => by
      simp [mem_Cgrp, hz]
    have hCR : Cgrp J g ≤ GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1 := fun z hz => (mem_Cgrp.1 hz).1
    have hP : ∀ y, y ∈ prCat (Pr := Pr) cst.sharp j P.1 γ ↔ φ' y ∈ prX (Cgrp J g) :=
      GlobalTheory.T.mem_mirabolicProjection_iff_colSpaceAutToLocalGL ι e hcc heR hN1 hdN _ _ _ hOo hOR hCR hC
    have hG : ∀ y, y ∈ GLint X.E (R.N j) P.1 ↔ φ' y ∈ KO k _ := fun y =>
      GlobalTheory.T.mem_stabLocalizedStdLattice_iff_integralGL P.1 ι hcompl.int e' y
    have hpo : IsOpen (prX (Cgrp J g) : Set (GL (XIx (Fin R.k) (Fin R.t) j) k)) :=
      GlobalTheory.T.isOpen_mirabolicProjectionToGL _ _ hOo (by simp [J.one_mem]) (fun z hz hzO => (hOR z hz).2 hzO)
    have hden : ∀ z, z ∈ prX (Cgrp J g) ∨ z ∈ KO k _ → ∃ y, (φ' y)⁻¹ * z ∈ prX (Cgrp J g) ⊓ KO k _ := by
      intro z _
      have hV : IsOpen {v : GL (XIx (Fin R.k) (Fin R.t) j) k | v⁻¹ * z ∈ ((prX (Cgrp J g) ⊓ KO k _ : Subgroup _) : Set _)} :=
        (hpo.inter GlobalTheory.SplitFlip.isOpen_KO).preimage (by fun_prop)
      obtain ⟨y, hy⟩ := GlobalTheory.T.exists_colSpaceAutToLocalGL_mem_open_dense ι hcompl.dense e' z _ hV (by simp [one_mem])
      exact ⟨y, hy⟩
    have hle' : prX (Cgrp J g) ≤ KO k _ := by
      intro z hz
      obtain ⟨y, hy1, hy2⟩ := hden z (Or.inl hz)
      have hyC : φ' y ∈ prX (Cgrp J g) := by
        have := mul_mem hz (inv_mem hy1); simpa using this
      have hyK : φ' y ∈ KO k _ := (hG y).1 (hle ((hP y).2 hyC))
      have := mul_mem hyK hy2; simpa using this
    have hidx := GlobalTheory.VolBridge.relIndex_comap_of_dense_image φ' (prX (Cgrp J g)) (KO k _)
      (fun z hz => hden z (Or.inr hz))
    have hc1 : (prX (Cgrp J g)).comap φ' = prCat (Pr := Pr) cst.sharp j P.1 γ := by ext y; exact (hP y).symm
    have hc2 : (KO k _).comap φ' = GLint X.E (R.N j) P.1 := by ext y; exact (hG y).symm
    rw [hc1, hc2] at hidx
    rw [hidx]
    exact GlobalTheory.T.haar_open_subgroup_volume_inv_eq_relIndex m _ _ hle' hpo GlobalTheory.SplitFlip.isCompact_KO hm1

end GlobalTheory.VolBridge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OmIntegralComm
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.CommInt

theorem om_integral_comm : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (U : Type) [TopologicalSpace U] [SecondCountableTopology U] [MeasurableSpace U] [BorelSpace U] (m : Measure U) [SFinite m] (F : U → WO S T → ℂ) (p : GA D S × GA D T) (β : U → ℝ), (∀ u, IsThetaFunO ψ S T (F u)) → Continuous (Function.uncurry F) → Continuous (fun q : U × WO S T => om p (F q.1) q.2) → Integrable β m → (∀ u w, ‖F u w‖ ≤ β u ∧ ‖om p (F u) w‖ ≤ β u) → IsThetaFunO ψ S T (fun w => ∫ u, F u w ∂m) → ∀ w, om p (fun w' => ∫ u, F u w' ∂m) w = ∫ u, om p (F u) w ∂m := by
  intro D ψ S T χS χT om hom U _ _ _ _ m _ F p β hF hFc hOc hβ hdom hG w
  have hψ := hom.std
  obtain ⟨-, -, i3, -, -, -⟩ := GlobalTheory.MixModel.lattice_Mx D T.rank S.rank
  haveI : FirstCountableTopology (WO S T) := @TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _ _ i3
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨μ, 𝓕, hμ, h𝓕, h1⟩ := GlobalTheory.Size.exists_isCovolOne S T
  haveI hfin : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  haveI : SFinite (μ.restrict 𝓕) := @instSFiniteOfSigmaFinite _ _ _ (@IsFiniteMeasure.toSigmaFinite _ _ _ hfin)
  set G : WO S T → ℂ := fun w => ∫ u, F u w ∂m with hGdef
  set H : WO S T → ℂ := fun w => ∫ u, om p (F u) w ∂m with hHdef
  have hHc : Continuous H := by
    refine continuous_of_dominated (bound := β) (fun x => ?_) (fun x => ?_) hβ ?_
    · exact (hOc.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun u => (hdom u x).2
    · exact Filter.Eventually.of_forall fun u => hOc.comp (continuous_const.prodMk continuous_id)
  have hHb : ∀ x, ‖H x‖ ≤ ∫ u, β u ∂m := fun x =>
    norm_integral_le_of_norm_le hβ (Filter.Eventually.of_forall fun u => (hdom u x).2)
  have hOG := hom.om_pres p _ hG
  set q : WO S T → ℂ := fun x => om p G x - H x with hqdef
  have hq : q = 0 := by
    refine GlobalTheory.T.eq_zero_of_orthogonal_all_thetaFunctions D ψ hψ S T μ 𝓕 hμ h𝓕 q (hOG.cont.sub hHc) ?_ ?_
    · intro γ x
      have e1 := hOG.quasi γ x
      have e2 : H (ratW T S γ + x) = ψ (-(symplOH S T (ratW T S γ) x)) * H x := by
        simp only [hHdef]
        rw [← integral_const_mul]
        congr 1
        funext u
        exact (hom.om_pres p _ (hF u)).quasi γ x
      simp only [hqdef]
      rw [e1, e2]
      ring
    · intro f hf

      haveI : SecondCountableTopology (WO S T) := i3
      obtain ⟨CG, hCG⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ _ hOG
      have hf0 := hom.om_pres p⁻¹ f hf
      have hff0 : om p (om p⁻¹ f) = f := by
        change (om p * om p⁻¹) f = f
        rw [← map_mul, mul_inv_cancel, map_one]; rfl
      set f0 := om p⁻¹ f with hf0def
      obtain ⟨C0, hC0⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ _ hf0
      obtain ⟨Cf, hCf⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ _ hf
      have hint : ∀ (g h : WO S T → ℂ) (a b : ℝ), Continuous g → Continuous h → (∀ x, ‖g x‖ ≤ a) →
          (∀ x, ‖h x‖ ≤ b) → Integrable (fun x => g x * star (h x)) (μ.restrict 𝓕) := by
        intro g h a b hg hh ha hb
        refine Integrable.mono' (integrable_const (a * b)) (hg.mul hh.star).aestronglyMeasurable
          (ae_of_all _ fun x => ?_)
        rw [norm_mul, norm_star]
        exact mul_le_mul (ha x) (hb x) (norm_nonneg _) ((norm_nonneg _).trans (ha x))
      have hprod : ∀ (K : U → WO S T → ℂ) (h : WO S T → ℂ) (b : ℝ), Continuous (fun z : U × WO S T => K z.1 z.2) →
          (∀ u x, ‖K u x‖ ≤ β u) → Continuous h → (∀ x, ‖h x‖ ≤ b) →
          Integrable (Function.uncurry fun x u => K u x * star (h x)) ((μ.restrict 𝓕).prod m) := by
        intro K h b hK hKb hh hb
        refine Integrable.mono' (((integrable_const b).mul_prod hβ)) ?_ (ae_of_all _ fun z => ?_)
        · exact ((hK.comp (continuous_snd.prodMk continuous_fst)).mul (hh.comp continuous_fst).star).aestronglyMeasurable
        · show ‖K z.2 z.1 * star (h z.1)‖ ≤ b * β z.2
          rw [norm_mul, norm_star, mul_comm b]
          exact mul_le_mul (hKb z.2 z.1) (hb z.1) (norm_nonneg _) ((norm_nonneg _).trans (hKb z.2 z.1))
      have hsc := fun g g' (hg : IsThetaFunO ψ S T g) (hg' : IsThetaFunO ψ S T g') =>
        GlobalTheory.Mem.LiftPolar.scalar_eq D ψ hψ S T μ 𝓕 hμ h𝓕 (om p) (hom.om_pres p) (hom.om_unit μ 𝓕 hμ h𝓕 p) g g' hg hg'
      have A : ∫ x in 𝓕, om p G x * star (f x) ∂μ = ∫ x in 𝓕, G x * star (f0 x) ∂μ := by
        rw [← hff0]; exact hsc G f0 hG hf0
      have B : ∫ x in 𝓕, G x * star (f0 x) ∂μ = ∫ x in 𝓕, H x * star (f x) ∂μ := by
        calc ∫ x in 𝓕, G x * star (f0 x) ∂μ = ∫ x in 𝓕, ∫ u, F u x * star (f0 x) ∂m ∂μ := by
              refine integral_congr_ae (ae_of_all _ fun x => ?_)
              show (∫ u, F u x ∂m) * star (f0 x) = ∫ u, F u x * star (f0 x) ∂m
              rw [integral_mul_const]
          _ = ∫ u, ∫ x in 𝓕, F u x * star (f0 x) ∂μ ∂m :=
              integral_integral_swap (hprod F f0 C0 hFc (fun u x => (hdom u x).1) hf0.cont hC0)
          _ = ∫ u, ∫ x in 𝓕, om p (F u) x * star (f x) ∂μ ∂m := by
              refine integral_congr_ae (ae_of_all _ fun u => ?_)
              rw [← hff0]; exact (hsc (F u) f0 (hF u) hf0).symm
          _ = ∫ x in 𝓕, ∫ u, om p (F u) x * star (f x) ∂m ∂μ :=
              (integral_integral_swap (hprod (fun u => om p (F u)) f Cf hOc (fun u x => (hdom u x).2) hf.cont hCf)).symm
          _ = ∫ x in 𝓕, H x * star (f x) ∂μ := by
              refine integral_congr_ae (ae_of_all _ fun x => ?_)
              show ∫ u, om p (F u) x * star (f x) ∂m = (∫ u, om p (F u) x ∂m) * star (f x)
              rw [integral_mul_const]
      have i1 := hint (om p G) f CG Cf hOG.cont hf.cont hCG hCf
      have i2 := hint H f (∫ u, β u ∂m) Cf hHc hf.cont hHb hCf
      simp only [hqdef, sub_mul]
      rw [integral_sub i1 i2, A, B, sub_self]
  have := congrFun hq w
  simp only [hqdef, Pi.zero_apply, sub_eq_zero] at this
  exact this

end GlobalTheory.CommInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDeterminantsWittLeviFactor
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.SplitLeviDet

theorem smul_iff {R : Type*} [CommRing R] {m n : Type*} (ε : R) (N : Matrix m n R) :
    ε • N = N ↔ ∀ i j, ε * N i j = N i j :=
  ⟨fun h i j => congrFun (congrFun h i) j, fun h => by ext i j; exact h i j⟩

theorem smul_sandwich {R : Type*} [CommRing R] {k l m n : Type*} [Fintype l] [Fintype m] (ε : R)
    (P : Matrix k l R) (N : Matrix l m R) (Q : Matrix m n R) (hN : ε • N = N) : ε • (P * N * Q) = P * N * Q := by
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, hN]

theorem det_supp {R : Type*} [CommRing R] {n : ℕ} (ε : R) (hε : ε * ε = ε) (M : Matrix (Fin n) (Fin n) R)
    (hM : ε • (M - 1) = M - 1) : (1 - ε) * M.det = 1 - ε := by
  have hid : IsIdempotentElem (1 - ε) := by unfold IsIdempotentElem; linear_combination hε
  have hf : (1 - ε) • M = (1 - ε) • (1 : Matrix (Fin n) (Fin n) R) := by
    have h0 : (1 - ε) • (M - 1) = 0 := by rw [sub_smul, one_smul, hM, sub_self]
    rw [smul_sub, sub_eq_zero] at h0
    exact h0
  have key := congrArg Matrix.det hf
  rw [Matrix.det_smul, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at key
  cases n with
  | zero => rw [Matrix.det_isEmpty, mul_one]
  | succ k => rw [hid.pow_succ_eq] at key; exact key

variable {D : D7}

def locU (e : AE D) (h : e * e = e) (t : (AE D)ˣ) : (AE D)ˣ where
  val := e * t + (1 - e)
  inv := e * ↑t⁻¹ + (1 - e)
  val_inv := by
    have htu : (t : AE D) * ↑t⁻¹ = 1 := t.mul_inv
    linear_combination e * htu + ((t : AE D) * ↑t⁻¹ - t - ↑t⁻¹ + 1) * h
  inv_val := by
    have htu : (↑t⁻¹ : AE D) * t = 1 := t.inv_mul
    linear_combination e * htu + ((↑t⁻¹ : AE D) * t - ↑t⁻¹ - t + 1) * h

theorem locU_val (e : AE D) (h : e * e = e) (t : (AE D)ˣ) : (locU e h t : AE D) = e * t + (1 - e) := rfl

def detU (V : HSp D) (g : GA D V) : (AE D)ˣ where
  val := (mt V g).det
  inv := (mt V g⁻¹).det
  val_inv := by rw [← Matrix.det_mul, GlobalTheory.MixModel.mt_mul_inv, Matrix.det_one]
  inv_val := by rw [← Matrix.det_mul, GlobalTheory.MixModel.mt_inv_mul, Matrix.det_one]

theorem detU_val (V : HSp D) (g : GA D V) : (detU V g : AE D) = (mt V g).det := rfl

theorem det_adj {n : ℕ} (y : Mx D n n) : (adj y).det = cA D y.det := by
  rw [adj, Matrix.det_transpose]; exact (RingHom.map_det (cA D) y).symm

theorem one_add_sub {n : ℕ} (M : Mx D n n) : 1 + (M - 1) = M := by abel

end GlobalTheory.SplitLeviDet

open GlobalTheory.SplitLeviDet

theorem GlobalTheory.SplitLeviDet.emb0Part : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (e : AE D), IsSplitIdem D e → (∀ g, SuppAt e S₀ g → SuppAt e S (d.emb0 g) ∧ ∃ x, IsDetAt e S₀ g x ∧ IsDetAt e S (d.emb0 g) x) := by
  intro D S S₀ ρ d e he
  obtain ⟨h1, h2, -⟩ := he
  have hce : cA D e * cA D e = cA D e := by rw [← map_mul, h1]
  have hcc : cA D (cA D e) = e := Formalism.L2.Theta.cA_cA e
  have hεε : (e + cA D e) * (e + cA D e) = e + cA D e := by linear_combination h1 + 2 * h2 + hce
  have hcε : cA D (e + cA D e) = e + cA D e := by rw [map_add, hcc, add_comm]
  intro g hg
  have hN : (e + cA D e) • (mt S₀ g - 1) = mt S₀ g - 1 := (smul_iff _ _).2 hg
  have hm : mt S (d.emb0 g) = (1 : Mx D S.rank S.rank) + d.j0 ⬝ (mt S₀ g - 1) ⬝ d.p0 := by
    rw [d.unitaryMatrix_wittCoreEmbedding]; conv_rhs => rw [← d.sum_eq_one]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]; abel
  have hdet : (mt S (d.emb0 g)).det = (mt S₀ g).det := by
    rw [hm, Matrix.mul_assoc, Matrix.det_one_add_mul_comm, Matrix.mul_assoc, d.p0_j0, Matrix.mul_one, one_add_sub]
  refine ⟨?_, locU e h1 (detU S₀ g), ?_, ?_⟩
  · intro i j
    rw [hm, add_sub_cancel_left]
    exact (smul_iff _ _).1 (smul_sandwich _ _ _ _ hN) i j
  · rw [IsDetAt, locU_val, detU_val]
  · rw [IsDetAt, locU_val, detU_val, hdet]

set_option maxHeartbeats 1000000 in
theorem GlobalTheory.SplitLeviDet.leviPart : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (e : AE D), IsSplitIdem D e → ∀ (χ : (AE D)ˣ →* Circle) (n : ℕ), IsHeckeChar D χ → ResEta D χ n → ∀ a : GL (Fin ρ) (AE D), (∀ i j, (e + cA D e) * (a.1 - 1) i j = (a.1 - 1) i j) → SuppAt e S (d.levi a) ∧ ∃ x, IsDetAt e S (d.levi a) x ∧ χ x = χ (Matrix.GeneralLinearGroup.det a) := by
  intro D S S₀ ρ d e he
  obtain ⟨h1, h2, -⟩ := he
  have hce : cA D e * cA D e = cA D e := by rw [← map_mul, h1]
  have hcc : cA D (cA D e) = e := Formalism.L2.Theta.cA_cA e
  have hεε : (e + cA D e) * (e + cA D e) = e + cA D e := by linear_combination h1 + 2 * h2 + hce
  have hcε : cA D (e + cA D e) = e + cA D e := by rw [map_add, hcc, add_comm]
  intro χ n hχ hR a ha
  have hA : (e + cA D e) • (a.1 - 1 : Mx D ρ ρ) = (a.1 - 1 : Mx D ρ ρ) := by
    ext i j
    exact ha i j
  have hI : (e + cA D e) • ((a⁻¹).1 - 1 : Mx D ρ ρ) = ((a⁻¹).1 - 1 : Mx D ρ ρ) := by
    have hinv : ((a⁻¹).1 - 1 : Mx D ρ ρ) = -((a⁻¹).1 ⬝ (a.1 - 1 : Mx D ρ ρ)) := by
      rw [Matrix.mul_sub, Matrix.mul_one, Units.inv_mul, neg_sub]
    rw [hinv, smul_neg, ← Matrix.mul_smul, hA]
  have hB : (e + cA D e) • (adj (a⁻¹).1 - 1 : Mx D ρ ρ) = (adj (a⁻¹).1 - 1 : Mx D ρ ρ) := by
    have h' : (adj (a⁻¹).1 - 1 : Mx D ρ ρ) = adj ((a⁻¹).1 - 1 : Mx D ρ ρ) := by rw [adj_sub, adj_one]
    rw [h']
    calc (e + cA D e) • adj ((a⁻¹).1 - 1 : Mx D ρ ρ) = cA D (e + cA D e) • adj ((a⁻¹).1 - 1 : Mx D ρ ρ) := by rw [hcε]
      _ = adj ((e + cA D e) • ((a⁻¹).1 - 1 : Mx D ρ ρ)) := (adj_smul _ _).symm
      _ = adj ((a⁻¹).1 - 1 : Mx D ρ ρ) := by rw [hI]
  have hm : mt S (d.levi a) = (1 : Mx D S.rank S.rank) + (d.jX ⬝ (a.1 - 1 : Mx D ρ ρ) ⬝ d.pX + d.jY ⬝ (adj (a⁻¹).1 - 1 : Mx D ρ ρ) ⬝ d.pY) := by
    rw [d.mt_levi a]; conv_rhs => rw [← d.sum_eq_one]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]; abel
  have hdet : (mt S (d.levi a)).det = a.1.det * cA D (a⁻¹).1.det := by
    have h' : d.jX ⬝ (a.1 - 1 : Mx D ρ ρ) ⬝ d.pX + d.jY ⬝ (adj (a⁻¹).1 - 1 : Mx D ρ ρ) ⬝ d.pY =
        Matrix.fromCols d.jX d.jY ⬝ Matrix.fromRows ((a.1 - 1 : Mx D ρ ρ) ⬝ d.pX) ((adj (a⁻¹).1 - 1 : Mx D ρ ρ) ⬝ d.pY) := by
      rw [Matrix.fromCols_mul_fromRows, Matrix.mul_assoc, Matrix.mul_assoc]
    rw [hm, h', Matrix.det_one_add_mul_comm, Matrix.fromRows_mul_fromCols]
    simp only [Matrix.mul_assoc, d.pX_jX, d.pX_jY, d.pY_jX, d.pY_jY, Matrix.mul_one, Matrix.mul_zero]
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_add]
    simp only [add_zero, one_add_sub]
    rw [Matrix.det_fromBlocks_zero₂₁, det_adj]
  have hs : (1 - (e + cA D e)) * a.1.det = 1 - (e + cA D e) := det_supp _ hεε _ hA
  set t := Matrix.GeneralLinearGroup.det a with ht
  have ht1 : (t : AE D) = a.1.det := rfl
  have ht2 : ((t⁻¹ : (AE D)ˣ) : AE D) = (a⁻¹).1.det := by rw [ht, ← map_inv]; rfl
  refine ⟨?_, locU e h1 (t * Units.map (cA D).toMonoidHom t⁻¹), ?_, ?_⟩
  · have X : (e + cA D e) • (mt S (d.levi a) - 1) = mt S (d.levi a) - 1 := by
      rw [hm, add_sub_cancel_left, smul_add, smul_sandwich _ _ _ _ hA, smul_sandwich _ _ _ _ hB]
    intro i j
    exact congrFun (congrFun X i) j
  · rw [IsDetAt, locU_val, hdet, Units.val_mul, Units.coe_map, ht1, ht2]; rfl
  · set w := locU (cA D e) hce t with hw
    have hdc : cA D ((t⁻¹ : (AE D)ˣ) : AE D) * cA D (t : AE D) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have hs' : (1 - (e + cA D e)) * (t : AE D) = 1 - (e + cA D e) := by rw [ht1]; exact hs
    have key : t = locU e h1 (t * Units.map (cA D).toMonoidHom t⁻¹) * (w * Units.map (cA D).toMonoidHom w) := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, Units.coe_map, locU_val, Units.val_mul, Units.coe_map, hw, locU_val]
      simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, map_add, map_mul, map_sub, map_one, hcc]
      linear_combination (-((e * t * cA D ((t⁻¹ : (AE D)ˣ) : AE D) + 1 - e) * (t * cA D (t : AE D) - t - cA D (t : AE D) + 1) +
          ((t : AE D) ^ 2 * cA D ((t⁻¹ : (AE D)ˣ) : AE D) - t * cA D ((t⁻¹ : (AE D)ˣ) : AE D) - t + 1))) * h2 -
        ((t : AE D) * cA D ((t⁻¹ : (AE D)ˣ) : AE D) * cA D (t : AE D) - t * cA D ((t⁻¹ : (AE D)ˣ) : AE D) - cA D (t : AE D) + 1) * h1 -
        e * t * hdc + hs'
    conv_rhs => rw [key]
    rw [map_mul, map_mul, GlobalTheory.ConjAdjWeil.chi_conj hR w, mul_inv_cancel, mul_one]

theorem GlobalTheory.splitLeviDet : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (e : AE D), IsSplitIdem D e → (∀ g, SuppAt e S₀ g → SuppAt e S (d.emb0 g) ∧ ∃ x, IsDetAt e S₀ g x ∧ IsDetAt e S (d.emb0 g) x) ∧ ∀ (χ : (AE D)ˣ →* Circle) (n : ℕ), IsHeckeChar D χ → ResEta D χ n → ∀ a : GL (Fin ρ) (AE D), (∀ i j, (e + cA D e) * (a.1 - 1) i j = (a.1 - 1) i j) → SuppAt e S (d.levi a) ∧ ∃ x, IsDetAt e S (d.levi a) x ∧ χ x = χ (Matrix.GeneralLinearGroup.det a) := fun D S S₀ ρ d e he =>
  ⟨GlobalTheory.SplitLeviDet.emb0Part D S S₀ ρ d e he, GlobalTheory.SplitLeviDet.leviPart D S S₀ ρ d e he⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TsumAdelicMatrixSchwartzMajorantRationalNeTopStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tsum_adelicMatrixSchwartzMajorant_rational_ne_top : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ m n : ℕ, ∃ N : ℕ, ∀ K : Set (Mx D m n), IsCompact K → (∑' y : ratMx D m n, ENNReal.ofReal (maj θ K N y)) ≠ ⊤ := by
  first | exact @GlobalTheory.MajSum.tsum_maj_ne_top | exact GlobalTheory.MajSum.tsum_maj_ne_top | (intros; apply GlobalTheory.MajSum.tsum_maj_ne_top <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumTransportSourceRationalIsometryStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_datum_transport_source_rational_isometry : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (d : HypDec S S₀ 0), IsStdChar D ψ (-1) → Function.Bijective d.emb0 ∧ Function.Bijective (d.ext0 T) ∧ (∀ f : WO S T → ℂ, IsThetaFunO ψ S₀ T (fun w => f (d.ext0 T w)) ↔ IsThetaFunO ψ S T f) ∧ ∀ (χS χT : (AE D)ˣ →* Circle) (om : Om S T) (om₀ : Om S₀ T), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S₀ T χS χT om₀ → ∀ g h f, IsThetaFunO ψ S T f → om₀ (g, h) (fun w => f (d.ext0 T w)) = fun w => om (d.emb0 g, h) f (d.ext0 T w) := by
  first | exact @GlobalTheory.WeilSrc.om0_ext0_eq_om_emb0_of_isWeilDatumO | exact GlobalTheory.WeilSrc.om0_ext0_eq_om_emb0_of_isWeilDatumO | (intros; apply GlobalTheory.WeilSrc.om0_ext0_eq_om_emb0_of_isWeilDatumO <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorOrthSummandSlicesSobolevBoundedStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_operator_orth_summand_slices_sobolev_bounded : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (S A B T : HSp D) (o : OrthDec S A B), (∀ (χ χ' : (AE D)ˣ →* Circle) (om : Om A T), IsWeilDatumO ψ A T χ χ' om → ∀ p, IsSobForm ψ θ S T fun f => om p (fun u => f ((o.resS T).symm (u, 0))) 0) ∧ ∀ (χ χ' : (AE D)ˣ →* Circle) (om : Om B T), IsWeilDatumO ψ B T χ χ' om → ∀ p, IsSobForm ψ θ S T fun f => om p (fun v => f ((o.resS T).symm (0, v))) 0 := by
  first | exact @GlobalTheory.SliceForm.weil_slice_isSobForm | exact GlobalTheory.SliceForm.weil_slice_isSobForm | (intros; apply GlobalTheory.SliceForm.weil_slice_isSobForm <;> assumption)
end

