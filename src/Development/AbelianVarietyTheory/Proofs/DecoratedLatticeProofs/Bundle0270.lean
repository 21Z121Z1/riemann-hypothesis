import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0238
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0138
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBoundedUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0252
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1500
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0964
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0877
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilRepresentationContinuous
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0254
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
import Formalism.LocalToGlobal.Columns.ChainTw
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0245
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EntriesWellDefined
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0062
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0051
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0005
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0031
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0032
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0279
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0235
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0405
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0397
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0336
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0223
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0255
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0257
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmHostImaginaryGeneratorNeZero
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unf.Inhab

variable {D : D7}

theorem nonempty_vol (V : HSp D) : Nonempty (Vol V) :=
  let ⟨μ, 𝓕, h1, h2⟩ := GlobalTheory.RawLift.exists_haar_fundDomain V
  ⟨⟨μ, 𝓕, h1, h2⟩⟩

theorem nonempty_volN {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) : Nonempty (VolN d) :=
  let ⟨ν, 𝓝, h⟩ := GlobalTheory.Per.UnitN.exists_isUnitN D S ρ d.e (isIsoSub_e d)
  ⟨⟨ν, 𝓝, h⟩⟩

theorem nonempty_volM (D : D7) (m n : ℕ) : Nonempty (VolM D m n) :=
  let ⟨μ, 𝓕, h⟩ := exists_isCovolOne D m n
  ⟨⟨μ, 𝓕, h⟩⟩

theorem nonempty_volU (D : D7) (ρ : ℕ) : Nonempty (VolU D ρ) :=
  let ⟨ν, h⟩ := (GlobalTheory.UnitU.isUnitU_exists_unique_rightInvariant D ρ).1
  ⟨⟨ν, h⟩⟩

theorem coCpt_of_mul {V : HSp D} (h : ∃ K : Set (GA D V), IsCompact K ∧ ∀ g, ∃ γ ∈ GQ V, ∃ k ∈ K, g = γ * k) : CoCpt V := by
  obtain ⟨K, hK, h⟩ := h
  refine ⟨K, hK, fun g => ?_⟩
  obtain ⟨γ, hγ, k, hk, rfl⟩ := h g
  exact ⟨γ⁻¹, inv_mem hγ, by rwa [inv_mul_cancel_left]⟩

theorem coCpt_of_isAniso {V : HSp D} (h : IsAniso V) : CoCpt V :=
  coCpt_of_mul (GlobalTheory.Mem.AnisoQuotient.exists_compact D V h)

theorem coCpt_of_posDef {V : HSp D} (h : ∀ τ, (gramAt D V τ).PosDef) : CoCpt V :=
  coCpt_of_mul (GlobalTheory.definite_unitary_cocompact V h)

theorem exists_weil {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D) {χS χT : (AE D)ˣ →* Circle}
    (h1 : IsHeckeChar D χS) (h2 : IsHeckeChar D χT) (h3 : ResEta D χS S.rank) (h4 : ResEta D χT T.rank) :
    ∃ om, IsWeilDatumO ψ S T χS χT om :=
  GlobalTheory.WeilExist.exists_isWeilDatumO D ψ hψ S T χS χT (GlobalTheory.WeilParts.exists_isEtaTilde_unramified D) h1 h2 h3 h4

theorem exists_weil_pair {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D) :
    ∃ χS χT om, IsWeilDatumO ψ S T χS χT om :=
  let ⟨χS, a1, a2⟩ := GlobalTheory.RawLift.exists_hecke_resEta D S.rank
  let ⟨χT, b1, b2⟩ := GlobalTheory.RawLift.exists_hecke_resEta D T.rank
  ⟨χS, χT, exists_weil hψ S T a1 b1 a2 b2⟩

theorem nonempty_step {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (V V₀ W W₀ : HSp D) (ρ σ : ℕ)
    (hV : V.rank % 2 = V₀.rank % 2) (hW : W.rank % 2 = W₀.rank % 2) : Nonempty (Step ψ V V₀ W W₀ ρ σ) := by
  obtain ⟨χV, a1, a2⟩ := GlobalTheory.RawLift.exists_hecke_resEta D V.rank
  obtain ⟨χW, b1, b2⟩ := GlobalTheory.RawLift.exists_hecke_resEta D W.rank
  obtain ⟨om, h⟩ := exists_weil hψ V W a1 b1 a2 b2
  obtain ⟨om₀, h₀⟩ := exists_weil hψ V₀ W₀ a1 b1 (resEta_parity a2 hV) (resEta_parity b2 hW)
  obtain ⟨vW⟩ := nonempty_vol W
  obtain ⟨vS⟩ := nonempty_volM D W.rank ρ
  obtain ⟨vT⟩ := nonempty_volM D σ V₀.rank
  obtain ⟨vU⟩ := nonempty_volU D ρ
  exact ⟨⟨χV, χW, om, om₀, h, h₀, vW, vS, vT, vU⟩⟩

theorem even_im_hermitian_sub {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) : S.rank % 2 = S₀.rank % 2 := by
  have := d.rank_add
  omega

theorem nonempty_stepBF {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {ρ : ℕ} (B : BesLev D ρ) (J : JacLev D ρ) :
    Nonempty (StepBF ψ B J) :=
  nonempty_step hψ _ _ _ _ _ _ (even_im_hermitian_sub B.d) (even_im_hermitian_sub J.d)

theorem nonempty_stepFB {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {σ : ℕ} (J : JacLev D (σ + 1))
    (B : BesLev D σ) : Nonempty (StepFB ψ J B) :=
  nonempty_step hψ _ _ _ _ _ _ (even_im_hermitian_sub J.d) (even_im_hermitian_sub B.d)

theorem cmHost_imaginaryGenerator_ne_zero (D : D7) : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D

def selfLink {ρ : ℕ} (B : BesLev D ρ) : Link B B.L (D.host.xi0⁻¹ • B.ζ) where
  τ := -(D.host.xi0 • (1 : Matrix (Fin B.L.rank) (Fin B.L.rank) D.host.E))
  map := by
    rw [neg_mulVec, smul_mulVec, one_mulVec, smul_smul, mul_inv_cancel₀ (cmHost_imaginaryGenerator_ne_zero D), one_smul]
  norm := by
    have h := cmHost_imaginaryGenerator_ne_zero D
    have h' : star D.host.xi0 ≠ 0 := star_ne_zero.2 h
    rw [star_smul, mulVec_smul, dotProduct_smul, smul_dotProduct, star_inv₀, smul_eq_mul, smul_eq_mul]
    field_simp

def hypRefl (S : HSp D) : HypDec S S 0 where
  e := 0
  e' := 0
  i₀ := 1
  ee := by ext i; exact i.elim0
  e'e' := by ext i; exact i.elim0
  e'e := by ext i; exact i.elim0
  iso := by rw [conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  i₀e := by ext i j; exact j.elim0
  i₀e' := by ext i j; exact j.elim0
  rank_add := rfl

abbrev posLine (D : D7) : HSp D := diagSp D 1 ![false] 1 0

abbrev negLine (D : D7) : HSp D := diagSp D 1 ![true] 0 1

abbrev plane (D : D7) : HSp D := diagSp D 2 ![false, true] 1 1

theorem posDef_posLine (D : D7) (τ : D.what₂.Tau) : (gramAt D (posLine D) τ).PosDef := by
  have h : gramAt D (posLine D) τ = 1 := by
    rw [gramAt, diagSp_gram]
    ext i j
    rw [Subsingleton.elim (α := Fin 1) i j, Subsingleton.elim (α := Fin 1) j (0 : Fin 1)]
    exact (congrArg (tauE D τ) (Matrix.diagonal_apply_eq _ _)).trans ((map_one (tauE D τ)).trans (Matrix.one_apply_eq _).symm)
  rw [h]
  exact Matrix.PosDef.one

theorem coCpt_posLine (D : D7) : CoCpt (posLine D) := coCpt_of_posDef (posDef_posLine D)

theorem isLineVec_negLine {c : D.host.E} (hc : c ≠ 0) : IsLineVec (negLine D) (fun _ => c) := by
  refine ⟨rfl, ?_⟩
  rw [diagSp_gram]
  change ∑ i : Fin 1, star c * ∑ j : Fin 1, Matrix.diagonal (fun i => Examples₂.sgn (![true] i)) i j * c ≠ 0
  simp [Examples₂.sgn, hc]

def besPlane {V : HSp D} {ρ : ℕ} (d : HypDec V (plane D) ρ) {c : D.host.E} (hc : c ≠ 0) : BesLev D ρ where
  V := V
  V₀ := plane D
  A := posLine D
  L := negLine D
  d := d
  o := orthDecPlane D
  ζ := fun _ => c
  line := isLineVec_negLine hc
  cpt := coCpt_posLine D
  vA := (nonempty_vol _).some
  vN := (nonempty_volN d).some

def jacLine {W : HSp D} {ρ : ℕ} (d : HypDec W (posLine D) ρ) : JacLev D ρ where
  W := W
  W₀ := posLine D
  d := d
  cpt := coCpt_posLine D
  v0 := (nonempty_vol _).some
  vN := (nonempty_volN d).some

theorem exists_last {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (B : BesLev D 0) (J : JacLev D 0)
    (hJ : CoCpt J.W) {T : HSp D} (hT : CoCpt T) : ∃ t : Last ψ T B, t.J = J := by
  obtain ⟨s⟩ := nonempty_stepBF hψ B J
  obtain ⟨χS, χT, om, h⟩ := exists_weil_pair hψ J.W T
  obtain ⟨vT⟩ := nonempty_vol T
  exact ⟨⟨J, s, hJ, hT, χS, χT, om, h, vT⟩, rfl⟩

noncomputable def AllNonzero {ψ : AddChar (AF D.host.F) ℂ} {T : HSp D} :
    {ρ : ℕ} → {B : BesLev D ρ} → (c : Chain ψ T ρ B) → c.Data → Prop
  | _, _, .last _, Φ => Φ.1 ≠ 0 ∧ Φ.2 ≠ 0
  | _, _, .step _ _ _ _ _ _ c, Φ => Φ.1 ≠ 0 ∧ Φ.2.1 ≠ 0 ∧ AllNonzero c Φ.2.2

noncomputable def CoresPos {ψ : AddChar (AF D.host.F) ℂ} {T : HSp D} : {ρ : ℕ} → {B : BesLev D ρ} → Chain ψ T ρ B → Prop
  | _, _, .last t => 0 < t.J.W₀.rank
  | _, _B, .step J B' _ _ _ _ c => 0 < J.W₀.rank ∧ 0 < B'.A.rank ∧ CoresPos c

theorem exists_data {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {T : HSp D} {ρ : ℕ} {B : BesLev D ρ}
    (c : Chain ψ T ρ B) : ∃ Φ : c.Data, c.IsTheta Φ ∧ AllNonzero c Φ := by
  induction c with
  | @last B t =>
    obtain ⟨f, hf, f0⟩ := GlobalTheory.Mem.ThetaNonzero.exists_thetaO_ne_zero hψ B.V t.J.W
    obtain ⟨g, hg, g0⟩ := GlobalTheory.Mem.ThetaNonzero.exists_thetaO_ne_zero hψ t.J.W T
    exact ⟨(f, g), ⟨hf, hg⟩, f0, g0⟩
  | @step σ B J B' s₁ s₂ l vL c ih =>
    obtain ⟨f, hf, f0⟩ := GlobalTheory.Mem.ThetaNonzero.exists_thetaO_ne_zero hψ B.V J.W
    obtain ⟨g, hg, g0⟩ := GlobalTheory.Mem.ThetaNonzero.exists_thetaO_ne_zero hψ J.W B'.V
    obtain ⟨Φ, h, h0⟩ := ih
    exact ⟨(f, g, Φ), ⟨hf, hg, h⟩, f0, g0, h0⟩

theorem exists_chain_of_isStdChar {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) :
    ∃ (T : HSp D) (B : BesLev D 1) (c : Chain ψ T 1 B), 0 < B.A.rank ∧ 0 < T.rank ∧ CoresPos c ∧
      ∃ Φ : c.Data, c.IsTheta Φ ∧ AllNonzero c Φ := by
  let B : BesLev D 1 := besPlane (GlobalTheory.RegSW.Model.hypFour D) (cmHost_imaginaryGenerator_ne_zero D)
  let J : JacLev D 1 := jacLine (hypDecThree D)
  let B' : BesLev D 0 := besPlane (hypRefl (plane D)) one_ne_zero
  obtain ⟨t, ht⟩ := exists_last hψ B' (jacLine (hypRefl (posLine D))) (coCpt_posLine D) (coCpt_posLine D)
  obtain ⟨s₁⟩ := nonempty_stepBF hψ B J
  obtain ⟨s₂⟩ := nonempty_stepFB (σ := 0) hψ J B'
  have e : D.host.xi0⁻¹ • B.ζ = B'.ζ := funext fun _ => inv_mul_cancel₀ (cmHost_imaginaryGenerator_ne_zero D)
  have l : Link B B.L B'.ζ := e ▸ selfLink B
  obtain ⟨vL⟩ := nonempty_volM D B'.L.rank J.W₀.rank
  refine ⟨posLine D, B, .step J B' s₁ s₂ l vL (.last t), Nat.one_pos, Nat.one_pos, ⟨Nat.one_pos, Nat.one_pos, ?_⟩,
    exists_data hψ _⟩
  show 0 < t.J.W₀.rank
  rw [ht]
  exact Nat.one_pos

theorem isThetaFam_om {ψ : AddChar (AF D.host.F) ℂ} {S L : HSp D} {χS χL : (AE D)ˣ →* Circle} {om : Om S L}
    (hom : IsWeilDatumO ψ S L χS χL om) {Φ₀ : WO S L → ℂ} (hΦ : IsThetaFunO ψ S L Φ₀) :
    IsThetaFam ψ S L fun h => om (h, 1) Φ₀ where
  theta h := hom.om_pres _ _ hΦ
  cont := (GlobalTheory.ThetaJointCont.continuous_om_oriented hom hΦ).comp
    ((continuous_fst.prodMk continuous_const).prodMk continuous_snd)
  left γ hγ h w := by
    have h1 : ∀ V : HSp D, Formalism.L2.Theta.mt V 1 = 1 := fun V => by simp [Formalism.L2.Theta.mt]
    have e : actO S L γ 1 (w ⬝ Formalism.L2.Theta.mt S γ) = w := by
      rw [actO, h1, Matrix.one_mul, Matrix.mul_assoc, ← mt_mul, mul_inv_cancel, h1, Matrix.mul_one]
    have e' : ((γ * h, 1) : GA D S × GA D L) = (γ, 1) * (h, 1) := by simp
    rw [e', map_mul, Module.End.mul_apply,
      ← GlobalTheory.WeilRat.om_rat_actO D ψ hom.std S L χS χL om hom γ hγ 1 (one_mem _) _ (hom.om_pres _ _ hΦ) (w ⬝ Formalism.L2.Theta.mt S γ), e]

theorem exists_isThetaFam {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S L : HSp D) :
    ∃ Y, IsThetaFam ψ S L Y ∧ ∀ h, Y h ≠ 0 := by
  obtain ⟨χS, χL, om, hom⟩ := exists_weil_pair hψ S L
  obtain ⟨f, hf, f0⟩ := GlobalTheory.Mem.ThetaNonzero.exists_thetaO_ne_zero hψ S L
  refine ⟨_, isThetaFam_om hom hf, fun h h0 => f0 ?_⟩
  have : om (h, 1)⁻¹ (om (h, 1) f) = f := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [← this, show om (h, 1) f = 0 from h0, map_zero]

theorem exists_chain (D : D7) : (∃ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1)) ∧
    ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) →
      (∃ (T : HSp D) (B : BesLev D 1) (c : Chain ψ T 1 B), 0 < B.A.rank ∧ 0 < T.rank ∧ CoresPos c ∧
        ∃ Φ : c.Data, c.IsTheta Φ ∧ AllNonzero c Φ) ∧
      ∀ S L : HSp D, ∃ Y, IsThetaFam ψ S L Y ∧ ∀ h, Y h ≠ 0 :=
  ⟨(GlobalTheory.Ker.exists_infFam_and_stdChar D).2, fun _ hψ => ⟨exists_chain_of_isStdChar hψ, exists_isThetaFam hψ⟩⟩

end GlobalTheory.Unf.Inhab

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompletionRepresentativesNormalFormModUnipotentStatement
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completion_representatives_normal_form_mod_unipotent : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → ∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m), L.Ok Ch sel mu cst G s → IdxProd sel mu cst L → (∀ j c (h : j + 1 + c = s) (b : L.β (j + 1)) (g' : GL (XIx (Fin R.k) (Fin R.t) (j + 1) ⊕ Fin (c + 1)) k), IsGL ι (L.h (j + 1) b P) g' → ∃ (al : L.β j) (g : GL (XIx (Fin R.k) (Fin R.t) (j) ⊕ Fin (c + 1 + 1)) k), IsGL ι (L.h j al P) g ∧ flat W.ψ ν ((W.T s R).mu (j + 1)) ((W.T s R).Phi j (c + 1) (by omega)) g g' ≠ 0) → ∀ j c (h : j + c = s) (al : L.β j) (g : GL (XIx (Fin R.k) (Fin R.t) (j) ⊕ Fin (c + 1)) k), IsGL ι (L.h j al P) g → ∃ r ∈ GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) (j)) (c + 1) 1, GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice.IsNormalRep (W.T s R) W.ϖ j c h (r * g) := by
  first | exact @GlobalTheory.TwNormalReps.exists_normal_rep | exact GlobalTheory.TwNormalReps.exists_normal_rep | (intros; apply GlobalTheory.TwNormalReps.exists_normal_rep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateIntertwinerValuesSmoothAutomorphic
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjRowAut

theorem conj_lie {n : ℕ} {P H J E : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) (hs : Pᴴ * H * P = J)
    (hE : Eᴴ * J + J * E = 0) : (P * E * P⁻¹)ᴴ * H + H * (P * E * P⁻¹) = 0 := by
  have hd := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have hPi : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hd
  have hPiH : (P⁻¹)ᴴ * Pᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hPi, Matrix.conjTranspose_one]
  calc _ = (P⁻¹)ᴴ * Eᴴ * Pᴴ * H * (P * P⁻¹) + ((P⁻¹)ᴴ * Pᴴ) * H * (P * E * P⁻¹) := by
        rw [hPi, hPiH]; simp only [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_one, Matrix.one_mul]
    _ = (P⁻¹)ᴴ * (Eᴴ * J + J * E) * P⁻¹ := by
        rw [← hs]; simp only [Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
    _ = 0 := by rw [hE]; simp

theorem exp_conj {n : ℕ} {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) (E : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    P⁻¹ * NormedSpace.exp (t • (P * E * P⁻¹)) * P = NormedSpace.exp (t • E) := by
  have h : t • (P * E * P⁻¹) = P * (t • E) * P⁻¹ := by simp
  rw [h, Matrix.exp_conj _ _ hP]
  exact (GlobalTheory.IotaReal.conj_eq_iff _ _ _ hP).2 rfl

theorem iota_data {D : D7} (θ : InfFam D) (hθ : IsInfFam θ)
    (hexp : ∀ τ, ∀ Y ∈ lieAt (D.sp.Y 0) τ, ∀ t : ℝ, NormedSpace.exp (t • Y) ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ))
    (I : AutInst) (h : I = Formalism.L2.SG.InstExistsPf.instOf D) :
    let ι := (Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm)
    (∀ k ∈ GQ (D.sp.Y 0), ι k ∈ I.GFset) ∧ (∀ k ∈ GfC (D.sp.Y 0), (ι k).1 = 1) ∧
    (∀ k ∈ GinfC (D.sp.Y 0), (ι k).2 = 1) ∧
    (∀ v E, Formalism.REAL.inG (I.ε v) E → ∃ τ, ∃ Y ∈ lieAt (D.sp.Y 0) τ, ∀ t : ℝ,
      (ι (oneP θ (D.sp.Y 0) τ Y t)).2 = 1 ∧ uMat ((ι (oneP θ (D.sp.Y 0) τ Y t)).1 v) = NormedSpace.exp (t • E) ∧
        ∀ w, w ≠ v → uMat ((ι (oneP θ (D.sp.Y 0) τ Y t)).1 w) = 1) ∧
    (1 ≤ I.n → ∀ v, ∃ c : ℝ, 0 ≤ c ∧ ∀ g, Real.exp (GlobalTheory.Count.dOp (uMat ((ι g).1 v))) ≤ c * normInf θ (D.sp.Y 0) g) := by
  intro ι
  subst h
  have key : ∀ k, (∀ v, uMat ((ι k).1 v) = Formalism.L2.SG.AdBridge.ofHAInf (Formalism.L2.SG.InstExistsPf.instOf D) k v) ∧
      (Formalism.L2.SG.InstExistsPf.instOf D).fmat (ι k).2 = Formalism.L2.SG.AdBridge.ofHAFin _ k := by
    intro k
    have := Formalism.IndefR.RationalEmbedding.iota_symm_isBridge D (Formalism.IndefR.RationalEmbedding.iota D k)
    have e := (Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply k
    exact ⟨fun v => (this.1 v).trans (congrArg (fun z => Formalism.L2.SG.AdBridge.ofHAInf (Formalism.IndefR.RationalEmbedding.inst D) z v) e),
      this.2.trans (congrArg (Formalism.L2.SG.AdBridge.ofHAFin (Formalism.IndefR.RationalEmbedding.inst D)) e)⟩
  have hinf : ∀ k v, uMat ((ι k).1 v) = ((Formalism.L2.SG.InstExistsPf.instOf D).P v)⁻¹ *
      Formalism.MainNotions.StandardLattice.infMat (Formalism.L2.SG.InstExistsPf.instOf D).cm.sig (Formalism.L2.SG.InstExistsPf.instOf D).J
        (θ ((Formalism.L2.Host.tauPl D).symm v)) k * (Formalism.L2.SG.InstExistsPf.instOf D).P v := fun k v =>
    ((key k).1 v).trans (congrArg (fun M => ((Formalism.L2.SG.InstExistsPf.instOf D).P v)⁻¹ * M *
      (Formalism.L2.SG.InstExistsPf.instOf D).P v)
      (GlobalTheory.IotaReal.map_thetaV_gen (Formalism.L2.SG.InstExistsPf.instOf D) v (θ ((Formalism.L2.Host.tauPl D).symm v)) (hθ _) k))
  have hPu := (Formalism.L2.SG.InstExistsPf.instOf D).P_unit
  have hd : ∀ v, IsUnit ((Formalism.L2.SG.InstExistsPf.instOf D).P v).det := fun v =>
    (Matrix.isUnit_iff_isUnit_det _).1 (hPu v)
  have hsnd : ∀ k ∈ GinfC (D.sp.Y 0), (ι k).2 = 1 := by
    intro k hk
    apply Subtype.ext
    apply Units.ext
    refine (key k).2.trans (GlobalTheory.IotaReal.ofHAFin_eq_one _ _ ?_)
    have e3 : (finHom (D.sp.Y 0) k).val = 1 := by
      rw [show finHom (D.sp.Y 0) k = 1 from hk]; rfl
    ext i j
    exact congrFun (congrFun e3 i) j
  refine ⟨fun k hk => (Formalism.IndefR.RationalEmbedding.iota_rat D k).1 hk, fun k hk => ?_, hsnd, fun v E hE => ?_, fun hn v => ?_⟩
  · funext v
    apply Subtype.ext
    apply Units.ext
    show uMat ((ι k).1 v) = 1
    rw [hinf k v]
    have e : Formalism.MainNotions.StandardLattice.infMat (Formalism.L2.SG.InstExistsPf.instOf D).cm.sig (Formalism.L2.SG.InstExistsPf.instOf D).J
        (θ ((Formalism.L2.Host.tauPl D).symm v)) k = 1 := GlobalTheory.IotaReal.infMat_of_mem_GfC k hk _
    rw [e, Matrix.mul_one, Matrix.nonsing_inv_mul _ (hd v)]
  · have hY : (Formalism.L2.SG.InstExistsPf.instOf D).P v * E * ((Formalism.L2.SG.InstExistsPf.instOf D).P v)⁻¹ ∈
        lieAt (D.sp.Y 0) ((Formalism.L2.Host.tauPl D).symm v) :=
      conj_lie (hPu v) ((Formalism.L2.SG.InstExistsPf.instOf D).P_spec v) hE
    refine ⟨_, _, hY, fun t => ?_⟩
    have hat := GlobalTheory.IotaReal.isAtTau_atTau θ hθ _ _ (hexp _ _ hY t)
    refine ⟨hsnd _ hat.1, ?_, fun w hw => ?_⟩
    · refine (hinf _ v).trans (Eq.trans ?_ (exp_conj (hPu v) E t))
      exact congrArg (fun M : Matrix (Fin (Formalism.L2.SG.InstExistsPf.instOf D).n) (Fin (Formalism.L2.SG.InstExistsPf.instOf D).n) ℂ => ((Formalism.L2.SG.InstExistsPf.instOf D).P v)⁻¹ * M *
        (Formalism.L2.SG.InstExistsPf.instOf D).P v) hat.2.1
    · refine (hinf _ w).trans ?_
      refine (congrArg (fun M : Matrix (Fin (Formalism.L2.SG.InstExistsPf.instOf D).n) (Fin (Formalism.L2.SG.InstExistsPf.instOf D).n) ℂ => ((Formalism.L2.SG.InstExistsPf.instOf D).P w)⁻¹ * M *
        (Formalism.L2.SG.InstExistsPf.instOf D).P w) (hat.2.2 _ fun e => hw ((Formalism.L2.Host.tauPl D).symm.injective e))).trans ?_
      show ((Formalism.L2.SG.InstExistsPf.instOf D).P w)⁻¹ * (1 : Matrix (Fin (Formalism.L2.SG.InstExistsPf.instOf D).n) (Fin (Formalism.L2.SG.InstExistsPf.instOf D).n) ℂ) * (Formalism.L2.SG.InstExistsPf.instOf D).P w = 1
      rw [Matrix.mul_one, Matrix.nonsing_inv_mul _ (hd w)]
  · obtain ⟨c, hc0, hc⟩ := GlobalTheory.TauNorm.exp_dOp_le ((Formalism.L2.SG.InstExistsPf.instOf D).P v)⁻¹
      ((Formalism.L2.SG.InstExistsPf.instOf D).P v)
    refine ⟨c, hc0, fun g => ?_⟩
    have h0 := GlobalTheory.TauNorm.uMat_ne_zero _ hn (ι g) v
    rw [hinf g v] at h0 ⊢
    exact (hc _ h0).trans (mul_le_mul_of_nonneg_left (GlobalTheory.TauNorm.sum_le_normInf θ g _) hc0)

set_option maxHeartbeats 800000 in

theorem conjMap_isAutFunSm : GlobalTheory.Published.DiscreteSeriesClassification → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), S = parB (Ptw D) 0 → IsInfFam θ → GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → IdE X → Matches X h J χ t → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ (M.rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : M.Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u))) ψ) → ∀ u : M.Vec, IsAutFunSm θ (D.sp.Y 0) (GlobalTheory.ConjRowMult.conjMap X M c Φ h t u) := by
  intro hP D X h θ S M J χ t c hS hθ hgap hid hm hc Φ hΦ hrep
  have he : GlobalTheory.RepSmooth.IsEquiv θ (GlobalTheory.ConjRowMult.conjMap X M c Φ h t) :=
    GlobalTheory.T.conjugate_evaluation_map_intertwines_real_places hP D X h θ S M J χ t c hS hθ hgap hid hm hc Φ hΦ hrep
  have hs : GlobalTheory.RepSmooth.IsSob (GlobalTheory.ConjRowMult.conjMap X M c Φ h t) :=
    GlobalTheory.T.conjIntertwiner_pointValue_sobolevContinuous hP D X h θ S M J χ t c hS hθ hgap hid hm hc Φ hΦ hrep
  obtain ⟨hrat, hfst, hsnd, hone, hgr⟩ := iota_data θ hθ
    (fun τ Y hY s => GlobalTheory.SmVec.exp_mem_UH (GlobalTheory.SmVec.gram_unit (M.fr_unit τ) (M.fr_gram τ)) hY s) X.B.I h
  change ∀ k ∈ _, iotaX X h k ∈ _ at hrat
  change ∀ k ∈ _, (iotaX X h k).1 = 1 at hfst
  change ∀ k ∈ _, (iotaX X h k).2 = 1 at hsnd
  choose f hf using hrep
  have hval : ∀ u y, GlobalTheory.ConjRowMult.conjMap X M c Φ h t u y = star (f u (iotaX X h (y * t⁻¹))) := fun u y => by
    rw [GlobalTheory.ConjRowMult.conjMap_apply, GlobalTheory.ConjRowMult.contRepL_spec X (hf u)]
  have hg : 1 ≤ X.B.g := by
    rw [X.g_eq]
    exact Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  have hlev : ∀ u, ∀ k ∈ X.B.I.Kg X.B.g, ∀ y, f u (y * (1, k)) = f u y := by
    intro u k hk y
    obtain ⟨A, -, hA⟩ := hΦ
    have hA' : Φ = X.B.Re.comp A := hA.symm
    have h1 := Formalism.L2.SG.EvalTOntoRep.contRep_reg X (hf u) (1, k)
    have h2 : X.B.R (1, k) (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u))) =
        Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u)) := by
      rw [hA']
      exact congrArg (fun L : L2X X →L[ℂ] L2X X => L (A (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u))))
        (GlobalTheory.Dec.CuspFrame.re_fixed X.B k hk)
    rw [h2] at h1
    exact congrFun (Formalism.L2.SG.EvalTOntoRep.contRep_unique X h1 (hf u)) y
  have ht : t ∈ GfC (D.sp.Y 0) := hm.1
  have hcomm : ∀ a b : X.B.I.GA, a.1 = 1 → b.2 = 1 → a * b = b * a := fun a b ha hb =>
    Prod.ext (by simp [ha]) (by simp [hb])
  have hcont : ∀ u, Continuous (GlobalTheory.ConjRowMult.conjMap X M c Φ h t u) := fun u => by
    have : GlobalTheory.ConjRowMult.conjMap X M c Φ h t u = fun y => star (f u (iotaX X h (y * t⁻¹))) := funext (hval u)
    rw [this]
    exact ((hf u).1.comp ((iotaX X h).continuous.comp (continuous_mul_right _))).star
  have haut : ∀ u, IsAutFun (D.sp.Y 0) (GlobalTheory.ConjRowMult.conjMap X M c Φ h t u) := by
    intro u
    refine ⟨fun γ hγ y => ?_, ?_, hcont u⟩
    · rw [hval, hval, mul_assoc, map_mul, (hf u).2.1 _ (hrat γ hγ)]
    · obtain ⟨hKo, ⟨K, hK⟩, -⟩ := (GlobalTheory.CongTop.adelic_topology X.B.I).2.2.2.2.2.2 X.B.g hg
      refine ⟨K.comap ((MonoidHom.snd _ _).comp ((iotaX X h).toMulEquiv.toMonoidHom.comp
        (MulAut.conj t).toMonoidHom)), ?_, fun k hk hkf y => ?_⟩
      · rw [← hK] at hKo
        exact hKo.preimage (f := fun k => (iotaX X h (t * k * t⁻¹)).2)
          (continuous_snd.comp ((iotaX X h).continuous.comp
            ((continuous_mul_right _).comp (continuous_mul_left _))))
      · have hk' : (iotaX X h (t * k * t⁻¹)).2 ∈ X.B.I.Kg X.B.g := by rw [← hK]; exact hk
        have h1 : (iotaX X h (t * k * t⁻¹)).1 = 1 :=
          hfst _ ((GfC _).mul_mem ((GfC _).mul_mem ht hkf) ((GfC _).inv_mem ht))
        have e : y * k * t⁻¹ = y * t⁻¹ * (t * k * t⁻¹) := by group
        have e2 : iotaX X h (t * k * t⁻¹) = (1, (iotaX X h (t * k * t⁻¹)).2) := Prod.ext h1 rfl
        rw [hval, hval, e, map_mul, e2, hlev u _ hk']
  intro u
  refine ⟨haut u, GlobalTheory.RepSmooth.smooth hθ he hs hcont u, GlobalTheory.RepSmooth.zfin he hs u, ?_⟩
  have key : ∃ N : ℕ, ∀ v x, ∃ C : ℝ, ∀ a ∈ GinfC (D.sp.Y 0),
      ‖GlobalTheory.ConjRowMult.conjMap X M c Φ h t v (x * a)‖ ≤ C * normInf θ (D.sp.Y 0) a ^ N := by
    rcases Nat.eq_zero_or_pos (D.sp.Y 0).rank with hn | hn
    · refine ⟨0, fun v x => ⟨‖GlobalTheory.ConjRowMult.conjMap X M c Φ h t v x‖, fun a _ => ?_⟩⟩
      have : a = 1 := Subtype.ext (Units.ext (Matrix.ext fun i => (Fin.cast hn i).elim0))
      rw [this, mul_one, pow_zero, mul_one]
    have hn' : 1 ≤ X.B.I.n := by rw [← rank_eq X h]; exact hn
    have hti : (iotaX X h t⁻¹).1 = 1 := hfst _ ((GfC _).inv_mem ht)
    obtain ⟨m, hm⟩ := GlobalTheory.T.derivativeClosedClass_bounded_by_inverseLeastSize X.B hn' hg
    refine ⟨m, fun v x => ?_⟩
    obtain ⟨C, hC⟩ := hm (Set.range f) (by
      rintro _ ⟨u, rfl⟩
      refine ⟨⟨_, hf u⟩, hlev u, fun w E => ?_⟩
      obtain ⟨τ, Y, hY, hι⟩ := hone w E.1 E.2
      refine ⟨_, ⟨Function.update u τ (GlobalTheory.RepSmooth.der u τ hY), rfl⟩, fun y => ?_⟩
      have h1 := (GlobalTheory.RepSmooth.hasDerivAt_apply he hs τ u hY ((iotaX X h).symm y * t)).star
      simp only [hval, star_star, mul_inv_cancel_right, ContinuousMulEquiv.apply_symm_apply] at h1
      refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
      have e1 : iotaX X h (oneP θ (D.sp.Y 0) τ Y s) =
          GlobalTheory.SobolevBound.onePar X.B (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.atPlace X.B w E) s :=
        GlobalTheory.RepSmooth.eq_onePar X.B w E s (hι s).1 (hι s).2.1 (hι s).2.2
      have e2 : iotaX X h ((iotaX X h).symm y * t * oneP θ (D.sp.Y 0) τ Y s * t⁻¹) =
          y * iotaX X h (oneP θ (D.sp.Y 0) τ Y s) := by
        have h3 : (iotaX X h (oneP θ (D.sp.Y 0) τ Y s)).2 = 1 := (hι s).1
        rw [map_mul, map_mul, mul_assoc, ← hcomm _ _ hti h3, ← mul_assoc, ← map_mul, mul_inv_cancel_right,
          ContinuousMulEquiv.apply_symm_apply]
      show f u _ = f u _
      rw [e2, e1]) _ ⟨v, rfl⟩
    choose b hb0 hb using hgr hn'
    have hp := (GlobalTheory.TauLipschitz.tauLip X.B.I hn').1
    have hB : 0 ≤ ∑ w, b w := Finset.sum_nonneg fun w _ => hb0 w
    refine ⟨|C| * ((GlobalTheory.Count.tau1 X.B.I (iotaX X h (x * t⁻¹)))⁻¹ * ∑ w, b w) ^ m, fun a ha => ?_⟩
    have hN : 0 ≤ normInf θ (D.sp.Y 0) a := by unfold normInf; positivity
    have e : iotaX X h (x * a * t⁻¹) = iotaX X h (x * t⁻¹) * iotaX X h a := by
      rw [map_mul, map_mul, map_mul, mul_assoc, ← hcomm _ _ hti (hsnd a ha), mul_assoc]
    have h2 := GlobalTheory.TauNorm.inv_tau_mul_le X.B.I hn' (iotaX X h (x * t⁻¹)) (iotaX X h a) (hsnd a ha)
      ((∑ w, b w) * normInf θ (D.sp.Y 0) a) fun w => (hb w a).trans
        (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun w _ => hb0 w) (Finset.mem_univ w)) hN)
    rw [hval, norm_star, e]
    refine (hC _).trans ?_
    have h0 := inv_nonneg.2 (hp (iotaX X h (x * t⁻¹) * iotaX X h a)).le
    rw [mul_assoc, ← mul_pow, mul_assoc]
    exact mul_le_mul (le_abs_self _) (pow_le_pow_left₀ h0 h2 m) (pow_nonneg h0 m) (abs_nonneg _)
  obtain ⟨N, hN⟩ := key
  refine ⟨N, fun l hl x => ?_⟩
  obtain ⟨v, hv⟩ := GlobalTheory.RepSmooth.foldr_rder he hs u l hl
  rw [hv]
  exact hN v x

end GlobalTheory.ConjRowAut

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DictionaryColumnScalarFormEqTraceColumnFormStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dictionaryColumnScalarForm_eq_traceColumnForm : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (B : SBes X h u ψ (D.sp.X 0)) (F : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F) (hK : X.LevelSubgroupCharacter) (θ : InfFam D) (a₀ : GA D (D.sp.X 0)), IsInfFam θ → GlobalTheory.Core.Mi.IdE X → B.Adapted tr.wt → IsTransportAdelicCorrection tr a₀ → Formalism.L2.SG.ColDict.LevelMatch X tr hK → ∃ ξ : (D.mem u).C.Y 0 → X.Vpi u, Submodule.span ℂ (Set.range ξ) = ⊤ ∧ ∀ (T : Cu X u hK) (y : (D.mem u).C.Y 0) (g : GA D (D.sp.X 0)), (chart0 F).rd θ (Formalism.L2.SG.ColDict.colDictL X tr hK T) y g = B.colForm T.1 (ξ y) (g * a₀⁻¹) := by
  first | exact @GlobalTheory.Core.Mi.colDict_rd_eq_colForm | exact GlobalTheory.Core.Mi.colDict_rd_eq_colForm | (intros; apply GlobalTheory.Core.Mi.colDict_rd_eq_colForm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiGroupHaarIsMulRightInvariantStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobiGroup_haar_isMulRightInvariant : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (μ : Measure (jacGrp d)), μ.IsHaarMeasure → μ.IsMulRightInvariant := by
  first | exact @GlobalTheory.JacUnimod.jacGrp_rightInv | exact GlobalTheory.JacUnimod.jacGrp_rightInv | (intros; apply GlobalTheory.JacUnimod.jacGrp_rightInv <;> assumption)
end

