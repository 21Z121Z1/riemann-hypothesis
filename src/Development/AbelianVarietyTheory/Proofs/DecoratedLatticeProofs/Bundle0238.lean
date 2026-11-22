import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0080
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0141
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0185
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0220
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0135
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0170
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0327
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.Bundle0008
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0171
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0229
import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.FundamentalContinuity.AdelicIsomorphismStatement
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0222
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0217
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0228
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001
import Formalism.LocalToGlobal.Columns.HeckeSp

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCentralRealPointUnitScalarSinglePlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

noncomputable section

namespace GlobalTheory.CentralUnit

variable {D : D7}

theorem exists_unit {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    ∃ a : AE D, finPart D a = 1 ∧ (∀ ρ, θ ρ (infPart D a) = if ρ = τ then ζ else 1) ∧ cA D a * a = 1 := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.FockCompare.exists_chart hθ
  let v : D.what₂.Tau → ℂ := fun ρ => if ρ = τ then ζ - 1 else 0
  let a : AE D := 1 + σ v
  have a1 : finPart D a = 1 := by
    simp only [a]; rw [RingHom.map_add, hσ.fin, RingHom.map_one, add_zero]
  have a2 : ∀ ρ, θ ρ (infPart D a) = if ρ = τ then ζ else 1 := by
    intro ρ
    simp only [a]; rw [RingHom.map_add, RingHom.map_add, hσ.comp, RingHom.map_one, RingHom.map_one]
    simp only [v]
    split_ifs <;> ring
  refine ⟨a, a1, a2, sub_eq_zero.1 (hσ.ext _ ?_ fun ρ => ?_)⟩
  · have e : finPart D (cA D a) = sigR (Af D.host.F) D.sp.cm.sig (finPart D a) :=
      GlobalTheory.FockCompare.LiftUnitary.snd_sigR D.sp.cm.sig a
    rw [RingHom.map_sub, RingHom.map_mul, RingHom.map_one, e, a1, RingHom.map_one, one_mul, sub_self]
  · rw [RingHom.map_sub, RingHom.map_sub, RingHom.map_mul, RingHom.map_mul, RingHom.map_one, RingHom.map_one,
      GlobalTheory.FockCompare.comp_cA hθ, a2]
    split_ifs
    · rw [Complex.conj_mul', hζ, Complex.ofReal_one, one_pow, sub_self]
    · rw [RingHom.map_one, one_mul, sub_self]

theorem scalar_mem (S : HSp D) {a : AE D} (ha : cA D a * a = 1) :
    Formalism.UG.cT (cA D) (Matrix.diagonal fun _ : Fin S.rank => a) * JR (AF D.host.F) S.gram *
      (Matrix.diagonal fun _ : Fin S.rank => a) = JR (AF D.host.F) S.gram := by
  rw [Formalism.UG.cT, Matrix.diagonal_map (RingHom.map_zero _), Matrix.diagonal_transpose]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  linear_combination (JR (AF D.host.F) S.gram i j) * ha

noncomputable def scalarElt (S : HSp D) {a : AE D} (ha : cA D a * a = 1) : GA D S :=
  ⟨⟨Matrix.diagonal fun _ => a, Matrix.diagonal fun _ => cA D a,
    by rw [Matrix.diagonal_mul_diagonal, mul_comm, ha, Matrix.diagonal_one],
    by rw [Matrix.diagonal_mul_diagonal, ha, Matrix.diagonal_one]⟩, scalar_mem S ha⟩

theorem mt_scalarElt (S : HSp D) {a : AE D} (ha : cA D a * a = 1) :
    Formalism.L2.Theta.mt S (scalarElt S ha) = Matrix.diagonal fun _ => a := rfl

theorem scalarElt_mem_GinfC (S : HSp D) {a : AE D} (ha : cA D a * a = 1) (h1 : finPart D a = 1) :
    scalarElt S ha ∈ GinfC S := by
  rw [GinfC, MonoidHom.mem_ker]
  refine Units.ext ?_
  ext i j
  change ((Matrix.diagonal fun _ : Fin S.rank => a).map (finPart D)) i j =
    (1 : Matrix (Fin S.rank) (Fin S.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) i j
  rw [Matrix.map_apply, Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs
  · exact h1
  · exact RingHom.map_zero _

theorem scalarElt_mem_center (S : HSp D) {a : AE D} (ha : cA D a * a = 1) :
    scalarElt S ha ∈ Subgroup.center (GA D S) := by
  refine Subgroup.mem_center_iff.2 fun k => Subtype.ext (Units.ext ?_)
  ext i j
  change (k.1.val * Matrix.diagonal fun _ : Fin S.rank => a) i j = ((Matrix.diagonal fun _ : Fin S.rank => a) * k.1.val) i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]

theorem compAt_scalarElt (θ : InfFam D) (τ : D.what₂.Tau) (S : HSp D) {a : AE D} (ha : cA D a * a = 1) :
    compAt θ τ (Formalism.L2.Theta.mt S (scalarElt S ha)) = θ τ (infPart D a) • (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ) := by
  rw [mt_scalarElt]
  ext i j
  rw [compAt, Matrix.map_apply, Matrix.smul_apply, Matrix.diagonal_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> simp

theorem exists_central_of_norm_one : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (S : HSp D) (τ : D.what₂.Tau) (ζ : ℂ), ‖ζ‖ = 1 → ∃ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) ∧ compAt θ τ (Formalism.L2.Theta.mt S z) = ζ • (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ) ∧ ∀ ρ : D.what₂.Tau, ρ ≠ τ → compAt θ ρ (Formalism.L2.Theta.mt S z) = 1 := by
  intro D θ hθ S τ ζ hζ
  obtain ⟨a, a1, a2, ac⟩ := exists_unit hθ τ hζ
  refine ⟨scalarElt S ac, scalarElt_mem_GinfC S ac a1, scalarElt_mem_center S ac, ?_, fun ρ hρ => ?_⟩
  · rw [compAt_scalarElt, a2, if_pos rfl]
  · rw [compAt_scalarElt, a2, if_neg hρ, one_smul]

end GlobalTheory.CentralUnit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsComplMapEq
section
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW GlobalTheory.Core.Rk.SWQ
open Formalism.UG (IsUnifV qV Ov ordL diagJ)
open GlobalTheory.LFun (KGL toCompl IsSplitChart IsSatVecGL satEig)
open scoped Classical

noncomputable section

namespace GlobalTheory.Core.Rk.SWQ.LatHalf

open scoped TensorProduct
open GlobalTheory.FinPl (latMul latV latA idAt MxAt)
open GlobalTheory.LFun (latAt IsFrameAt complMap)

variable {D : D7} {q : FinPl D} {w : HeightOneSpectrum (𝓞 D.host.E)}

theorem exists_gen {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hI : I ≠ 0) :
    ∃ a₀ ∈ I, a₀ ≠ 0 ∧ ∀ a ∈ I, ∃ c ∈ Ov E w,
      algebraMap E (w.adicCompletion E) a = algebraMap E (w.adicCompletion E) a₀ * c := by
  obtain ⟨s, hs⟩ : (I : Submodule (𝓞 E) E).FG := FractionalIdeal.fg_of_isNoetherianRing le_rfl I
  have hne : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    apply hI
    rw [← FractionalIdeal.coeToSubmodule_eq_bot, ← hs]
    simp
  obtain ⟨a₀, ha₀, hmax⟩ := s.exists_max_image (fun a => Valued.v (algebraMap E (w.adicCompletion E) a)) hne
  have hle : ∀ a ∈ (I : Submodule (𝓞 E) E),
      Valued.v (algebraMap E (w.adicCompletion E) a) ≤ Valued.v (algebraMap E (w.adicCompletion E) a₀) := by
    intro a ha
    rw [← hs] at ha
    induction ha using Submodule.span_induction with
    | mem x hx => exact hmax x hx
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact (Valuation.map_add _ _ _).trans (max_le hx hy)
    | smul r x _ hx =>
      rw [Algebra.smul_def, map_mul, map_mul]
      have hr : Valued.v (algebraMap E (w.adicCompletion E) (algebraMap (𝓞 E) E r)) ≤ 1 :=
        GlobalTheory.AdeleBaseChange.algebraMap_int_mem r w
      exact (mul_le_mul_left hr _).trans (by rw [one_mul]; exact hx)
  have h0 : a₀ ≠ 0 := by
    rintro rfl
    apply hI
    rw [← FractionalIdeal.coeToSubmodule_eq_bot, eq_bot_iff]
    intro a ha
    have := hle a ha
    simpa using this
  have h0' : algebraMap E (w.adicCompletion E) a₀ ≠ 0 := (map_ne_zero _).2 h0
  refine ⟨a₀, show a₀ ∈ (I : Submodule (𝓞 E) E) from hs ▸ Submodule.subset_span ha₀, h0, fun a ha =>
    ⟨algebraMap E _ a / algebraMap E _ a₀, ?_, by field_simp⟩⟩
  change Valued.v (algebraMap E (w.adicCompletion E) a / algebraMap E (w.adicCompletion E) a₀) ≤ 1
  rw [map_div₀]
  exact div_le_one_of_le₀ (hle a ha) zero_le'

theorem mul_mem_gen {S : HSp D} {𝔞 : Set D.host.E} {L : Lat S} {P : FinPl D → Prop} {z : AE D}
    (hz : finPart D z ∈ intAE D) {β : Af D.host.F} (hβi : β ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F)
    (hβ : ∀ v, ¬ P v → evalV D.host.F v β = 0) {a : D.host.E} (ha : a ∈ 𝔞) {x : Fin S.rank → D.host.E} (hx : x ∈ L) :
    (fun i => z * (pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x i))) ∈ latMul S 𝔞 L P := by
  let Φ : Af D.host.F ⊗[D.host.F] D.host.E →+ (Fin S.rank → AE D) :=
    AddMonoidHom.mk' (fun c i => GlobalTheory.LatticeStable.liftFin D (c * (β ⊗ₜ[D.host.F] (a * x i))))
      fun c c' => funext fun i => by rw [add_mul, LinearMap.map_add]; rfl
  have hle : intAE D ≤ (latMul S 𝔞 L P).comap Φ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨γ, hγ, o, rfl⟩
    refine AddSubgroup.subset_closure ⟨γ * β, fun v => by rw [map_mul]; exact mul_mem (hγ v) (hβi v),
      fun v hv => by rw [map_mul, hβ v hv, mul_zero], a, ha, o • x, L.smul_mem o hx, ?_⟩
    funext i
    change GlobalTheory.LatticeStable.liftFin D ((γ ⊗ₜ[D.host.F] (o : D.host.E)) * (β ⊗ₜ[D.host.F] (a * x i))) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, GlobalTheory.LatticeStable.liftFin_tmul, Pi.smul_apply, Algebra.smul_def,
      show algebraMap (𝓞 D.host.E) D.host.E o = (o : D.host.E) from rfl]
    congr 1
    ring
  have e : (fun i => z * (pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x i))) = Φ (finPart D z) :=
    funext fun i => GlobalTheory.LatticeStable.mul_pair_tmul D z β _
  rw [e]
  exact hle hz

theorem cw_tmul (h : w.under (𝓞 D.host.F) = q) (α : Af D.host.F) (x : D.host.E) :
    cw h (pairA D.host.F 0 α ⊗ₜ[D.host.F] x) = complMap h (evalV D.host.F q α) * algebraMap D.host.E _ x := rfl

theorem cw_mem (h : w.under (𝓞 D.host.F) = q) {S : HSp D} {𝔞 : Set D.host.E} {L : Lat S} {P : FinPl D → Prop}
    {a₀ : w.adicCompletion D.host.E} (h𝔞 : ∀ a ∈ 𝔞, ∃ c ∈ Ov D.host.E w, algebraMap D.host.E _ a = a₀ * c)
    {y : Fin S.rank → AE D} (hy : y ∈ latMul S 𝔞 L P) : ∃ z ∈ latAt w L, ∀ i, cw h (y i) = a₀ * z i := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hαi, -, a, ha, x, hx, rfl⟩ := hy
    obtain ⟨c, hc, e⟩ := h𝔞 a ha
    refine ⟨_, (latAt w L).smul_mem ⟨complMap h (evalV D.host.F q α) * c,
      mul_mem (GlobalTheory.LFun.complMap_mem h (hαi q)) hc⟩ (Submodule.subset_span ⟨x, hx, rfl⟩), fun i => ?_⟩
    rw [cw_tmul, map_mul, e]
    change _ = a₀ * (complMap h (evalV D.host.F q α) * c * algebraMap D.host.E _ (x i))
    ring
  | zero => exact ⟨0, zero_mem _, fun i => by simp⟩
  | add y y' _ _ hy hy' =>
    obtain ⟨z, hz, e⟩ := hy
    obtain ⟨z', hz', e'⟩ := hy'
    exact ⟨z + z', add_mem hz hz', fun i => by simp [e, e', mul_add]⟩
  | neg y _ hy =>
    obtain ⟨z, hz, e⟩ := hy
    exact ⟨-z, neg_mem hz, fun i => by simp [e]⟩

theorem exists_complMap_eq (h : w.under (𝓞 D.host.F) = q) (hs : Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) q)
    {c : w.adicCompletion D.host.E} (hc : c ∈ Ov D.host.E w) :
    ∃ α ∈ q.adicCompletionIntegers D.host.F, complMap h α = c := by
  obtain ⟨τ, rfl⟩ := GlobalTheory.LFun.SplitChart.exists_splitPrime_eq (isCMExt_host D) hs h
  obtain ⟨ψ, h1, -, h3, -⟩ := GlobalTheory.LFun.SplitChart.exists_equiv_complMap τ h
  obtain ⟨α, rfl⟩ := ψ.surjective c
  exact ⟨α, (GlobalTheory.LFun.SplitChart.map_mem_Ov_iff h3).1 hc, (h1 α).symm⟩

theorem singleFin_supp (α : Fv D.host.F q) : ∀ v, ¬ v = q → evalV D.host.F v (singleFin q α) = 0 :=
  fun _ hv => evalV_singleFin_ne hv α

theorem iota_mem (h : w.under (𝓞 D.host.F) = q) (hs : Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) q)
    {ι : w.adicCompletion D.host.E →+ AE D} (h1 : ∀ x, cw h (ι x) = x) (h4 : ∀ a x, a * ι x = ι (cw h a * x))
    {S : HSp D} {𝔞 : Set D.host.E} {L : Lat S} {a₀ : D.host.E} (ha₀ : a₀ ∈ 𝔞)
    {z : Fin S.rank → w.adicCompletion D.host.E} (hz : z ∈ latAt w L) :
    (fun i => ι (algebraMap D.host.E _ a₀ * z i)) ∈ latMul S 𝔞 L (fun v => v = q) := by
  have hint : finPart D (ι 1) ∈ intAE D :=
    GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, h4, h1, one_mul])
  have key : ∀ c ∈ Ov D.host.E w,
      (fun i => ι (algebraMap D.host.E _ a₀ * (c * z i))) ∈ latMul S 𝔞 L (fun v => v = q) := by
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, hx, rfl⟩ := hz
      intro c hc
      obtain ⟨α, hα, rfl⟩ := exists_complMap_eq h hs hc
      have hαi : singleFin q α ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F := fun v => by
        by_cases hv : v = q
        · rw [hv, evalV_singleFin_self]; exact hα
        · rw [singleFin_supp α v hv]; exact zero_mem _
      convert mul_mem_gen (P := fun v => v = q) hint hαi (singleFin_supp α) ha₀ hx using 2 with i
      rw [mul_comm (ι 1), h4, cw_tmul, evalV_singleFin_self, (algebraMap D.host.E (w.adicCompletion D.host.E)).map_mul]
      congr 1
      ring
    | zero =>
      intro c _
      convert zero_mem (latMul S 𝔞 L (fun v => v = q)) using 2 with i
      simp
    | add x y _ _ hx hy =>
      intro c hc
      convert add_mem (hx c hc) (hy c hc) using 2 with i
      simp [mul_add]
    | smul r x _ hx =>
      intro c hc
      convert hx (c * r) (mul_mem hc r.2) using 3 with i
      change _ * (c * ((r : w.adicCompletion D.host.E) * x i)) = _
      ring
  simpa using key 1 (one_mem _)

end GlobalTheory.Core.Rk.SWQ.LatHalf

open GlobalTheory.Core.Rk.SWQ.LatHalf in

theorem GlobalTheory.Core.Rk.SWQ.LatHalf.mem_latO_iff_intM : ∀ (D : D7) (q : FinPl D) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = q), Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) q → ∀ (S T : HSp D) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∀ a : GL (Fin S.rank) (w.adicCompletion D.host.E), GlobalTheory.LFun.IsFrameAt w LS a → ∃ b : GL (Fin T.rank) (w.adicCompletion D.host.E), ∀ u : WO S T, offM q u = 0 → (∀ i j, cw h (cA D (u i j)) = 0) → (u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (fun v => v = q) ↔ IntM ((b⁻¹).1 * u.map (cw h) * a.1)) := by
  intro D q w h hs S T LS LT hS hT a ha
  obtain ⟨ι, -, h1, -, -, h4, h5, -, -⟩ := GlobalTheory.Core.Rk.SplitIota.exists_iota D q w h hs
  obtain ⟨e, ⟨⟨b₀, hb₀, -⟩, -⟩, -, -⟩ := GlobalTheory.LFun.SplitChart.exists_isSplitChart (isCMExt_host D)
    (GlobalTheory.Doubling.isHermND_gram T) hT.1.fg hT.1.span_eq_top h hs
    (GlobalTheory.Core.Rk.IwSplit.isSelfDualAt_of_isSelfDualC hT q)
  clear e
  obtain ⟨a₀, ha₀, h0, hgen⟩ := exists_gen w D.host.AA (GlobalTheory.ModelLatticeCheck.AA_ne_zero D)
  set π : w.adicCompletion D.host.E := algebraMap D.host.E _ a₀ with hπ
  have hπ0 : π ≠ 0 := (map_ne_zero _).2 h0
  let b : GL (Fin T.rank) (w.adicCompletion D.host.E) :=
    ⟨π • b₀.1, π⁻¹ • (b₀⁻¹).1, by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hπ0, one_smul, Units.mul_inv], by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hπ0, one_smul, Units.inv_mul]⟩
  have hb : (b⁻¹).1 = π⁻¹ • (b₀⁻¹).1 := rfl
  have hone : ∀ x ∈ ({1} : Set D.host.E), ∃ c ∈ Ov D.host.E w,
      algebraMap D.host.E (w.adicCompletion D.host.E) x = 1 * c := by
    rintro _ rfl
    exact ⟨1, one_mem _, by simp⟩
  refine ⟨b, fun u hoff hc => ?_⟩
  have hu1 : ∀ i j, algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleFin q 1)) * u i j = u i j := fun i j =>
    (sub_eq_zero.1 (congrFun (congrFun hoff i) j)).symm
  have hu : ∀ i j, u i j = ι (cw h (u i j)) := fun i j => by
    conv_lhs => rw [← hu1, h5, hc, map_zero, map_zero, add_zero]
  have hmv : ∀ (y : Fin S.rank → AE D) i, cw h ((u *ᵥ y) i) = (u.map (cw h) *ᵥ fun j => cw h (y j)) i :=
    fun y i => RingHom.map_mulVec (cw h) u y i
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D S T LS LT hS hT, hb]
  constructor
  · rintro ⟨-, H⟩ i j
    have hj : a.1 *ᵥ (Pi.single j 1) ∈ GlobalTheory.LFun.latAt w LS := (ha _).1 fun k => by
      by_cases e : k = j
      · subst e; simp
      · simp [e]
    have hy := iota_mem h hs h1 h4 (𝔞 := {1}) rfl hj
    obtain ⟨z, hz, e⟩ := cw_mem h (a₀ := π) hgen (H _ hy)
    have e' : u.map (cw h) *ᵥ (a.1 *ᵥ (Pi.single j 1)) = π • z := by
      funext k
      have := e k
      rw [hmv] at this
      simp only [h1, map_one, one_mul] at this
      exact this
    have hz' := (hb₀ ((b₀⁻¹).1 *ᵥ z)).2 (by rwa [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]) i
    have : (π⁻¹ • (b₀⁻¹).1 * u.map (cw h) * a.1) *ᵥ (Pi.single j 1) = (b₀⁻¹).1 *ᵥ z := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e', Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul,
        inv_mul_cancel₀ hπ0, one_smul]
    rw [← this, Matrix.mulVec_single_one] at hz'
    exact hz'
  · intro H
    refine ⟨fun i j => ?_, fun y hy => ?_⟩
    · rw [← hu1]
      exact Ideal.mul_mem_right _ _ (GlobalTheory.FinPl.LatMem.tmul_mem_idAt (singleFin_supp 1) 1)
    · obtain ⟨z, hz, e⟩ := cw_mem h hone hy
      have hx := (ha ((a⁻¹).1 *ᵥ z)).2 (by rwa [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec])
      have hM := (hb₀ ((π⁻¹ • (b₀⁻¹).1 * u.map (cw h) * a.1) *ᵥ ((a⁻¹).1 *ᵥ z))).1 fun i =>
        sum_mem fun k _ => mul_mem (H i k) (hx k)
      have e2 : b₀.1 *ᵥ ((π⁻¹ • (b₀⁻¹).1 * u.map (cw h) * a.1) *ᵥ ((a⁻¹).1 *ᵥ z)) = π⁻¹ • (u.map (cw h) *ᵥ z) := by
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec z, Units.mul_inv, Matrix.one_mulVec,
          Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      rw [e2] at hM
      refine (congrArg (· ∈ GlobalTheory.FinPl.latA T LT (fun v => v = q)) ?_).mpr
        (iota_mem h hs h1 h4 (𝔞 := {x | x ∈ D.host.AA}) ha₀ hM)
      funext i
      rw [← hπ, Pi.smul_apply, smul_eq_mul, mul_inv_cancel_left₀ hπ0]
      simp only [Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      conv_lhs => rw [hu, mul_comm, h4, e, one_mul, mul_comm]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLeviPreimageOfFixIsotropicFrames
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.AdBridge GlobalTheory.BesselChar

noncomputable section

namespace GlobalTheory.MixModel.HypDec

variable {D : D7}

theorem gram_mt {S : HSp D} (g : GA D S) {k l : ℕ} (x : Mx D S.rank k) (y : Mx D S.rank l) :
    adj (mt S g ⬝ x) ⬝ (gA S ⬝ (mt S g ⬝ y)) = adj x ⬝ (gA S ⬝ y) := by
  rw [adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA S), ← Matrix.mul_assoc (adj (mt S g)),
    mt_unitary]

theorem exists_emb0_eq_of_fix_jX_jY {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (g : GA D S)
    (hX : mt S g ⬝ d.jX = d.jX) (hY : mt S g ⬝ d.jY = d.jY) : ∃ b : GA D S₀, d.emb0 b = g := by
  set M := mt S g with hM
  set B := d.p0 ⬝ M ⬝ d.j0 with hB
  have h1 : d.pX ⬝ M ⬝ d.j0 = 0 := by
    rw [pX_eq, Matrix.mul_assoc, Matrix.mul_assoc, ← hY, adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA S) M,
      ← Matrix.mul_assoc (adj M), mt_unitary, gramR_Y0_eq_TI]
  have h2 : d.pY ⬝ M ⬝ d.j0 = 0 := by
    rw [pY_eq, Matrix.mul_assoc, Matrix.mul_assoc, ← hX, adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA S) M,
      ← Matrix.mul_assoc (adj M), mt_unitary, wittDecomp_gram_X_anisotropic]
  have h3 : M ⬝ d.j0 = d.j0 ⬝ B := by
    rw [Matrix.mul_assoc] at h1 h2
    rw [← Matrix.one_mul (M ⬝ d.j0), ← d.sum_eq_one]
    simp only [Matrix.add_mul, Matrix.mul_assoc, h1, h2, Matrix.mul_zero, add_zero, zero_add, hB]
  have h4 : adj B * (gA S₀ * B) = gA S₀ := by
    have e1 := gram_mt g d.j0 d.j0
    rw [← hM, h3, d.gram_00, adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA S), ← Matrix.mul_assoc (adj d.j0),
      ← Matrix.mul_assoc (adj d.j0), Matrix.mul_assoc (adj d.j0), d.gram_00] at e1
    exact e1
  refine ⟨ofMat S₀ B h4, d.ga_ext ?_ ?_ ?_⟩
  · rw [wittDecomp_anisotropicEmbedding_inclX, ← hM, hX]
  · rw [wittDecomp_anisotropicEmbedding_inclAnisotropic, mt_ofMat, ← hM, h3]
  · rw [wittDecomp_anisotropicEmbedding_inclY, ← hM, hY]

end GlobalTheory.MixModel.HypDec

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsOrthogonalComplementPreimageOfFixLine
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.AdBridge GlobalTheory.BesselChar

namespace GlobalTheory.LineFix

set_option maxHeartbeats 1000000 in

theorem exists_emb_of_fix_line : ∀ {D : D7} {S₀ A L : HSp D} (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E),
    IsLineVec L ζ → ∀ (b : GA D S₀), (mt S₀ b *ᵥ (fun k => incA D (vecB o ζ k)) = fun k => incA D (vecB o ζ k)) →
      ∃ a : GA D A, o.emb (a, 1) = b := by
  intro D S₀ A L o ζ hζ b hb
  have hv : (fun k => incA D (vecB o ζ k)) = o.jB *ᵥ (fun k => incA D (ζ k)) := by
    funext k
    exact RingHom.map_mulVec (incA D) o.iB ζ k
  have hr := hζ.1
  obtain ⟨k0, hk0⟩ : ∃ k0 : Fin L.rank, ∀ k, k = k0 :=
    ⟨⟨0, by omega⟩, fun k => Fin.ext (by have := k.2; simp only; omega)⟩
  have hz : ζ k0 ≠ 0 := by
    intro h0
    apply hζ.2
    have : ζ = 0 := funext fun k => by rw [hk0 k, h0]; rfl
    rw [this]; simp
  have hu : IsUnit (incA D (ζ k0)) := (isUnit_iff_ne_zero.2 hz).map (incA D)
  have h1 : mt S₀ b ⬝ o.jB = o.jB := by
    have e := hb
    rw [hv, Matrix.mulVec_mulVec] at e
    funext i k
    rw [hk0 k]
    have ei := congrFun e i
    simp only [Matrix.mulVec, dotProduct] at ei
    rw [Fintype.sum_eq_single k0 (fun k hk => absurd (hk0 k) hk),
      Fintype.sum_eq_single k0 (fun k hk => absurd (hk0 k) hk)] at ei
    exact hu.mul_right_cancel ei
  have hu2 : GlobalTheory.MixModel.adj (mt S₀ b) * (gA S₀ * mt S₀ b) = gA S₀ := GlobalTheory.MixModel.mt_unitary S₀ b
  have h2' : GlobalTheory.MixModel.adj o.jB ⬝ (gA S₀ ⬝ (mt S₀ b ⬝ o.jA)) = 0 := by
    calc GlobalTheory.MixModel.adj o.jB ⬝ (gA S₀ ⬝ (mt S₀ b ⬝ o.jA))
        = GlobalTheory.MixModel.adj (mt S₀ b ⬝ o.jB) ⬝ (gA S₀ ⬝ (mt S₀ b ⬝ o.jA)) := by rw [h1]
      _ = GlobalTheory.MixModel.adj o.jB ⬝ (GlobalTheory.MixModel.adj (mt S₀ b) ⬝ (gA S₀ ⬝ (mt S₀ b ⬝ o.jA))) := by
          rw [GlobalTheory.MixModel.adj_mul, Matrix.mul_assoc]
      _ = 0 := by rw [GlobalTheory.MixModel.cancel₃ hu2, o.gram_BA]
  have h2 : o.pB ⬝ (mt S₀ b ⬝ o.jA) = 0 := by
    rw [o.pB_eq]; simp only [Matrix.mul_assoc]; rw [h2', Matrix.mul_zero]
  have h3 : mt S₀ b ⬝ o.jA = o.jA ⬝ (o.pA ⬝ (mt S₀ b ⬝ o.jA)) := by
    calc mt S₀ b ⬝ o.jA = (o.jA ⬝ o.pA + o.jB ⬝ o.pB) ⬝ (mt S₀ b ⬝ o.jA) := by rw [o.sum_eq_one, Matrix.one_mul]
      _ = o.jA ⬝ (o.pA ⬝ (mt S₀ b ⬝ o.jA)) := by
          rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc o.jB, h2, Matrix.mul_zero, add_zero]
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : Mx D A.rank A.rank, mt S₀ b ⬝ o.jA = o.jA ⬝ a₀ := ⟨_, h3⟩
  have h4 : GlobalTheory.MixModel.adj a₀ ⬝ (gA A ⬝ a₀) = gA A := by
    have e : GlobalTheory.MixModel.adj (mt S₀ b ⬝ o.jA) ⬝ (gA S₀ ⬝ (mt S₀ b ⬝ o.jA)) = gA A := by
      rw [GlobalTheory.MixModel.adj_mul, Matrix.mul_assoc, GlobalTheory.MixModel.cancel₃ hu2, o.gram_AA]
    rw [ha₀, GlobalTheory.MixModel.adj_mul, Matrix.mul_assoc, GlobalTheory.MixModel.cancel₃ o.gram_AA] at e
    exact e
  have e3 : mt S₀ b ⬝ o.jA ⬝ o.pA + mt S₀ b ⬝ o.jB ⬝ o.pB = mt S₀ b ⬝ (o.jA ⬝ o.pA + o.jB ⬝ o.pB) := by
    rw [Matrix.mul_add, Matrix.mul_assoc, Matrix.mul_assoc]
  have e4 : mt S₀ b ⬝ (o.jA ⬝ o.pA + o.jB ⬝ o.pB) = mt S₀ b := by
    rw [o.sum_eq_one]; exact Matrix.mul_one _
  refine ⟨GlobalTheory.MixModel.ofMat A a₀ h4, GlobalTheory.MixModel.mt_injective S₀ ?_⟩
  have e1 : mt S₀ (o.emb (GlobalTheory.MixModel.ofMat A a₀ h4, 1)) = o.jA ⬝ a₀ ⬝ o.pA + o.jB ⬝ o.pB := by
    rw [OrthDec.mt_emb, GlobalTheory.MixModel.mt_ofMat, GlobalTheory.MixModel.mt_one, Matrix.mul_one]
  have e2 : o.jA ⬝ a₀ ⬝ o.pA + o.jB ⬝ o.pB = mt S₀ b ⬝ o.jA ⬝ o.pA + mt S₀ b ⬝ o.jB ⬝ o.pB := by
    rw [← ha₀, h1]
  rw [e1, e2, e3, e4]

end GlobalTheory.LineFix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRationalAdelicPointOfUnitaryBaseSpaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rationalAdelicPoint_of_unitary_baseSpace : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ γ : GL (Fin (D.R.N 0)) D.host.E, γ ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) → ∃ a : GA D (D.sp.X 0), a ∈ GQ (D.sp.X 0) ∧ GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a = (Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ).1 ∧ ∀ τ, GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a τ = Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) (γ : Matrix _ _ _) τ := by
  first | exact @GlobalTheory.Core.Mi.exists_GQ_of_unitary0 | exact GlobalTheory.Core.Mi.exists_GQ_of_unitary0 | (intros; apply GlobalTheory.Core.Mi.exists_GQ_of_unitary0 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRationalRepLevelDecompositionFiniteUnitaryStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rationalRepLevelDecomposition_finiteUnitary : ∀ (D : D7) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (g : GA D (D.sp.X 0)), ∃ p, GlobalTheory.AdForm.IsDec F.cls0.lev F.cls0.y (GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) g) p := by
  first | exact @GlobalTheory.Core.Mi.exists_isDec_finM | exact GlobalTheory.Core.Mi.exists_isDec_finM | (intros; apply GlobalTheory.Core.Mi.exists_isDec_finM <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerBlockParameterTransferInvariantPairingStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowerBlockParameter_transfer_invariantPairing : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D D' : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ t : ℕ, Fintype.card D' = Fintype.card D + t → ∀ (ξ μS μT : kˣ →* ℂˣ), IsTame ξ → IsUnram (μS * ξ⁻¹) → IsUnram (μT * ξ⁻¹) → ∀ (W : Submodule ℂ (Matrix (A ⊕ D') (A ⊕ D) k → ℂ)) (hW : ∀ g h, ∀ u ∈ W, omTwo μS μT g h u ∈ W) (hΦ : datum ξ⁻¹ ∈ W) (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (GL (A ⊕ D) k) X) (x : X) (B : Multiset ℂˣ), IsGen ρ ξ ϖ B x → ∀ (X' : Type) [AddCommGroup X'] [Module ℂ X'] (ρ' : Representation ℂ (GL (A ⊕ D') k) X') (b : W →ₗ[ℂ] X →ₗ[ℂ] X'), (∀ g h (u : W) y, b ⟨omTwo μS μT g h u, hW g h u u.2⟩ (ρ g y) = ρ' h (b u y)) → IsGen ρ' ξ ϖ (B.map (· * (μS ϖ * (μT ϖ)⁻¹)) + segL ϖ (μS ϖ) t) (b ⟨datum ξ⁻¹, hΦ⟩ x) := by
  first | exact @GlobalTheory.ParHeckeTransfer.transfer | exact GlobalTheory.ParHeckeTransfer.transfer | (intros; apply GlobalTheory.ParHeckeTransfer.transfer <;> assumption)
end

