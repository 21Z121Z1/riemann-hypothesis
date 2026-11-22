import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0199
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0186
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0553
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumTransportSourceRationalIsometry
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0106
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsLatInd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0155
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0304
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0323
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0256
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0201
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0367
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0234
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0222
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0109
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HasConductorMulShift
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0555
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapHandedFunctionVanishingPeriodInvariant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MixModel MeasureTheory Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 200000

namespace GlobalTheory.FlatRInv

variable {D : D7}

theorem addChar_ne_zero {A : Type} [AddGroup A] (ψ : AddChar A ℂ) (a : A) : ψ a ≠ 0 := by
  intro h
  have := ψ.map_add_eq_mul a (-a)
  rw [add_neg_cancel, ψ.map_zero_eq_one, h, zero_mul] at this
  exact one_ne_zero this

theorem mem_congGrp_iff (V : HSp D) (I : Ideal (AE D)) (g : GA D V) :
    g ∈ congGrp V I ↔ (mt V g).map (Ideal.Quotient.mk I) = 1 := by
  unfold congGrp
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Units.ext_iff]
  rfl

theorem unitaryMatrix_wittCoreEmbedding {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (h : GA D S₀) :
    mt S (d.emb0 h) = d.jX ⬝ d.pX + d.j0 ⬝ mt S₀ h ⬝ d.p0 + d.jY ⬝ d.pY := by
  conv_lhs => rw [← Matrix.mul_one (mt S (d.emb0 h)), ← d.sum_eq_one]
  simp only [Matrix.mul_add, ← Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclX, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, d.wittDecomp_anisotropicEmbedding_inclY]

theorem wittCoreEmbedding_preserves_supportedUnitarySubgroup {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (P : Pl D → Prop) {h : GA D S₀}
    (hh : h ∈ grpAt S₀ P) : d.emb0 h ∈ grpAt S P := by
  rw [grpAt, mem_congGrp_iff] at hh ⊢
  have key : (mt S (d.emb0 h)).map (Ideal.Quotient.mk (idAt D P)) =
      (d.jX ⬝ d.pX + d.j0 ⬝ d.p0 + d.jY ⬝ d.pY).map (Ideal.Quotient.mk (idAt D P)) := by
    have hadd : ∀ A B : Matrix (Fin S.rank) (Fin S.rank) (AE D), (A + B).map (Ideal.Quotient.mk (idAt D P)) =
        A.map (Ideal.Quotient.mk (idAt D P)) + B.map (Ideal.Quotient.mk (idAt D P)) :=
      fun A B => Matrix.map_add _ (Ideal.Quotient.mk (idAt D P)).map_add A B
    rw [unitaryMatrix_wittCoreEmbedding]; simp only [hadd, Matrix.map_mul, hh, Matrix.mul_one]
  rw [key, d.sum_eq_one]; exact Matrix.map_one _ (Ideal.Quotient.mk (idAt D P)).map_zero (Ideal.Quotient.mk (idAt D P)).map_one

theorem comp_mem_grpAt {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (P : Pl D → Prop) {n : GA D S}
    (hn : n ∈ flagN d) {h : GA D S₀} (hr : n * d.emb0 h ∈ grpAt S P) : h ∈ grpAt S₀ P := by
  rw [grpAt, mem_congGrp_iff] at hr ⊢
  rw [← GlobalTheory.BesClosed.witt_anisotropic_block_flag_mul_embedded d hn h]
  simp only [Matrix.map_mul, hr, Matrix.one_mul]
  rw [← Matrix.map_mul, d.p0_j0]; exact Matrix.map_one _ (Ideal.Quotient.mk (idAt D P)).map_zero (Ideal.Quotient.mk (idAt D P)).map_one

theorem jac_decomp {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (P : Pl D → Prop) {r : GA D S}
    (hr : r ∈ jacGrp d) (hP : r ∈ grpAt S P) :
    ∃ n ∈ flagN d, n ∈ grpAt S P ∧ ∃ h ∈ grpAt S₀ P, r = n * d.emb0 h := by
  obtain ⟨n, hn, h, rfl⟩ := (GlobalTheory.MixPer.Decomp.mem_jacGrp_iff d).1 hr
  have hh := comp_mem_grpAt d P hn hP
  refine ⟨n, hn, ?_, h, hh, rfl⟩
  have e : n = n * d.emb0 h * (d.emb0 h)⁻¹ := by group
  rw [e]; exact mul_mem hP (inv_mem (wittCoreEmbedding_preserves_supportedUnitarySubgroup d P hh))

theorem heisO_eq_zero_iff (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w₀ : WO S T) (F : WO S T → ℂ) :
    heisO ψ S T w₀ F = 0 ↔ F = 0 := by
  constructor
  · intro h; funext w
    have := congrFun h (w - w₀)
    simp only [heisO, Pi.zero_apply, sub_add_cancel] at this
    exact (mul_eq_zero.1 this).resolve_left (addChar_ne_zero ψ _)
  · rintro rfl; funext w; simp [heisO]

theorem om_eq_zero_iff {S T : HSp D} (om : Om S T) (g : GA D S × GA D T) (F : WO S T → ℂ) :
    om g F = 0 ↔ F = 0 := by
  constructor
  · intro h0
    have e : om g⁻¹ (om g F) = F := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [← e, h0, map_zero]
  · rintro rfl; exact map_zero _

theorem orth_comp_mem {S₀ A L : HSp D} (o : OrthDec S₀ A L) (P : Pl D → Prop) {h : GA D A}
    (hh : o.emb (h, 1) ∈ grpAt S₀ P) : h ∈ grpAt A P := by
  rw [grpAt, mem_congGrp_iff] at hh ⊢
  have e : mt A h = o.pA ⬝ mt S₀ (o.emb (h, 1)) ⬝ o.jA := by
    rw [o.pA_emb, Matrix.mul_assoc, o.pA_jA, Matrix.mul_one]
  rw [e, Matrix.map_mul, Matrix.map_mul, hh, Matrix.mul_one, ← Matrix.map_mul, o.pA_jA]
  exact Matrix.map_one _ (Ideal.Quotient.mk (idAt D P)).map_zero (Ideal.Quotient.mk (idAt D P)).map_one

theorem bes_decomp {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) (P : Pl D → Prop)
    {r : GA D S} (hr : r ∈ besGrp d o) (hP : r ∈ grpAt S P) :
    ∃ n ∈ flagN d, n ∈ grpAt S P ∧ ∃ h ∈ grpAt A P, r = n * embA d o h := by
  obtain ⟨n, hn, h, rfl⟩ := (GlobalTheory.CharLaws.mem_besGrp d o r).1 hr
  have hP' : n * d.emb0 (o.emb (h, 1)) ∈ grpAt S P := by rwa [embA_apply] at hP
  have h0 := comp_mem_grpAt d P hn hP'
  refine ⟨n, hn, ?_, h, orth_comp_mem o P h0, rfl⟩
  have e : n = n * embA d o h * (embA d o h)⁻¹ := by group
  rw [e]; exact mul_mem hP (inv_mem (wittCoreEmbedding_preserves_supportedUnitarySubgroup d P h0))

theorem opA_eq_zero_iff (ψ : AddChar (AF D.host.F) ℂ) {W W₀ V₀ A L : HSp D} {ρ : ℕ} (dW : HypDec W W₀ ρ)
    (o : OrthDec V₀ A L) (ζ : Fin L.rank → D.host.E) (om : Om V₀ W₀) (n : GA D W) (h : GA D W₀)
    (Ξ : WO V₀ W₀ → ℂ) : opA ψ dW o ζ om n h Ξ = 0 ↔ Ξ = 0 := by
  unfold opA jacT
  rw [smul_eq_zero_iff_right (addChar_ne_zero ψ _), heisO_eq_zero_iff, om_eq_zero_iff]

theorem handFB_smul_om_at {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {J : JacLev D (σ + 1)} {B : BesLev D σ}
    (s : StepFB ψ J B) (vL : VolM D B.L.rank J.W₀.rank) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (Ξ : WO J.W₀ B.V₀ → ℂ)
    (c : ℂ) (h₁ g : GA D B.A) :
    handFB s vL Y (c • s.om₀ (1, B.o.emb (h₁, 1)) Ξ) g = c * handFB s vL Y Ξ (g * h₁) := by
  unfold handFB
  rw [← integral_const_mul]
  congr 1
  funext h₀
  have e : s.om₀ (h₀, B.o.emb (g, 1)) (c • s.om₀ (1, B.o.emb (h₁, 1)) Ξ) = c • s.om₀ (h₀, B.o.emb (g * h₁, 1)) Ξ := by
    rw [map_smul, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, ← map_mul, Prod.mk_mul_mk]
    simp only [mul_one]
  unfold pairKer
  rw [e]
  simp only [contractT, thPair, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  funext w
  ring

theorem vanish_invariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (P : Pl D → Prop), (∀ (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (f : WO B.V J.W → ℂ), IsThetaFunO ψ B.V J.W f → ∀ r ∈ jacGrp J.d, r ∈ grpAt J.W P → (flatBF s (s.om (1, r) f) = 0 ↔ flatBF s f = 0)) ∧ ∀ (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B) (vL : VolM D B.L.rank J.W₀.rank) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (f : WO J.W B.V → ℂ), IsThetaFunO ψ J.W B.V f → ∀ r ∈ besGrp B.d B.o, r ∈ grpAt B.V P → (handFB s vL Y (flatFB s (s.om (1, r) f)) = 0 ↔ handFB s vL Y (flatFB s f) = 0) := by
  intro D ψ P
  have hL := GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D ψ P
  refine ⟨fun ρ B J s f hf r hr hrP => ?_, fun σ J B s vL Y f hf r hr hrP => ?_⟩
  · obtain ⟨n, hn, hnP, h, hh, rfl⟩ := jac_decomp J.d P hr hrP
    rw [(hL.1 ρ B J s).equiv f hf n hn hnP h hh]
    have hc : star (psiFlag ψ J.d n) ≠ 0 := star_ne_zero.2 (by unfold psiFlag psiE; exact addChar_ne_zero ψ _)
    rw [smul_eq_zero_iff_right hc, opA_eq_zero_iff]
  · obtain ⟨n, hn, hnP, h, hh, rfl⟩ := bes_decomp B.d B.o P hr hrP
    rw [(hL.2 σ J B s).equiv f hf n hn hnP h hh]
    have hc : star (psiBes ψ B.d 1 (vecB B.o B.ζ) n) ≠ 0 :=
      star_ne_zero.2 (by unfold psiBes psiE; exact addChar_ne_zero ψ _)
    constructor
    · intro h0; funext g
      have := congrFun h0 (g * h⁻¹)
      rw [handFB_smul_om_at, inv_mul_cancel_right, Pi.zero_apply] at this
      exact (mul_eq_zero.1 this).resolve_left hc
    · intro h0; funext g
      rw [handFB_smul_om_at, h0, Pi.zero_apply, Pi.zero_apply, mul_zero]

end GlobalTheory.FlatRInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapPreservesVacuumProof
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.FlatVacuum

variable {D : D7}

theorem mulVec_mem_ideal {m n : ℕ} (I : Ideal (AE D)) (M : Matrix (Fin m) (Fin n) (AE D)) {y : Fin n → AE D}
    (hy : ∀ i, y i ∈ I) (i : Fin m) : (M *ᵥ y) i ∈ I := by
  show ∑ j, M i j * y j ∈ I
  exact I.sum_mem fun j _ => I.mul_mem_left _ (hy j)

theorem mulVec_latV_of_local {S S' : HSp D} {L : Lat S} {L' : Lat S'} (hL : Submodule.IsLattice D.host.E L)
    (hL' : Submodule.IsLattice D.host.E L') {P : Pl D → Prop} (M : Matrix (Fin S'.rank) (Fin S.rank) (AE D))
    (h : ∀ v, P v → ∀ y ∈ latV S L (· = v), M *ᵥ y ∈ latV S' L' (· = v)) {y : Fin S.rank → AE D}
    (hy : y ∈ latV S L P) : M *ᵥ y ∈ latV S' L' P := by
  obtain ⟨h1, h2⟩ := (((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D P).2 S).2.2.2 L y hL).1 hy
  refine (((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D P).2 S').2.2.2 L' _ hL').2 ⟨mulVec_mem_ideal _ M h1, fun v hv e he => ?_⟩
  rw [← Matrix.mulVec_smul]
  exact h v hv _ (h2 v hv e he)

theorem smul_mem_latA {S : HSp D} {L : Lat S} {P : Pl D → Prop} {a : D.host.E} (ha : a ∈ D.host.AA)
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L P) :
    ((1 : AF D.host.F) ⊗ₜ[D.host.F] a : AE D) • y ∈ latA S L P := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, c, hc, x, hx, rfl⟩ := hz
    rw [Set.mem_singleton_iff] at hc
    subst hc
    refine AddSubgroup.subset_closure ⟨β, hβi, hβ, a, ha, x, hx, ?_⟩
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [smul_add]; exact add_mem hz hz'
  | neg z _ hz => rw [smul_neg]; exact neg_mem hz

theorem mulVec_latA {S S' : HSp D} {L : Lat S} {L' : Lat S'} {P : Pl D → Prop}
    (M : Matrix (Fin S'.rank) (Fin S.rank) (AE D)) (h : ∀ y ∈ latV S L P, M *ᵥ y ∈ latV S' L' P)
    {y : Fin S.rank → AE D} (hy : y ∈ latA S L P) : M *ᵥ y ∈ latA S' L' P := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, a, ha, x, hx, rfl⟩ := hz
    have e : (fun i => (pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x i) : AE D)) =
        ((1 : AF D.host.F) ⊗ₜ[D.host.F] a : AE D) • fun i => (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i) : AE D) := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [e, Matrix.mulVec_smul]
    exact smul_mem_latA ha (h _ (AddSubgroup.subset_closure ⟨β, hβi, hβ, 1, rfl, x, hx, rfl⟩))
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
  | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz

section Mono

variable {S S₀ : HSp D} {ρ : ℕ} {d : HypDec S S₀ ρ} {L : Lat S} {L₀ : Lat S₀}

theorem p0_mem {v : Pl D} (h : MonoAt d L L₀ v) {y : Fin S.rank → AE D} (hy : y ∈ latV S L (· = v)) :
    d.p0 *ᵥ y ∈ latV S₀ L₀ (· = v) := ((h y).1 hy).2.2

theorem wittCoreInclusion_mulVec_mem_latticeCompletionAtPlace {v : Pl D} (h : MonoAt d L L₀ v) {y : Fin S₀.rank → AE D} (hy : y ∈ latV S₀ L₀ (· = v)) :
    d.j0 *ᵥ y ∈ latV S L (· = v) := by
  have hX : d.pX *ᵥ (d.j0 *ᵥ y) = 0 := by
    rw [Matrix.mulVec_mulVec]; exact (congrArg (· *ᵥ y) d.pX_j0).trans (Matrix.zero_mulVec _)
  have hY : d.pY *ᵥ (d.j0 *ᵥ y) = 0 := by
    rw [Matrix.mulVec_mulVec]; exact (congrArg (· *ᵥ y) d.pY_j0).trans (Matrix.zero_mulVec _)
  have h0 : d.p0 *ᵥ (d.j0 *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec]; exact (congrArg (· *ᵥ y) d.p0_j0).trans (Matrix.one_mulVec _)
  have hc : ∀ (x : Mx D S.rank ρ) i, colMul x i 0 = 0 := fun x i => funext fun k => zero_mul _
  refine (h _).2 ⟨fun i => ?_, fun i => ?_, ?_⟩
  · rw [hX, Pi.zero_apply, hc]; exact zero_mem _
  · rw [hY, Pi.zero_apply, hc]; exact zero_mem _
  · rw [h0]; exact hy

theorem wittExtendByZero_mem_completedHomLattice {T : HSp D} {LT : Lat T} {P : Pl D → Prop} (hL : IsSelfDualC S L) (hL₀ : IsSelfDualC S₀ L₀)
    (hT : IsSelfDualC T LT) (h : ∀ v, P v → MonoAt d L L₀ v) {w : WO S₀ T}
    (hw : w ∈ latO S₀ T (L₀ : Set _) (LT : Set _) P) : d.ext0 T w ∈ latO S T (L : Set _) (LT : Set _) P := by
  obtain ⟨h1, h2⟩ := (LatMem.mem_latO_iff D S₀ T L₀ LT hL₀ hT P w).1 hw
  refine (LatMem.mem_latO_iff D S T L LT hL hT P _).2 ⟨fun i j => ?_, fun y hy => ?_⟩
  · show ∑ k, w i k * d.p0 k j ∈ idAt D P
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (h1 i k)
  · have := h2 _ (mulVec_latV_of_local hL.1 hL₀.1 d.p0 (fun v hv z hz => p0_mem (h v hv) hz) hy)
    rw [Matrix.mulVec_mulVec] at this
    exact this

theorem wittCoreInclusion_mem_completedHomLattice {T : HSp D} {LT : Lat T} {P : Pl D → Prop} (hL : IsSelfDualC S L) (hL₀ : IsSelfDualC S₀ L₀)
    (hT : IsSelfDualC T LT) (h : ∀ v, P v → MonoAt d L L₀ v) {w : WO T S₀}
    (hw : w ∈ latO T S₀ (LT : Set _) (L₀ : Set _) P) : d.inc0 T w ∈ latO T S (LT : Set _) (L : Set _) P := by
  obtain ⟨h1, h2⟩ := (LatMem.mem_latO_iff D T S₀ LT L₀ hT hL₀ P w).1 hw
  refine (LatMem.mem_latO_iff D T S LT L hT hL P _).2 ⟨fun i j => ?_, fun y hy => ?_⟩
  · show ∑ k, d.j0 i k * w k j ∈ idAt D P
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (h1 k j)
  · have := mulVec_latA d.j0
      (fun z hz => mulVec_latV_of_local hL₀.1 hL.1 d.j0 (fun v hv z hz => wittCoreInclusion_mulVec_mem_latticeCompletionAtPlace (h v hv) hz) hz) (h2 y hy)
    rw [Matrix.mulVec_mulVec] at this
    exact this

theorem isHalf_wittExtendByZero {T : HSp D} {e : AE D} {w : WO S₀ T} (hw : IsHalf e w) : IsHalf e (d.ext0 T w) :=
  fun i j => GlobalTheory.WeilSrc.entries_fix_right e hw d.p0 i j

theorem isHalf_wittCoreInclusion {T : HSp D} {e : AE D} {w : WO T S₀} (hw : IsHalf e w) : IsHalf e (d.inc0 T w) := by
  intro i j
  show e * (∑ k, d.j0 i k * w k j) = ∑ k, d.j0 i k * w k j
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_left_comm, hw k j]

end Mono

theorem isLatVac_of_intertwine {m n m' n' : ℕ} {hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ)}
    {hs' : Mx D m' n' → (Mx D m' n' → ℂ) → (Mx D m' n' → ℂ)} {Λ : AddSubgroup (Mx D m n)} {Λ' : AddSubgroup (Mx D m' n')}
    (ι : Mx D m' n' →+ Mx D m n) (hΛ : ∀ u ∈ Λ', ι u ∈ Λ) (hh : ∀ e u, IsHalf e u → IsHalf e (ι u))
    (𝔉 : (Mx D m n → ℂ) → (Mx D m' n' → ℂ)) {f : Mx D m n → ℂ} (hF : ∀ u ∈ Λ', 𝔉 (hs (ι u) f) = hs' u (𝔉 f))
    (hf : IsLatVac hs Λ f) : IsLatVac hs' Λ' (𝔉 f) := by
  refine ⟨fun u hu => ?_, fun e he u hu hue => ?_⟩
  · rw [← hF _ (Λ'.nsmul_mem hu 2), map_nsmul, hf.1 _ (hΛ u hu)]
  · rw [← hF _ hu, hf.2 e he _ (hΛ u hu) (hh e u hue)]

theorem latO_empty {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {P : Pl D → Prop} (hP : ∀ v, ¬ P v) {u : WO S T} (hu : u ∈ latO S T LS LT P) : u = 0 := by
  ext i j
  have h1 := LatMem.mul_indP (LatMem.latO_mxAt hu i j)
  have h2 : LatMem.indP D.host.F P = 0 := by
    classical
    refine Subtype.ext (funext fun v => ?_)
    exact if_neg (hP v)
  have h3 : pairA D.host.F 0 (0 : Af D.host.F) = 0 := rfl
  rw [h2, h3, TensorProduct.zero_tmul, mul_zero] at h1
  exact h1.symm

theorem vac_of_heisLaws {ψ : AddChar (AF D.host.F) ℂ} {V V₀ W W₀ : HSp D} {ρ σ : ℕ} {dV : HypDec V V₀ ρ}
    {dW : HypDec W W₀ σ} {x : Mx D W.rank ρ} {y : Mx D V₀.rank σ} {P : Pl D → Prop}
    {𝔉 : (WO V W → ℂ) → (WO V₀ W₀ → ℂ)} (H : HeisLaws ψ dV dW x y P 𝔉) {LV : Lat V} {LV₀ : Lat V₀} {LW : Lat W}
    {LW₀ : Lat W₀}
    (h : ∀ v, P v → IsSelfDualC V LV ∧ IsSelfDualC V₀ LV₀ ∧ IsSelfDualC W LW ∧ IsSelfDualC W₀ LW₀ ∧
      MonoAt dV LV LV₀ v ∧ MonoAt dW LW LW₀ v) {Φ : WO V W → ℂ} (hΦ : Vac ψ V W LV LW P Φ) :
    Vac ψ V₀ W₀ LV₀ LW₀ P (𝔉 Φ) := by
  refine ⟨H.theta Φ hΦ.1, isLatVac_of_intertwine ((dV.ext0 W).comp (dW.inc0 V₀)) (fun u hu => ?_)
    (fun e u hu => isHalf_wittExtendByZero (isHalf_wittCoreInclusion hu)) 𝔉 (fun u hu => H.core Φ hΦ.1 u (LatMem.latO_mxAt hu)) hΦ.2⟩
  by_cases hP : ∃ v, P v
  · obtain ⟨v, hv⟩ := hP
    obtain ⟨a, b, c, e, -⟩ := h v hv
    exact wittExtendByZero_mem_completedHomLattice a b c (fun v hv => (h v hv).2.2.2.2.1) (wittCoreInclusion_mem_completedHomLattice c e b (fun v hv => (h v hv).2.2.2.2.2) hu)
  · rw [latO_empty (not_exists.1 hP) hu, map_zero]
    exact zero_mem _

theorem flatVac : ∀ D : D7, GlobalTheory.FinPl.FlatVac D := by
  intro D ψ P
  refine ⟨fun ρ B J s LV LV₀ LW LW₀ h Φ hΦ => ?_, fun σ J B s LV LV₀ LW LW₀ h Φ hΦ => ?_,
    fun V V₀ T d L L₀ LT hL hL₀ hT h Φ hΦ => ?_⟩
  · exact vac_of_heisLaws ((GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D ψ P).1 ρ B J s).Heisenberg₂
      (fun v hv => ⟨(h v hv).sdV, (h v hv).sdV₀, (h v hv).sdW, (h v hv).sdW₀, (h v hv).monoV, (h v hv).monoW⟩) hΦ
  · exact vac_of_heisLaws ((GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D ψ P).2 σ J B s).Heisenberg₂
      (fun v hv => ⟨(h v hv).sdV, (h v hv).sdV₀, (h v hv).sdW, (h v hv).sdW₀, (h v hv).monoV, (h v hv).monoW⟩) hΦ
  · exact ⟨(GlobalTheory.WeilSrc.Zero.theta_iff d Φ).2 hΦ.1, isLatVac_of_intertwine (d.ext0 T)
      (fun u hu => wittExtendByZero_mem_completedHomLattice hL hL₀ hT h hu) (fun e u hu => isHalf_wittExtendByZero hu) (fun f w => f (d.ext0 T w))
      (fun u _ => GlobalTheory.WeilSrc.Zero.heisO_eqv d u Φ) hΦ.2⟩

end GlobalTheory.FinPl.FlatVacuum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FoldrSplitPlaceSecondCombinationsVacuumNeZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

noncomputable section
namespace GlobalTheory.VacComb

variable {D : D7}

theorem isThetaFunO_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : IsThetaFunO ψ S T 0 where
  quasi _ _ := by simp
  level := ⟨⊤, isOpen_univ, fun _ _ _ => funext fun _ => by simp [heisO]⟩
  cont := continuous_const
  smooth _ _ _ _ _ := by simpa using (contDiff_const : ContDiff ℝ _ fun _ : Fin _ → ℝ => (0 : ℂ))

theorem heisO_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (u : WO S T) : heisO ψ S T u 0 = 0 :=
  funext fun _ => by simp [heisO]

theorem isModel_zero {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y']
    [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) :
    p.IsModel ψ FS FT (0 : SB (Matrix Y Y' k) →ₗ[ℂ] (WO S T → ℂ)) where
  theta _ := isThetaFunO_zero ψ S T
  trans _ _ _ _ := by simp [heisO_zero]
  modul _ _ _ _ _ := by simp [heisO_zero]

theorem model_ne_zero {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {Y Y' : Type} [Fintype Y]
    [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {FS : Frame k S.rank Y'} {FT : Frame k T.rank Y} {Tm}
    (hTm : p.IsModel ψ FS FT Tm) {Φ₀ : SB (Matrix Y Y' k)} (h₀ : Tm Φ₀ ≠ 0) {O : SB (Matrix Y Y' k)} (hO : O ≠ 0) :
    Tm O ≠ 0 := by
  intro h
  have := (GlobalTheory.T.localSchrodingerModel_uniq_transport_exists D k p Y Y' S T FS FT ψ hψ).1 Tm 0 hTm (isModel_zero p ψ FS FT) O hO (by simpa using h)
  exact h₀ (by rw [this]; rfl)

end GlobalTheory.VacComb

namespace GlobalTheory.VacComb

theorem exists_adapted_frame : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) (M : GlobalTheory.FinPl.Lat S), IsSelfDualC S M → ∀ (Y : Type) [Fintype Y] [DecidableEq Y] (F : Frame k S.rank Y), ∃ G : Frame k S.rank Y, ∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((G.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV S M (· = q.v) := by
  intro D k _ _ _ _ q S M hM Y _ _ F
  obtain ⟨gl, h1, h2⟩ := GlobalTheory.T.exists_GL_embedding_unitaryAdelic_splitPlace_basis D k q S Y F.β F.γ F.βγ F.γβ
  let α : GlobalTheory.FinPl.Frame q S Y := ⟨F.β, F.γ, F.βγ, F.γβ, gl, h1, h2⟩
  obtain ⟨Λ, hΛ, hα, -⟩ := GlobalTheory.FinPl.FrameLat.exists_lat D k q S Y α M hM
  haveI := hΛ
  obtain ⟨g, hg⟩ := GlobalTheory.LatPair.exists_smul_lat (GlobalTheory.LatPair.stdLat k Y) Λ
  have hgg : g.1 * (g⁻¹).1 = 1 := by rw [← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one]
  have hgg' : (g⁻¹).1 * g.1 = 1 := by rw [← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one]
  refine ⟨⟨F.β * g.1, (g⁻¹).1 * F.γ, ?_, ?_⟩, fun y => ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc g.1, hgg, Matrix.one_mul, F.βγ]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc F.γ, F.γβ, Matrix.one_mul, hgg']
  · have e1 : (∀ i, y i ∈ 𝒪[k]) ↔ g • y ∈ Λ := by
      rw [← hg, GlobalTheory.LatPair.mem_smul_iff, inv_smul_smul, GlobalTheory.LatPair.mem_stdLat]
    rw [e1, hα (g • y)]
    show _ ∈ _ ↔ _ ∈ _
    have e2 : F.β *ᵥ (g • y) = (F.β * g.1) *ᵥ y := by
      rw [← Matrix.mulVec_mulVec]; rfl
    change (fun i => q.sec ((F.β *ᵥ (g • y)) i)) ∈ _ ↔ _
    rw [e2]

end GlobalTheory.VacComb

namespace GlobalTheory.VacComb

variable {D : D7}

theorem down_up {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {S T : HSp D} {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
    (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (x : Matrix Y Y' k) : p.down FS FT (p.up FS FT x) = x := by
  unfold Place.down Place.up
  have h : ((FT.β * x * FS.γ).map p.ι : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map p.π = FT.β * x * FS.γ := by
    ext i j; simp [p.π_ι]
  rw [h, Matrix.mul_assoc FT.β, ← Matrix.mul_assoc FT.γ, FT.γβ, Matrix.one_mul, Matrix.mul_assoc, FS.γβ, Matrix.mul_one]

theorem exists_model_vac : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k), q.UnitAA → ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (M : GlobalTheory.FinPl.Lat S) (M' : GlobalTheory.FinPl.Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ G, GlobalTheory.FinPl.Vac ψ S T M M' (· = q.v) G → ∃ Tm, (ofSplit q).IsModel ψ FS FT Tm ∧ ∀ Φ₀ : SB (Matrix Y Y' k), Φ₀.1 = Set.indicator {x | (ofSplit q).up FS FT x ∈ latO S T (M : Set (Fin S.rank → D.host.E)) (M' : Set (Fin T.rank → D.host.E)) (· = q.v)} (fun _ => 1) → Tm Φ₀ = G := by
  intro D k _ _ _ _ q hU Y Y' _ _ _ _ S T FS FT ψ hψ M M' hM hM' G hG
  obtain ⟨GS, hGS⟩ := exists_adapted_frame D k q S M hM Y' FS
  obtain ⟨GT, hGT⟩ := exists_adapted_frame D k q T M' hM' Y FT
  obtain ⟨ψk, hch, hcond⟩ := GlobalTheory.SplitWeilChar.weil_char_conductor_one D k q ψ hψ hU
  obtain ⟨Tm', hTm', hO'⟩ := (GlobalTheory.T.integralIndicator_gives_localVacuum_splitPlace D k q hU Y Y' S T GS GT ψ ψk hψ hch hcond M M' hM hM' hGS hGT).2 G hG
  obtain ⟨Tm, hTm, hrel⟩ := GlobalTheory.LocMod.Place.exists_isModel_chg D k (ofSplit q) Y Y' S T GS GT Y Y' FS FT ψ Tm' hTm'
  obtain ⟨O, hO, -⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := k) (Y := Y) (Y' := Y')
  refine ⟨Tm, hTm, fun Φ₀ h₀ => ?_⟩
  rw [hrel O Φ₀ ?_, hO' O hO]
  intro x
  have hup : (ofSplit q).up FS FT (FT.γ * GT.β * x * (GS.γ * FS.β)) = (ofSplit q).up GS GT x :=
    GlobalTheory.LocMod.Place.up_chg (ofSplit q) GS GT FS FT x
  rw [hO, h₀]
  by_cases hx : ∀ r s, x r s ∈ 𝒪[k]
  · rw [Set.indicator_of_mem (show x ∈ {x : Matrix Y Y' k | ∀ r s, x r s ∈ 𝒪[k]} from hx), Set.indicator_of_mem]
    show (ofSplit q).up FS FT (FT.γ * GT.β * x * (GS.γ * FS.β)) ∈ latO S T (M : Set (Fin S.rank → D.host.E)) (M' : Set (Fin T.rank → D.host.E)) (· = q.v)
    rw [hup]
    exact GlobalTheory.T.up_image_integral_matrix_mem_completed_hom_lattice D k q hU Y Y' S T GS GT M M' hM hM' hGS hGT x hx
  · rw [Set.indicator_of_notMem (show x ∉ {x : Matrix Y Y' k | ∀ r s, x r s ∈ 𝒪[k]} from hx), Set.indicator_of_notMem]
    intro hmem
    change (ofSplit q).up FS FT (FT.γ * GT.β * x * (GS.γ * FS.β)) ∈ latO S T (M : Set (Fin S.rank → D.host.E)) (M' : Set (Fin T.rank → D.host.E)) (· = q.v) at hmem
    rw [hup] at hmem
    obtain ⟨x', hx', he⟩ := GlobalTheory.T.exists_integral_matrix_up_image_completed_hom_lattice D k q hU Y Y' S T GS GT M M' hM hM' hGS hGT _ hmem
      (GlobalTheory.LocMod.Witness.up_half (ofSplit q) GS GT x)
    have : x = x' := by rw [← down_up (ofSplit q) GS GT x, he, down_up]
    exact hx (this ▸ hx')

end GlobalTheory.VacComb

namespace GlobalTheory.VacComb

variable {D : D7}

theorem comb_o_ne_zero {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {M : GlobalTheory.FinPl.Lat S} {M' : GlobalTheory.FinPl.Lat T} (hM : IsSelfDualC S M) (hM' : IsSelfDualC T M')
    (L : LocPl ψ S T M M') {G : WO S T → ℂ} (hG : GlobalTheory.FinPl.Vac ψ S T M M' (· = L.q.v) G) (hG0 : G ≠ 0) :
    comb ψ S T L.o G ≠ 0 := by
  obtain ⟨Tm, hTm, hTG⟩ := exists_model_vac D L.k L.q L.unit L.Y L.Y' S T L.FS L.FT ψ hψ M M' hM hM' G hG
  obtain ⟨Φ₀, h₀⟩ := GlobalTheory.SeeSaw.LocPlModel.exists_latInd L.q L.unit L.FS L.FT hM hM'
  obtain ⟨O, hO, hO0⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := L.k) (Y := L.Y) (Y' := L.Y')
  have hO' : O ≠ 0 := by rintro rfl; simp at hO0
  rw [← hTG Φ₀ h₀, ← L.o_is Tm hTm Φ₀ O hO h₀]
  exact model_ne_zero _ hψ hTm (by rwa [hTG Φ₀ h₀]) hO'

theorem combAt_o {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {M : GlobalTheory.FinPl.Lat S} {M' : GlobalTheory.FinPl.Lat T}
    (L : LocPl ψ S T M M') : GlobalTheory.FinPl.CombAt (· = L.q.v) L.o := fun u hu r c =>
  (GlobalTheory.FinPl.FrameLat.idem_iff L.q _).2 (L.o_at u hu r c)

theorem foldr_comb_ne_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (M : GlobalTheory.FinPl.Lat S) (M' : GlobalTheory.FinPl.Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ (n : ℕ) (L : Fin n → GlobalTheory.SeeSaw.LocPl ψ S T M M'), (Function.Injective fun i => (L i).q.v) → ∀ F, GlobalTheory.FinPl.Vac ψ S T M M' (fun _ => True) F → F ≠ 0 → (List.finRange n).foldr (fun i g => comb ψ S T (L i).o g) F ≠ 0 := by
  intro D ψ hψ S T M M' hM hM' n L hL F hF hF0
  have hI := fun P P' hd => GlobalTheory.T.heisenbergCombination_disjoint_places_commute_vacua D ψ hψ S T P P' hd
  let g : Fin n → (WO S T → ℂ) → (WO S T → ℂ) := fun i f => comb ψ S T (L i).o f
  have key : ∀ l : List (Fin n), l.Nodup → l.foldr g F ≠ 0 ∧
      ∀ j, j ∉ l → GlobalTheory.FinPl.Vac ψ S T M M' (· = (L j).q.v) (l.foldr g F) := by
    intro l
    induction l with
    | nil =>
      intro _
      exact ⟨hF0, fun j _ => GlobalTheory.GSuppComb.vac_mono (fun _ _ => trivial) hF⟩
    | cons a l ih =>
      intro hl
      obtain ⟨ha, hl'⟩ := List.nodup_cons.1 hl
      obtain ⟨h0, hv⟩ := ih hl'
      have hdisj : ∀ j, j ≠ a → ∀ p, p = (L a).q.v → ¬ p = (L j).q.v := fun j hj p hp hq =>
        hj (hL (hq.symm.trans hp))
      refine ⟨comb_o_ne_zero hψ hM hM' (L a) (hv a ha) h0, fun j hj => ?_⟩
      have hja : j ≠ a := fun h => hj (h ▸ List.mem_cons_self)
      have hjl : j ∉ l := fun h => hj (List.mem_cons_of_mem _ h)
      exact ((hI _ _ (hdisj j hja)).2.1 _ (combAt_o (L a))).2 M M' _ (hv j hjl)
  exact (key _ (List.nodup_finRange n)).1

end GlobalTheory.VacComb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrincipalCongruenceFixesDefiniteStepVectorStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalCongruence_fixes_definiteStepVector : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A H : HSp D) (χA : (AE D)ˣ →* Circle) (om : WRep A H) (sA : RealMat A) (sH : RealMat H), IsInfFam θ → (∃ η, GlobalTheory.WeilParts.IsEtaTilde D η) → IsWeilDatumO ψ A H χA 1 om → (∀ τ, IsCartanInv (gramAt D A τ) (sA τ)) → (∀ τ, IsCartanInv (gramAt D H τ) (sH τ)) → A.rank ≤ H.rank → ∀ (β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D)) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)), Places A β Z → ∀ (βH : GL (Fin H.rank) (Formalism.IndefR.Lev.EAf D)) (f₀ f : WO A H → ℂ), Formalism.L2.DIV.IsFrame βH (frameLat H) → IsStepVecOf ψ θ A H sA sH (frameLat A) (frameLat H) β βH (prinDat A Z) (fun _ => 1) ∅ (fun _ => 1) f₀ f → IsThetaFunO ψ A H f → ∀ κ ∈ prin A β Z, om (κ, 1) f = f := by
  first | exact @GlobalTheory.SmallFix.prin_fixes_stepVec | exact GlobalTheory.SmallFix.prin_fixes_stepVec | (intros; apply GlobalTheory.SmallFix.prin_fixes_stepVec <;> assumption)
end

