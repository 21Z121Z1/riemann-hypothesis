import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0176
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0178
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeAdelicVectorSizeProductMulUnitaryQuotientHeigh
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0144
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelsReadOnProductPrimeFieldGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactTypePrime
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalFactorRealPlaceEqHeisenbergIntegralBase
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0137
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0037

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFrameFrameChangeInverseGLMul
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open GlobalTheory.AdSpan.ReVec
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdSpan.ReVec

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem hatL_mulVec_mem (M : Matrix (Fin n) (Fin n) E) (Λ Λ' : Submodule (𝓞 E) (Fin n → E))
    (h : ∀ y ∈ Λ, M *ᵥ y ∈ Λ') (x : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) (hx : x ∈ Formalism.L2.Herm.hatL (F := F) Λ) :
    M.map (Algebra.TensorProduct.includeLeftRingHom : E →+* E ⊗[F] Formalism.L2.Herm.Af F) *ᵥ x ∈
      Formalism.L2.Herm.hatL (F := F) Λ' := by
  unfold Formalism.L2.Herm.hatL Formalism.UG.latS at *
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨z, hz, rfl⟩ := hy
    apply Submodule.subset_span
    refine ⟨M *ᵥ z, h z hz, ?_⟩
    funext i
    simp [Matrix.mulVec, dotProduct, Formalism.UG.inclE, map_sum]
  | zero => simp
  | add y z _ _ hy hz =>
    rw [Matrix.mulVec_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    rw [Subring.smul_def, Matrix.mulVec_smul]
    exact Submodule.smul_mem _ c hy

end General

theorem sum_smul_frame_frP {D : D7} (S : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V)
    (y : Fin S.rank → D.host.E) :
    ∑ i, y i • b i = ∑ j, (frP S b *ᵥ y) j • S.frame j := by
  simp only [frP, Matrix.mulVec, dotProduct, Module.Basis.toMatrix_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_lhs => rw [← S.frame.sum_repr (b i), Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul, mul_comm]

theorem mem_stdL_iff {D : D7} (S : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V)
    (hO : StdFrame.OrthFrame (reS S b)) (y : Fin S.rank → D.host.E) :
    y ∈ stdL D.host.E S.rank ↔ ∑ i, y i • b i ∈ S.L0 := by
  have hpi : (Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 D.host.E) D.host.E)) =
      stdL D.host.E S.rank := by
    apply le_antisymm
    · intro x hx
      rw [← Finset.univ_sum_single x]
      refine Submodule.sum_mem _ fun a _ => ?_
      obtain ⟨c, hc⟩ := Submodule.mem_one.1 (hx a trivial)
      have : (Pi.single a (x a) : Fin S.rank → D.host.E) = c • (Pi.single a 1 : Fin S.rank → D.host.E) := by
        rw [← Pi.single_smul, ← hc, Algebra.smul_def, mul_one]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨a, rfl⟩ j -
      by_cases h : j = a
      · subst h
        exact Submodule.mem_one.2 ⟨1, by simp⟩
      · simp [h]
  rw [← hpi, Submodule.mem_pi]
  exact (⟨fun k a => k a trivial, fun k a _ => k a⟩ : _ ↔ _).trans (hO.mem_iff (V := reS S b) y).symm

theorem isFrame_frPinvGL_mul : ∀ (D : D7) (S : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (βS : GL (Fin S.rank) (Lev.EAf D)) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)), StdFrame.OrthFrame (reS S b) → (ΛS : Set (Fin S.rank → D.host.E)) = L0c D S → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame (frPinvGL S b * βS) (stdL D.host.E (reS S b).rank) := by
  intro D S b βS ΛS hO hΛ hfr
  change Formalism.L2.DIV.IsFrame _ (stdL D.host.E S.rank)
  have hA : ∀ y ∈ stdL D.host.E S.rank, frP S b *ᵥ y ∈ ΛS := by
    intro y hy
    have h1 : frP S b *ᵥ y ∈ (ΛS : Set (Fin S.rank → D.host.E)) := by
      rw [hΛ]
      show ∑ j, (frP S b *ᵥ y) j • S.frame j ∈ S.L0
      rw [← sum_smul_frame_frP]
      exact (mem_stdL_iff S b hO y).1 hy
    exact h1
  have hB : ∀ y ∈ ΛS, frPinv S b *ᵥ y ∈ stdL D.host.E S.rank := by
    intro y hy
    rw [mem_stdL_iff S b hO, sum_smul_frame_frP, Matrix.mulVec_mulVec, frameMatrix_mul_frameMatrixInv, Matrix.one_mulVec]
    have h1 : y ∈ (ΛS : Set (Fin S.rank → D.host.E)) := hy
    rw [hΛ] at h1
    exact h1
  unfold Formalism.L2.DIV.IsFrame at hfr ⊢
  intro x
  have hinv : ((frPinvGL S b * βS)⁻¹ : GL (Fin S.rank) (Lev.EAf D)).val *ᵥ x =
      (βS⁻¹ : GL (Fin S.rank) (Lev.EAf D)).val *ᵥ ((frP S b).map (eToEAf D) *ᵥ x) := by
    rw [_root_.mul_inv_rev, Units.val_mul, frPinvGL_inv_val, Matrix.mulVec_mulVec]
  rw [hinv, ← hfr]
  constructor
  · intro hx
    exact hatL_mulVec_mem (frP S b) _ ΛS hA x hx
  · intro hx
    have h2 := hatL_mulVec_mem (F := D.host.F) (frPinv S b) ΛS _ hB _ hx
    have h3 : (frPinv S b).map (eToEAf D) *ᵥ ((frP S b).map (eToEAf D) *ᵥ x) = x := by
      rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, frPinv_mul_frP, Matrix.map_one _ (map_zero _) (map_one _),
        Matrix.one_mulVec]
    exact h3 ▸ h2

end GlobalTheory.AdSpan.ReVec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSmoothThetaFunctionReframeFunctionOnHoms
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open GlobalTheory.AdSpan.ReVec
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdSpan.ReVec.ThetaCarry

theorem continuous_reW {D : D7} (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) :
    Continuous (reW S T b : WO (reS S b) T → WO S T) := by
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  exact (continuous_id.matrix_mul continuous_const :
    Continuous fun x : Matrix (Fin T.rank) (Fin S.rank) (AE D) =>
      HMul.hMul (α := Matrix (Fin T.rank) (Fin S.rank) (AE D)) x ((frPinv S b).map (incA D)))

theorem reW_ratW {D : D7} (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V)
    (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    reW S T b (ratW T (reS S b) γ) = ratW T S (γ * frPinv S b) := by
  unfold reW ratW
  rw [Matrix.map_mul]
  rfl

theorem reW_map_inf {D : D7} (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) {u : WO (reS S b) T}
    (hu : u.map (infPart D) = 0) : (reW S T b u).map (infPart D) = 0 := by
  refine (Matrix.map_mul (L := (show Matrix (Fin T.rank) (Fin S.rank) (AE D) from u))
    (M := (frPinv S b).map (incA D)) (f := infPart D)).trans ?_
  rw [show (show Matrix (Fin T.rank) (Fin S.rank) (AE D) from u).map (infPart D) = 0 from hu, Matrix.zero_mul]

theorem reW_map_fin {D : D7} (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) {u : WO (reS S b) T}
    (hu : u.map (finPart D) = 0) : (reW S T b u).map (finPart D) = 0 := by
  refine (Matrix.map_mul (L := (show Matrix (Fin T.rank) (Fin S.rank) (AE D) from u))
    (M := (frPinv S b).map (incA D)) (f := finPart D)).trans ?_
  rw [show (show Matrix (Fin T.rank) (Fin S.rank) (AE D) from u).map (finPart D) = 0 from hu, Matrix.zero_mul]

theorem isThetaFunO_reF : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V), (∀ x y : WO (reS S b) T, symplO (reS S b) T x y = symplO S T (reW S T b x) (reW S T b y)) → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ (reS S b) T (reF S T b f) := by
  intro D ψ S T b hs f hf
  have hsH : ∀ x y : WO (reS S b) T, symplOH (reS S b) T x y = symplOH S T (reW S T b x) (reW S T b y) := by
    intro x y
    unfold symplOH
    rw [hs]
  have hc := continuous_reW S T b
  refine ⟨fun γ w => ?_, ?_, hf.cont.comp hc, fun k L h1 h2 w => ?_⟩
  · have e := reW_ratW S T b γ
    rw [reF_apply, reF_apply, reW_add, hsH]
    erw [e]
    exact hf.quasi _ _
  · obtain ⟨U, hU, h⟩ := hf.level
    refine ⟨U.comap (reWHom S T b), hU.preimage hc, fun u hu h0 => ?_⟩
    rw [heisO_reF S T b ψ hs u f, h (reW S T b u) hu (reW_map_inf S T b h0)]
  · have := hf.smooth k ((reWHom S T b).comp L) (hc.comp h1) (fun t => reW_map_fin S T b (h2 t)) (reW S T b w)
    simp only [reF_apply, reW_add]
    exact this

end GlobalTheory.AdSpan.ReVec.ThetaCarry

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaAtSplitPlaceReframe
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open GlobalTheory.AdSpan.ReVec
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaAtReframe

section
variable {D : D7} (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V)

noncomputable def reFi : (WO (reS S b) T → ℂ) →ₗ[ℂ] (WO S T → ℂ) := LinearMap.funLeft ℂ ℂ (reWi S T b)

theorem reWi_add (x y : WO S T) : reWi S T b (x + y) = reWi S T b x + reWi S T b y := by
  conv_lhs => rw [← reW_reWi S T b x, ← reW_reWi S T b y, ← reW_add, reWi_reW]

theorem reWi_nsmul (k : ℕ) (x : WO S T) : reWi S T b (k • x) = k • reWi S T b x := by
  conv_lhs => rw [← reW_reWi S T b x, ← reW_nsmul, reWi_reW]

theorem isHalf_reWi_iff (e : AE D) (x : WO S T) : IsHalf e (reWi S T b x) ↔ IsHalf e x := by
  have h := isHalf_reW_iff S T b e (reWi S T b x)
  rw [reW_reWi] at h
  exact h.symm

theorem reF_reFi (g : WO (reS S b) T → ℂ) : reF S T b (reFi S T b g) = g := by
  funext x
  simp only [reF, reFi, LinearMap.funLeft_apply, reWi_reW]

theorem reFi_reF (g : WO S T → ℂ) : reFi S T b (reF S T b g) = g := by
  funext x
  simp only [reF, reFi, LinearMap.funLeft_apply, reW_reWi]

theorem heisO_reFi (ψ : AddChar (AF D.host.F) ℂ)
    (hB : ∀ x y : WO (reS S b) T, symplO (reS S b) T x y = symplO S T (reW S T b x) (reW S T b y))
    (u : WO (reS S b) T) (g : WO (reS S b) T → ℂ) :
    reFi S T b (heisO ψ (reS S b) T u g) = heisO ψ S T (reW S T b u) (reFi S T b g) := by
  have h := heisO_reF S T b ψ hB u (reFi S T b g)
  rw [reF_reFi] at h
  rw [h, reFi_reF]

variable (e : AE D) (Λ : AddSubgroup (WO S T)) (Λ' : AddSubgroup (WO (reS S b) T))

theorem isSBHalf_comp_reW (hΛ : ∀ u, u ∈ Λ' ↔ reW S T b u ∈ Λ) (Φ : WO S T → ℂ)
    (h : IsSBHalf e Λ Φ) : IsSBHalf e Λ' (fun x => Φ (reW S T b x)) := by
  obtain ⟨h1, k, hk, h2, h3⟩ := h
  refine ⟨fun t ht => (isHalf_reW_iff S T b e t).1 (h1 _ ht), k, hk, ?_, ?_⟩
  · intro u hu hh t
    simp only [reW_add, reW_nsmul]
    exact h2 _ ((hΛ u).1 hu) ((isHalf_reW_iff S T b e u).2 hh) _
  · intro t ht
    rw [hΛ, reW_nsmul]
    exact h3 _ ht

theorem isSBHalf_comp_reWi (hΛ : ∀ u, u ∈ Λ' ↔ reW S T b u ∈ Λ) (Ψ : WO (reS S b) T → ℂ)
    (h : IsSBHalf e Λ' Ψ) : IsSBHalf e Λ (fun x => Ψ (reWi S T b x)) := by
  obtain ⟨h1, k, hk, h2, h3⟩ := h
  refine ⟨fun t ht => (isHalf_reWi_iff S T b e t).1 (h1 _ ht), k, hk, ?_, ?_⟩
  · intro u hu hh t
    simp only [reWi_add, reWi_nsmul]
    exact h2 _ ((hΛ _).2 (by rwa [reW_reWi])) ((isHalf_reWi_iff S T b e u).2 hh) _
  · intro t ht
    have h4 := (hΛ _).1 (h3 _ ht)
    rwa [reW_nsmul, reW_reWi] at h4

theorem reF_halfInd (hΛ : ∀ u, u ∈ Λ' ↔ reW S T b u ∈ Λ) :
    reF S T b (halfInd e Λ) = halfInd e Λ' := by
  funext x
  simp only [reF, LinearMap.funLeft_apply, halfInd, ← hΛ, isHalf_reW_iff]

theorem reFi_halfInd (hΛ : ∀ u, u ∈ Λ' ↔ reW S T b u ∈ Λ) :
    reFi S T b (halfInd e Λ') = halfInd e Λ := by
  rw [← reF_halfInd S T b e Λ Λ' hΛ, reFi_reF]

end

theorem isThetaAt_reframe : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (e : AE D) (Λ : AddSubgroup (WO S T)) (Λ' : AddSubgroup (WO (reS S b) T)) (c : ℂ) (f₀ Φ f : WO S T → ℂ), (∀ x y : WO (reS S b) T, symplO (reS S b) T x y = symplO S T (reW S T b x) (reW S T b y)) → (∀ u, u ∈ Λ' ↔ reW S T b u ∈ Λ) → IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Φ f → IsThetaAt ψ (symplO (reS S b) T) (heisO ψ (reS S b) T) e Λ' c (reF S T b f₀) (fun x => Φ (reW S T b x)) (reF S T b f) := by
  intro D ψ S T b e Λ Λ' c f₀ Φ f hB hΛ hθ
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hθ
  refine ⟨⟨(reF S T b) ∘ₗ Tm ∘ₗ reFi S T b, ?_⟩, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro Ψ hΨ x hx
      simp only [LinearMap.comp_apply]
      have h1 : reFi S T b (fun t => Ψ (t + x)) =
          fun s => (fun s' => Ψ (reWi S T b s')) (s + reW S T b x) := by
        funext s
        simp only [reFi, LinearMap.funLeft_apply, reWi_add, reWi_reW]
      rw [h1, hTm.trans _ (isSBHalf_comp_reWi S T b e Λ Λ' hΛ Ψ hΨ) _
        ((isHalf_reW_iff S T b e x).2 hx), ← heisO_reF S T b ψ hB]
      rfl
    · intro Ψ hΨ y hy
      simp only [LinearMap.comp_apply]
      have h1 : reFi S T b (fun t => ψ (symplO (reS S b) T t y) * Ψ t) =
          fun s => ψ (symplO S T s (reW S T b y)) * (fun s' => Ψ (reWi S T b s')) s := by
        funext s
        simp only [reFi, LinearMap.funLeft_apply, hB, reW_reWi]
      rw [h1, hTm.modul _ (isSBHalf_comp_reWi S T b e Λ Λ' hΛ Ψ hΨ) _
        ((isHalf_reW_iff S T b _ y).2 hy), ← heisO_reF S T b ψ hB]
      rfl
    · rw [LinearMap.comp_apply, LinearMap.comp_apply, map_smul (reFi S T b),
        reFi_halfInd S T b e Λ Λ' hΛ, hTm.vac]
  · intro Tm' hTm'
    let Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) := reFi S T b ∘ₗ Tm' ∘ₗ reF S T b
    have hPM : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Tm := by
      refine ⟨?_, ?_, ?_⟩
      · intro Φ hΦ x hx
        simp only [Tm, LinearMap.comp_apply]
        have h1 : reF S T b (fun t => Φ (t + x)) =
            fun s => (fun s' => Φ (reW S T b s')) (s + reWi S T b x) := by
          funext s
          simp only [reF, LinearMap.funLeft_apply, reW_add, reW_reWi]
        rw [h1, hTm'.trans _ (isSBHalf_comp_reW S T b e Λ Λ' hΛ Φ hΦ) _
          ((isHalf_reWi_iff S T b e x).2 hx), heisO_reFi S T b ψ hB, reW_reWi]
        rfl
      · intro Φ hΦ y hy
        simp only [Tm, LinearMap.comp_apply]
        have h1 : reF S T b (fun t => ψ (symplO S T t y) * Φ t) =
            fun s => ψ (symplO (reS S b) T s (reWi S T b y)) * (fun s' => Φ (reW S T b s')) s := by
          funext s
          simp only [reF, LinearMap.funLeft_apply, hB, reW_reWi]
        rw [h1, hTm'.modul _ (isSBHalf_comp_reW S T b e Λ Λ' hΛ Φ hΦ) _
          ((isHalf_reWi_iff S T b _ y).2 hy), heisO_reFi S T b ψ hB, reW_reWi]
        rfl
      · simp only [Tm, LinearMap.comp_apply]
        rw [map_smul (reF S T b), reF_halfInd S T b e Λ Λ' hΛ, hTm'.vac, reFi_reF]
    rw [hall Tm hPM]
    exact reF_reFi S T b _

end GlobalTheory.ThetaAtReframe
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeTransportCongruenceOfFrameVectors
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevCong

variable {D : D7}

theorem one_mem_intAf : (1 : Af D.host.F) ∈ intAf D.host.F := by
  intro v
  simp only [map_one]
  exact one_mem _

theorem toAf_mem_hatV {k : ℕ} {L : Lt D.host.E k} {x : Fin k → D.host.E} (hx : x ∈ L) :
    toAf (D := D) x ∈ hatV L :=
  AddSubgroup.subset_closure ⟨1, one_mem_intAf, x, hx, rfl⟩

theorem hatV_mono {k : ℕ} {L L' : Lt D.host.E k} (h : L ≤ L') : hatV (D := D) L ≤ hatV L' :=
  AddSubgroup.closure_mono fun _ ⟨a, ha, x, hx, e⟩ => ⟨a, ha, x, h hx, e⟩

theorem toAf_add {k : ℕ} (x y : Fin k → D.host.E) : toAf (D := D) (x + y) = toAf x + toAf y := by
  funext i; simp [toAf, TensorProduct.tmul_add]

theorem toAf_sub {k : ℕ} (x y : Fin k → D.host.E) : toAf (D := D) (x - y) = toAf x - toAf y := by
  funext i; simp [toAf, TensorProduct.tmul_sub]

theorem toAf_zero {k : ℕ} : toAf (D := D) (0 : Fin k → D.host.E) = 0 := by
  funext i; simp [toAf]

theorem toAf_smul {k : ℕ} (c : 𝓞 D.host.E) (x : Fin k → D.host.E) :
    toAf (D := D) (c • x) = ((1 : Af D.host.F) ⊗ₜ[D.host.F] (c : D.host.E)) • toAf x := by
  funext i
  simp [toAf, Algebra.TensorProduct.tmul_mul_tmul, Algebra.smul_def]

theorem smul_mem_hatV {k : ℕ} (c : 𝓞 D.host.E) {L L' : Lt D.host.E k} (h : ∀ x ∈ L, c • x ∈ L')
    {u : Fin k → AfE D} (hu : u ∈ hatV L) :
    ((1 : Af D.host.F) ⊗ₜ[D.host.F] (c : D.host.E)) • u ∈ hatV L' := by
  induction hu using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨a, ha, c • x, h x hx, ?_⟩
    funext i
    simp [Algebra.TensorProduct.tmul_mul_tmul, Algebra.smul_def]
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact add_mem hy hz
  | neg y _ hy => rw [smul_neg]; exact neg_mem hy

section
variable {r : ℕ} (m : Matrix (Fin r) (Fin r) (AfE D))

theorem fadd (x y : Fin r → D.host.E) : m *ᵥ toAf (D := D) (x + y) - toAf (x + y) =
    (m *ᵥ toAf x - toAf x) + (m *ᵥ toAf y - toAf y) := by
  rw [toAf_add, Matrix.mulVec_add]; abel

theorem fsmul (c : 𝓞 D.host.E) (x : Fin r → D.host.E) : m *ᵥ toAf (D := D) (c • x) - toAf (c • x) =
    ((1 : Af D.host.F) ⊗ₜ[D.host.F] (c : D.host.E)) • (m *ᵥ toAf x - toAf x) := by
  rw [toAf_smul, Matrix.mulVec_smul, smul_sub]

theorem sum_one_smul (β : Fin r → Fin r → D.host.E) (i : Fin r) :
    ∑ j, (1 : Matrix (Fin r) (Fin r) (𝓞 D.host.E)) j i • β j = β i := by
  simp only [Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem sum_sub_one (β : Fin r → Fin r → D.host.E) (κ' : Matrix (Fin r) (Fin r) (𝓞 D.host.E)) (i : Fin r) :
    ∑ j, (κ' j i - (1 : Matrix (Fin r) (Fin r) (𝓞 D.host.E)) j i) • β j = ∑ j, κ' j i • β j - β i := by
  rw [← sum_one_smul β i, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sub_smul]
end

theorem mem_of_smul {r : ℕ} (Λ : Lt D.host.E r) (𝔪 I : Ideal (𝓞 D.host.E)) (h𝔪I : 𝔪 ≤ I)
    (m : Matrix (Fin r) (Fin r) (AfE D)) (hmov : IsMov m Λ Λ) :
    ∀ t ∈ 𝔪 • Λ, m *ᵥ toAf (D := D) t - toAf t ∈ hatV (I • Λ) := by
  intro t ht
  refine Submodule.smul_induction_on ht ?_ ?_
  · intro p hp y hy
    have h1 : m *ᵥ toAf (D := D) y ∈ hatV Λ := (hmov _).2 ⟨_, toAf_mem_hatV hy, rfl⟩
    rw [fsmul]
    rw [smul_sub]
    refine sub_mem (smul_mem_hatV p (fun x hx => Submodule.smul_mem_smul (h𝔪I hp) hx) h1) ?_
    rw [← toAf_smul]; exact toAf_mem_hatV (Submodule.smul_mem_smul (h𝔪I hp) hy)
  · intro x y hx hy; rw [fadd]; exact add_mem hx hy

theorem mem_of_span {r : ℕ} (Λ : Lt D.host.E r) (β : Fin r → Fin r → D.host.E) (𝔪 I : Ideal (𝓞 D.host.E))
    (hβ : ∀ i, β i ∈ Λ) (h𝔪I : 𝔪 ≤ I) (m : Matrix (Fin r) (Fin r) (AfE D))
    (κ' : Matrix (Fin r) (Fin r) (𝓞 D.host.E))
    (hκ : ∀ i j, κ' i j - (1 : Matrix (Fin r) (Fin r) (𝓞 D.host.E)) i j ∈ I)
    (hfr : ∀ i, m *ᵥ toAf (β i) - toAf (∑ j, κ' j i • β j) ∈ hatV (𝔪 • Λ)) :
    ∀ s ∈ Submodule.span (𝓞 D.host.E) (Set.range β), m *ᵥ toAf (D := D) s - toAf s ∈ hatV (I • Λ) := by
  intro s hs
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    have e : m *ᵥ toAf (D := D) (β i) - toAf (β i) = (m *ᵥ toAf (β i) - toAf (∑ j, κ' j i • β j)) +
        toAf (∑ j, (κ' j i - (1 : Matrix (Fin r) (Fin r) (𝓞 D.host.E)) j i) • β j) := by
      rw [sum_sub_one, toAf_sub, sub_add_sub_cancel]
    rw [e]
    exact add_mem (hatV_mono (Submodule.smul_mono_left h𝔪I) (hfr i))
      (toAf_mem_hatV (sum_mem fun j _ => Submodule.smul_mem_smul (hκ j i) (hβ j)))
  | zero => rw [toAf_zero, Matrix.mulVec_zero, sub_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [fadd]; exact add_mem hx hy
  | smul c x _ hx =>
    rw [fsmul]; exact smul_mem_hatV c (fun y hy => Submodule.smul_mem _ c hy) hx

theorem cong_of_frame : ∀ (D : D7) {r : ℕ} (Λ : Lt D.host.E r) (β : Fin r → Fin r → D.host.E) (𝔪 I : Ideal (𝓞 D.host.E)), (∀ i, β i ∈ Λ) → Λ ≤ Submodule.span (𝓞 D.host.E) (Set.range β) ⊔ 𝔪 • Λ → 𝔪 ≤ I → ∀ (m : Matrix (Fin r) (Fin r) (AfE D)) (κ' : Matrix (Fin r) (Fin r) (𝓞 D.host.E)), (∀ i j, κ' i j - (1 : Matrix (Fin r) (Fin r) (𝓞 D.host.E)) i j ∈ I) → IsMov m Λ Λ → (∀ i, m *ᵥ toAf (β i) - toAf (∑ j, κ' j i • β j) ∈ hatV (𝔪 • Λ)) → ∀ x ∈ Λ, m *ᵥ toAf x - toAf x ∈ hatV (I • Λ) := by
  intro D r Λ β 𝔪 I hβ hspan h𝔪I m κ' hκ hmov hfr x hx
  obtain ⟨s, hs', t, ht', rfl⟩ := Submodule.mem_sup.1 (hspan hx)
  rw [fadd]
  exact add_mem (mem_of_span Λ β 𝔪 I hβ h𝔪I m κ' hκ hfr s hs') (mem_of_smul Λ 𝔪 I h𝔪I m hmov t ht')

end GlobalTheory.LevCong

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeAdelicVectorSizeProductMulUnitaryQuotientHeighStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.le_adelicVectorSizeProduct_mul_unitaryQuotientHeight_pow : ∀ (D : D7) (V : HSp D), ∃ (c : ℝ) (N : ℕ), 0 < c ∧ ∀ (g : GA D V) (ξ : Fin V.rank → D.host.E), ξ ≠ 0 → c ≤ GlobalTheory.HtOrth.vsize (GlobalTheory.HtOrth.seen V g ξ) * GlobalTheory.Grow.quotHeight V g ^ N := by
  first | exact @GlobalTheory.SeenSize.le_vsize_mul_quotHeight | exact GlobalTheory.SeenSize.le_vsize_mul_quotHeight | (intros; apply GlobalTheory.SeenSize.le_vsize_mul_quotHeight <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelCharacterPlacesOddAndPrincipalLevelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelCharacter_places_odd_and_principal_level : ∀ (D : D7) (T0 : Type) (L : LevCh D T0) (μ0 : T0), L.Is μ0 → L.Pg.Nonempty ∧ (∀ t PP, PP ∈ L.Pg ∨ PP ∈ L.Q t → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) ∧ ∀ (i : Fin D.R.m) (k : GA D (Wc D i)), k ∈ GfC (Wc D i) → Lev.finE (Wc D i) k ∈ Formalism.L2.DIV.St (L.βW i) → (∀ PP ∈ L.Pg, Formalism.L2.DIV.redFn (L.βW i) PP (Lev.finE (Wc D i) k) = 1) → k ∈ Lev.levG (Wc D i) (L.βW i) (L.datWp i L.triv) ∧ Lev.levChi (Wc D i) (L.βW i) (L.datWp i L.triv) k = 1 := by
  first | exact @GlobalTheory.SpanPlaces.places_level | exact GlobalTheory.SpanPlaces.places_level | (intros; apply GlobalTheory.SpanPlaces.places_level <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelsReadOnProductPrimeFieldGLStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levels_read_on_product_primeFieldGL : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.IsGrp F → ∀ b : Bool, ∃ (Φ : G ≃* GProd D) (L₁ : D.nd.PlG 0 → GlobalTheory.BadShare.Lev (D.host.g 0) D.R.r) (L₂ : D.nd.PlG 1 → GlobalTheory.BadShare.Lev (D.host.g 1) D.R.r), (∀ g : G, g ∈ (F.lvl b).P ↔ (∀ v, (L₁ v).Mem ((Φ g).1 v)) ∧ ∀ v, (L₂ v).Mem ((Φ g).2 v)) ∧ (∀ g : (F.lvl b).P, D.what₂.embLL (((F.lvl b).ψ⁻¹ g : D.what₂.LLˣ) : D.what₂.LL) = (∏ v, (L₁ v).chi ((Φ g).1 v)) * ∏ v, (L₂ v).chi ((Φ g).2 v)) ∧ (∀ g : G, GlobalTheory.BadShare.AllUnip (Φ g).1 ∨ GlobalTheory.BadShare.AllUnip (Φ g).2 → ∃ (k : Fin 2) (PP : R.Pg), CharP (kP PP.1) (D.host.g k) ∧ IsNilpotent ((R.eG g PP).val - 1)) ∧ ∀ (g : G) (γ : G0g D.nd), (∀ v, γ ⟨0, v⟩ = (Φ g).1 v) → (∀ v, γ ⟨1, v⟩ = (Φ g).2 v) → D.what₂.embLL ((idemOf A.X).coeff g) = D.ntypes.e0.coeff γ := by
  first | exact @GlobalTheory.LevelsProd.levels_prod | exact GlobalTheory.LevelsProd.levels_prod | (intros; apply GlobalTheory.LevelsProd.levels_prod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalFactorRealPlaceEqHeisenbergIntegralBaseStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localFactorRealPlace_eq_heisenbergIntegral_base : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (τ : D.what₂.Tau) (x : WO S T → ℂ), IsLocal ψ θ S T sS sT ΛS ΛT (.inr τ) x → IsLocOp ψ S T μ 𝓕 f₀ (.inr τ) x := by
  first | exact @GlobalTheory.RealLocOp.isLocOp_real | exact GlobalTheory.RealLocOp.isLocOp_real | (intros; apply GlobalTheory.RealLocOp.isLocOp_real <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalFactorStableUnitaryGroupsAtPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localFactor_stable_unitaryGroupsAtPlace : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ (p : Place D) (f : WO S T → ℂ), IsLocal ψ θ S T sS sT ΛS ΛT p f → ∀ g h, IsLocal ψ θ S T sS sT ΛS ΛT p (om (gAt S p g, gAt T p h) f) := by
  first | exact @GlobalTheory.LocalFactorUnitary.isLocal_om_gAt | exact GlobalTheory.LocalFactorUnitary.isLocal_om_gAt | (intros; apply GlobalTheory.LocalFactorUnitary.isLocal_om_gAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemStdMaxParabolicOfBlockParabolicLeConjStatement
section
open MeasureTheory ValuativeRel GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_stdMaxParabolic_of_blockParabolic_le_conj : ∀ (F : Type) [Field F] {r a b s : ℕ} (h : a + b = r) (d : Fin s → ℕ) (hd : ∑ i, d i = r) (g : GL (Fin r) F),
    parab F (stdBlocks d hd) ≤ conjBy g (stdMaxParab F h) → g ∈ stdMaxParab F h := by
  first | exact @GlobalTheory.ParabConj.mem_stdMaxParab_of_le_conjBy | exact GlobalTheory.ParabConj.mem_stdMaxParab_of_le_conjBy | (intros; apply GlobalTheory.ParabConj.mem_stdMaxParab_of_le_conjBy <;> assumption)
end

