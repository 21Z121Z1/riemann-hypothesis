import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1444
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1455
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1456
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1459
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapRangeAdjointLeBlockSum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0187
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0213
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0243
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0208
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0228
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1462
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartREqPartLSwap
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval

noncomputable section

namespace GlobalTheory.DblEval.BlockSwap

section Generic

variable {A : Type} {κ κ' κ₁' : Type}

def swapV (z : κ' ⊕ κ → A) : κ ⊕ κ' → A := z ∘ Sum.swap

theorem partR_eq_partL_swap (T : ((κ' → A) → ℂ) → (κ₁' → A) → ℂ) (Φ : (κ ⊕ κ' → A) → ℂ) (y : κ ⊕ κ₁' → A) :
    partR T Φ y = partL T (fun z : κ' ⊕ κ → A => Φ (swapV z)) (swapV y) := by
  simp only [partR, partL, swapV]
  congr 1
  funext x
  congr 1
  funext i
  cases i <;> rfl

end Generic

section Adelic

open scoped Classical

variable {F : Type} [Field F] [NumberField F]

def swapCLE (M : Type) [NormedAddCommGroup M] [NormedSpace ℝ M] (κ κ' : Type) : (κ' ⊕ κ → M) ≃L[ℝ] (κ ⊕ κ' → M) :=
  { LinearEquiv.funCongrLeft ℝ M (Equiv.sumComm κ κ') with
    continuous_toFun := continuous_pi fun _ => continuous_apply _
    continuous_invFun := continuous_pi fun _ => continuous_apply _ }

def swapH (X : Type) [TopologicalSpace X] (κ κ' : Type) : (κ' ⊕ κ → X) ≃ₜ (κ ⊕ κ' → X) where
  toFun := swapV
  invFun := swapV
  left_inv z := by funext i; cases i <;> rfl
  right_inv z := by funext i; cases i <;> rfl
  continuous_toFun := continuous_pi fun _ => continuous_apply _
  continuous_invFun := continuous_pi fun _ => continuous_apply _

theorem sb_swap {X : Type} [TopologicalSpace X] {κ κ' : Type} {g : (κ ⊕ κ' → X) → ℂ} (hg : g ∈ SB (κ ⊕ κ' → X)) :
    (fun z : κ' ⊕ κ → X => g (swapV z)) ∈ SB (κ' ⊕ κ → X) :=
  ⟨hg.1.comp_continuous (swapH X κ κ').continuous, hg.2.comp_homeomorph (swapH X κ κ')⟩

theorem partR_of_partL {κ κ' κ₁' : Type} [Fintype κ] [Fintype κ'] [Fintype κ₁']
    (e : ((κ' → AF F) → ℂ) →ₗ[ℂ] (κ₁' → AF F) → ℂ)
    (hL : ∃ P : SInf F (κ' ⊕ κ) →L[ℂ] SInf F (κ₁' ⊕ κ), ∀ g ∈ SB (κ' ⊕ κ → Af F), ∃ g₁ ∈ SB (κ₁' ⊕ κ → Af F),
      ∀ f : SInf F (κ' ⊕ κ), partL e (pureA F f g) = pureA F (P f) g₁) :
    ∃ P : SInf F (κ ⊕ κ') →L[ℂ] SInf F (κ ⊕ κ₁'), ∀ g ∈ SB (κ ⊕ κ' → Af F), ∃ g₁ ∈ SB (κ ⊕ κ₁' → Af F),
      ∀ f : SInf F (κ ⊕ κ'), partR e (pureA F f g) = pureA F (P f) g₁ := by
  obtain ⟨PL, hPL⟩ := hL
  refine ⟨(SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (swapCLE _ κ₁' κ)).comp
    (PL.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (swapCLE _ κ κ'))), fun g hg => ?_⟩
  obtain ⟨g₁, hg₁, h⟩ := hPL _ (sb_swap hg)
  refine ⟨fun w => g₁ (swapV w), sb_swap hg₁, fun f => ?_⟩
  funext y
  rw [partR_eq_partL_swap]
  have hpure : (fun z : κ' ⊕ κ → AF F => pureA F (⇑f) g (swapV z)) =
      pureA F (⇑(SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (swapCLE _ κ κ') f)) (fun w => g (swapV w)) := rfl
  rw [hpure, h]
  rfl

end Adelic

end GlobalTheory.DblEval.BlockSwap

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
section
noncomputable section

namespace GlobalTheory.IndLine

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}

def fockDeg (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (k : ℕ) : Submodule ℂ (SInf F (Fin n × Fin d)) :=
  Nat.rec (motive := fun _ => Submodule ℂ (SInf F (Fin n × Fin d))) (Submodule.span ℂ {f₀ | M.IsGauss ψ τ f₀})
    (fun _ N => N ⊔ Submodule.span ℂ {f₁ | ∃ u, At (evI F) u ∧ ∃ f ∈ N, ActsD (evI F) (M.heisLine ψ u) f f₁}) k

theorem fockDeg_zero (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w) :
    fockDeg M ψ τ 0 = Submodule.span ℂ {f₀ | M.IsGauss ψ τ f₀} := rfl

theorem fockDeg_succ (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (k : ℕ) :
    fockDeg M ψ τ (k + 1) = fockDeg M ψ τ k ⊔ Submodule.span ℂ {f₁ | ∃ u, At (evI F) u ∧ ∃ f ∈ fockDeg M ψ τ k,
      ActsD (evI F) (M.heisLine ψ u) f f₁} := rfl

def lowDegInf (B : Base F E) (M : Model σ Y W) {P : Type} [AddCommGroup P] [Module ℂ P]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) : ℕ :=
  sInf {k | ∃ f ∈ fockDeg M B.ψ B.emb k, p f ≠ 0}

def lowPartInf (B : Base F E) (M : Model σ Y W) {P : Type} [AddCommGroup P] [Module ℂ P]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) : Submodule ℂ P :=
  (fockDeg M B.ψ B.emb (lowDegInf B M p)).map p

theorem fockDeg_mono (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w) :
    Monotone (fockDeg M ψ τ) :=
  monotone_nat_of_le_succ fun _ => le_sup_left

theorem fockDeg_le_pol (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (k : ℕ) :
    fockDeg M ψ τ k ≤ M.Pol ψ τ := by
  induction k with
  | zero => exact Submodule.span_le.2 fun f hf => Submodule.mem_sInf.2 fun N hN => hN.1 f hf
  | succ k ih =>
    refine sup_le ih (Submodule.span_le.2 ?_)
    rintro f₁ ⟨u, hu, f, hf, hd⟩
    exact Submodule.mem_sInf.2 fun N hN => hN.2 u hu f (Submodule.mem_sInf.1 (ih hf) N hN) f₁ hd

theorem pol_eq_iSup_fockDeg (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w) :
    M.Pol ψ τ = ⨆ k, fockDeg M ψ τ k := by
  refine le_antisymm (sInf_le ⟨fun f₀ hf₀ => ?_, fun u hu f hf f₁ hd => ?_⟩) (iSup_le (fockDeg_le_pol M ψ τ))
  · exact Submodule.mem_iSup_of_mem 0 (Submodule.subset_span hf₀)
  · obtain ⟨k, hk⟩ := (Submodule.mem_iSup_of_directed _ (fockDeg_mono M ψ τ).directed_le).1 hf
    exact Submodule.mem_iSup_of_mem (k + 1)
      (Submodule.mem_sup_right (Submodule.subset_span ⟨u, hu, f, hk, hd⟩))

theorem lowPartInf_ne_bot (B : Base F E) (M : Model σ Y W) {P : Type} [AddCommGroup P] [Module ℂ P]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (h : ∃ f ∈ M.Pol B.ψ B.emb, p f ≠ 0) : lowPartInf B M p ≠ ⊥ := by
  obtain ⟨f, hf, hp⟩ := h
  rw [pol_eq_iSup_fockDeg] at hf
  obtain ⟨k, hk⟩ := (Submodule.mem_iSup_of_directed _ (fockDeg_mono M B.ψ B.emb).directed_le).1 hf
  have hne : {k | ∃ f ∈ fockDeg M B.ψ B.emb k, p f ≠ 0}.Nonempty := ⟨k, f, hk, hp⟩
  obtain ⟨g, hg, hpg⟩ := Nat.sInf_mem hne
  intro hbot
  exact hpg ((Submodule.eq_bot_iff _).1 hbot (p g) ⟨g, hg, rfl⟩)

end GlobalTheory.IndLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDataDecomposesAtFinitePlaces
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThK.CycGen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem smul_pure {κ : Type} [Fintype κ] (c : ℂ) (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) :
    c • pure f φ = pure (c • f) φ := by
  funext x
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]

theorem DecOn.mono {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {T T' : Finset (Pl F)}
    {Ψ : (Fin n × Fin d → AF F) → ℂ} {m : ℕ} {f : Fin m → SInf F (Fin n × Fin d)}
    {φ : Fin m → ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ} (hT : T ⊆ T') (h : DecOn B M T Ψ m f φ) :
    DecOn B M T' Ψ m f φ :=
  ⟨fun j => ⟨(h.1 j).1, (h.1 j).2.1, fun v hv => (h.1 j).2.2 v fun hv' => hv (hT hv')⟩, h.2⟩

theorem exists_decOn_some {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W)
    (Φ : (Fin n × Fin d → AF F) → ℂ) (hΦ : Φ ∈ PolData B M) :
    ∃ (T₀ : Finset (Pl F)) (m : ℕ) (f : Fin m → SInf F (Fin n × Fin d))
      (φ : Fin m → ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ), DecOn B M T₀ Φ m f φ := by
  classical
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, φ, hφ, hcof, rfl⟩ := hx
    have hfin : {v | ¬ φ v = M.vac v}.Finite := Filter.eventually_cofinite.1 hcof
    refine ⟨hfin.toFinset, 1, fun _ => f, fun _ => φ, fun _ => ⟨hf, hφ, fun v hv => ?_⟩, ?_⟩
    · by_contra h
      exact hv (hfin.mem_toFinset.2 h)
    · simp
  | zero =>
    exact ⟨∅, 0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨T, m, f, φ, h1, rfl⟩ := hx
    obtain ⟨T', m', f', φ', h1', rfl⟩ := hy
    refine ⟨T ∪ T', m + m', Fin.append f f', Fin.append φ φ', fun j => ?_, ?_⟩
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simp only [Fin.append_left]
        exact ⟨(h1 i).1, (h1 i).2.1, fun v hv => (h1 i).2.2 v fun h => hv (Finset.mem_union_left _ h)⟩
      · simp only [Fin.append_right]
        exact ⟨(h1' i).1, (h1' i).2.1, fun v hv => (h1' i).2.2 v fun h => hv (Finset.mem_union_right _ h)⟩
    · rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
  | smul c x _ hx =>
    obtain ⟨T, m, f, φ, h1, rfl⟩ := hx
    refine ⟨T, m, fun j => c • f j, φ, fun j => ⟨Submodule.smul_mem _ c (h1 j).1, (h1 j).2.1, (h1 j).2.2⟩, ?_⟩
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => smul_pure c (f j) (φ j)

end GlobalTheory.ThK.CycGen

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureLApply
section
noncomputable section

namespace GlobalTheory.ThetaFacInf

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F : Type} [Field F] [NumberField F]

def pureL {κ : Type} [Fintype κ] (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) : SInf F κ →ₗ[ℂ] ((κ → AF F) → ℂ) where
  toFun f := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ
  map_add' f g := by funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, add_mul]
  map_smul' c f := by funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]

theorem pureL_apply {κ : Type} [Fintype κ] (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) (f : SInf F κ) :
    pureL φ f = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := rfl

end GlobalTheory.ThetaFacInf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticInjectivePlaneCoordinates
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.MixedLagr
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.MixedLagr

theorem le_finrank_lagr : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n d d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁),
    Module.finrank F E = 2 → d = d₁ + 2 → form σ W.J H'.x H'.y = 1 → (∀ u, form σ W.J (H'.ι *ᵥ u) H'.y = 0) →
    (Function.Injective fun z : Matrix (Fin n) (Fin d₁) E => z * H'.ιᵀ) →
    ∀ f : Matrix (Fin n) (Fin d) E →ₗ[F] (Fin n × Fin d → F) × (Fin n × Fin d → F),
      Function.Injective f → (∀ x, hat (f x) = M.co.e (incM F x)) →
    ∀ K : Submodule F (Matrix (Fin n) (Fin d₁) E), Module.finrank F K = n * d₁ → (∀ z ∈ K, (M₁.co.e (incM F z)).1 = 0) →
      n * d ≤ Module.finrank F (lagr M M₁ H') := by
  intro F E _ _ _ _ _ σ n d d₁ X W W₁ M M₁ H' hE hd hxy hιy hι f hf hfe K hK hK0
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)

  let Φ : (Fin n → E) × K →ₗ[F] Matrix (Fin n) (Fin d) E :=
    { toFun := fun p => Matrix.vecMulVec p.1 H'.x + (p.2 : Matrix (Fin n) (Fin d₁) E) * H'.ιᵀ
      map_add' := fun p q => by
        simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, Matrix.add_vecMulVec, Matrix.add_mul]; abel
      map_smul' := fun c p => by
        ext i j
        simp [Matrix.vecMulVec_apply, Matrix.mul_apply, Finset.smul_sum, smul_mul_assoc, smul_add] }
  have hΦ : ∀ p, Φ p = Matrix.vecMulVec p.1 H'.x + (p.2 : Matrix (Fin n) (Fin d₁) E) * H'.ιᵀ := fun _ => rfl
  have h1 : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := by
    ext i j
    by_cases h : i = j
    · subst h; simp [incM]
    · simp [incM, Matrix.one_apply, h]
  have hmem : ∀ p, f (Φ p) ∈ lagr M M₁ H' := by
    intro p
    rw [mem_lagr, hfe, LinearEquiv.symm_apply_apply]
    refine ⟨Matrix.vecMulVec (incV F p.1) (incV F H'.x), ⟨incV F p.1, rfl⟩, incM F (p.2 : Matrix (Fin n) (Fin d₁) E),
      hK0 _ p.2.2, ?_⟩
    rw [h1, Matrix.one_mul, hΦ]
    ext i j
    simp [incM, incV, Matrix.vecMulVec_apply, Matrix.mul_apply, map_sum, map_mul]
  have hform : ∀ (a : E) (u v : Fin d → E), form σ W.J (a • u + v) H'.y = a * form σ W.J u H'.y + form σ W.J v H'.y := by
    intro a u v
    simp [form, add_dotProduct, smul_dotProduct]
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro p hp
    rw [hΦ] at hp
    have hrow : ∀ i, (p.1 i) • H'.x + H'.ι *ᵥ ((p.2 : Matrix (Fin n) (Fin d₁) E) i) = 0 := by
      intro i
      funext j
      have := congrFun (congrFun hp i) j
      simp only [Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.transpose_apply,
        Matrix.zero_apply] at this
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Pi.zero_apply]
      rw [← this]
      congr 1
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    have hy : p.1 = 0 := by
      funext i
      have : form σ W.J ((p.1 i) • H'.x + H'.ι *ᵥ ((p.2 : Matrix (Fin n) (Fin d₁) E) i)) H'.y = form σ W.J 0 H'.y := by
        rw [hrow i]
      rw [hform, hxy, hιy] at this
      simpa [form] using this
    have hz : (p.2 : Matrix (Fin n) (Fin d₁) E) = 0 := by
      apply hι
      simp only
      rw [Matrix.zero_mul, ← hp, hy, Matrix.zero_vecMulVec, zero_add]
    exact Prod.ext hy (Subtype.ext hz)
  let g := (f ∘ₗ Φ).codRestrict (lagr M M₁ H') hmem
  have hg : Function.Injective g := by
    intro p q h
    apply hinj; apply hf
    simpa [g] using congrArg Subtype.val h
  have hle := LinearMap.finrank_le_finrank_of_injective hg
  have hdom : Module.finrank F ((Fin n → E) × K) = n * d := by
    rw [Module.finrank_prod, Module.finrank_pi_fintype, hK]
    simp [hE, hd]
    ring
  omega

end GlobalTheory.MixedLagr

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeAdjointCompositeLiftLeSpanBlockEigenspaces
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.AdjSpan

open Formalism.L2 in

theorem eigSum_le_span {K V H I : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] {σ : K →+* ℂ} {j : V →ₛₗ[σ] H}
    (hsp : Submodule.span ℂ (Set.range j) = ⊤) {op : I → Module.End K V} {U : I → Module.End ℂ H}
    (hU : ∀ i v, U i (j v) = j (op i v)) (hc : Col.PairComm op) (hs : Col.SplitOver op)
    {C : (I → K) → Prop} {CC : (I → ℂ) → Prop} (hC : ∀ x, CC (fun i => σ (x i)) → C x) :
    Col.eigSum U CC ≤ Submodule.span ℂ (j '' (Col.eigSum op C : Set V)) := by
  have hcU : Col.PairComm U := fun i i' => GlobalTheory.AdjBlock.ext_of_span hsp fun v => by
    simp only [Module.End.mul_apply, hU]
    exact congrArg j (LinearMap.congr_fun (hc i i').eq v)
  have h1 : ∀ x, Col.eigAt op x ≤ (Col.eigAt U fun i => σ (x i)).comap j := by
    intro x v hv
    rw [Submodule.mem_comap, Col.eigAt, Submodule.mem_iInf]
    intro i
    obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 (Col.eigAt_le op x i hv)
    refine (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨k, ?_⟩
    have : ∀ (k : ℕ) w, ((U i - σ (x i) • (1 : Module.End ℂ H)) ^ k) (j w) =
        j (((op i - x i • (1 : Module.End K V)) ^ k) w) := by
      intro k
      induction k with
      | zero => intro w; simp
      | succ k ih =>
        intro w
        rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ← ih]
        simp [hU, map_smulₛₗ]
    rw [this, hk, map_zero]
  have h2 : ∀ Q : (I → K) → Prop, Submodule.span ℂ (j '' (Col.eigSum op Q : Set V)) ≤
      Col.eigSum U fun y => ∃ x, Q x ∧ y = fun i => σ (x i) := fun Q => by
    have : Col.eigSum op Q ≤ (Col.eigSum U fun y => ∃ x, Q x ∧ y = fun i => σ (x i)).comap j :=
      iSup₂_le fun x hx => (h1 x).trans (Submodule.comap_mono (Col.eigAt_le_eigSum ⟨x, hx, rfl⟩))
    rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    exact this hv
  have h3 : Submodule.span ℂ (j '' (Col.eigSum op C : Set V)) ⊔
      Submodule.span ℂ (j '' (Col.eigSum op (fun x => ¬ C x) : Set V)) = ⊤ := by
    rw [eq_top_iff, ← hsp, Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    obtain ⟨a, ha, c, hc', rfl⟩ := Submodule.mem_sup.1
      ((Col.isCompl_eigSum hc hs C).sup_eq_top ▸ (Submodule.mem_top : v ∈ (⊤ : Submodule K V)))
    rw [map_add]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨a, ha, rfl⟩) (Submodule.subset_span ⟨c, hc', rfl⟩)
  have h4 : Disjoint (Col.eigSum U fun y => CC y ∨ ∃ x, C x ∧ y = fun i => σ (x i))
      (Col.eigSum U fun y => ∃ x, ¬ C x ∧ y = fun i => σ (x i)) := by
    refine Col.disjoint_eigSum hcU ?_
    rintro y hy ⟨x, hx, rfl⟩
    rcases hy with hy | ⟨x', hx', he⟩
    · exact hx (hC x hy)
    · have : x = x' := funext fun i => σ.injective (congrFun he i)
      exact hx (this ▸ hx')
  rw [Col.eigSum_or] at h4
  intro w hw
  obtain ⟨a, ha, c, hc', rfl⟩ := Submodule.mem_sup.1 (h3 ▸ (Submodule.mem_top : w ∈ (⊤ : Submodule ℂ H)))
  have h5 : c = 0 := by
    refine (Submodule.disjoint_def.1 h4) _ ?_ (h2 _ hc')
    have : c = (a + c) - a := by abel
    rw [this]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left hw) (Submodule.mem_sup_right (h2 _ ha))
  rw [h5, add_zero]
  exact ha

theorem heckePolyOf_congr {L : Type} [Field L] (n q : ℕ) {a b : ℕ → L} (h : ∀ k, k ≤ n → a k = b k) :
    Formalism.L2.Col.heckePolyOf n q a = Formalism.L2.Col.heckePolyOf n q b := by
  unfold Formalism.L2.Col.heckePolyOf
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [h i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))]

open Classical in
theorem evC_splitC {D : D7} (V : HSp D) (P : Pl D.host.E) (a : List ℤ → ℂ) (z : ℕ → ℂ) :
    GlobalTheory.Hk3.evC V P a (GlobalTheory.Hk3.splitC V.rank z) = ∑ j ∈ Finset.range (V.rank + 1),
      z j * (if IsLab V P (splitLab V.rank j) then a (splitLab V.rank j) else 0) := by
  unfold GlobalTheory.Hk3.evC GlobalTheory.Hk3.splitC
  rw [← Finsupp.sum_finset_sum_index (by simp) (by intro d x y; split_ifs <;> simp [add_mul])]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finsupp.sum_single_index (by simp)]
  split_ifs <;> simp

open Formalism.L2 in

theorem range_le_span_blockSum {K V H E Pl ι : Type} [Field K] [AddCommGroup V] [Module K V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] {σ : K →+* ℂ} {j : V →ₛₗ[σ] H}
    (hV : FiniteDimensional K V)
    (hsp : Submodule.span ℂ (Set.range j) = ⊤) {op : Pl × ℕ → Module.End K V} (hc : Col.PairComm op)
    (hs : Col.SplitOver op) {n m t : ℕ} (hm : m = n) {q : Pl → ℕ} {bl : List (Pl → K)}
    (hz : ∀ P k, m < k → op (P, k) = 0) (Θ : H →ₗ[ℂ] E) (W : ι → Submodule ℂ E) (hW : ⨆ c, W c = ⊤)
    (T : Pl → ℕ → Module.End ℂ H) (hT : ∀ P k, k ≤ m → ∀ v, j (op (P, k) v) = T P k (j v))
    (ev : ι → Pl → ℕ → ℂ) (g : ι → Pl → ℂ[X])
    (hg : ∀ c P, Col.heckePolyOf m (q P) (ev c P) = g c P * ((bl.map fun ν => Col.blockPoly (ν P) (q P) t).prod).map σ)
    (hev : ∀ c, ∀ w ∈ W c, ∀ P k, k ≤ m → T P k (LinearMap.adjoint Θ w) = ev c P k • LinearMap.adjoint Θ w) :
    LinearMap.range (LinearMap.adjoint Θ) ≤ Submodule.span ℂ (j '' (Col.blockSum n q t bl op : Set V)) := by
  subst hm
  let U : Pl × ℕ → Module.End ℂ H := fun i => if i.2 ≤ m then T i.1 i.2 else 0
  have hU : ∀ i v, U i (j v) = j (op i v) := by
    rintro ⟨P, k⟩ v
    by_cases hk : k ≤ m
    · simp only [U, if_pos hk]
      exact (hT P k hk v).symm
    · simp only [U, if_neg hk]
      rw [hz P k (not_le.1 hk)]
      simp
  refine le_trans ?_ (eigSum_le_span (U := U) hsp hU hc hs fun x hx => (Col.hasBlocks_map σ m q t bl x).1 hx)
  rw [LinearMap.range_eq_map, ← hW, Submodule.map_iSup]
  refine iSup_le fun c => ?_
  rintro _ ⟨w, hw, rfl⟩
  let x : Pl × ℕ → ℂ := fun i => if i.2 ≤ m then ev c i.1 i.2 else 0
  refine Col.eigAt_le_eigSum (x := x) (fun P => ?_) (Col.mem_eigAt_of_forall_apply ?_)
  · have h1 : Col.heckePolyOf m (q P) (fun k => x (P, k)) = _ :=
      (heckePolyOf_congr _ _ fun k hk => if_pos hk).trans (hg c P)
    refine Dvd.intro_left (g c P) (Eq.trans ?_ h1.symm)
    simp only [Polynomial.map_list_prod, List.map_map, Function.comp_def, Col.map_blockPoly]
  · rintro ⟨P, k⟩
    by_cases hk : k ≤ m
    · simp only [U, x, if_pos hk]
      exact hev c w hw P k hk
    · simp only [U, x, if_neg hk]
      simp

theorem range_adjoint_le_span : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A.fam.Ok s → Core R F → SchurAll R → ∀ t, LinearMap.range (LinearMap.adjoint (R.Th t)) ≤ Submodule.span ℂ (R.jX t '' ((A.fam.R t).ZH : Set (A.fam.R t).S.Forms)) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F s hI hOk hC hS t
  classical
  have hSF : IsSF R (R.Pg.image fun PP => PP.under (𝓞 D.host.F)) := by
    intro v
    simp only [Finset.mem_image, HeightOneSpectrum.ext_iff]
    rfl
  have htop : ⨆ c, EEc R _ c = ⊤ := (GlobalTheory.T.exists_sphericalOperators_rows_normal_eigenspaces R F hC hS _ hSF).elim fun _ h => h.2.2.1
  choose hX hXo _ using (GlobalTheory.T.realization_family_normal_operators R F hC.lev hC.fam hC.models).1 t
  have hsplit := (GlobalTheory.SplitHeckeLabel.split_ops R F hC.lev hC.fam hC.models).1 t hX hXo
  have hf := GlobalTheory.AdjBlock.model_form (W := R.cX.W) (ι := Bridge.ratF D.sp.X') (ρ := R.cX.coef.ρ)
    (J := (levEnv _ R.βX (R.datXt t)).J) (χ := (levEnv _ R.βX (R.datXt t)).χ) (R.B.R t).pres (R.HX t) (hC.models.HX t)
    (hC.models.jX t)
  choose z hm hp using fun P : A.ok t => GlobalTheory.T.exists_splitPrime_heckeTransfer_compositeLift R F hI hC hS t P
  let a : (Pl D.host.E → List ℤ → ℂ) → A.ok t → ℕ → ℂ := fun c P j =>
    if IsLab (Yc D 0) (R.pl P) (splitLab (Yc D 0).rank j) then c (R.pl P) (dualLab (splitLab (Yc D 0).rank j)) else 0
  exact range_le_span_blockSum (Pl := A.ok t) (q := fun P => A.q P) (Module.Finite.of_basis (A.MtildeCSD t).basis) hf.2.1 (hOk.what₂ t).comm (hOk.what₂ t).split R.B.rankR
    (fun P => (hC.fam.degR t P).2) (R.Th t) _ htop
    (fun P k => hX (R.pl P) (Finsupp.single (splitLab D.sp.X'.rank k) 1)) hsplit
    (fun c P k => ∑ j ∈ Finset.range ((Yc D 0).rank + 1), z P k j * a c P j) _ (fun c P => hp P (a c P))
    fun c w hw P k hk => ((GlobalTheory.T.matched_spherical_pairs_commute_composite_lift R F hC hS _ hSF t (R.pl P)
      ((GlobalTheory.GoodPrimes.good_primes R F hC.lev).2.2.2 hC.fam t P.1 P.2).1 _ _ (hm P k hk) hX hXo).2 c w hw).trans
        (congrArg (· • LinearMap.adjoint (R.Th t) w) (evC_splitC _ _ _ _))

end GlobalTheory.AdjSpan

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothingRightTranslateMaxCompactStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothing_right_translate_maxCompact : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (α : Lie E a → ℂ), KInv α → ∀ (ψ : GA E a → ℂ) (k : Kinf E a) (g : GA E a), smoothing ν α (fun x => ψ (x * infGL E a (Unitary.toUnits k))) g = smoothing ν α ψ (g * infGL E a (Unitary.toUnits k)) := by
  first | exact @GlobalTheory.AutGrowth.smoothing_rt_Kinf | exact GlobalTheory.AutGrowth.smoothing_rt_Kinf | (intros; apply GlobalTheory.AutGrowth.smoothing_rt_Kinf <;> assumption)
end

