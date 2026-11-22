import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1466
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1459
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0040
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1444
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1465
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1468
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1445
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1467
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleQuotientCompactFundamentalSetStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipMass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adele_quotient_compact_fundamental_set : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∃ K : Set (AE F E), IsCompact K ∧ ∀ a : AE F E, ∃ e : E, a - inclR (F := F) (AF F) e ∈ K := by
  first | exact @GlobalTheory.AdeleCocompactExt.exists_compact_adeleE | exact GlobalTheory.AdeleCocompactExt.exists_compact_adeleE | (intros; apply GlobalTheory.AdeleCocompactExt.exists_compact_adeleE <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzConjMemStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_schwartz_conj_mem : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ], ∀ Φ ∈ schA F κ, (fun x => starRingEnd ℂ (Φ x)) ∈ schA F κ := by
  first | exact @GlobalTheory.ConjSch.conj_mem_schA | exact GlobalTheory.ConjSch.conj_mem_schA | (intros; apply GlobalTheory.ConjSch.conj_mem_schA <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzContinuousHasDerivAtArchimedeanLin
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix ENNReal
open scoped Classical
open GlobalTheory.ArchDecay

noncomputable section

namespace GlobalTheory.ArchDecay.SchLine

theorem continuous_pureA (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) : Continuous (pureA F f g) := by
  unfold pureA
  refine Continuous.mul (f.continuous.comp (continuous_pi fun i => ?_)) (hg.1.continuous.comp (continuous_pi fun i => ?_))
  · exact (continuous_mixed F).comp (continuous_fst.comp (continuous_apply i))
  · exact continuous_snd.comp (continuous_apply i)

theorem continuous_of_mem (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]
    {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) : Continuous Φ := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    exact continuous_pureA F f g hg
  | zero => exact continuous_const
  | add Φ Ψ _ _ h1 h2 => exact h1.add h2
  | smul a Φ _ h => exact h.const_smul a

theorem line_shift (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (x : κ → AF F) (v : κ → mixedEmbedding.mixedSpace F) (t s : ℝ) :
    x + (fun i => infAd F (s • v i)) = (x + fun i => infAd F (t • v i)) + fun i => infAd F ((s - t) • v i) := by
  funext i
  simp only [Pi.add_apply]
  rw [add_assoc, ← infAd_add, ← add_smul, add_sub_cancel]

theorem schline : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∀ g ∈ schA F κ, Continuous g ∧
    ∀ (v : κ → mixedEmbedding.mixedSpace F) (x : κ → AF F) (t : ℝ),
      HasDerivAt (fun s : ℝ => g (x + fun i => infAd F (s • v i))) (dD F v g (x + fun i => infAd F (t • v i))) t := by
  intro F _ _ κ _ g hg
  refine ⟨continuous_of_mem F hg, fun v x t => ?_⟩
  set y : κ → AF F := x + fun i => infAd F (t • v i)
  have h0 : HasDerivAt (fun u : ℝ => g (y + fun i => infAd F (u • v i))) (dD F v g y) (t - t) := by
    rw [sub_self]
    exact ((SchAStab.archimedeanDirectionalDerivative_mem_adelicSchwartz F v hg).1 y).hasDerivAt
  have h1 := h0.comp_sub_const t t
  refine h1.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  show g (x + fun i => infAd F (s • v i)) = g (y + fun i => infAd F ((s - t) • v i))
  rw [line_shift F x v t s]

end GlobalTheory.ArchDecay.SchLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchBoundCoordinates
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDecay
open scoped TensorProduct NNReal Matrix

noncomputable section

namespace GlobalTheory.ThetaDecay.Coord

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def embEquiv (w : InfinitePlace F) :
    letI : Algebra F ℂ := w.embedding.toAlgebra
    EmbOver E w ≃ (E →ₐ[F] ℂ) :=
  letI : Algebra F ℂ := w.embedding.toAlgebra
  { toFun := fun t => { t.1 with commutes' := fun x => RingHom.congr_fun t.2 x }
    invFun := fun s => ⟨s, RingHom.ext s.commutes⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

open Classical in
theorem embedding_trace (w : InfinitePlace F) (x : E) :
    w.embedding (Algebra.trace F E x) = ∑ τ : EmbOver E w, τ.1 x := by
  letI : Algebra F ℂ := w.embedding.toAlgebra
  have h := trace_eq_sum_embeddings (K := F) (L := E) ℂ (x := x)
  refine h.trans ?_
  exact (Fintype.sum_equiv (embEquiv w) _ _ fun _ => rfl).symm

theorem exists_repr_eq_trace (r : Fin (Module.finrank F E)) :
    ∃ c : E, ∀ x : E, (Module.finBasis F E).repr x r = Algebra.trace F E (c * x) := by
  classical
  refine ⟨(Module.finBasis F E).traceDual r, fun x => ?_⟩
  conv_rhs => rw [← (Module.finBasis F E).sum_repr x]
  rw [Finset.mul_sum, map_sum]
  simp only [mul_smul_comm, map_smul, Module.Basis.trace_traceDual_mul]
  simp

theorem archAt_algebraMap (w : InfinitePlace F) (x : F) :
    archAt F w (algebraMap F (AF F) x) = w.embedding x := by
  change InfinitePlace.Completion.extensionEmbedding w (evInf F w (algebraMap F (AF F) x)) = _
  rw [AlgHom.commutes]
  exact InfinitePlace.Completion.extensionEmbedding_coe w ((WithAbs.equiv w.1).symm x)

open Classical in
theorem archAt_repr (r : Fin (Module.finrank F E)) {c : E}
    (hc : ∀ x : E, (Module.finBasis F E).repr x r = Algebra.trace F E (c * x)) (w : InfinitePlace F) (y : AE F E) :
    archAt F w ((coB F E).repr y r) = ∑ τ : EmbOver E w, τ.1 c * piInf τ y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy, mul_add, Finset.sum_add_distrib]
  | tmul a x =>
    have h1 : (coB F E).repr (a ⊗ₜ[F] x) r = a * algebraMap F (AF F) ((Module.finBasis F E).repr x r) := by
      simp [coB, Algebra.TensorProduct.basis_repr_tmul]
    have h2 : ∀ τ : EmbOver E w, piInf τ (a ⊗ₜ[F] x) = archAt F w a * τ.1 x := fun τ => rfl
    rw [h1, map_mul, archAt_algebraMap, hc, embedding_trace, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [h2, map_mul]; ring

theorem coord_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∃ K : ℝ, 0 ≤ K ∧
    ∀ (y : AE F E) (B : ℝ), 0 ≤ B → (∀ (w : InfinitePlace F) (τ : EmbOver E w), ‖piInf τ y‖ ≤ B) →
    ∀ r w, ‖archAt F w ((coB F E).repr y r)‖ ≤ K * B := by
  classical
  intro F E _ _ _ _ _
  choose c hc using exists_repr_eq_trace (F := F) (E := E)
  let f : Fin (Module.finrank F E) × InfinitePlace F → ℝ := fun p => ∑ τ : EmbOver E p.2, ‖τ.1 (c p.1)‖
  have hf : ∀ p, 0 ≤ f p := fun p => Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨∑ p, f p, Finset.sum_nonneg fun p _ => hf p, fun y B hB h r w => ?_⟩
  rw [archAt_repr r (hc r) w y]
  refine (norm_sum_le _ _).trans (le_trans ?_ (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (f := f) (fun p _ => hf p) (Finset.mem_univ (r, w))) hB))
  simp only [f]
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun τ _ => ?_
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (h w τ) (norm_nonneg _)

end GlobalTheory.ThetaDecay.Coord

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchBoundLinearCoordinates
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDecay
open scoped TensorProduct NNReal Matrix

noncomputable section
namespace GlobalTheory.ThetaDecay

theorem arch_bound_functional (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n d : ℕ) (g : Matrix (Fin n) (Fin d) (AE F E) →ₗ[AF F] AF F) (w : InfinitePlace F)
    (x : Matrix (Fin n) (Fin d) (AE F E)) (B : ℝ) (hB : 0 ≤ B)
    (hx : ∀ k l r, ‖archAt F w ((coB F E).repr (x k l) r)‖ ≤ B) :
    ‖archAt F w (g x)‖ ≤ B * ∑ k, ∑ l, ∑ r, ‖archAt F w (g (Matrix.single k l (coB F E r)))‖ := by
  have hx' : x = ∑ k, ∑ l, ∑ r, (coB F E).repr (x k l) r • Matrix.single k l (coB F E r) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single x]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    conv_lhs => rw [← (coB F E).sum_repr (x k l)]
    simp only [Matrix.smul_single]
    exact map_sum (Matrix.singleAddMonoidHom k l) _ _
  rw [hx']
  simp only [map_sum, map_smul, smul_eq_mul, map_mul]
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hx k l r) (norm_nonneg _)

theorem arch_bound_pair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n d : ℕ) (κ : Type) [Fintype κ]
    (f : Matrix (Fin n) (Fin d) (AE F E) →ₗ[AF F] (κ → AF F) × (κ → AF F)), ∃ K : ℝ, 0 ≤ K ∧
    ∀ (x : Matrix (Fin n) (Fin d) (AE F E)) (B : ℝ), 0 ≤ B →
    (∀ w k l r, ‖archAt F w ((coB F E).repr (x k l) r)‖ ≤ B) →
    ∀ w i, ‖archAt F w ((f x).1 i)‖ ≤ K * B ∧ ‖archAt F w ((f x).2 i)‖ ≤ K * B := by
  intro F E _ _ _ _ _ n d κ _ f
  classical
  let S : InfinitePlace F → κ → ℝ := fun w i =>
    (∑ k, ∑ l, ∑ r, ‖archAt F w ((f (Matrix.single k l (coB F E r))).1 i)‖) +
    ∑ k, ∑ l, ∑ r, ‖archAt F w ((f (Matrix.single k l (coB F E r))).2 i)‖
  have hS : ∀ w i, 0 ≤ S w i := fun w i => by positivity
  refine ⟨∑ w, ∑ i, S w i, Finset.sum_nonneg fun w _ => Finset.sum_nonneg fun i _ => hS w i, ?_⟩
  intro x B hB hx w i
  have hle : S w i ≤ ∑ w, ∑ i, S w i :=
    (Finset.single_le_sum (f := fun i => S w i) (fun i _ => hS w i) (Finset.mem_univ i)).trans
      (Finset.single_le_sum (f := fun w => ∑ i, S w i)
        (fun w _ => Finset.sum_nonneg fun i _ => hS w i) (Finset.mem_univ w))
  have h1 := arch_bound_functional F E n d ((LinearMap.proj i).comp ((LinearMap.fst _ _ _).comp f)) w x B hB (hx w)
  have h2 := arch_bound_functional F E n d ((LinearMap.proj i).comp ((LinearMap.snd _ _ _).comp f)) w x B hB (hx w)
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj, Function.eval,
    LinearMap.fst_apply, LinearMap.snd_apply] at h1 h2
  have hA : 0 ≤ ∑ k, ∑ l, ∑ r, ‖archAt F w ((f (Matrix.single k l (coB F E r))).1 i)‖ := by positivity
  have hC : 0 ≤ ∑ k, ∑ l, ∑ r, ‖archAt F w ((f (Matrix.single k l (coB F E r))).2 i)‖ := by positivity
  constructor
  · refine h1.trans ((mul_le_mul_of_nonneg_left ?_ hB).trans_eq (mul_comm _ _))
    exact (le_add_of_nonneg_right hC).trans hle
  · refine h2.trans ((mul_le_mul_of_nonneg_left ?_ hB).trans_eq (mul_comm _ _))
    exact (le_add_of_nonneg_left hA).trans hle

end GlobalTheory.ThetaDecay
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchBoundLinearMatrix
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDecay
open scoped TensorProduct NNReal Matrix

noncomputable section
namespace GlobalTheory.ThetaDecay

theorem piInf_algebraMap (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {w : InfinitePlace F} (τ : EmbOver E w) (a : AF F) :
    piInf τ (algebraMap (AF F) (AE F E) a) = archAt F w a := by
  change infEmb τ (compInf F E w (a ⊗ₜ[F] 1)) = _
  unfold compInf
  simp [archAt]

theorem linMap_archBound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n d : ℕ) (κ : Type) [Fintype κ]
    (f : (κ → AF F) × (κ → AF F) →ₗ[AF F] Matrix (Fin n) (Fin d) (AE F E)), ∃ K : ℝ, 0 ≤ K ∧
    ∀ (v : (κ → AF F) × (κ → AF F)) (B : ℝ), 0 ≤ B → (∀ w i, ‖archAt F w (v.1 i)‖ ≤ B ∧ ‖archAt F w (v.2 i)‖ ≤ B) →
    ∀ (w : InfinitePlace F) (τ : EmbOver E w) k l, ‖piInf τ (f v k l)‖ ≤ K * B := by
  intro F E _ _ _ _ _ n d κ _ f
  classical
  let e1 : κ → (κ → AF F) × (κ → AF F) := fun i => (Pi.single i 1, 0)
  let e2 : κ → (κ → AF F) × (κ → AF F) := fun i => (0, Pi.single i 1)
  let S : ∀ w : InfinitePlace F, EmbOver E w → Fin n → Fin d → ℝ := fun w τ k l =>
    ∑ i, (‖piInf τ (f (e1 i) k l)‖ + ‖piInf τ (f (e2 i) k l)‖)
  have hS : ∀ w τ k l, 0 ≤ S w τ k l := fun w τ k l =>
    Finset.sum_nonneg fun i _ => add_nonneg (norm_nonneg _) (norm_nonneg _)
  refine ⟨∑ w, ∑ τ : EmbOver E w, ∑ k, ∑ l, S w τ k l,
    Finset.sum_nonneg fun w _ => Finset.sum_nonneg fun τ _ => Finset.sum_nonneg fun k _ =>
      Finset.sum_nonneg fun l _ => hS w τ k l, ?_⟩
  intro v B hB hv w τ k l
  have hvdec : v = ∑ i, (v.1 i • e1 i + v.2 i • e2 i) := by
    refine Prod.ext (funext fun j => ?_) (funext fun j => ?_) <;>
      simp [e1, e2, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  have hfv : f v k l = ∑ i, (algebraMap (AF F) (AE F E) (v.1 i) * f (e1 i) k l +
      algebraMap (AF F) (AE F E) (v.2 i) * f (e2 i) k l) := by
    conv_lhs => rw [hvdec]
    simp only [map_sum, map_add, LinearMap.map_smul, Matrix.sum_apply, Matrix.add_apply, Matrix.smul_apply]
    simp only [Algebra.smul_def]
  have h1 : ‖piInf τ (f v k l)‖ ≤ B * S w τ k l := by
    rw [hfv, map_sum]
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [map_add, map_mul, map_mul, piInf_algebraMap, piInf_algebraMap, mul_add]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_mul]
    · exact mul_le_mul_of_nonneg_right (hv w i).1 (norm_nonneg _)
    · exact mul_le_mul_of_nonneg_right (hv w i).2 (norm_nonneg _)
  have h2 : S w τ k l ≤ ∑ w, ∑ τ : EmbOver E w, ∑ k, ∑ l, S w τ k l := by
    refine le_trans ?_ (Finset.single_le_sum (f := fun w => ∑ τ : EmbOver E w, ∑ k, ∑ l, S w τ k l)
      (fun w _ => Finset.sum_nonneg fun τ _ => Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ => hS w τ k l)
      (Finset.mem_univ w))
    refine le_trans ?_ (Finset.single_le_sum (f := fun τ => ∑ k, ∑ l, S w τ k l)
      (fun τ _ => Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ => hS w τ k l) (Finset.mem_univ τ))
    refine le_trans ?_ (Finset.single_le_sum (f := fun k => ∑ l, S w τ k l)
      (fun k _ => Finset.sum_nonneg fun l _ => hS w τ k l) (Finset.mem_univ k))
    exact Finset.single_le_sum (f := fun l => S w τ k l) (fun l _ => hS w τ k l) (Finset.mem_univ l)
  calc ‖piInf τ (f v k l)‖ ≤ B * S w τ k l := h1
    _ ≤ B * ∑ w, ∑ τ : EmbOver E w, ∑ k, ∑ l, S w τ k l := mul_le_mul_of_nonneg_left h2 hB
    _ = _ := mul_comm _ _

end GlobalTheory.ThetaDecay
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchBoundUnitaryAction
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDecay
open scoped TensorProduct NNReal Matrix

noncomputable section

namespace GlobalTheory.WeilDirBound

open GlobalTheory.AdelicU

theorem norm_entry_le_opNorm {m : Type} [Fintype m] [DecidableEq m] (A : Matrix m m ℂ) (i k : m) :
    ‖A i k‖ ≤ (opNorm A : ℝ) := by
  have h1 : Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ) A (EuclideanSpace.single k 1) =
      WithLp.toLp 2 (A *ᵥ Pi.single k 1) := Matrix.toEuclideanCLM_toLp A _
  have h2 : (A *ᵥ Pi.single k (1 : ℂ)) i = A i k := by simp
  calc ‖A i k‖ = ‖(Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ) A (EuclideanSpace.single k 1)).ofLp i‖ := by
        rw [h1, ← h2]
    _ ≤ ‖Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ) A (EuclideanSpace.single k 1)‖ := PiLp.norm_apply_le _ _
    _ ≤ ‖Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ) A‖ * ‖EuclideanSpace.single k (1 : ℂ)‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ = (opNorm A : ℝ) := by rw [EuclideanSpace.norm_single, norm_one, mul_one]; rfl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem norm_piInf_entry_le_heightGL {m : Type} [Fintype m] [DecidableEq m] (g : GL m (AF F ⊗[F] E))
    (w : InfinitePlace F) (τ : EmbOver E w) (i k : m) :
    ‖piInf τ ((g : Matrix m m (AF F ⊗[F] E)) i k)‖ ≤ (heightGL F g : ℝ) := by
  have e : piInf τ ((g : Matrix m m (AF F ⊗[F] E)) i k) =
      (((Formalism.UG.bc (compInf F E w) g : GL m (w.Completion ⊗[F] E)) : Matrix m m _).map (infEmb τ)) i k := rfl
  rw [e]
  refine (norm_entry_le_opNorm _ i k).trans ?_
  have h1 : opNorm (((Formalism.UG.bc (compInf F E w) g : GL m (w.Completion ⊗[F] E)) : Matrix m m _).map (infEmb τ))
      ≤ heightGL F g := by
    refine ((normInf_le_iff F w).1 le_rfl τ).trans ((le_htOf _ _).trans ?_)
    refine le_trans ?_ (le_mul_of_one_le_right' (one_le_finprod' fun _ => one_le_htOf _ _))
    exact Finset.single_le_prod' (f := fun w => htInf F w (Formalism.UG.bc (compInf F E w) g))
      (fun _ _ => one_le_htOf _ _) (Finset.mem_univ w)
  exact_mod_cast h1

end GlobalTheory.WeilDirBound

end

namespace GlobalTheory.WeilDirBound

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem norm_piInf_actAB_le (σ : E →ₐ[F] E) (n d : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (J' : Matrix (Fin d) (Fin d) E) (p : UA σ J × UA σ J')
    (x : Matrix (Fin n) (Fin d) (AE F E)) (B : ℝ) (hB : 0 ≤ B)
    (hx : ∀ (w : InfinitePlace F) (τ : EmbOver E w) k l, ‖piInf τ (x k l)‖ ≤ B) :
    ∀ (w : InfinitePlace F) (τ : EmbOver E w) i j,
      ‖piInf τ (actAB (cA σ) p x i j)‖ ≤ n * d * ((ht p.1 : ℝ) * ht p.2) * B := by
  intro w τ i j
  set g : GL (Fin n) (AF F ⊗[F] E) := (p.1 : GL (Fin n) (AF F ⊗[F] E)) with hg
  set h : GL (Fin d) (AF F ⊗[F] E) := (p.2 : GL (Fin d) (AF F ⊗[F] E)) with hh
  have hg1 : (ht p.1 : ℝ) = heightGL F g := rfl
  have hh1 : (ht p.2 : ℝ) = heightGL F h := rfl
  have e : actAB (cA σ) p x i j = ∑ l, ∑ k,
      (g : Matrix (Fin n) (Fin n) _) i k * x k l * (h : Matrix (Fin d) (Fin d) _) j l := by
    simp only [actAB, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    rfl
  have hG := fun k => norm_piInf_entry_le_heightGL g w τ i k
  have hH := fun l => norm_piInf_entry_le_heightGL h w τ j l
  have hG0 : (0 : ℝ) ≤ heightGL F g := NNReal.coe_nonneg _
  have hH0 : (0 : ℝ) ≤ heightGL F h := NNReal.coe_nonneg _
  rw [e, hg1, hh1]
  calc ‖piInf τ (∑ l, ∑ k, (g : Matrix (Fin n) (Fin n) _) i k * x k l * (h : Matrix (Fin d) (Fin d) _) j l)‖
      ≤ ∑ l : Fin d, ∑ k : Fin n, ((heightGL F g : ℝ) * heightGL F h * B) := by
        rw [map_sum]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
        rw [map_sum]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
        rw [map_mul, map_mul, norm_mul, norm_mul]
        calc ‖piInf τ ((g : Matrix (Fin n) (Fin n) _) i k)‖ * ‖piInf τ (x k l)‖ *
              ‖piInf τ ((h : Matrix (Fin d) (Fin d) _) j l)‖
            ≤ (heightGL F g : ℝ) * B * heightGL F h :=
              mul_le_mul (mul_le_mul (hG k) (hx w τ k l) (norm_nonneg _) hG0) (hH l) (norm_nonneg _)
                (mul_nonneg hG0 hB)
          _ = (heightGL F g : ℝ) * heightGL F h * B := by ring
    _ = n * d * ((heightGL F g : ℝ) * heightGL F h) * B := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end GlobalTheory.WeilDirBound

theorem GlobalTheory.WeilDirBound.norm_piInf_actAB_le_target : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (J' : Matrix (Fin d) (Fin d) E) (p : UA σ J × UA σ J')
    (x : Matrix (Fin n) (Fin d) (AE F E)) (B : ℝ), 0 ≤ B →
    (∀ (w : InfinitePlace F) (τ : EmbOver E w) k l, ‖piInf τ (x k l)‖ ≤ B) →
    ∀ (w : InfinitePlace F) (τ : EmbOver E w) i j,
      ‖piInf τ (actAB (cA σ) p x i j)‖ ≤ n * d * ((ht p.1 : ℝ) * ht p.2) * B :=
  fun F E _ _ _ _ _ σ n d J J' p x B hB hx => GlobalTheory.WeilDirBound.norm_piInf_actAB_le σ n d J J' p x B hB hx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanCoordsMovedStaySupportedAndRecovered
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay

namespace GlobalTheory.ArchDecay

theorem at_mul_of_at {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {n d : ℕ} (G : Matrix (Fin n) (Fin n) (AE F E)) (H : Matrix (Fin d) (Fin d) (AE F E))
    (L : Matrix (Fin n) (Fin d) (AE F E)) (hL : At (evI F) L) : At (evI F) (G * L * Hᵀ) := by
  intro u hu
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, hL u hu, Matrix.mul_zero, Matrix.zero_mul]

theorem mul_infAd_of_evI {F : Type} [Field F] [NumberField F] (u : AF F) (hu : evI F u = 0)
    (α : mixedEmbedding.mixedSpace F) : u * infAd F α = 0 := by
  have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.mp hu
  refine Prod.ext ?_ ?_
  · show u.1 * _ = 0
    rw [h1, zero_mul]
  · show u.2 * 0 = 0
    rw [mul_zero]

theorem eq_infAd_of_ann {F : Type} [Field F] [NumberField F] (z : AF F)
    (hz : ∀ a : AF F, evI F a = 0 → a * z = 0) : z = infAd F (evI F z) := by
  obtain ⟨a, ha1, ha2⟩ : ∃ a : AF F, a.1 = 0 ∧ a.2 = 1 := ⟨(0, 1), rfl, rfl⟩
  have h0 : evI F a = 0 := by
    have e : evI F a = InfiniteAdeleRing.ringEquiv_mixedSpace F a.1 := rfl
    rw [e, ha1, map_zero]
  have h2 : z.2 = 0 := by
    have h3 := congrArg Prod.snd (hz a h0)
    have h4 : (a * z).2 = a.2 * z.2 := rfl
    rw [h4, ha2, one_mul] at h3
    exact h3
  refine Prod.ext ?_ ?_
  · show z.1 = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (InfiniteAdeleRing.ringEquiv_mixedSpace F z.1)
    rw [RingEquiv.symm_apply_apply]
  · show z.2 = 0
    exact h2

theorem liftI_at_movI : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (p : UA σ X.J × UA σ W.J) (ζ : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)), At (evI F) (liftI M ζ) ∧ liftI M (movI M p ζ) = actAB (cA σ) p⁻¹ (liftI M ζ) := by
  intro F E _ _ _ _ _ σ n d X W M p ζ
  have hL : At (evI F) (liftI M ζ) := by
    intro u hu
    unfold liftI
    rw [← LinearEquiv.map_smul]
    convert (M.co.e.symm).map_zero using 2
    refine Prod.ext ?_ ?_
    · funext i
      exact mul_infAd_of_evI u hu _
    · funext i
      exact mul_infAd_of_evI u hu _
  refine ⟨hL, ?_⟩
  have hw : At (evI F) (actAB (cA σ) p⁻¹ (liftI M ζ)) := at_mul_of_at _ _ _ hL
  set w := actAB (cA σ) p⁻¹ (liftI M ζ) with hwdef
  have hc : ∀ u : AF F, evI F u = 0 → u • M.co.e w = 0 := by
    intro u hu
    rw [← LinearEquiv.map_smul, hw u hu, LinearEquiv.map_zero]
  unfold liftI movI arch
  conv_rhs => rw [← M.co.e.symm_apply_apply w]
  congr 1
  refine Prod.ext ?_ ?_
  · funext i
    exact (eq_infAd_of_ann _ fun a ha => congrFun (congrArg Prod.fst (hc a ha)) i).symm
  · funext i
    exact (eq_infAd_of_ann _ fun a ha => congrFun (congrArg Prod.snd (hc a ha)) i).symm

end GlobalTheory.ArchDecay
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanDecayOperatorApplyMemAdelicSchwartzStatement
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanDecayOperatorApply_mem_adelicSchwartz : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (o : Op F κ), ∀ f ∈ schA F κ, app F o f ∈ schA F κ := by
  first | exact @GlobalTheory.ArchDecay.SchAStab.app_mem_schA | exact GlobalTheory.ArchDecay.SchAStab.app_mem_schA | (intros; apply GlobalTheory.ArchDecay.SchAStab.app_mem_schA <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BadPartDimLeSumLocalSharesWhittakerStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bad_part_dim_le_sum_local_shares_whittaker : ∀ (D : D7) (Γ V : Type) [Group Γ] [Finite Γ] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (π : Γ →* G0g D.nd) (ι : G0g D.nd →* Γ), IsSplit π ι → ∀ (ρ : Representation ℂ Γ V) (P : Subgroup (G0g D.nd)) (lam : P →* ℂˣ) (ψ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ), IsWhit D P lam ψ → ∀ (lamb : P.comap π →* ℂˣ), (∀ γ : P.comap π, lamb γ = lam ⟨π γ, γ.2⟩) → ∀ (H : Fin 2 → Subgroup (G0g D.nd)), (∀ k, IsHalf D k (H k)) → ∀ (n : Fin 2 → ℕ) (c : ℝ), (∀ k, EmbReg ρ ((H k).comap π) (n k)) → (∀ k, (n k : ℝ) * Nat.card ((H k).comap π) ≤ c * Nat.card (P.comap π) * finrank ℂ (eig ρ (P.comap π) lamb)) → ∀ ψ₀ : ∀ k : Fin 2, AddChar (ZMod (D.host.g k)) ℂ, (∀ k, ψ₀ k ≠ 1) → ∃ S : ∀ k : Fin 2, Finset (Tup D k), (∀ k, ∀ t ∈ S k, ¬ goodAt D k t) ∧ (finrank ℂ (eig ρ (P.comap π) lamb ⊓ LinearMap.ker (Representation.asAlgebraHom (ρ.comp ι : Representation ℂ (G0g D.nd) V) D.ntypes.e0) : Submodule ℂ V) : ℝ) ≤ c * (locShare D (fun k _ => eUk D k (ψ₀ k)) 0 (S 0) + locShare D (fun k _ => eUk D k (ψ₀ k)) 1 (S 1)) * finrank ℂ (eig ρ (P.comap π) lamb) := by
  first | exact @GlobalTheory.BadCount.bad_part_le_locShare | exact GlobalTheory.BadCount.bad_part_le_locShare | (intros; apply GlobalTheory.BadCount.bad_part_le_locShare <;> assumption)
end

