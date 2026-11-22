import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0066
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0209
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1439
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1340
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1344
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSplitFinMulSplitInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1422
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1406
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1421
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1440
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegFamOfContinuousAt
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThK.DblKer

open Classical in

def regFam {Y : Type} (Ei : ℂ → Y → ℂ) (s : ℂ) (y : Y) : ℂ :=
  if h : ∀ y, ∃ c, Tendsto (fun t => Ei t y) (𝓝[≠] s) (𝓝 c) then (h y).choose else 0

theorem regFam_eq_of_tendsto {Y : Type} {Ei : ℂ → Y → ℂ} {s : ℂ} {v : Y → ℂ}
    (h : ∀ y, Tendsto (fun t => Ei t y) (𝓝[≠] s) (𝓝 (v y))) (y : Y) : regFam Ei s y = v y := by
  have h' : ∀ y, ∃ c, Tendsto (fun t => Ei t y) (𝓝[≠] s) (𝓝 c) := fun y => ⟨v y, h y⟩
  rw [regFam, dif_pos h']
  exact tendsto_nhds_unique (h' y).choose_spec (h y)

theorem regFam_of_continuousAt {Y : Type} {Ei : ℂ → Y → ℂ} {s : ℂ} (h : ∀ y, ContinuousAt (fun t => Ei t y) s)
    (y : Y) : regFam Ei s y = Ei s y :=
  regFam_eq_of_tendsto (fun y => (h y).tendsto.mono_left nhdsWithin_le_nhds) y

theorem regFam_of_not {Y : Type} {Ei : ℂ → Y → ℂ} {s : ℂ}
    (h : ¬ ∀ y, ∃ c, Tendsto (fun t => Ei t y) (𝓝[≠] s) (𝓝 c)) (y : Y) : regFam Ei s y = 0 := by
  rw [regFam, dif_neg h]

example {Y : Type} (f : Y → ℂ) (s : ℂ) (y : Y) : regFam (fun _ => f) s y = f y :=
  regFam_of_continuousAt (Ei := fun _ => f) (s := s) (fun y => continuousAt_const (y := f y)) y

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def chiInv (χ : Chr F E) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (h : UA σ J) : ℂ :=
  (((χ (Matrix.GeneralLinearGroup.det h.1))⁻¹ : Circle) : ℂ)

def dblKer {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E} (κ : ℂ)
    (Ei : ℂ → UA σ J₂ → ℂ) (i : UA σ J × UA σ J →* UA σ J₂) (χ : Chr F E) (s : ℂ) (h h' : UA σ J) : ℂ :=
  κ * (regFam Ei s (i (h, h')) * chiInv χ h')

def dbl {n : ℕ} (W : Spc F E n) : Spc F E (n + n) where
  J := GlobalTheory.Doubling.dblGram finSumFinEquiv W.J
  L := GlobalTheory.Doubling.sumLat finSumFinEquiv W.L W.L
  θ := fun w => GlobalTheory.Doubling.blkMat finSumFinEquiv (W.θ w) (-W.θ w)
  bas := fun _ => 1

end GlobalTheory.ThK.DblKer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzCoordinatesInInfiniteFamily
section
open scoped TensorProduct ENNReal Matrix Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SchwartzCoord

variable {D : D7}

theorem repr_map {R : Type} [CommRing R] [Algebra D.host.F R] (π : AF D.host.F →ₐ[D.host.F] R) {d : ℕ}
    (ε : Module.Basis (Fin d) D.host.F D.host.E) (z : AE D) (k : Fin d) :
    π ((Algebra.TensorProduct.basis (AF D.host.F) ε).repr z k) =
      (Algebra.TensorProduct.basis R ε).repr (Algebra.TensorProduct.map π (AlgHom.id D.host.F D.host.E) z) k := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp [Algebra.TensorProduct.basis_repr_tmul, Algebra.TensorProduct.map_tmul, Finsupp.mapRange_apply]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

end GlobalTheory.SchwartzCoord

namespace GlobalTheory.SchwartzCoord
variable {D : D7}
theorem finPart_eq (z : AE D) : finPart D z = Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) z := rfl
theorem infPart_eq (z : AE D) : infPart D z = Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) z := rfl
theorem snd_eq (a : AF D.host.F) : a.2 = sndA D.host.F a := rfl
theorem fin_coord {d : ℕ} (ε : Module.Basis (Fin d) D.host.F D.host.E) (z : AE D) (k : Fin d) :
    ((Algebra.TensorProduct.basis (AF D.host.F) ε).repr z k).2 =
      (Algebra.TensorProduct.basis (Af D.host.F) ε).repr (finPart D z) k := by
  rw [snd_eq, finPart_eq]
  exact repr_map (sndA D.host.F) ε z k
end GlobalTheory.SchwartzCoord

namespace GlobalTheory.SchwartzCoord

variable {D : D7}

def finCoord {m n d : ℕ} (ε : Module.Basis (Fin d) D.host.F D.host.E) :
    (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) ≃ₜ (Fin m × Fin n × Fin d → Af D.host.F) := by
  haveI : IsModuleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (Af D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (Af D.host.F) _
  let b := Algebra.TensorProduct.basis (Af D.host.F) ε
  exact
  { toFun := fun y p => b.equivFun (y p.1 p.2.1) p.2.2
    invFun := fun c i j => b.equivFun.symm fun k => c (i, j, k)
    left_inv := fun y => by
      funext i j
      simp only
      conv_rhs => rw [← b.equivFun.symm_apply_apply (y i j)]
    right_inv := fun c => by
      funext p
      simp only [LinearEquiv.apply_symm_apply]
    continuous_toFun := continuous_pi fun p =>
      ((continuous_apply p.2.2).comp (IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap)).comp
        ((continuous_apply p.2.1).comp (continuous_apply p.1))
    continuous_invFun := continuous_pi fun i => continuous_pi fun j =>
      (IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap).comp
        (continuous_pi fun k => continuous_apply (i, j, k)) }

theorem finCoord_apply {m n d : ℕ} (ε : Module.Basis (Fin d) D.host.F D.host.E)
    (y : Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) (p : Fin m × Fin n × Fin d) :
    finCoord ε y p = (Algebra.TensorProduct.basis (Af D.host.F) ε).repr (y p.1 p.2.1) p.2.2 := by
  simp [finCoord]

end GlobalTheory.SchwartzCoord

namespace GlobalTheory.SchwartzCoord

variable {D : D7}

theorem continuous_mixed (F : Type) [Field F] [NumberField F] :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  have : (InfiniteAdeleRing.ringEquiv_mixedSpace F : InfiniteAdeleRing F → mixedEmbedding.mixedSpace F) =
      fun x => ((fun v : {w : InfinitePlace F // InfinitePlace.IsReal w} =>
          InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
        (fun v : {w : InfinitePlace F // InfinitePlace.IsComplex w} =>
          InfinitePlace.Completion.extensionEmbedding v.1 (x v))) := by
    funext x; exact InfiniteAdeleRing.ringEquiv_mixedSpace_apply F x
  rw [this]
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp
      (continuous_apply _)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp
      (continuous_apply _)

def realCoord (σ : (D.what₂.Tau → ℂ) →+ AE D) {m n d : ℕ} (ε : Module.Basis (Fin d) D.host.F D.host.E) :
    (D.what₂.Tau → Fin m → Fin n → ℂ) →+ (Fin m × Fin n × Fin d → mixedEmbedding.mixedSpace D.host.F) where
  toFun c p := InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F
    (fstA D.host.F ((Algebra.TensorProduct.basis (AF D.host.F) ε).repr (σ fun τ => c τ p.1 p.2.1) p.2.2))
  map_zero' := by
    funext p
    have : (σ fun τ => (0 : D.what₂.Tau → Fin m → Fin n → ℂ) τ p.1 p.2.1) = 0 := σ.map_zero
    show InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F (fstA D.host.F
      ((Algebra.TensorProduct.basis (AF D.host.F) ε).repr (σ fun τ => (0 : D.what₂.Tau → Fin m → Fin n → ℂ) τ p.1 p.2.1)
        p.2.2)) = 0
    rw [this, map_zero, Finsupp.zero_apply, map_zero, map_zero]
  map_add' c c' := by
    funext p
    have : (σ fun τ => (c + c') τ p.1 p.2.1) = σ (fun τ => c τ p.1 p.2.1) + σ (fun τ => c' τ p.1 p.2.1) :=
      σ.map_add _ _
    show InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F (fstA D.host.F
      ((Algebra.TensorProduct.basis (AF D.host.F) ε).repr (σ fun τ => (c + c') τ p.1 p.2.1) p.2.2)) = _
    rw [this, map_add, Finsupp.add_apply, map_add, map_add]
    rfl

theorem continuous_realCoord {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : Continuous σ) {m n d : ℕ}
    (ε : Module.Basis (Fin d) D.host.F D.host.E) : Continuous (realCoord σ (m := m) (n := n) ε) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  refine continuous_pi fun p => (continuous_mixed D.host.F).comp (continuous_fst.comp ?_)
  exact ((continuous_apply p.2.2).comp (IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.basis (AF D.host.F) ε).equivFun.toLinearMap)).comp
    (hσ.comp (continuous_pi fun τ => (continuous_apply p.2.1).comp ((continuous_apply p.1).comp (continuous_apply τ))))

end GlobalTheory.SchwartzCoord

namespace GlobalTheory.SchwartzCoord

variable {D : D7}

theorem finCoord_coord {m n d : ℕ} (ε : Module.Basis (Fin d) D.host.F D.host.E) (x : Mx D m n) :
    (fun p => (coord ε x p).2) = finCoord ε (fun i j => finPart D (x i j)) := by
  funext p
  rw [finCoord_apply]
  exact fin_coord ε (x p.1 p.2.1) p.2.2

theorem inf_coord {d : ℕ} (ε : Module.Basis (Fin d) D.host.F D.host.E) (z : AE D) (k : Fin d) :
    ((Algebra.TensorProduct.basis (AF D.host.F) ε).repr z k).1 =
      (Algebra.TensorProduct.basis (Ainf D.host.F) ε).repr (infPart D z) k := by
  rw [infPart_eq]
  exact repr_map (fstA D.host.F) ε z k

theorem realCoord_compAt {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ)
    {s : (Af D.host.F ⊗[D.host.F] D.host.E) →+ AE D} (hsf : ∀ a, finPart D (s a) = a) (hsi : ∀ a, infPart D (s a) = 0)
    {m n d : ℕ} (ε : Module.Basis (Fin d) D.host.F D.host.E) (x : Mx D m n) :
    (fun p => InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F (coord ε x p).1) =
      realCoord σ ε (fun τ i j => compAt θ τ x i j) := by
  funext p
  have hx : x p.1 p.2.1 = s (finPart D (x p.1 p.2.1)) + σ (fun τ => compAt θ τ x p.1 p.2.1) :=
    congrFun (congrFun (GlobalTheory.SchwartzBruhatTensor.decomp hσ hsf hsi x) p.1) p.2.1
  have h0 : fstA D.host.F ((Algebra.TensorProduct.basis (AF D.host.F) ε).repr (s (finPart D (x p.1 p.2.1))) p.2.2) = 0 :=
    (inf_coord ε _ _).trans (by rw [hsi, map_zero, Finsupp.zero_apply])
  show InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F
      (fstA D.host.F ((Algebra.TensorProduct.basis (AF D.host.F) ε).repr (x p.1 p.2.1) p.2.2)) =
    InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F
      (fstA D.host.F ((Algebra.TensorProduct.basis (AF D.host.F) ε).repr (σ fun τ => compAt θ τ x p.1 p.2.1) p.2.2))
  conv_lhs => rw [hx]
  rw [map_add, Finsupp.add_apply, map_add (fstA D.host.F), h0, zero_add]

end GlobalTheory.SchwartzCoord

namespace GlobalTheory.SchwartzCoord

variable {D : D7}

theorem injective_realCoord {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) {m n d : ℕ}
    (ε : Module.Basis (Fin d) D.host.F D.host.E) : Function.Injective (realCoord σ (m := m) (n := n) ε) := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  funext τ i j
  have h0 : infPart D (σ fun τ => c τ i j) = 0 := by
    apply (Algebra.TensorProduct.basis (Ainf D.host.F) ε).repr.injective
    ext k
    rw [map_zero, Finsupp.zero_apply]
    have e : InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F
        (fstA D.host.F ((Algebra.TensorProduct.basis (AF D.host.F) ε).repr (σ fun τ => c τ i j) k)) = 0 :=
      congrFun hc (i, j, k)
    have e2 := (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).injective).1 e
    rw [← e2, repr_map (fstA D.host.F) ε]
    rfl
  have h1 := hσ.comp (fun τ => c τ i j) τ
  rw [h0, map_zero] at h1
  exact h1.symm

theorem mem_schwartzA_comp_coord : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n d : ℕ)
    (ε : Module.Basis (Fin d) D.host.F D.host.E) (φ : WeilM.schA D.host.F (Fin m × Fin n × Fin d)),
    φ.1 ∘ coord ε ∈ GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ m n := by
  intro D θ hθ m n d ε φ
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨s, -, hsf, hsi⟩ := GlobalTheory.SchwartzBruhatTensor.exists_finSection D
  obtain ⟨M, hM⟩ : ∃ M : (D.what₂.Tau → Fin m → Fin n → ℂ) →L[ℝ] (Fin m × Fin n × Fin d → mixedEmbedding.mixedSpace D.host.F),
      ⇑M = ⇑(realCoord σ ε) := ⟨(realCoord σ ε).toRealLinearMap (continuous_realCoord hσ.cont ε), rfl⟩
  have hMi : Function.Injective M.toLinearMap := by
    intro a b h
    have h' : M a = M b := h
    rw [hM] at h'
    exact injective_realCoord hσ ε h'
  obtain ⟨K, -, hK⟩ := (LinearMap.injective_iff_antilipschitz _).1 hMi
  have hbound : ∃ (k : ℕ) (C : ℝ), ∀ x, ‖x‖ ≤ C * (1 + ‖M x‖) ^ k := ⟨1, K, fun x => by
    have h := hK.le_mul_dist x 0
    rw [dist_zero_right, map_zero, dist_zero_right] at h
    have hK0 : (0 : ℝ) ≤ K := K.coe_nonneg
    calc ‖x‖ ≤ K * ‖M x‖ := h
      _ ≤ K * (1 + ‖M x‖) ^ 1 := by rw [pow_one]; exact mul_le_mul_of_nonneg_left (by linarith) hK0⟩
  obtain ⟨φ, hφ⟩ := φ
  induction hφ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    let f' : SchwartzMap (D.what₂.Tau → Fin m → Fin n → ℂ) ℂ := SchwartzMap.compCLM ℂ M.hasTemperateGrowth hbound f
    have hf' : ∀ c, f' c = f (M c) := fun c => rfl
    let g' : (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ := g ∘ finCoord ε
    have hg' : g' ∈ WeilM.SB (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) :=
      ⟨hg.1.comp_continuous (finCoord ε).continuous, hg.2.comp_homeomorph _⟩
    have heq : WeilM.pureA D.host.F f g ∘ coord ε =
        fun x => f' (fun τ i j => compAt θ τ x i j) * g' (fun i j => finPart D (x i j)) := by
      funext x
      rw [hf']
      show f (fun p => InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F (coord ε x p).1) * g (fun p => (coord ε x p).2) =
        f (M (fun τ i j => compAt θ τ x i j)) * g (finCoord ε (fun i j => finPart D (x i j)))
      rw [realCoord_compAt hσ hsf hsi ε x, finCoord_coord ε x, ← hM]
    rw [heq]
    exact Submodule.subset_span ⟨f', g', hg', rfl⟩
  | zero =>
    have e : (0 : (Fin m × Fin n × Fin d → AdeleRing (𝓞 D.host.F) D.host.F) → ℂ) ∘ coord ε = 0 := rfl
    rw [e]
    exact Submodule.zero_mem _
  | add Φ Ψ _ _ h1 h2 =>
    have e : (Φ + Ψ) ∘ coord ε = Φ ∘ coord ε + Ψ ∘ coord ε := rfl
    rw [e]
    exact Submodule.add_mem _ h1 h2
  | smul a Φ _ h =>
    have e : (a • Φ) ∘ coord ε = a • (Φ ∘ coord ε) := rfl
    rw [e]
    exact Submodule.smul_mem _ a h

end GlobalTheory.SchwartzCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelTorusElementInvFinitePartOneDualFrameEigen
section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TorusInv

theorem dual_mul_compl {R : Type} [CommRing R] {m r : ℕ} (X Y : Matrix (Fin m) (Fin r) R)
    (X' Y' : Matrix (Fin r) (Fin m) R) (xx : X' * X = 0) (yy : Y' * Y = 0) (xy : X' * Y = 1) (yx : Y' * X = 1) :
    X' * (1 - X * Y' - Y * X') = 0 ∧ Y' * (1 - X * Y' - Y * X') = 0 := by
  constructor
  · rw [Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, xx, xy]; simp
  · rw [Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, yx, yy]; simp

theorem mapped {E : Type} [CommRing E] (f : E →+* ℂ) {m r : ℕ} (X Y : Matrix (Fin m) (Fin r) E)
    (X' Y' : Matrix (Fin r) (Fin m) E) (xx : X' * X = 0) (yy : Y' * Y = 0) (xy : X' * Y = 1) (yx : Y' * X = 1)
    (t : Fin r → ℝ) (ht : ∀ i, 0 < t i) (A B : Matrix (Fin m) (Fin m) ℂ)
    (hX : A * X.map f = X.map f * Matrix.diagonal (fun i => ((t i : ℝ) : ℂ)))
    (hY : A * Y.map f = Y.map f * Matrix.diagonal (fun i => ((t i : ℝ) : ℂ)⁻¹))
    (hz : ∀ z : Fin m → E, X' *ᵥ z = 0 → Y' *ᵥ z = 0 → A *ᵥ (fun i => f (z i)) = fun i => f (z i))
    (hAB : A * B = 1) :
    Y'.map f * B = Matrix.diagonal (fun i => ((t i : ℝ) : ℂ)⁻¹) * Y'.map f ∧
    X'.map f * B = Matrix.diagonal (fun i => ((t i : ℝ) : ℂ)) * X'.map f ∧
    (1 - X * Y' - Y * X').map f * B = (1 - X * Y' - Y * X').map f := by
  have hP : (1 - X * Y' - Y * X').map f = 1 - X.map f * Y'.map f - Y.map f * X'.map f := by
    rw [Matrix.map_sub _ (map_sub f), Matrix.map_sub _ (map_sub f), Matrix.map_mul, Matrix.map_mul,
      Matrix.map_one _ (map_zero f) (map_one f)]
  obtain ⟨k1, k2⟩ := dual_mul_compl X Y X' Y' xx yy xy yx
  have hA : A * (1 - X * Y' - Y * X').map f = (1 - X * Y' - Y * X').map f := by
    ext i j
    have := hz (fun k => (1 - X * Y' - Y * X' : Matrix (Fin m) (Fin m) E) k j)
      (by funext a; exact congrFun (congrFun k1 a) j) (by funext a; exact congrFun (congrFun k2 a) j)
    exact congrFun this i
  have hne : ∀ i, ((t i : ℝ) : ℂ) ≠ 0 := fun i => Complex.ofReal_ne_zero.2 (ht i).ne'
  rw [hP] at hA ⊢
  refine GlobalTheory.T.torusElement_dualFrameRows_eigen_inverse ℂ m r (X.map f) (Y.map f) (X'.map f) (Y'.map f) _ _ A B ?_ ?_ ?_ ?_ ?_ ?_ hX hY hA hAB
  · rw [← Matrix.map_mul, xx, Matrix.map_zero _ (map_zero f)]
  · rw [← Matrix.map_mul, yy, Matrix.map_zero _ (map_zero f)]
  · rw [← Matrix.map_mul, xy, Matrix.map_one _ (map_zero f) (map_one f)]
  · rw [← Matrix.map_mul, yx, Matrix.map_one _ (map_zero f) (map_one f)]
  · rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; exact mul_inv_cancel₀ (hne i)
  · rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; exact inv_mul_cancel₀ (hne i)

theorem torus_inv : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (t : Fin r → ℝ), (∀ i, 0 < t i) → ∀ a : GA D V, GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig V.gram X Y t a → (Formalism.L2.Theta.mt V a⁻¹).map (finPart D) = 1 ∧ ∀ τ, (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * V.gram).map (tauE D τ) * Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a⁻¹) = Matrix.diagonal (fun i => ((t i : ℝ) : ℂ)⁻¹) * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * V.gram).map (tauE D τ) ∧ (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram).map (tauE D τ) * Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a⁻¹) = Matrix.diagonal (fun i => ((t i : ℝ) : ℂ)) * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram).map (tauE D τ) ∧ (1 - X * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * V.gram) - Y * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram)).map (tauE D τ) * Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a⁻¹) = (1 - X * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * V.gram) - Y * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram)).map (tauE D τ) := by
  intro D θ hθ V r X Y hW t ht a ha
  obtain ⟨hf, hr⟩ := GlobalTheory.T.siegelTorusElement_real_components_of_frame D θ hθ V r X Y t a ha
  have h1 : Formalism.L2.Theta.mt V a * Formalism.L2.Theta.mt V a⁻¹ = 1 := by simp [Formalism.L2.Theta.mt]
  refine ⟨?_, fun τ => ?_⟩
  · have h2 := congrArg (fun M => Matrix.map M (finPart D)) h1
    rw [Matrix.map_mul, hf, Matrix.one_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h2
    exact h2
  · obtain ⟨hX, hY, hz⟩ := hr τ
    have hAB : Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a) *
        Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a⁻¹) = 1 := by
      have h3 : Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a * Formalism.L2.Theta.mt V a⁻¹) =
          Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a) * Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a⁻¹) :=
        Matrix.map_mul (f := (θ τ).comp (infPart D))
      rw [← h3, h1]
      exact Matrix.map_one _ (map_zero ((θ τ).comp (infPart D))) (map_one ((θ τ).comp (infPart D)))
    exact mapped (tauE D τ) X Y _ _ hW.xx hW.yy hW.xy (GlobalTheory.T.witt_frame_conjugate_gram_inv D V r X Y hW) t ht _ _ hX hY hz hAB

end GlobalTheory.TorusInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianTwistToHermitian
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.SkewToHerm

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem exists_sigma_ne {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) : ∃ x : E, σ x ≠ x := by
  by_contra hc
  push_neg at hc
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hτ : NumberField.ComplexEmbedding.IsReal τ := by
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext x
    simp only [NumberField.ComplexEmbedding.conjugate_coe_eq]
    have e := h.2.2.2 τ x
    rw [hc x] at e
    exact e.symm
  have hc' := h.2.1.isComplex (NumberField.InfinitePlace.mk τ)
  rw [← NumberField.InfinitePlace.not_isReal_iff_isComplex] at hc'
  exact hc' ⟨τ, hτ, rfl⟩

theorem det_ne_zero_of_hasSig {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (r s : ℕ) (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  subst hrs
  let e : Fin r ⊕ Fin s ≃ Fin (r + s) := finSumFinEquiv
  let A' : Matrix (Fin (r + s)) (Fin (r + s)) ℂ := A.submatrix id e.symm
  have hA' : A'ᵀ * M * A'.map star = (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix e.symm e.symm := by
    rw [← hA]
    ext i j
    simp [A', Matrix.mul_apply]
  have hd : (A'ᵀ * M * A'.map star).det ≠ 0 := by
    rw [hA', Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg]
    simp
  intro h0
  apply hd
  rw [Matrix.det_mul, Matrix.det_mul, h0]
  simp

theorem sigma_invol {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem exists_hermND (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hCM : IsCMExt F E σ) (B : Base F E) (n : ℕ) (W : Spc F E n) (r s : ℕ) (hW : W.IsSkew σ B r s) :
    ∃ c₀ : E, c₀ ≠ 0 ∧ IsHermND σ (c₀ • W.J.map σ) := by
  obtain ⟨x, hx⟩ := exists_sigma_ne σ hCM
  have hss := sigma_invol σ hCM
  refine ⟨x - σ x, sub_ne_zero.mpr (Ne.symm hx), fun i j => ?_, ?_⟩
  · simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, map_sub, hss]
    rw [hW.skew j i]
    ring
  · have hdet : (W.J.map σ).det = σ W.J.det := by rw [AlgHom.map_det]; rfl
    rw [Matrix.det_smul, hdet]
    refine mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm hx))) ?_
    rw [map_ne_zero_iff σ σ.toRingHom.injective]
    obtain ⟨w⟩ : Nonempty (NumberField.InfinitePlace F) := inferInstance
    have hd := det_ne_zero_of_hasSig _ r s (hW.sig w)
    have hdτ : (W.J.map (B.emb w).1).det = (B.emb w).1 W.J.det := by rw [RingHom.map_det]; rfl
    rw [Matrix.det_smul, hdτ] at hd
    intro h0
    apply hd
    rw [h0, map_zero, mul_zero]

theorem skew_to_hermND : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (B : Base F E) (n : ℕ) (W : Spc F E n) (r s : ℕ), W.IsSkew σ B r s → ∃ c₀ : E, c₀ ≠ 0 ∧ IsHermND σ (c₀ • W.J.map σ) :=
  fun F E _ _ _ _ _ σ hCM B n W r s hW => exists_hermND F E σ hCM B n W r s hW

end GlobalTheory.SkewToHerm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanRealPointsWeightRepresentationEqTop
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct Topology
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.TrKer

theorem span_range_wInf_comp_infU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (lam : InfinitePlace E → DomWeight n),
    Submodule.span ℂ (Set.range ((wInf lam).comp (infU E n).subtype)) = ⊤ := by
  intro E _ _ _ n lam
  exact span_wInf lam

end GlobalTheory.BCT.TrKer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemAdelicSchwartzSpaceNumberFieldStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.star_mem_adelicSchwartzSpaceNumberField : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (Φ : (κ → AF F) → ℂ), Φ ∈ schA F κ → (fun x => star (Φ x)) ∈ schA F κ := by
  first | exact @GlobalTheory.SchAConj.star_mem_schA | exact GlobalTheory.SchAConj.star_mem_schA | (intros; apply GlobalTheory.SchAConj.star_mem_schA <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupportedAdelicUnitaryPointOfLocalMatrixStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.supported_adelic_unitary_point_of_local_matrix : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : Pl F) (n : ℕ) (X : Spc F E n) (L : Type) [Field L]
    (ι : L →+ AE F E), (∀ z : AE F E, At (evFin F v) z ↔ ∃ x, ι x = z) →
      ∀ (g : UA σ X.J) (A : Matrix (Fin n) (Fin n) L),
        mat g = (1 - ι 1) • (1 : Matrix (Fin n) (Fin n) (AE F E)) + A.map ι → g ∈ UAt σ X (evFin F v) := by
  first | exact @GlobalTheory.InertLocFrame.uAt_of_local | exact GlobalTheory.InertLocFrame.uAt_of_local | (intros; apply GlobalTheory.InertLocFrame.uAt_of_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralLevelFunctionInertEqLatticStatement
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedOrbitalIntegral_levelFunction_inert_eq_latticeCount : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → qV E w = K.q ^ 2 → ∀ (k : ℕ) (t : K.O), K.Small t → GlobalTheory.UnitLemma.val K.O (algebraMap K.O K.E t) = k → ∀ (m : ℕ) (Q : (w.adicCompletion E)[X]) (B : GlobalTheory.UnitLemma.InvAlg K), Q.Monic → Q.natDegree = m → Q.Separable → IsCsr w Q → Algebra.adjoin K.E {(1 + algebraMap K.O B.A t * B.g)} = ⊤ → aeval (1 + algebraMap K.O B.A t * B.g) (Q.map e.symm.toRingHom) = 0 → Module.finrank K.E B.A = Q.natDegree → (1 + algebraMap K.O B.A t * B.g) * B.σ (1 + algebraMap K.O B.A t * B.g) = 1 → stTw m w Q (fun y : GLw m w => if y ∈ GlobalTheory.LFun.KGL w m ∧ nrmL m w y ∈ {g : GLw m w | g ∈ GlobalTheory.LFun.KGL w m ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} then 1 else 0) = ((B.stSum : ℚ) : ℂ) := by
  first | exact @GlobalTheory.TwOrbLevel.twOrb_level_eq_stSum | exact GlobalTheory.TwOrbLevel.twOrb_level_eq_stSum | (intros; apply GlobalTheory.TwOrbLevel.twOrb_level_eq_stSum <;> assumption)
end

