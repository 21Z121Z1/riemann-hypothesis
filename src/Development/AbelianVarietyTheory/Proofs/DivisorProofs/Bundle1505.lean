import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1446
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1444
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1479
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1478
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1459
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1460
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1480
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1466
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOneParameterLinesOfLieLines
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneVectorCcOfSiegelWeil
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1481
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1443
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1469
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1464
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1448

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineReps
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open IsDedekindDomain
open GlobalTheory.Doubling (absE absEv absEw)

namespace GlobalTheory.EisMidHt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

variable (F) in

def adVec (z : Fin n → E) : Fin n → AF F ⊗[F] E := fun i => inclR (F := F) (AF F) (z i)

def firstColumn {r : ℕ} (X : Matrix (Fin n) (Fin (r + 1)) E) : Fin n → E := fun i => X i 0

variable (F) in

def normFin (L : Submodule (𝓞 E) (Fin n → E)) (v : HeightOneSpectrum (𝓞 F)) (u : Fin n → Fv F v ⊗[F] E) : ℝ≥0 :=
  sInf {c | ∃ l : (Fv F v ⊗[F] E)ˣ, ((l⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) • u ∈ latLoc F L v ∧ c = absEv F E v l}

def normInf (a : GL (Fin n) (AF F ⊗[F] E)) (w : InfinitePlace F) (u : Fin n → w.Completion ⊗[F] E) : ℝ :=
  let b : GL (Fin n) (w.Completion ⊗[F] E) := (Formalism.UG.bc (compInf F E w) a)⁻¹
  Norm.norm (Finset.univ.sum fun i => Algebra.norm w.Completion ((b.1 *ᵥ u) i)) ^ w.mult

def ht (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (u : Fin n → AF F ⊗[F] E) : ℝ :=
  (∏ᶠ v, (normFin F L v (fun i => compFin F E v (u i)) : ℝ)) * ∏ w, normInf a w (fun i => compInf F E w (u i))

variable (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)

def IsLineReps (x y : Fin n → E) (Y : Set (Fin n → E)) : Prop :=
  (∀ z ∈ Y, z ≠ 0 ∧ hE σ J z z = 0 ∧ hE σ J x z = 0 ∧ hE σ J y z = 0) ∧
  (∀ z ∈ Y, ∀ z' ∈ Y, ∀ c : E, z = c • z' → z = z') ∧
  ∀ z : Fin n → E, z ≠ 0 → hE σ J z z = 0 → hE σ J x z = 0 → hE σ J y z = 0 → ∃ z' ∈ Y, ∃ c : E, z = c • z'

end GlobalTheory.EisMidHt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMidJacAt
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.ThK.DetProd

namespace GlobalTheory.ThK.MidJac

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def e3 (l n d : ℕ) (h : l + n ≤ d) : (Σ i : Fin 3, Fin (![l, n, d - l - n] i)) ≃ Fin d :=
  finSigmaFinEquiv.trans (finCongr (by simp [Fin.sum_univ_three]; omega))

def e2 (a a' : ℕ) : (Σ i : Fin 2, Fin (![a, a'] i)) ≃ Fin (a + a') :=
  finSigmaFinEquiv.trans (finCongr (by simp [Fin.sum_univ_two]))

def midIncl (l n c : ℕ) : GL (Fin n) k →* Levi k (fun i : Fin 3 => Fin (![l, n, c] i)) :=
  MonoidHom.mulSingle (fun i : Fin 3 => GL (Fin (![l, n, c] i)) k) 1

def midJac {V : Type} [AddCommGroup V] [Module ℂ V] (l n d : ℕ) (h : l + n ≤ d) (π : Representation ℂ (GL (Fin d) k) V) :
    Representation ℂ (GL (Fin n) k) (Jacquet π (unipRad k (e3 l n d h))) :=
  (jac (e3 l n d h) π).comp (midIncl l n (d - l - n))

def detInd (a a' : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ) :
    Representation ℂ (GL (Fin (a + a')) k) (IndSp (e2 a a') (ofChar (twoDet a a' χ₁ χ₂))) :=
  parInd (e2 a a') (ofChar (twoDet a a' χ₁ χ₂))

section Place

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E]

def absPowAt (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) (s : ℂ) : (w.adicCompletion E)ˣ →* ℂˣ :=
  absPow _ s

def IsMidJacAt (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) {n : ℕ} (a a' l : ℕ) (h : l + n ≤ a + a')
    (χ₁ χ₂ : (w.adicCompletion E)ˣ →* ℂˣ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) : Prop :=
  IsSubquotient π (midJac l n (a + a') h (detInd a a' χ₁ χ₂))

end Place

end GlobalTheory.ThK.MidJac
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianDimensionBoundStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.MixedLagr
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lagrangian_dimension_bound : ∀ (F : Type) [Field F] (κ : Type) [Fintype κ] (L : Submodule F ((κ → F) × (κ → F))),
    (∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) → Module.finrank F L ≤ Fintype.card κ := by
  first | exact @GlobalTheory.finrank_le_card_of_isotropic_prod_pi | exact GlobalTheory.finrank_le_card_of_isotropic_prod_pi | (intros; apply GlobalTheory.finrank_le_card_of_isotropic_prod_pi <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianEvaluationGauss
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.ThK.EvAt0
open GlobalTheory.ThK.EvAt0.PolD

noncomputable section

namespace GlobalTheory.ThK.EvAt0.PlaneQ

section Complex

def qLoc {n : ℕ} (k : ℝ) (J θ : Matrix (Fin n) (Fin n) ℂ) : LinearMap.BilinForm ℝ (Fin n → ℂ) :=
  LinearMap.mk₂ ℝ (fun s t => 2 * k * (s ⬝ᵥ J *ᵥ star (θ *ᵥ t)).re)
    (fun s s' t => by rw [add_dotProduct, Complex.add_re]; ring)
    (fun c s t => by rw [smul_dotProduct, Complex.smul_re, smul_eq_mul, smul_eq_mul]; ring)
    (fun s t t' => by rw [Matrix.mulVec_add, star_add, Matrix.mulVec_add, dotProduct_add, Complex.add_re]; ring)
    (fun c s t => by
      rw [Matrix.mulVec_smul, star_smul, Matrix.mulVec_smul, dotProduct_smul, Complex.smul_re, smul_eq_mul, smul_eq_mul,
        star_trivial]; ring)

end Complex

section Adelic

open scoped Classical
open GlobalTheory.RealLift.KLineProof

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def rho [IsTotallyReal F] (w : InfinitePlace F) : mixedEmbedding.mixedSpace F →ₐ[ℝ] ℝ :=
  (Pi.evalAlgHom ℝ (fun _ : {w : InfinitePlace F // w.IsReal} => ℝ) ⟨w, IsTotallyReal.isReal w⟩).comp (AlgHom.fst ℝ _ _)

theorem trace_rho [IsTotallyReal F] (v : mixedEmbedding.mixedSpace F) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) v = ∑ w, rho w v := by
  haveI : IsEmpty {w : InfinitePlace F // w.IsComplex} :=
    ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.2 w.2 (IsTotallyReal.isReal w.1)⟩
  rw [Algebra.trace_prod_apply, PI.ProdFormulaE.Tr.trace_pi, PI.ProdFormulaE.Tr.trace_pi, Finset.univ_eq_empty (α := {w : InfinitePlace F // w.IsComplex}),
    Finset.sum_empty, add_zero]
  refine Fintype.sum_equiv (Equiv.subtypeUnivEquiv fun w => IsTotallyReal.isReal w) _ _ fun w => ?_
  rw [Algebra.trace_self_apply]
  rfl

theorem rho_evI [IsTotallyReal F] (w : InfinitePlace F) (a : AF F) :
    ((rho w (evI F a) : ℝ) : ℂ) = InfinitePlace.Completion.extensionEmbedding w (evInf F w a) := by
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (IsTotallyReal.isReal w)]
  rfl

theorem piInf_algebraMap [IsTotallyReal F] {w : InfinitePlace F} (τ : EmbOver E w) (a : AF F) :
    piInf τ (algebraMap (AF F) (AE F E) a) = ((rho w (evI F a) : ℝ) : ℂ) := by
  rw [rho_evI]
  change piInf τ (a ⊗ₜ[F] (1 : E)) = _
  rw [piInf_tmul, map_one, mul_one]

theorem piInf_inclR {w : InfinitePlace F} (τ : EmbOver E w) (e : E) :
    piInf τ (inclR (F := F) (AF F) e) = τ.1 e := by
  change piInf τ ((1 : AF F) ⊗ₜ[F] e) = _
  rw [piInf_tmul, map_one, map_one, one_mul]

theorem rho_trace [IsTotallyReal F] {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w)
    (z : AE F E) : rho w (evI F (Algebra.trace (AF F) (AE F E) z)) = 2 * (piInf τ z).re := by
  have h1 : z + cA σ z = algebraMap (AF F) (AE F E) (Algebra.trace (AF F) (AE F E) z) :=
    GlobalTheory.GaussMean.OneVec.add_sigR (AF F) hCM z
  have h2 := congrArg (fun y => (piInf τ y).re) h1
  simp only [map_add, piInf_cA hCM, piInf_algebraMap, Complex.ofReal_re, Complex.add_re] at h2
  rw [← h2]
  simp [two_mul]

def phi [IsTotallyReal F] (h2 : Module.finrank F E = 2) {n : ℕ} {w : InfinitePlace F} (τ : EmbOver E w) :
    (Fin n × Fin 2 → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (Fin n → ℂ) where
  toFun t i := ∑ r, ((rho w (t (i, r)) : ℝ) : ℂ) * piInf τ (tb F E h2 r)
  map_add' t t' := by
    funext i
    simp only [Pi.add_apply, map_add, Complex.ofReal_add, add_mul, Finset.sum_add_distrib]
  map_smul' c t := by
    funext i
    simp only [Pi.smul_apply, map_smul, smul_eq_mul, Complex.ofReal_mul, RingHom.id_apply, Complex.real_smul,
      Finset.mul_sum, mul_assoc]

end Adelic

end GlobalTheory.ThK.EvAt0.PlaneQ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianEvaluationTranslation
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.ThK.EvAt0
open GlobalTheory.ThK.EvAt0.PolD

noncomputable section

namespace GlobalTheory.ThK.EvAt0.ZPartArc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem piInf_inclR' {w : InfinitePlace F} (τ : EmbOver E w) (x : E) : piInf τ (inclR (F := F) (AF F) x) = τ.1 x := by
  simp [piInf, inclR, compInf, infEmb_tmul]

end GlobalTheory.ThK.EvAt0.ZPartArc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeSumPolynomialBound
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus

noncomputable section
namespace GlobalTheory.ThKTorusLatSum
open mixedEmbedding
open scoped Classical

variable {F : Type} [Field F] [NumberField F]

theorem exists_one_le_place (x : F) (hx : IsIntegral ℤ x) (h0 : x ≠ 0) : ∃ w : InfinitePlace F, 1 ≤ w x := by
  by_contra h
  push_neg at h
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have ha : (⟨x, hx⟩ : 𝓞 F) ≠ 0 := fun e => h0 (congrArg Subtype.val e)
  have := InfinitePlace.one_le_of_lt_one (w := w) ha (fun z _ => h z)
  exact absurd this (not_le.mpr (h w))

theorem place_natCast_mul (w : InfinitePlace F) (m : ℕ) (x : F) : w ((m : F) * x) = m * w x := by
  rw [← InfinitePlace.norm_embedding_eq, ← InfinitePlace.norm_embedding_eq, map_mul, map_natCast, norm_mul,
    Complex.norm_natCast]

theorem inv_le_sum_places (m : ℕ) (hm : 1 ≤ m) (x : F) (hint : IsIntegral ℤ ((m : F) * x)) (h0 : x ≠ 0) :
    (m : ℝ)⁻¹ ≤ ∑ w : InfinitePlace F, w x := by
  have hm0 : (m : F) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hm)
  obtain ⟨w, hw⟩ := exists_one_le_place _ hint (mul_ne_zero hm0 h0)
  rw [place_natCast_mul, mul_comm] at hw
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  calc (m : ℝ)⁻¹ ≤ w x := by rw [inv_le_iff_one_le_mul₀ hmpos]; exact hw
    _ ≤ _ := Finset.single_le_sum (f := fun w : InfinitePlace F => w x) (fun w _ => apply_nonneg w x) (Finset.mem_univ w)

theorem norm_mixedEmbedding_le (x : F) : ‖(mixedEmbedding F x : NumberField.mixedEmbedding.mixedSpace F)‖ ≤ ∑ w : InfinitePlace F, w x := by
  have hs : 0 ≤ ∑ w : InfinitePlace F, w x := Finset.sum_nonneg fun w _ => apply_nonneg w x
  rw [Prod.norm_def]
  refine max_le ((pi_norm_le_iff_of_nonneg hs).mpr fun w => ?_) ((pi_norm_le_iff_of_nonneg hs).mpr fun w => ?_)
  · rw [mixedEmbedding_apply_isReal, InfinitePlace.norm_embedding_of_isReal]
    exact Finset.single_le_sum (f := fun w : InfinitePlace F => w x) (fun w _ => apply_nonneg w x) (Finset.mem_univ _)
  · rw [mixedEmbedding_apply_isComplex, InfinitePlace.norm_embedding_eq]
    exact Finset.single_le_sum (f := fun w : InfinitePlace F => w x) (fun w _ => apply_nonneg w x) (Finset.mem_univ _)

theorem norm_pi_mixedEmbedding_le {κ : Type} [Fintype κ] (ξ : κ → F) :
    ‖((fun j => mixedEmbedding F (ξ j)) : κ → NumberField.mixedEmbedding.mixedSpace F)‖ ≤ ∑ j, ∑ w : InfinitePlace F, w (ξ j) := by
  have hs : 0 ≤ ∑ j, ∑ w : InfinitePlace F, w (ξ j) :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun w _ => apply_nonneg w _
  refine (pi_norm_le_iff_of_nonneg hs).mpr fun j => (norm_mixedEmbedding_le (ξ j)).trans ?_
  exact Finset.single_le_sum (f := fun j => ∑ w : InfinitePlace F, w (ξ j))
    (fun j _ => Finset.sum_nonneg fun w _ => apply_nonneg w _) (Finset.mem_univ j)

theorem stepB (P P0 : ℝ) (hP0 : 0 < P0) (h : P0 ≤ P) (A N₀ D : ℕ) :
    P ^ A * (1 + P) ^ N₀ * (P ^ (A + N₀ + D))⁻¹ ≤ (1 + P0⁻¹) ^ N₀ * (P0 ^ D)⁻¹ := by
  have hP : 0 < P := hP0.trans_le h
  have e : P ^ A * (1 + P) ^ N₀ * (P ^ (A + N₀ + D))⁻¹ = (1 + P⁻¹) ^ N₀ * (P ^ D)⁻¹ := by
    have hP' : P ≠ 0 := hP.ne'
    rw [show (1 : ℝ) + P⁻¹ = (1 + P) * P⁻¹ by rw [add_mul, one_mul, mul_inv_cancel₀ hP', add_comm], mul_pow, pow_add, pow_add, inv_pow]
    field_simp
  rw [e]
  gcongr

theorem latG_tsum_le : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [DecidableEq κ] (q : ℕ) (blk : Fin q → Finset κ)
    (A N₀ : ℕ) (c : ℝ), 0 < c → ∃ (N : ℕ) (C : ℝ) (K : ℕ), ∀ (m : ℕ) (t : Fin q → ℝ), 1 ≤ m → (∀ i, c ≤ t i) →
      Summable (latG (F := F) blk A N m t) ∧ (∑' ξ, latG (F := F) blk A N m t ξ) * (1 + ∏ i, t i) ^ N₀ ≤ C * (m : ℝ) ^ K := by
  intro F _ _ κ _ _ q blk A N₀ c hc
  set L := GlobalTheory.LatScaleSum.latPi F κ with hL
  set D : ℕ := Module.finrank ℤ L + 1 with hD
  set H : (κ → mixedSpace F) → ℝ := fun v => ((1 + ‖v‖) ^ D)⁻¹ with hH
  have hHs : Summable fun z : L => H z := GlobalTheory.LatScaleSum.summable_inv_one_add_pow F κ
  set P0 : ℝ := c ^ q with hP0def
  have hP0 : 0 < P0 := pow_pos hc q
  set B : ℝ := (1 + P0⁻¹) ^ N₀ * (P0 ^ D)⁻¹ with hB
  have hB0 : 0 ≤ B := by positivity
  refine ⟨A + N₀ + D, B * ∑' z : L, H z, q * (A + N₀ + D) + D, ?_⟩
  intro m t hm ht
  set N := A + N₀ + D with hN
  set P : ℝ := ∏ i, t i with hPdef
  have ht0 : ∀ i, 0 < t i := fun i => hc.trans_le (ht i)
  have hPP0 : P0 ≤ P := by
    rw [hP0def, hPdef]
    calc c ^ q = ∏ _i : Fin q, c := by simp
      _ ≤ ∏ i, t i := Finset.prod_le_prod (fun i _ => hc.le) (fun i _ => ht i)
  have hP : 0 < P := hP0.trans_le hPP0
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hm0 : (m : F) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hm)
  set ψ : (κ → F) → (κ → mixedSpace F) := fun ξ i => mixedEmbedding F (ξ i) with hψdef
  set g : (κ → F) → (κ → mixedSpace F) := fun ξ => ψ (fun i => (m : F) * ξ i) with hgdef
  have hginj : Function.Injective g := by
    intro ξ η h
    funext i
    have := congrFun h i
    simp only [hgdef, hψdef] at this
    exact mul_left_cancel₀ hm0 (mixedEmbedding_injective F this)
  have hgsmul : ∀ ξ, g ξ = m • ψ ξ := by
    intro ξ
    funext i
    simp only [hgdef, hψdef, Pi.smul_apply]
    rw [← nsmul_eq_mul, map_nsmul]
  set Lind : (κ → mixedSpace F) → ℝ := (L : Set (κ → mixedSpace F)).indicator H with hLind
  have hLs : Summable Lind := summable_subtype_iff_indicator.mp hHs
  have hLnn : ∀ v, 0 ≤ Lind v := fun v => Set.indicator_nonneg (fun v _ => by positivity) v
  have key : ∀ ξ, latG (F := F) blk A N m t ξ * (1 + P) ^ N₀ ≤ B * (m : ℝ) ^ (q * N + D) * Lind (g ξ) := by
    intro ξ
    have hR : 0 ≤ B * (m : ℝ) ^ (q * N + D) * Lind (g ξ) := mul_nonneg (by positivity) (hLnn _)
    unfold latG
    split_ifs with hblk
    swap
    · simpa using hR
    unfold majI
    split_ifs with hint
    swap
    · simpa using hR
    have hmem : g ξ ∈ L := GlobalTheory.LatScaleSum.mem_latPi F κ _ hint
    rw [hLind, Set.indicator_of_mem hmem]
    set S : Fin q → ℝ := fun i => ∑ j ∈ blk i, ∑ w : InfinitePlace F, w (ξ j) with hS
    set s : ℝ := ∑ j, ∑ w : InfinitePlace F, w (ξ j) with hs
    have hS0 : ∀ i, (m : ℝ)⁻¹ ≤ S i := by
      intro i
      obtain ⟨j, hj, hξ⟩ := hblk i
      exact (inv_le_sum_places m hm (ξ j) (hint j) hξ).trans
        (Finset.single_le_sum (f := fun j => ∑ w : InfinitePlace F, w (ξ j))
          (fun j _ => Finset.sum_nonneg fun w _ => apply_nonneg w _) hj)
    set Q : ℝ := ∏ i, (1 + t i * S i) with hQ
    have hQge : P * ((m : ℝ) ^ q)⁻¹ ≤ Q := by
      calc P * ((m : ℝ) ^ q)⁻¹ = ∏ i, (t i * (m : ℝ)⁻¹) := by
            rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, inv_pow]
        _ ≤ Q := Finset.prod_le_prod (fun i _ => by have := ht0 i; positivity) (fun i _ => by
              have := mul_le_mul_of_nonneg_left (hS0 i) (ht0 i).le
              exact le_add_of_nonneg_of_le zero_le_one this)
    have hs0 : 0 ≤ s := Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun w _ => apply_nonneg w _
    have hQpos : 0 < P * ((m : ℝ) ^ q)⁻¹ := by positivity
    have hmaj : majW blk A N t ξ = P ^ A * ((Q ^ N) * (1 + s) ^ N)⁻¹ := by
      unfold majW
      rw [Finset.prod_pow]
    rw [hmaj]
    have hψn : ‖ψ ξ‖ ≤ s := norm_pi_mixedEmbedding_le ξ
    have hgn : ‖g ξ‖ ≤ m * ‖ψ ξ‖ := by rw [hgsmul]; exact norm_nsmul_le
    have hcc : ((1 + s) ^ N)⁻¹ ≤ (m : ℝ) ^ D * H (g ξ) := by
      have h1 : ((1 + s) ^ N)⁻¹ ≤ ((1 + s) ^ D)⁻¹ := by
        apply inv_anti₀ (by positivity)
        exact pow_le_pow_right₀ (by linarith) (by omega)
      calc ((1 + s) ^ N)⁻¹ ≤ ((1 + s) ^ D)⁻¹ := h1
        _ ≤ ((1 + ‖ψ ξ‖) ^ D)⁻¹ := by gcongr
        _ = (m : ℝ) ^ D * (((m : ℝ) * (1 + ‖ψ ξ‖)) ^ D)⁻¹ := by
            rw [mul_pow, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hmpos.ne'), one_mul]
        _ ≤ (m : ℝ) ^ D * ((1 + ‖g ξ‖) ^ D)⁻¹ := by
            gcongr
            have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
            nlinarith [norm_nonneg (ψ ξ), hgn]
    have ha : (Q ^ N)⁻¹ ≤ (m : ℝ) ^ (q * N) * (P ^ N)⁻¹ := by
      calc (Q ^ N)⁻¹ ≤ ((P * ((m : ℝ) ^ q)⁻¹) ^ N)⁻¹ := by gcongr
        _ = _ := by rw [mul_pow, mul_inv, inv_pow, inv_inv, ← pow_mul, mul_comm]
    have hb := stepB P P0 hP0 hPP0 A N₀ D
    have hHg : 0 ≤ H (g ξ) := by positivity
    calc P ^ A * ((Q ^ N) * (1 + s) ^ N)⁻¹ * (1 + P) ^ N₀
        = P ^ A * (1 + P) ^ N₀ * (Q ^ N)⁻¹ * ((1 + s) ^ N)⁻¹ := by rw [mul_inv]; ring
      _ ≤ P ^ A * (1 + P) ^ N₀ * ((m : ℝ) ^ (q * N) * (P ^ N)⁻¹) * ((m : ℝ) ^ D * H (g ξ)) := by
          gcongr
      _ = (P ^ A * (1 + P) ^ N₀ * (P ^ N)⁻¹) * (m : ℝ) ^ (q * N + D) * H (g ξ) := by rw [pow_add]; ring
      _ ≤ B * (m : ℝ) ^ (q * N + D) * H (g ξ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb (by positivity)) hHg
  have hnn : ∀ ξ, 0 ≤ latG (F := F) blk A N m t ξ := fun ξ => latG_nonneg blk A N m t ξ (fun i => (ht0 i).le)
  have hpow : 0 < (1 + P) ^ N₀ := by positivity
  have key' : ∀ ξ, latG (F := F) blk A N m t ξ ≤ ((1 + P) ^ N₀)⁻¹ * (B * (m : ℝ) ^ (q * N + D)) * Lind (g ξ) := by
    intro ξ
    calc latG (F := F) blk A N m t ξ = ((1 + P) ^ N₀)⁻¹ * (latG (F := F) blk A N m t ξ * (1 + P) ^ N₀) := by
          field_simp
      _ ≤ ((1 + P) ^ N₀)⁻¹ * (B * (m : ℝ) ^ (q * N + D) * Lind (g ξ)) := mul_le_mul_of_nonneg_left (key ξ) (by positivity)
      _ = _ := by ring
  have hu : Summable fun ξ => Lind (g ξ) := hLs.comp_injective hginj
  have hsum : Summable (latG (F := F) blk A N m t) := Summable.of_nonneg_of_le hnn key' (hu.mul_left _)
  refine ⟨hsum, ?_⟩
  have hcomp : ∑' ξ, Lind (g ξ) ≤ ∑' v, Lind v := tsum_comp_le_tsum_of_inj hLs hLnn hginj
  have hsub : ∑' v, Lind v = ∑' z : L, H z := (tsum_subtype (L : Set (κ → mixedSpace F)) H).symm
  rw [← tsum_mul_right]
  calc ∑' ξ, latG (F := F) blk A N m t ξ * (1 + P) ^ N₀ ≤ ∑' ξ, B * (m : ℝ) ^ (q * N + D) * Lind (g ξ) :=
        (hsum.mul_right _).tsum_le_tsum key (hu.mul_left _)
    _ = B * (m : ℝ) ^ (q * N + D) * ∑' ξ, Lind (g ξ) := tsum_mul_left
    _ ≤ B * (m : ℝ) ^ (q * N + D) * ∑' z : L, H z := by
        rw [← hsub]; exact mul_le_mul_of_nonneg_left hcomp (by positivity)
    _ = B * (∑' z : L, H z) * (m : ℝ) ^ (q * N + D) := by ring

end GlobalTheory.ThKTorusLatSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevSplitOf
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ThK.DescB.PrimeSplit

open Matrix GlobalTheory.LeviLine

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem skew_gram (hσ : ∀ x, σ (σ x) = x) {n n₁ : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = -J i j) (ι : Matrix (Fin n) (Fin n₁) E) :
    ∀ k l, σ ((ιᵀ * J * ι.map σ) l k) = -(ιᵀ * J * ι.map σ) k l := by
  intro k l
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, hσ, Finset.sum_mul]
  simp only [hJ]
  refine Finset.sum_comm.trans ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  ring

theorem skew_sp (hσ : ∀ x, σ (σ x) = x) (B : Base F E) {d d₁ p : ℕ} {W : Spc F E d} (hW : ∀ i j, σ (W.J j i) = -W.J i j)
    {H' : Plane E d d₁} {i₀ i₁ : ℕ} {sp : ∀ j : ℕ, Spc F E (d₁ - 2 * j)}
    {pl : ∀ j : ℕ, Plane E (d₁ - 2 * j) (d₁ - 2 * (j + 1))} (hH : H'.IsAdapted σ B W (sp 0) i₀ i₁)
    (hiso : ∀ i < p, IsIsoPlane σ B (pl i) (sp i) (sp (i + 1))) :
    ∀ j ≤ p, ∀ k l, σ ((sp j).J l k) = -(sp j).J k l := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [← hH.gram]
    exact skew_gram hσ hW H'.ι
  | succ j ih =>
    intro hj
    rw [← (hiso j (by omega)).2.2.2.2.2.1]
    exact skew_gram hσ (ih (by omega)) (pl j).ι

end GlobalTheory.ThK.DescB.PrimeSplit

namespace GlobalTheory.ThK.DescB.PrimeSplit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def lawFn (χ : Chr F E) (z : ℝ) (t : (AE F E)ˣ) : ℂ := (χ t : ℂ) * (((absE F E t : ℝ) ^ z : ℝ) : ℂ)

theorem norm_lawFn (χ : Chr F E) (z : ℝ) (t : (AE F E)ˣ) : ‖lawFn χ z t‖ = (absE F E t : ℝ) ^ z := by
  rw [lawFn, norm_mul, Circle.norm_coe, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)]

theorem lawFn_ne (α β : Chr F E) {z z' : ℝ} (hz : z < z') {t : (AE F E)ˣ} (ht : 1 < (absE F E t : ℝ)) :
    lawFn α z t ≠ lawFn β z' t := fun e => by
  have h := congrArg norm e
  rw [norm_lawFn, norm_lawFn] at h
  exact (Real.rpow_lt_rpow_of_exponent_lt ht hz).ne h

theorem isLevi_one {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} (H : Plane E d d₁) :
    IsLevi (σ := σ) (W := W) (W₁ := W₁) H 1 1 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [mat]

theorem isLevi_mul {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H : Plane E d d₁} {t s : (AE F E)ˣ}
    {m m' : UA σ W.J} (h : IsLevi (W₁ := W₁) H t 1 m) (h' : IsLevi (W₁ := W₁) H s 1 m') :
    IsLevi (W₁ := W₁) H (t * s) 1 (m * m') := by
  have e : mat (m * m') = mat m * mat m' := rfl
  have e1 : mat (1 : UA σ W₁.J) = 1 := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [e, ← Matrix.mulVec_mulVec, h'.1, Matrix.mulVec_smul, h.1, smul_smul, Units.val_mul, mul_comm]
  · rw [e, ← Matrix.mulVec_mulVec, h'.2.1, Matrix.mulVec_smul, h.2.1, smul_smul, mul_inv_rev, Units.val_mul, map_mul]
  · rw [e, Matrix.mul_assoc, h'.2.2, e1, Matrix.mul_one]
    simpa [e1] using h.2.2

end GlobalTheory.ThK.DescB.PrimeSplit

namespace GlobalTheory.ThK.DescB.PrimeSplit

open GlobalTheory.LeviLine

end GlobalTheory.ThK.DescB.PrimeSplit

end
end

