import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AutomorphicFormsFiniteIdeal
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CenterEnvelopingAlgebraDirectSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1293
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1423
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1349
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0043
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1435
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1392
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAutOfMemAutForms
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.UAut GlobalTheory.Mem.Th GlobalTheory.SiegelSet
open scoped TensorProduct

namespace GlobalTheory.CentralOps

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

theorem isSm_of_smF (hθ : IsInfFam θ) (R : RealPoints θ V) (f : SmF θ V) : IsSm D.sp.cm.sig V.gram f.1 := by
  intro k γ hγ g
  choose p hp e using fun i => (hγ i).eq_oneP hθ
  simpa only [e] using (smooth_iff R f.1).2 f.2 k (fun i => (p i).1) (fun i => (p i).2) hp g

theorem exists_word (hθ : IsInfFam θ) (R : RealPoints θ V) (l : List (ℝ → GA D V))
    (hl : ∀ γ ∈ l, IsRealLine D.sp.cm.sig V.gram γ) :
    ∃ w : GlobalTheory.AutFinLit.Env V, ∀ f : SmF θ V, l.foldr lineDer f.1 = (envRepAll R w f).1 := by
  classical
  induction l with
  | nil => exact ⟨1, fun f => by rw [map_one]; rfl⟩
  | cons γ l ih =>
    obtain ⟨w, hw⟩ := ih fun δ hδ => hl δ (List.mem_cons_of_mem _ hδ)
    obtain ⟨⟨τ, X⟩, hX, rfl⟩ := (hl γ List.mem_cons_self).eq_oneP hθ
    refine ⟨UniversalEnvelopingAlgebra.ι ℂ (DirectSum.of (fun τ => ℂ ⊗[ℝ] LieAt V τ) τ ((1 : ℂ) ⊗ₜ[ℝ] ⟨X, hX⟩)) * w,
      fun f => ?_⟩
    rw [map_mul, Module.End.mul_apply, ← envIncl_ι, envRepAll_envIncl, envRep_ι, opInf_coe, ← hw, List.foldr_cons]
    exact Rder_eq R τ ⟨X, hX⟩ _

theorem exists_env (hθ : IsInfFam θ) (R : RealPoints θ V) (z : List (ℝ → GA D V) →₀ ℂ)
    (hz : ∀ l ∈ z.support, ∀ γ ∈ l, IsRealLine D.sp.cm.sig V.gram γ) :
    ∃ u : GlobalTheory.AutFinLit.Env V, ∀ f : SmF θ V, dop z f.1 = (envRepAll R u f).1 := by
  classical
  choose! w hw using fun l (hl : l ∈ z.support) => exists_word hθ R l (hz l hl)
  refine ⟨∑ l ∈ z.support, z l • w l, fun f => ?_⟩
  rw [map_sum, LinearMap.sum_apply, Submodule.coe_sum]
  funext g
  simp only [dop, Finsupp.sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [map_smul, LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, ← hw l hl]

theorem mem_center_of_comm (u : GlobalTheory.AutFinLit.Env V)
    (h : ∀ x, UniversalEnvelopingAlgebra.ι ℂ x * u = u * UniversalEnvelopingAlgebra.ι ℂ x) :
    u ∈ Subalgebra.center ℂ (GlobalTheory.AutFinLit.Env V) := by
  rw [Subalgebra.mem_center_iff]
  intro b
  have hs : Function.Surjective (UniversalEnvelopingAlgebra.mkAlgHom ℂ (GlobalTheory.AutFinLit.LieC V)) := by
    unfold UniversalEnvelopingAlgebra.mkAlgHom
    first | exact RingCon.mkₐ_surjective _ _ | exact RingCon.mkₐ_surjective _ | exact fun b => Quotient.inductionOn' b fun t => ⟨t, rfl⟩ | exact Quot.mk_surjective
  obtain ⟨t, rfl⟩ := hs b
  induction t using TensorAlgebra.induction with
  | algebraMap r => rw [AlgHom.commutes]; exact Algebra.commutes r u
  | ι x => exact h x
  | mul a b ha hb => rw [map_mul, mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
  | add a b ha hb => rw [map_add, add_mul, mul_add, ha, hb]

theorem mem_of_mem_center (R : RealPoints θ V) {W : Submodule ℂ (GA D V → ℂ)}
    (hs : ∀ τ k, ∀ f ∈ W, gelf θ V τ k f ∈ W) {u : GlobalTheory.AutFinLit.Env V}
    (hu : u ∈ Subalgebra.center ℂ (GlobalTheory.AutFinLit.Env V)) : ∀ f : SmF θ V, f.1 ∈ W → (envRepAll R u f).1 ∈ W := by
  classical
  choose c hc hg using exists_gelf R
  have hloc : ∀ τ, ∀ z ∈ Subalgebra.center ℂ (EnvAt V τ), ∀ f : SmF θ V, f.1 ∈ W → (envRep R τ z f).1 ∈ W := by
    intro τ z hz
    rw [hc τ] at hz
    induction hz using Algebra.adjoin_induction with
    | mem x hx => obtain ⟨k, rfl⟩ := hx; intro f hf; rw [← hg]; exact hs τ k _ hf
    | algebraMap r => intro f hf; rw [AlgHom.commutes]; exact W.smul_mem r hf
    | add x y _ _ hx hy => intro f hf; rw [map_add]; exact add_mem (hx f hf) (hy f hf)
    | mul x y _ _ hx hy => intro f hf; rw [map_mul]; exact hx _ (hy f hf)
  rw [GlobalTheory.EnvCentre.center_directSum D.what₂.Tau (fun τ => ℂ ⊗[ℝ] LieAt V τ) (fun τ => envIncl V τ)
    (fun τ x => envIncl_ι τ x)] at hu
  induction hu using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨τ, z, hz, rfl⟩ := Set.mem_iUnion.1 hx |>.imp fun τ h => h
    intro f hf; rw [envRepAll_envIncl]; exact hloc τ z hz f hf
  | algebraMap r => intro f hf; rw [AlgHom.commutes]; exact W.smul_mem r hf
  | add x y _ _ hx hy => intro f hf; rw [map_add]; exact add_mem (hx f hf) (hy f hf)
  | mul x y _ _ hx hy => intro f hf; rw [map_mul]; exact hx _ (hy f hf)

theorem exists_center (hθ : IsInfFam θ) (R : RealPoints θ V) {z : List (ℝ → GA D V) →₀ ℂ}
    (hz : IsCentral D.sp.cm.sig V.gram z) :
    ∃ u ∈ Subalgebra.center ℂ (GlobalTheory.AutFinLit.Env V), ∀ f : SmF θ V, dop z f.1 = (envRepAll R u f).1 := by
  obtain ⟨u, hu⟩ := exists_env hθ R z hz.1
  refine ⟨u, mem_center_of_comm u fun x => GlobalTheory.T.enveloping_representation_injective _ _ hθ V R ?_, hu⟩
  rw [map_mul, map_mul]
  refine GlobalTheory.T.enveloping_action_commutes_translation _ _ hθ V R u (fun a ha f hfa => ?_) x
  rw [← hu, ← hu]
  funext g
  exact hz.2 f.1 (isSm_of_smF hθ R f) a ha g

end GlobalTheory.CentralOps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
section
noncomputable section

namespace GlobalTheory.ThetaFac

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}

structure WStable (B : Base F E) (om : Rep σ Y W) (D N : Submodule ℂ (Fn F n d)) : Prop where
  fin : ∀ v : Pl F, ∀ h ∈ UAt σ W (evFin F v), ∀ Φ ∈ N, om (1, h) Φ ∈ N
  lie : ∀ γ ∈ Lines σ W, ∀ Φ ∈ N, ∀ Φ₁ ∈ D,
    (∀ x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0) → Φ₁ ∈ N
  cpt : ∀ k ∈ KInf σ W B.emb, ∀ Φ ∈ N, om (1, k) Φ ∈ N

structure CoinvLe (B : Base F E) (om : Rep σ Y W) (D N : Submodule ℂ (Fn F n d)) : Prop where
  fin : ∀ v : Pl F, ∀ g ∈ UAt σ Y (evFin F v), ∀ Φ ∈ D, om (g, 1) Φ - Φ ∈ N
  lie : ∀ γ ∈ Lines σ Y, ∀ Φ ∈ D, ∀ Φ₁ ∈ D,
    (∀ x, HasDerivAt (fun t : ℝ => om (γ (Multiplicative.ofAdd t), 1) Φ x) (Φ₁ x) 0) → Φ₁ ∈ N
  cpt : ∀ k ∈ KInf σ Y B.emb, ∀ Φ ∈ D, om (k, 1) Φ - Φ ∈ N

structure IsMaxTh (B : Base F E) (om : Rep σ Y W) (D N : Submodule ℂ (Fn F n d)) : Prop where
  le : N ≤ D
  ne : N ≠ D
  coinv : CoinvLe B om D N
  stab : WStable B om D N
  max : ∀ N' : Submodule ℂ (Fn F n d), N ≤ N' → N' ≤ D → WStable B om D N' → N' = N ∨ N' = D

end GlobalTheory.ThetaFac

end

namespace GlobalTheory.ThetaFac

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}

end GlobalTheory.ThetaFac
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulIntSingle
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix

namespace GlobalTheory.ThetaDenom

variable (F : Type) [Field F] [NumberField F] in

def IsMulInt {κ : Type} (M : ℕ) (z : κ → AF F) : Prop :=
  (∀ i, (z i).1 = 0) ∧ ∀ v i, ‖evFin F v (z i)‖ ≤ ‖(M : Fv F v)‖

theorem isMulInt_single {F : Type} [Field F] [NumberField F] {κ : Type} [DecidableEq κ] (K : ℕ) (i : κ) (t : AF F)
    (ht0 : t.1 = 0) (ht1 : ∀ v, ‖evFin F v t‖ ≤ 1) : IsMulInt F K (Pi.single i ((K : AF F) * t)) := by
  refine ⟨fun j => ?_, fun v j => ?_⟩
  · by_cases hj : j = i
    · subst hj
      rw [Pi.single_eq_same, show ((K : AF F) * t).1 = (K : AF F).1 * t.1 from rfl, ht0, mul_zero]
    · rw [Pi.single_eq_of_ne hj]; rfl
  · by_cases hj : j = i
    · subst hj
      rw [Pi.single_eq_same, map_mul, map_natCast, norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (ht1 v)
    · rw [Pi.single_eq_of_ne hj, map_zero, norm_zero]; exact norm_nonneg _

theorem IsMulInt.mono {F : Type} [Field F] [NumberField F] {κ : Type} {k m : ℕ} {a : κ → AF F}
    (h : IsMulInt F (k * m) a) : IsMulInt F m a := by
  refine ⟨h.1, fun v i => (h.2 v i).trans ?_⟩
  rw [Nat.cast_mul, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (GlobalTheory.SmoothForms.denom_norm_natCast_le_one v k)

theorem fin_step {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] [DecidableEq κ] (ψ : AddChar (AF F) ℂ)
    (K : ℕ) (Ψ : (κ → AF F) → ℂ) (hfix : ∀ y, IsMulInt F K y → schr ψ (0, y) Ψ = Ψ) (ξ : κ → F)
    (hξ : Ψ (fun j => algebraMap F (AF F) (ξ j)) ≠ 0) (i : κ) (t : AF F) (ht0 : t.1 = 0)
    (ht1 : ∀ v, ‖evFin F v t‖ ≤ 1) : ψ (algebraMap F (AF F) ((K : F) * ξ i) * t) = 1 := by
  have e1 := congrFun (hfix _ (isMulInt_single K i t ht0 ht1)) (fun j => algebraMap F (AF F) (ξ j))
  simp only [schr, dotProduct_single, zero_dotProduct, Pi.zero_apply, zero_mul, mul_zero, add_zero] at e1
  have e2 := (mul_eq_right₀ hξ).1 e1
  rw [← e2]
  congr 1
  rw [(algebraMap F (AF F)).map_mul, map_natCast]
  ring

def sand {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    (g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) (h : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)) :
    Matrix (Fin n) (Fin d) (AF F ⊗[F] E) →ₗ[AF F] Matrix (Fin n) (Fin d) (AF F ⊗[F] E) where
  toFun X := g * X * hᵀ
  map_add' X Y := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' a X := by rw [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul]

example {F : Type} [Field F] [NumberField F] (M : ℕ) : IsMulInt F M (0 : Fin 2 → AF F) :=
  ⟨fun _ => rfl, fun v _ => by rw [Pi.zero_apply, map_zero, norm_zero]; exact norm_nonneg _⟩

end GlobalTheory.ThetaDenom

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenRankGe
section
open ValuativeRel Matrix

theorem GlobalTheory.isOpen_setOf_le_rank_localField : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D]
    [DecidableEq D] (s : ℕ), IsOpen {X : Matrix A D k | s ≤ X.rank} := by
  intro k _ _ _ _ A D _ _ _ _ s
  rw [isOpen_iff_mem_nhds]
  intro X hX
  obtain ⟨H, Q, hHQ⟩ := GlobalTheory.T.matrix_rank_normal_form k A D X
  have hc : Continuous fun Y : Matrix A D k => (H * Y * Q).det :=
    ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_det
  have hopen : IsOpen {Y : Matrix A D k | (H * Y * Q).det ≠ 0} :=
    isOpen_ne_fun hc continuous_const
  filter_upwards [hopen.mem_nhds (by simp [hHQ])] with Y hY
  replace hY : (H * Y * Q).det ≠ 0 := hY
  show s ≤ Y.rank
  refine le_trans hX ?_
  have hu : IsUnit (H * Y * Q) := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hY)
  have hr : (H * Y * Q).rank = X.rank := by
    rw [Matrix.rank_of_isUnit _ hu]; simp
  calc X.rank = (H * Y * Q).rank := hr.symm
    _ ≤ (H * Y).rank := Matrix.rank_mul_le_left _ _
    _ ≤ Y.rank := Matrix.rank_mul_le_right _ _
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenScaledInt
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.EvAdm

variable (F : Type) [Field F] [NumberField F] (κ : Type)

def scaledInt (a : F) : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F) where
  carrier := {z | ∀ i (v : HeightOneSpectrum (𝓞 F)),
    (algebraMap F (v.adicCompletion F) a)⁻¹ * (z i) v ∈ v.adicCompletionIntegers F}
  zero_mem' := fun i v => by
    show (algebraMap F (v.adicCompletion F) a)⁻¹ * (0 : FiniteAdeleRing (𝓞 F) F) v ∈ _
    simp
  add_mem' := fun {z w} hz hw i v => by
    show (algebraMap F (v.adicCompletion F) a)⁻¹ * ((z i + w i) v) ∈ _
    have e : (z i + w i) v = (z i) v + (w i) v := rfl
    rw [e, mul_add]
    exact add_mem (hz i v) (hw i v)
  neg_mem' := fun {z} hz i v => by
    show (algebraMap F (v.adicCompletion F) a)⁻¹ * ((-z i) v) ∈ _
    have e : (-z i) v = -((z i) v) := rfl
    rw [e, mul_neg]
    exact neg_mem (hz i v)

variable {F κ}

theorem mem_scaledInt {a : F} {z : κ → FiniteAdeleRing (𝓞 F) F} :
    z ∈ scaledInt F κ a ↔ ∀ i (v : HeightOneSpectrum (𝓞 F)),
      (algebraMap F (v.adicCompletion F) a)⁻¹ * (z i) v ∈ v.adicCompletionIntegers F := Iff.rfl

theorem isOpen_scaledInt [Finite κ] (a : F) : IsOpen (scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)) := by
  have hO : IsOpen {x : FiniteAdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), x v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_mem fun v => Valued.isOpen_valuationSubring _
  have e : (scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)) = ⋂ i, (fun z : κ → FiniteAdeleRing (𝓞 F) F =>
      algebraMap F (FiniteAdeleRing (𝓞 F) F) a⁻¹ * z i) ⁻¹'
      {x : FiniteAdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), x v ∈ v.adicCompletionIntegers F} := by
    ext z
    simp only [SetLike.mem_coe, mem_scaledInt, Set.mem_iInter, Set.mem_preimage, Set.mem_setOf_eq]
    refine forall_congr' fun i => forall_congr' fun v => ?_
    have h : (algebraMap F (FiniteAdeleRing (𝓞 F) F) a⁻¹ * z i) v =
        (algebraMap F (v.adicCompletion F) a)⁻¹ * (z i) v := by
      have h1 := map_mul (evalV F v) (algebraMap F (FiniteAdeleRing (𝓞 F) F) a⁻¹) (z i)
      rw [AlgHom.commutes, map_inv₀ (algebraMap F (v.adicCompletion F))] at h1
      exact h1
    rw [h]
  rw [e]
  exact isOpen_iInter_of_finite fun i => hO.preimage (continuous_const.mul (continuous_apply i))

end GlobalTheory.EvAdm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairingStdP
section
noncomputable section

open scoped SchwartzMap

namespace GlobalTheory.ArchUniq

section Real

variable {V V₁ : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup V₁] [NormedSpace ℝ V₁]

def schrF (P : V → V → ℝ) (w : V × V) (f : V → ℂ) : V → ℂ :=
  fun y => Complex.exp (-(2 * Real.pi * Complex.I) * ((P y w.2 + P w.1 w.2 / 2 : ℝ) : ℂ)) * f (y + w.1)

def omega (P : V → V → ℝ) (w w' : V × V) : ℝ := P w.1 w'.2 - P w'.1 w.2

structure IsPairing (P : V → V → ℝ) : Prop where
  addL : ∀ x x' y, P (x + x') y = P x y + P x' y
  addR : ∀ x y y', P x (y + y') = P x y + P x y'
  smulL : ∀ (c : ℝ) x y, P (c • x) y = c * P x y
  smulR : ∀ (c : ℝ) x y, P x (c • y) = c * P x y
  nondegL : ∀ x, (∀ y, P x y = 0) → x = 0
  nondegR : ∀ y, (∀ x, P x y = 0) → y = 0

structure Setup (P : V → V → ℝ) (P₁ : V₁ → V₁ → ℝ) (j : V₁ × V₁ → V × V) (L : Set (V × V)) : Prop where
  pair : IsPairing P
  pair₁ : IsPairing P₁
  add : ∀ w w', j (w + w') = j w + j w'
  smul : ∀ (c : ℝ) w, j (c • w) = c • j w
  symp : ∀ w w', omega P (j w) (j w') = omega P₁ w w'
  iso : ∀ l ∈ L, ∀ l' ∈ L, omega P l l' = 0
  orth : ∀ l ∈ L, ∀ w, omega P l (j w) = 0
  max : ∀ v, (∀ l ∈ L, omega P v l = 0) → (∀ w, omega P v (j w) = 0) → v ∈ L

def Laws (P : V → V → ℝ) (P₁ : V₁ → V₁ → ℝ) (j : V₁ × V₁ → V × V) (L : Set (V × V))
    (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(V₁, ℂ)) : Prop :=
  (∀ w (f f₁ : 𝓢(V, ℂ)) (f₂ : 𝓢(V₁, ℂ)), ⇑f₁ = schrF P (j w) ⇑f → ⇑f₂ = schrF P₁ w ⇑(T f) → T f₁ = f₂) ∧
  ∀ l ∈ L, ∀ f f₁ : 𝓢(V, ℂ), ⇑f₁ = schrF P l ⇑f → T f₁ = T f

def stdP (P₁ : V₁ → V₁ → ℝ) (k : ℕ) (x y : V₁ × (Fin k → ℝ)) : ℝ := P₁ x.1 y.1 + ∑ i, x.2 i * y.2 i

def jStd (k : ℕ) (w : V₁ × V₁) : (V₁ × (Fin k → ℝ)) × (V₁ × (Fin k → ℝ)) := ((w.1, 0), (w.2, 0))

variable (V₁) in

def LStd (k : ℕ) : Set ((V₁ × (Fin k → ℝ)) × (V₁ × (Fin k → ℝ))) :=
  {l | ∃ b : Fin k → ℝ, l = ((0, 0), (0, b))}

theorem isPairing_stdP {P₁ : V₁ → V₁ → ℝ} (h : IsPairing P₁) (k : ℕ) : IsPairing (stdP P₁ k) where
  addL x x' y := by
    simp only [stdP, Prod.fst_add, Prod.snd_add, h.addL, Pi.add_apply, add_mul, Finset.sum_add_distrib]; ring
  addR x y y' := by
    simp only [stdP, Prod.fst_add, Prod.snd_add, h.addR, Pi.add_apply, mul_add, Finset.sum_add_distrib]; ring
  smulL c x y := by
    simp only [stdP, Prod.smul_fst, Prod.smul_snd, h.smulL, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
    ring
  smulR c x y := by
    simp only [stdP, Prod.smul_fst, Prod.smul_snd, h.smulR, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c,
      ← Finset.mul_sum]
    ring
  nondegL x hx := by
    have h1 : x.1 = 0 := h.nondegL _ fun y => by simpa [stdP] using hx (y, 0)
    have h2 : ∑ i, x.2 i * x.2 i = 0 := by
      have := hx (0, x.2)
      simp only [stdP] at this
      rwa [show P₁ x.1 0 = 0 by simpa using h.smulR 0 x.1 0, zero_add] at this
    have h3 : x.2 = 0 := by
      funext i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_self_nonneg (x.2 i))).1 h2 i (Finset.mem_univ _)
      simpa using this
    exact Prod.ext h1 h3
  nondegR y hy := by
    have h1 : y.1 = 0 := h.nondegR _ fun x => by simpa [stdP] using hy (x, 0)
    have h2 : ∑ i, y.2 i * y.2 i = 0 := by
      have := hy (0, y.2)
      simp only [stdP] at this
      rwa [show P₁ 0 y.1 = 0 by simpa using h.smulL 0 0 y.1, zero_add] at this
    have h3 : y.2 = 0 := by
      funext i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_self_nonneg (y.2 i))).1 h2 i (Finset.mem_univ _)
      simpa using this
    exact Prod.ext h1 h3

theorem IsPairing.zero_left {P : V → V → ℝ} (h : IsPairing P) (y : V) : P 0 y = 0 := by
  simpa using h.smulL 0 0 y

theorem IsPairing.zero_right {P : V → V → ℝ} (h : IsPairing P) (x : V) : P x 0 = 0 := by
  simpa using h.smulR 0 x 0

theorem setup_std {P₁ : V₁ → V₁ → ℝ} (h : IsPairing P₁) (k : ℕ) : Setup (stdP P₁ k) P₁ (jStd k) (LStd V₁ k) where
  pair := isPairing_stdP h k
  pair₁ := h
  add w w' := by simp [jStd]
  smul c w := by simp [jStd]
  symp w w' := by simp [omega, stdP, jStd]
  iso := by
    rintro _ ⟨b, rfl⟩ _ ⟨b', rfl⟩
    simp [omega, stdP, h.zero_left]
  orth := by
    rintro _ ⟨b, rfl⟩ w
    simp [omega, stdP, jStd, h.zero_left, h.zero_right]
  max := by
    rintro ⟨⟨a₁, a₂⟩, ⟨b₁, b₂⟩⟩ hL hj
    have e2 : a₂ = 0 := by
      have := hL ((0, 0), (0, a₂)) ⟨a₂, rfl⟩
      simp only [omega, stdP, h.zero_right, h.zero_left, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
        zero_add, sub_zero] at this
      funext i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_self_nonneg (a₂ i))).1 this i (Finset.mem_univ _)
      simpa using this
    have e1 : a₁ = 0 := h.nondegL _ fun y => by
      have := hj (0, y)
      simpa [omega, stdP, jStd, h.zero_left] using this
    have e3 : b₁ = 0 := h.nondegR _ fun x => by
      have := hj (x, 0)
      simpa [omega, stdP, jStd, h.zero_right] using this
    exact ⟨b₂, by simp [e1, e2, e3]⟩

theorem isPairing_mul : IsPairing (fun x y : ℝ => x * y) where
  addL x x' y := add_mul x x' y
  addR x y y' := mul_add x y y'
  smulL c x y := by simp [mul_assoc]
  smulR c x y := by simp only [smul_eq_mul]; ring
  nondegL x hx := by simpa using hx 1
  nondegR y hy := by simpa using hy 1

example : Setup (stdP (fun x y : ℝ => x * y) 1) (fun x y : ℝ => x * y) (jStd 1) (LStd ℝ 1) :=
  setup_std isPairing_mul 1

end Real

section Adelic

open scoped Matrix
open NumberField GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F : Type} [Field F] [NumberField F]

variable (F) in

def trP (κ : Type) [Fintype κ] (y b : κ → mixedEmbedding.mixedSpace F) : ℝ :=
  Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * b i)

def locV {κ : Type} (x : κ → AF F) : κ → mixedEmbedding.mixedSpace F := fun i => evI F (x i)

def liftV {κ : Type} (y : κ → mixedEmbedding.mixedSpace F) : κ → AF F :=
  fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i), 0)

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁}

def jMap (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁)
    (w : (Fin n × Fin d₁ → mixedEmbedding.mixedSpace F) × (Fin n × Fin d₁ → mixedEmbedding.mixedSpace F)) :
    (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F) :=
  let c := M.co.e (incM F (1 : Matrix (Fin n) (Fin n) E) * M₁.co.e.symm (liftV w.1, liftV w.2) * (incM F H'.ι)ᵀ)
  (locV c.1, locV c.2)

def LSet (M : Model σ X W) {d₁ : ℕ} (H' : Plane E d d₁) :
    Set ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) :=
  {l | ∃ u ∈ GlobalTheory.ThK.iso0 (F := F) n H', At (evI F) u ∧ l = (locV (M.co.e u).1, locV (M.co.e u).2)}

end Adelic

end GlobalTheory.ArchUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieDerivativeRealLieSmoothingEqDensityStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieDerivative_realLieSmoothing_eq_density : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (α : Lie E a → ℂ), IsTest (invSet E a) α → ∀ ψ ∈ Sm E a, ∀ (X : Lie E a) (g : GA E a), lieD X (smoothing ν α ψ) g = smoothing ν (dens X α) ψ g := by
  first | exact @GlobalTheory.AutGrowth.lieD_smoothing_eq_dens | exact GlobalTheory.AutGrowth.lieD_smoothing_eq_dens | (intros; apply GlobalTheory.AutGrowth.lieD_smoothing_eq_dens <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocPt
section
noncomputable section

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.FinComm

variable {F : Type} [Field F] [NumberField F]

def indO {κ : Type} (v : Pl F) : (κ → Fv F v) → ℂ :=
  Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1

def locOp (ψ : AddChar (AF F) ℂ) (v : Pl F) {κ : Type} [Fintype κ] (p : (κ → Fv F v) × (κ → Fv F v))
    (φ : (κ → Fv F v) → ℂ) : (κ → Fv F v) → ℂ :=
  fun x => psiLoc ψ v (x ⬝ᵥ p.2 + p.1 ⬝ᵥ p.2 / 2) * φ (x + p.1)

def locPt (v : Pl F) {κ : Type} (p : (κ → AF F) × (κ → AF F)) : (κ → Fv F v) × (κ → Fv F v) :=
  (fun i => evFin F v (p.1 i), fun i => evFin F v (p.2 i))

end GlobalTheory.FinComm
end
end

