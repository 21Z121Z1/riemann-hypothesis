import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1438
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0323
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0325
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0128
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1371
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousDblIncl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1405
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1419
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1425
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1439
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSplitFinMulSplitInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1441
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormLeIncInf
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThK.EvAt0

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def colEq {d d₁ : ℕ} (h : d = d₁ + 2) : Fin d ≃ Fin d₁ ⊕ Fin 2 := (finCongr h).trans finSumFinEquiv.symm

def idx {n d d₁ : ℕ} (h : d = d₁ + 2) : Fin n × Fin d ≃ (Fin n × Fin d₁) ⊕ (Fin n × Fin 2) :=
  (Equiv.prodCongr (Equiv.refl _) (colEq h)).trans (Equiv.prodSumDistrib _ _ _)

def basM {d d₁ : ℕ} (h : d = d₁ + 2) (H' : Plane E d d₁) : Matrix (Fin d) (Fin d) E :=
  fun r c => Sum.elim (fun j => H'.ι r j) (fun k : Fin 2 => if k = 0 then H'.x r else H'.y r) (colEq h c)

def dec {n d d₁ : ℕ} (h : d = d₁ + 2) (H' : Plane E d d₁) :
    Matrix (Fin n) (Fin d) (AE F E) →ₗ[AF F] Matrix (Fin n) (Fin d) (AE F E) where
  toFun w := w * (incM F (basM h H')⁻¹)ᵀ
  map_add' w w' := Matrix.add_mul _ _ _
  map_smul' c w := Matrix.smul_mul _ _ _

def zPart {n d d₁ : ℕ} (h : d = d₁ + 2) (H' : Plane E d d₁) :
    Matrix (Fin n) (Fin d) (AE F E) →ₗ[AF F] Matrix (Fin n) (Fin d₁) (AE F E) where
  toFun w i j := dec h H' w i ((colEq h).symm (Sum.inl j))
  map_add' w w' := by ext i j; simp only [map_add]; rfl
  map_smul' c w := by ext i j; simp only [map_smul]; rfl

def aPart {n d d₁ : ℕ} (h : d = d₁ + 2) (H' : Plane E d d₁) :
    Matrix (Fin n) (Fin d) (AE F E) →ₗ[AF F] (Fin n → AE F E) where
  toFun w i := dec h H' w i ((colEq h).symm (Sum.inr 0))
  map_add' w w' := by ext i; simp only [map_add]; rfl
  map_smul' c w := by ext i; simp only [map_smul]; rfl

def bPart {n d d₁ : ℕ} (h : d = d₁ + 2) (H' : Plane E d d₁) :
    Matrix (Fin n) (Fin d) (AE F E) →ₗ[AF F] (Fin n → AE F E) where
  toFun w i := dec h H' w i ((colEq h).symm (Sum.inr 1))
  map_add' w w' := by ext i; simp only [map_add]; rfl
  map_smul' c w := by ext i; simp only [map_smul]; rfl

variable (F E) in

def tb (h2 : Module.finrank F E = 2) : Module.Basis (Fin 2) (AF F) (AE F E) :=
  Algebra.TensorProduct.basis (AF F) (Module.finBasisOfFinrankEq F E h2)

def tCo (h2 : Module.finrank F E = 2) {n : ℕ} : (Fin n → AE F E) →ₗ[AF F] (Fin n × Fin 2 → AF F) where
  toFun b p := (tb F E h2).repr (b p.1) p.2
  map_add' b b' := by ext p; simp
  map_smul' c b := by ext p; simp

def mCo (σ : E →ₐ[F] E) (h2 : Module.finrank F E = 2) {n : ℕ} (X : Spc F E n) :
    (Fin n → AE F E) →ₗ[AF F] (Fin n × Fin 2 → AF F) where
  toFun a p := Algebra.trace (AF F) (AE F E) (tb F E h2 p.2 * (incM F X.J *ᵥ fun k => cA σ (a k)) p.1)
  map_add' a a' := by
    ext p
    have e : (fun k => cA σ (a k + a' k)) = (fun k => cA σ (a k)) + fun k => cA σ (a' k) := by
      ext k; simp
    simp only [Pi.add_apply]
    rw [e, Matrix.mulVec_add, Pi.add_apply, mul_add, map_add]
  map_smul' c a := by
    ext p
    have e : (fun k => cA σ (c • a k)) = c • fun k => cA σ (a k) := by
      ext k; simp
    simp only [RingHom.id_apply, Pi.smul_apply]
    rw [e, Matrix.mulVec_smul, Pi.smul_apply, mul_smul_comm, map_smul]

def glue {n d d₁ : ℕ} (h : d = d₁ + 2) {R : Type} (p : Fin n × Fin d₁ → R) (q : Fin n × Fin 2 → R) : Fin n × Fin d → R :=
  fun k => Sum.elim p q (idx h k)

theorem glue_inl {n d d₁ : ℕ} (h : d = d₁ + 2) {R : Type} (p : Fin n × Fin d₁ → R) (q : Fin n × Fin 2 → R)
    (j : Fin n × Fin d₁) : glue h p q ((idx h).symm (Sum.inl j)) = p j := by
  simp [glue]

variable (σ : E →ₐ[F] E) {n d d₁ : ℕ} (h2 : Module.finrank F E = 2) (X : Spc F E n) (W : Spc F E d) {W₁ : Spc F E d₁}
  (h : d = d₁ + 2) (H' : Plane E d d₁) (M₁ : Model σ X W₁)

def coL : Matrix (Fin n) (Fin d) (AE F E) →ₗ[AF F] (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F) where
  toFun w := (glue h (M₁.co.e (zPart h H' w)).1 (tCo h2 (bPart h H' w)),
    glue h (M₁.co.e (zPart h H' w)).2 (mCo σ h2 X (aPart h H' w)))
  map_add' w w' := by
    ext k <;> simp only [glue, map_add, Prod.fst_add, Prod.snd_add, Prod.fst_add, Pi.add_apply] <;>
      cases idx h k <;> simp
  map_smul' c w := by
    ext k <;> simp only [glue, map_smul, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, RingHom.id_apply] <;>
      cases idx h k <;> simp

def coA (hb : Function.Bijective (coL σ h2 X h H' M₁))
    (hf : ∀ w w', symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) w w' =
      (coL σ h2 X h H' M₁ w).1 ⬝ᵥ (coL σ h2 X h H' M₁ w').2 - (coL σ h2 X h H' M₁ w').1 ⬝ᵥ (coL σ h2 X h H' M₁ w).2) :
    Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin d) :=
  ⟨LinearEquiv.ofBijective (coL σ h2 X h H' M₁) hb, hf⟩

def latPl (v : Pl F) : Set (Fin n × Fin 2 → Fv F v) :=
  {t | ∃ γ ∈ latAtV X W v, zPart h H' γ = 0 ∧ aPart h H' γ = 0 ∧ t = fun p => evFin F v (tCo h2 (bPart h H' γ) p)}

def vacA (v : Pl F) (x : Fin n × Fin d → Fv F v) : ℂ :=
  Set.indicator (latPl h2 X W h H' v) 1 (fun p => x ((idx h).symm (Sum.inr p))) *
    M₁.vac v (fun q => x ((idx h).symm (Sum.inl q)))

def Ma (M : Model σ X W) (hb : Function.Bijective (coL σ h2 X h H' M₁))
    (hf : ∀ w w', symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) w w' =
      (coL σ h2 X h H' M₁ w).1 ⬝ᵥ (coL σ h2 X h H' M₁ w').2 - (coL σ h2 X h H' M₁ w').1 ⬝ᵥ (coL σ h2 X h H' M₁ w).2) :
    Model σ X W :=
  ⟨coA σ h2 X W h H' M₁ hb hf, vacA σ h2 X W h H' M₁, M.μ, M.dom⟩

omit σ h2 X W H' M₁

def eA : Fn F n d →ₗ[ℂ] Fn F n d₁ := LinearMap.funLeft ℂ ℂ fun y => glue h y 0

def evA (v : Pl F) : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d₁ → Fv F v) → ℂ :=
  LinearMap.funLeft ℂ ℂ fun y => glue h y 0

open scoped Classical in

def incInf : (Fin n × Fin d₁ → mixedEmbedding.mixedSpace F) →L[ℝ] (Fin n × Fin d → mixedEmbedding.mixedSpace F) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => glue h y 0
      map_add' := fun y y' => by funext k; simp only [glue, Pi.add_apply]; cases idx h k <;> simp
      map_smul' := fun c y => by funext k; simp only [glue, Pi.smul_apply, RingHom.id_apply]; cases idx h k <;> simp }

open scoped Classical in
theorem norm_le_incInf (y : Fin n × Fin d₁ → mixedEmbedding.mixedSpace F) : ‖y‖ ≤ ‖incInf h y‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_
  have e : y j = incInf h y ((idx h).symm (Sum.inl j)) := (glue_inl h y 0 j).symm
  rw [e]
  exact norm_le_pi_norm (incInf h y) _

open scoped Classical in

def eiA : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d₁) :=
  SchwartzMap.compCLM ℂ (incInf (F := F) h).hasTemperateGrowth
    ⟨1, 1, fun y => by
      have := norm_le_incInf (F := F) h y
      have h0 := norm_nonneg (incInf (F := F) h y)
      simp only [pow_one, one_mul]
      linarith⟩

end GlobalTheory.ThK.EvAt0
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaneZeroInsertionLinearApply
section
noncomputable section

namespace GlobalTheory.ThK.PlaneEv

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {n d d₁ : ℕ}

def idx (hd : d = d₁ + 2) : Fin n × Fin d ≃ Fin n × Fin d₁ ⊕ Fin n × Fin 2 :=
  ((Equiv.refl (Fin n)).prodCongr ((finCongr hd).trans finSumFinEquiv.symm)).trans (Equiv.prodSumDistrib _ _ _)

def ins0 {R : Type} [Zero R] (hd : d = d₁ + 2) (x : Fin n × Fin d₁ → R) : Fin n × Fin d → R :=
  fun k => Sum.elim x 0 (idx hd k)

section Ins

variable {R : Type} (hd : d = d₁ + 2)

@[simp] theorem planeZeroInsertion_apply_inl [Zero R] (x : Fin n × Fin d₁ → R) (p : Fin n × Fin d₁) :
    ins0 hd x ((idx hd).symm (Sum.inl p)) = x p := by
  simp [ins0]

@[simp] theorem planeZeroInsertion_apply_inr [Zero R] (x : Fin n × Fin d₁ → R) (p : Fin n × Fin 2) :
    ins0 hd x ((idx hd).symm (Sum.inr p)) = 0 := by
  simp [ins0]

theorem ins0_zero [Zero R] : ins0 hd (0 : Fin n × Fin d₁ → R) = 0 := by
  funext k; simp only [ins0]; rcases idx hd k with p | p <;> rfl

theorem ins0_add [AddZeroClass R] (x y : Fin n × Fin d₁ → R) : ins0 hd (x + y) = ins0 hd x + ins0 hd y := by
  funext k; simp only [ins0, Pi.add_apply]; rcases idx hd k with p | p <;> simp

theorem ins0_smul {S : Type} [Zero R] [SMulZeroClass S R] (c : S) (x : Fin n × Fin d₁ → R) :
    ins0 hd (c • x) = c • ins0 hd x := by
  funext k; simp only [ins0, Pi.smul_apply]; rcases idx hd k with p | p <;> simp

theorem ins0_map {R' : Type} [Zero R] [Zero R'] (g : R → R') (hg : g 0 = 0) (x : Fin n × Fin d₁ → R) :
    (fun k => g (ins0 hd x k)) = ins0 hd (fun p => g (x p)) := by
  funext k; simp only [ins0]; rcases idx hd k with p | p <;> simp [hg]

theorem ins0_dotProduct [NonUnitalNonAssocSemiring R] (x : Fin n × Fin d₁ → R) (b : Fin n × Fin d → R) :
    ins0 hd x ⬝ᵥ b = x ⬝ᵥ fun p => b ((idx hd).symm (Sum.inl p)) := by
  simp only [dotProduct]
  rw [← (idx hd).symm.sum_comp, Fintype.sum_sum_type]
  simp

theorem ins0_dotProduct_ins0 [NonUnitalNonAssocSemiring R] (x y : Fin n × Fin d₁ → R) :
    ins0 hd x ⬝ᵥ ins0 hd y = x ⬝ᵥ y := by
  rw [ins0_dotProduct]; simp

end Ins

open scoped Classical

variable (F : Type) [Field F] [NumberField F]

def insertZerosCLM (hd : d = d₁ + 2) :
    (Fin n × Fin d₁ → mixedEmbedding.mixedSpace F) →L[ℝ] (Fin n × Fin d → mixedEmbedding.mixedSpace F) :=
  LinearMap.toContinuousLinearMap
    { toFun := ins0 hd
      map_add' := ins0_add hd
      map_smul' := fun c x => ins0_smul hd c x }

@[simp] theorem planeZeroInsertionLinear_apply (hd : d = d₁ + 2) (x : Fin n × Fin d₁ → mixedEmbedding.mixedSpace F) :
    insertZerosCLM F hd x = ins0 hd x := rfl

theorem norm_le_ins0 (hd : d = d₁ + 2) (x : Fin n × Fin d₁ → mixedEmbedding.mixedSpace F) : ‖x‖ ≤ ‖ins0 hd x‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun p => ?_
  have := norm_le_pi_norm (ins0 hd x) ((idx hd).symm (Sum.inl p))
  rwa [planeZeroInsertion_apply_inl] at this

def ei (hd : d = d₁ + 2) : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d₁) :=
  SchwartzMap.compCLM ℂ (insertZerosCLM F hd).hasTemperateGrowth
    ⟨1, 1, fun x => by
      have := norm_le_ins0 F hd x
      simp only [planeZeroInsertionLinear_apply, pow_one, one_mul]
      linarith [norm_nonneg (ins0 hd x)]⟩

@[simp] theorem ei_apply (hd : d = d₁ + 2) (f : SInf F (Fin n × Fin d)) (x : Fin n × Fin d₁ → mixedEmbedding.mixedSpace F) :
    ei F hd f x = f (ins0 hd x) := rfl

variable {F}

def ev (hd : d = d₁ + 2) (v : Pl F) : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d₁ → Fv F v) → ℂ :=
  LinearMap.funLeft ℂ ℂ (ins0 hd)

@[simp] theorem ev_apply (hd : d = d₁ + 2) (v : Pl F) (φ : (Fin n × Fin d → Fv F v) → ℂ) (x : Fin n × Fin d₁ → Fv F v) :
    ev hd v φ x = φ (ins0 hd x) := rfl

variable (F) in

def evA (hd : d = d₁ + 2) : Fn F n d →ₗ[ℂ] Fn F n d₁ := LinearMap.funLeft ℂ ℂ (ins0 hd)

@[simp] theorem evA_apply (hd : d = d₁ + 2) (Φ : Fn F n d) (x : Fin n × Fin d₁ → AF F) : evA F hd Φ x = Φ (ins0 hd x) := rfl

theorem ei_ne_zero (hd : d = d₁ + 2) : ei (n := n) F hd ≠ 0 := by
  classical
  intro h
  let b : ContDiffBump (0 : Fin n × Fin d → mixedEmbedding.mixedSpace F) := ⟨1, 2, one_pos, one_lt_two⟩
  have hs : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) := b.hasCompactSupport.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun x => ((b x : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp b.contDiff
  have h1 := congrArg (fun T : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d₁) => T (hs.toSchwartzMap hc) 0) h
  have h2 : b 0 = 1 := b.one_of_mem_closedBall (by simp [b])
  simp [ins0_zero, h2] at h1

theorem evA_pure (hd : d = d₁ + 2) (f : SInf F (Fin n × Fin d)) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) :
    evA F hd (pure f φ) = pure (ei F hd f) fun v => ev hd v (φ v) := by
  funext x
  simp only [evA_apply, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, ei_apply, ev_apply]
  rw [ins0_map hd (evI F) (by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : AF F).1 = 0
    rw [show (0 : AF F).1 = 0 from rfl, map_zero])]
  congr 1
  congr 1
  funext v
  rw [ins0_map hd (evFin F v) (map_zero _)]

end GlobalTheory.ThK.PlaneEv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticModelRationalCoordinates
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.RatCoord

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def hat {κ : Type} (w : (κ → F) × (κ → F)) : (κ → AF F) × (κ → AF F) :=
  (fun i => algebraMap F (AF F) (w.1 i), fun i => algebraMap F (AF F) (w.2 i))

theorem hat_injective {κ : Type} : Function.Injective (hat (F := F) (κ := κ)) := by
  intro w w' h
  have hinj := AdeleRing.algebraMap_injective (𝓞 F) F
  simp only [hat, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  ext i
  · exact hinj (congrFun h1 i)
  · exact hinj (congrFun h2 i)

theorem hat_add {κ : Type} (w w' : (κ → F) × (κ → F)) : hat (w + w') = hat w + hat w' := by
  simp only [hat, Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add]; rfl

theorem hat_smul {κ : Type} (c : F) (w : (κ → F) × (κ → F)) :
    hat (c • w) = algebraMap F (AF F) c • hat w := by
  simp only [hat, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, map_mul]; rfl

theorem incM_add {m k : Type} (x x' : Matrix m k E) : incM F (x + x') = incM F x + incM F x' := by
  ext i j; simp [incM]

theorem incM_smul' {m k : Type} (c : F) (x : Matrix m k E) :
    incM F (c • x) = algebraMap F (AF F) c • incM F x := by
  ext i j
  simp only [incM, Matrix.map_apply, Matrix.smul_apply]
  show (1 : AF F) ⊗ₜ[F] (c • x i j) = algebraMap F (AF F) c • ((1 : AF F) ⊗ₜ[F] x i j)
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem incM_injective {m k : Type} : Function.Injective (incM F (E := E) (m := m) (n := k)) := by
  intro x x' h
  have hinj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
    Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 F) F)
  ext i j
  exact hinj (congrFun (congrFun h i) j)

end GlobalTheory.RatCoord

open GlobalTheory.RatCoord in
theorem GlobalTheory.RatCoord.ratEquiv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ), M.IsGood ψ → Module.finrank F E = 2 → ∃ Φ : Matrix (Fin n) (Fin d) E ≃ₗ[F] (Fin n × Fin d → F) × (Fin n × Fin d → F), ∀ x, M.co.e (incM F x) = ((fun i => algebraMap F (AF F) ((Φ x).1 i)), (fun i => algebraMap F (AF F) ((Φ x).2 i))) := by
  intro F E _ _ _ _ _ σ n d X W M ψ hM hE
  classical
  let Φ₀ : Matrix (Fin n) (Fin d) E → (Fin n × Fin d → F) × (Fin n × Fin d → F) :=
    fun x => ((hM.rat x).choose, (hM.rat x).choose_spec.choose)
  have hΦ₀ : ∀ x, M.co.e (incM F x) = hat (Φ₀ x) := fun x => (hM.rat x).choose_spec.choose_spec
  let L : Matrix (Fin n) (Fin d) E →ₗ[F] (Fin n × Fin d → F) × (Fin n × Fin d → F) :=
    { toFun := Φ₀
      map_add' := fun x x' => by
        apply hat_injective
        rw [hat_add, ← hΦ₀, ← hΦ₀, ← hΦ₀, incM_add, map_add]
      map_smul' := fun c x => by
        apply hat_injective
        rw [RingHom.id_apply, hat_smul, ← hΦ₀, ← hΦ₀, incM_smul', LinearEquiv.map_smul] }
  have hinj : Function.Injective L := by
    intro x x' h
    apply incM_injective (F := F)
    apply M.co.e.injective
    rw [hΦ₀, hΦ₀]
    exact congrArg hat h
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  have hrank : Module.finrank F (Matrix (Fin n) (Fin d) E) =
      Module.finrank F ((Fin n × Fin d → F) × (Fin n × Fin d → F)) := by
    rw [Module.finrank_matrix, Module.finrank_prod, Module.finrank_fintype_fun_eq_card, hE,
      Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    ring
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).1 hinj
  refine ⟨LinearEquiv.ofBijective L ⟨hinj, hsurj⟩, fun x => ?_⟩
  exact hΦ₀ x
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalBoundedInfiniteCompactFinitePolyCountStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_boundedInfinite_compactFinite_polyCount : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], ∃ m : ℕ, ∀ Kf : Set (Af E), IsCompact Kf → ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T → {ξ : E | ‖pInf E (algebraMap E (Ad E) ξ)‖ ≤ T ∧ pFin E (algebraMap E (Ad E) ξ) ∈ Kf}.Finite ∧ ({ξ : E | ‖pInf E (algebraMap E (Ad E) ξ)‖ ≤ T ∧ pFin E (algebraMap E (Ad E) ξ) ∈ Kf}.ncard : ℝ) ≤ C * T ^ m := by
  first | exact @GlobalTheory.rat_bounded_compact_polynomial | exact GlobalTheory.rat_bounded_compact_polynomial | (intros; apply GlobalTheory.rat_bounded_compact_polynomial <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLieSmoothingMemSlowlyIncreasingStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realLieSmoothing_mem_slowlyIncreasing : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (α : Lie E a → ℂ), IsTest (invSet E a) α → ∀ f ∈ growth E a, smoothing ν α f ∈ growth E a := by
  first | exact @GlobalTheory.AutGrowth.smoothing_mem_growth | exact GlobalTheory.AutGrowth.smoothing_mem_growth | (intros; apply GlobalTheory.AutGrowth.smoothing_mem_growth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLieSmoothingMemSmoothAdelicFunctionsStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realLieSmoothing_mem_smoothAdelicFunctions : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (α : Lie E a → ℂ), IsTest (invSet E a) α → ∀ ψ ∈ Sm E a, smoothing ν α ψ ∈ Sm E a := by
  first | exact @GlobalTheory.AutGrowth.smoothing_mem_Sm | exact GlobalTheory.AutGrowth.smoothing_mem_Sm | (intros; apply GlobalTheory.AutGrowth.smoothing_mem_Sm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealPlaceComponentAdeleConjugationEqComplexConj
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.RealPlaceConj

theorem piInf_cA_eq_star : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (w : InfinitePlace F) (τ : EmbOver E w) (z : AE F E), piInf τ (cA σ z) = star (piInf τ z) := by
  intro F E _ _ _ _ _ σ hσ w τ z

  have hcomp : compInf F E w (cA σ z) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ (compInf F E w z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      simp [cA, compInf, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Algebra.TensorProduct.map_tmul]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

  change infEmb τ (compInf F E w (cA σ z)) = star (infEmb τ (compInf F E w z))
  rw [hcomp, ← GlobalTheory.AdelicU.infEmb_sigR hσ τ]
  rfl

end GlobalTheory.RealPlaceConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealPlaceSplittingConstantEqDoubledSpace
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

namespace GlobalTheory.RealLift.Compare

theorem constant_eq_dbl :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) (Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ)
    (Φd : Tens F P Q (R + S) (S + R) →ₗ[ℂ] SInf F (κ ⊕ κ))
    (om : UG (cA σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)) (omd : UG (cA σ) (dbl JB) →* Module.End ℂ ((κ ⊕ κ → AF F) → ℂ))
    (c cd : InfinitePlace F → ℂ),
    IsCMExt F E σ → IsStd ψ → IsFockMap ψ τ d A C Φ →
    (∀ (g : UG (cA σ) JB) (gd : UG (cA σ) (dbl JB)),
      ((gd : GL (β ⊕ β) (AE F E)) : Matrix (β ⊕ β) (β ⊕ β) (AE F E)) =
        Matrix.fromBlocks ((g : GL β (AE F E)) : Matrix β β (AE F E)) 0 0 1 →
      ∀ φ₁ ∈ (adeleClass F).sp κ, ∀ φ₂ ∈ (adeleClass F).sp κ, omd gd (boxFun φ₁ φ₂) = boxFun (om g φ₁) φ₂) →
    ActsBy τ C om Φ (fockAct2 P Q R S) c →
    ActsBy τ (fun w => dblM (C w)) omd Φd (fockAct2 P Q (R + S) (S + R)) cd →
    (∃ z : ℂ, z ≠ 0 ∧ ∀ x : κ ⊕ κ → mixedEmbedding.mixedSpace F,
      Φd (PiTensorProduct.tprod ℂ fun _ => 1) x = z * Φ (PiTensorProduct.tprod ℂ fun _ => 1) (x ∘ Sum.inl) *
        star (Φ (PiTensorProduct.tprod ℂ fun _ => 1) (x ∘ Sum.inr))) →
    0 < R + S → ∀ w, c w = cd w :=
  compare_of GlobalTheory.T.exists_central_circle_oneParameter_unitary_realPlace GlobalTheory.VacuumWeight.fockAct2_diagonal_one GlobalTheory.tprod_one_pol_ne_zero

end GlobalTheory.RealLift.Compare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealStableOfCharactersStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_stable_of_characters : GlobalTheory.Published.HarishChandraCharacters → RealStable := by
  first | exact @GlobalTheory.TrMult.realStable_of_harishChandra | exact GlobalTheory.TrMult.realStable_of_harishChandra | (intros; apply GlobalTheory.TrMult.realStable_of_harishChandra <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatMatrixCoefficientCompactSupportFinStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix GlobalTheory.VacAny
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_matrixCoefficient_compactSupport_finitePlace : ∀ {F : Type} [Field F] [NumberField F] (v : Pl F) (ψ₀ : AddChar (Fv F v) ℂ) (κ : Type) [Fintype κ]
    [MeasurableSpace (κ → Fv F v)] [BorelSpace (κ → Fv F v)] (μ : MeasureTheory.Measure (κ → Fv F v))
    [μ.IsAddHaarMeasure], Continuous ψ₀ →
    (∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, ψ₀ (x * y) = 1) → x ∈ v.adicCompletionIntegers F) →
    ∀ φ ∈ SB (κ → Fv F v), ∀ g ∈ SB (κ → Fv F v),
    ∃ C : Set ((κ → Fv F v) × (κ → Fv F v)), IsCompact C ∧
      ∀ w, ∫ y, schr ψ₀ w φ y * (starRingEnd ℂ) (g y) ∂μ ≠ 0 → w ∈ C := by
  first | exact @GlobalTheory.SchrSuppFin.support_compact | exact GlobalTheory.SchrSuppFin.support_compact | (intros; apply GlobalTheory.SchrSuppFin.support_compact <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanInfinitePlacesWeightRepresentationEqTopStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_infinitePlacesWeightRepresentation_eq_top : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (lam : InfinitePlace E → DomWeight n), Submodule.span ℂ (Set.range fun x : infU E n => wInf lam (x : UA E n)) = ⊤ := by
  first | exact @GlobalTheory.BCT.TrKer.span_wInf_infU_eq_top | exact GlobalTheory.BCT.TrKer.span_wInf_infU_eq_top | (intros; apply GlobalTheory.BCT.TrKer.span_wInf_infU_eq_top <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLocalFinitenessRegularSemisimpleCentralizStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_local_finiteness_regular_semisimple_centralizer : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (y : UL n w), y.1.val.charpoly.Separable → ∀ K' : Subgroup (UL n w), IsLevel (MonoidHom.id _) (KL n w) K' → (∀ x : UL n w, twCent (MonoidHom.id _) y ⊓ (KL n w).map (MulAut.conj x).toMonoidHom ≤ cptPart (twCent (MonoidHom.id _) y) ∧ (twCent (MonoidHom.id _) y ⊓ K'.map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent (MonoidHom.id _) y)) ≠ 0) ∧ ∀ C : Set (UL n w), IsCompact C → {q : DoubleCoset.Quotient (twCent (MonoidHom.id (UL n w)) y : Set (UL n w)) (K' : Set (UL n w)) | (Quotient.out q)⁻¹ * y * Quotient.out q ∈ C}.Finite := by
  first | exact @GlobalTheory.LocFinU.locFin | exact GlobalTheory.LocFinU.locFin | (intros; apply GlobalTheory.LocFinU.locFin <;> assumption)
end

