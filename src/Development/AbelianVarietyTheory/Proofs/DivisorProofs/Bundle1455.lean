import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1434
import Formalism.RealPlaceAnalysis.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralUnipotentRadicalConjToSquareInertPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1406
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1435
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneComplementForm
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.LeviPlaneSection

open Matrix

section Alg

variable {S : Type*} [CommRing S] {m : Type*} [Fintype m] [DecidableEq m] {k : ℕ}

def conjM (Q : Matrix m (Fin k ⊕ Fin 2) S) (R : Matrix (Fin k ⊕ Fin 2) m S) (a : Matrix (Fin k) (Fin k) S) :
    Matrix m m S :=
  Q * fromBlocks a (0 : Matrix (Fin k) (Fin 2) S) 0 (1 : Matrix (Fin 2) (Fin 2) S) * R

theorem conjM_mul {Q : Matrix m (Fin k ⊕ Fin 2) S} {R : Matrix (Fin k ⊕ Fin 2) m S} (hRQ : R * Q = 1)
    (a b : Matrix (Fin k) (Fin k) S) : conjM Q R a * conjM Q R b = conjM Q R (a * b) := by
  have h : fromBlocks a 0 0 1 * (R * Q) * fromBlocks b 0 0 (1 : Matrix (Fin 2) (Fin 2) S) = fromBlocks (a * b) 0 0 1 := by
    rw [hRQ, Matrix.mul_one, fromBlocks_multiply]; simp
  unfold conjM
  rw [← h]; simp only [Matrix.mul_assoc]

theorem conjM_one {Q : Matrix m (Fin k ⊕ Fin 2) S} {R : Matrix (Fin k ⊕ Fin 2) m S} (hQR : Q * R = 1) :
    conjM Q R (1 : Matrix (Fin k) (Fin k) S) = 1 := by
  unfold conjM; rw [fromBlocks_one, Matrix.mul_one, hQR]

def conjHom {Q : Matrix m (Fin k ⊕ Fin 2) S} {R : Matrix (Fin k ⊕ Fin 2) m S} (hRQ : R * Q = 1) (hQR : Q * R = 1) :
    Matrix (Fin k) (Fin k) S →* Matrix m m S where
  toFun := conjM Q R
  map_one' := conjM_one hQR
  map_mul' a b := (conjM_mul hRQ a b).symm

theorem conjM_map {T : Type*} [CommRing T] (f : S →+* T) (Q : Matrix m (Fin k ⊕ Fin 2) S) (R : Matrix (Fin k ⊕ Fin 2) m S)
    (a : Matrix (Fin k) (Fin k) S) : (conjM Q R a).map f = conjM (Q.map f) (R.map f) (a.map f) := by
  simp [conjM, Matrix.map_mul, fromBlocks_map]

theorem conjM_unitary (c : S →+* S) {Q : Matrix m (Fin k ⊕ Fin 2) S} {R : Matrix (Fin k ⊕ Fin 2) m S} {J : Matrix m m S}
    {J₁ : Matrix (Fin k) (Fin k) S} {S₂ : Matrix (Fin 2) (Fin 2) S}
    (hK : Qᵀ * J * Q.map c = fromBlocks J₁ 0 0 S₂) (hQR : Q * R = 1) {a : Matrix (Fin k) (Fin k) S}
    (ha : aᵀ * J₁ * a.map c = J₁) : (conjM Q R a)ᵀ * J * (conjM Q R a).map c = J := by
  have h1 : Rᵀ * Qᵀ = 1 := by rw [← transpose_mul, hQR, transpose_one]
  have h2 : Q.map c * R.map c = 1 := by rw [← Matrix.map_mul, hQR, Matrix.map_one c (map_zero c) (map_one c)]
  have hmid : (fromBlocks a 0 0 (1 : Matrix (Fin 2) (Fin 2) S))ᵀ * fromBlocks J₁ 0 0 S₂ *
      (fromBlocks a 0 0 (1 : Matrix (Fin 2) (Fin 2) S)).map c = fromBlocks J₁ 0 0 S₂ := by
    rw [fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, fromBlocks_multiply]
    simp [ha, Matrix.map_one c (map_zero c) (map_one c)]
  calc (conjM Q R a)ᵀ * J * (conjM Q R a).map c
      = Rᵀ * ((fromBlocks a 0 0 (1 : Matrix (Fin 2) (Fin 2) S))ᵀ * (Qᵀ * J * Q.map c) *
          (fromBlocks a 0 0 (1 : Matrix (Fin 2) (Fin 2) S)).map c) * R.map c := by
        simp only [conjM, transpose_mul, Matrix.map_mul, Matrix.mul_assoc]
    _ = Rᵀ * Qᵀ * J * (Q.map c * R.map c) := by rw [hK, hmid, ← hK]; simp only [Matrix.mul_assoc]
    _ = J := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

end Alg

section Forms

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem gram_apply (σ : E →ₐ[F] E) {N : ℕ} {ι₁ ι₂ : Type*} (J : Matrix (Fin N) (Fin N) E) (A : Matrix (Fin N) ι₁ E)
    (B : Matrix (Fin N) ι₂ E) (i : ι₁) (j : ι₂) :
    (Aᵀ * J * B.map σ) i j = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J (fun r => A r i) (fun r => B r j) := by
  simp only [Matrix.mul_apply, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, dotProduct, mulVec, transpose_apply, map_apply, Finset.sum_mul,
    Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem form_skew {σ : E →ₐ[F] E} (hσ : ∀ e, σ (σ e) = e) {N : ℕ} {J : Matrix (Fin N) (Fin N) E}
    (hsk : ∀ i j, σ (J j i) = -J i j) (a b : Fin N → E) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J a b = -σ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J b a) := by
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, dotProduct, mulVec, map_sum, map_mul, hσ, Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hsk]; ring

end Forms

theorem cA_inclR' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [cA, inclR, Algebra.TensorProduct.includeRight_apply]

theorem continuous_unitsMap {M N : Type*} [Monoid M] [Monoid N] [TopologicalSpace M] [TopologicalSpace N]
    (φ : M →* N) (hφ : Continuous φ) : Continuous (Units.map φ) :=
  Units.continuous_iff.2 ⟨hφ.comp Units.continuous_val,
    (hφ.comp Units.continuous_coe_inv).congr fun x => (Units.coe_map_inv φ x).symm⟩

set_option maxHeartbeats 1000000 in

theorem leviSection : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n n₁ : ℕ} (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁), (∀ x, σ (σ x) = x) →
    (∀ i j, σ (Y.J j i) = -Y.J i j) → n = n₁ + 2 → form σ Y.J H.x H.x = 0 → form σ Y.J H.y H.y = 0 → form σ Y.J H.x H.y = 1 →
    (∀ u, form σ Y.J (H.ι *ᵥ u) H.x = 0 ∧ form σ Y.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * Y.J * H.ι.map σ = Y₁.J → Y₁.J.det ≠ 0 →
    ∃ M : UA σ Y₁.J → UA σ Y.J, Continuous M ∧ (∀ h₁, IsLevi (W₁ := Y₁) H 1 h₁ (M h₁)) ∧
      ∀ γ ∈ ratU σ Y₁.J, M γ ∈ ratU σ Y.J := by
  intro F E _ _ _ _ _ σ n n₁ Y Y₁ H hσ hsk hn hxx hyy hxy horth hgram hdet
  subst hn
  set XY : Matrix (Fin (n₁ + 2)) (Fin 2) E := Matrix.of fun r t => ![H.x, H.y] t r with hXY
  set Q : Matrix (Fin (n₁ + 2)) (Fin n₁ ⊕ Fin 2) E := fromCols H.ι XY with hQ
  set S₂ : Matrix (Fin 2) (Fin 2) E := !![0, 1; -1, 0] with hS₂
  have hyx : form σ Y.J H.y H.x = -1 := by rw [form_skew hσ hsk, hxy, map_one]
  have horth' : ∀ i, form σ Y.J (fun r => H.ι r i) H.x = 0 ∧ form σ Y.J (fun r => H.ι r i) H.y = 0 := by
    intro i
    have e : (fun r => H.ι r i) = H.ι *ᵥ Pi.single i 1 := by
      funext r; simp [mulVec, dotProduct, Pi.single_apply]
    rw [e]; exact horth _
  have hK : Qᵀ * Y.J * Q.map σ = fromBlocks Y₁.J 0 0 S₂ := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · rw [fromBlocks_apply₁₁, ← hgram, gram_apply, gram_apply]; rfl
    · rw [fromBlocks_apply₁₂, gram_apply]
      fin_cases j
      · simpa [Q, XY] using (horth' i).1
      · simpa [Q, XY] using (horth' i).2
    · rw [fromBlocks_apply₂₁, gram_apply, form_skew hσ hsk]
      fin_cases i
      · simp [Q, XY, (horth' j).1]
      · simp [Q, XY, (horth' j).2]
    · rw [fromBlocks_apply₂₂, gram_apply]
      fin_cases i <;> fin_cases j <;> simp [Q, XY, S₂, hxx, hyy, hxy, hyx]
  have hdetK : (fromBlocks Y₁.J 0 0 S₂).det ≠ 0 := by
    rw [det_fromBlocks_zero₂₁]; simp [S₂, Matrix.det_fin_two_of, hdet]
  have hKu : IsUnit (fromBlocks Y₁.J 0 0 S₂).det := isUnit_iff_ne_zero.2 hdetK
  set R : Matrix (Fin n₁ ⊕ Fin 2) (Fin (n₁ + 2)) E := ((fromBlocks Y₁.J 0 0 S₂)⁻¹ * Qᵀ * Y.J).map σ with hR
  have h0 : (fromBlocks Y₁.J 0 0 S₂)⁻¹ * Qᵀ * Y.J * Q.map σ = 1 := by
    have : (fromBlocks Y₁.J 0 0 S₂)⁻¹ * Qᵀ * Y.J * Q.map σ = (fromBlocks Y₁.J 0 0 S₂)⁻¹ * (Qᵀ * Y.J * Q.map σ) := by
      simp only [Matrix.mul_assoc]
    rw [this, hK, nonsing_inv_mul _ hKu]
  have hQQ : (Q.map σ).map (σ : E →+* E) = Q := by ext i j; simp [hσ]
  have hRQ : R * Q = 1 := by
    calc R * Q = ((fromBlocks Y₁.J 0 0 S₂)⁻¹ * Qᵀ * Y.J).map (σ : E →+* E) * (Q.map σ).map (σ : E →+* E) := by
          rw [hQQ]; rfl
      _ = ((fromBlocks Y₁.J 0 0 S₂)⁻¹ * Qᵀ * Y.J * Q.map σ).map (σ : E →+* E) := Matrix.map_mul.symm
      _ = 1 := by rw [h0]; exact Matrix.map_one _ (map_zero _) (map_one _)
  have hQR : Q * R = 1 := (mul_eq_one_comm_of_equiv finSumFinEquiv).1 hRQ
  set f : E →+* AE F E := inclR (F := F) (AF F) with hf
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hRQA : R.map f * Q.map f = 1 := by rw [← Matrix.map_mul, hRQ, Matrix.map_one f (map_zero f) (map_one f)]
  have hQRA : Q.map f * R.map f = 1 := by rw [← Matrix.map_mul, hQR, Matrix.map_one f (map_zero f) (map_one f)]
  have hcf : ∀ {a b : Type} (X : Matrix a b E), (X.map f).map (cA σ) = (X.map σ).map f := fun X => by
    ext i j; exact cA_inclR' σ _
  have hKA : (Q.map f)ᵀ * incM F Y.J * (Q.map f).map (cA σ).toRingHom = fromBlocks (incM F Y₁.J) 0 0 (S₂.map f) := by
    change (Q.map f)ᵀ * Y.J.map f * (Q.map f).map (cA σ) = fromBlocks (Y₁.J.map f) 0 0 (S₂.map f)
    rw [hcf, ← transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hK, fromBlocks_map]
    simp
  let φ := conjHom hRQA hQRA
  have hmem : ∀ h : UA σ Y₁.J, Units.map φ h.1 ∈ UG (cA σ) (incM F Y.J) := by
    intro h
    show (conjM (Q.map f) (R.map f) (h.1 : Matrix _ _ (AE F E)))ᵀ * incM F Y.J *
      (conjM (Q.map f) (R.map f) (h.1 : Matrix _ _ (AE F E))).map (cA σ) = incM F Y.J
    exact conjM_unitary (cA σ).toRingHom hKA hQRA h.2
  let Mf : UA σ Y₁.J → UA σ Y.J := fun h => ⟨Units.map φ h.1, hmem h⟩
  have hmat : ∀ h, mat (Mf h) = conjM (Q.map f) (R.map f) (mat h) := fun h => rfl
  refine ⟨Mf, ?_, ?_, ?_⟩
  · have hφ : Continuous φ := by
      change Continuous fun a => conjM (Q.map f) (R.map f) a
      unfold conjM
      exact (continuous_const.matrix_mul (continuous_id.matrix_fromBlocks continuous_const continuous_const
        continuous_const)).matrix_mul continuous_const
    exact Continuous.subtype_mk ((continuous_unitsMap φ hφ).comp continuous_subtype_val) _
  · intro h
    have hMQ : mat (Mf h) * Q.map f = Q.map f * fromBlocks (mat h) 0 0 (1 : Matrix (Fin 2) (Fin 2) (AE F E)) := by
      rw [hmat]; unfold conjM; rw [Matrix.mul_assoc, hRQA, Matrix.mul_one]
    have hcol : ∀ t : Fin 2, mat (Mf h) *ᵥ (fun r => f (XY r t)) = fun r => f (XY r t) := by
      intro t
      have e1 : (fun r => f (XY r t)) = Q.map f *ᵥ Pi.single (Sum.inr t) 1 := by
        funext r; simp [Q, mulVec, dotProduct, Pi.single_apply]
      have e2 : fromBlocks (mat h) 0 0 (1 : Matrix (Fin 2) (Fin 2) (AE F E)) *ᵥ Pi.single (Sum.inr t) 1 =
          Pi.single (Sum.inr t) 1 := by
        ext i; rcases i with i | i <;> simp [mulVec, dotProduct, Pi.single_apply, one_apply, Fintype.sum_sum_type]
      rw [e1, mulVec_mulVec, hMQ, ← mulVec_mulVec, e2]
    refine ⟨?_, ?_, ?_⟩
    · rw [Units.val_one, one_smul]; exact hcol 0
    · rw [inv_one, Units.val_one, map_one, one_smul]; exact hcol 1
    · have e3 : incM F H.ι = Q.map f * fromRows (1 : Matrix (Fin n₁) (Fin n₁) (AE F E)) (0 : Matrix (Fin 2) (Fin n₁) (AE F E)) := by
        ext r k; simp [incM, Q, mul_apply, Fintype.sum_sum_type, one_apply, hf]
      have e4 : fromBlocks (mat h) 0 0 (1 : Matrix (Fin 2) (Fin 2) (AE F E)) *
          fromRows (1 : Matrix (Fin n₁) (Fin n₁) (AE F E)) (0 : Matrix (Fin 2) (Fin n₁) (AE F E)) =
          fromRows (1 : Matrix (Fin n₁) (Fin n₁) (AE F E)) (0 : Matrix (Fin 2) (Fin n₁) (AE F E)) * mat h := by
        ext i k; rcases i with i | i <;> simp [mul_apply, Fintype.sum_sum_type, one_apply]
      rw [e3, ← Matrix.mul_assoc, hMQ, Matrix.mul_assoc, e4, Matrix.mul_assoc]
  · intro γ hγ
    rw [ratU, Subgroup.mem_subgroupOf] at hγ ⊢
    obtain ⟨g, hg⟩ := hγ
    refine ⟨Units.map (conjHom hRQ hQR) g, ?_⟩
    have hgv : (g : Matrix (Fin n₁) (Fin n₁) E).map f = mat γ := by
      ext a b; rw [Matrix.map_apply, ← Matrix.GeneralLinearGroup.map_apply, hg]; rfl
    apply Matrix.GeneralLinearGroup.ext; intro i j
    rw [Matrix.GeneralLinearGroup.map_apply]
    change f (conjM Q R (g : Matrix _ _ E) i j) = conjM (Q.map f) (R.map f) (mat γ) i j
    rw [← hgv, ← conjM_map]; rfl

end GlobalTheory.LeviPlaneSection

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelesInf
section
open scoped TensorProduct NNReal Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section
namespace GlobalTheory.ThKCtFin

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def idelesInf : Set (AE F E)ˣ := {a | At (evI F) ((a : AE F E) - 1)}

def idelesFin : Set (AE F E)ˣ := {u | At (fun x : AF F => x.2) ((u : AE F E) - 1)}

example : (1 : (AE F E)ˣ) ∈ idelesInf F E := fun _ _ => by simp
example : (1 : (AE F E)ˣ) ∈ idelesFin F E := fun _ _ => by simp

end GlobalTheory.ThKCtFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImgSet
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThK.CycGen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def DecOn (B : Base F E) {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (T : Finset (Pl F))
    (Ψ : (Fin n × Fin d → AF F) → ℂ) (m : ℕ) (f : Fin m → SInf F (Fin n × Fin d))
    (φ : Fin m → ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) : Prop :=
  (∀ j, f j ∈ M.Pol B.ψ B.emb ∧ (∀ v, φ j v ∈ SB _) ∧ ∀ v ∉ T, φ j v = M.vac v) ∧ Ψ = ∑ j, pure (f j) (φ j)

def imgOn {a a' : ℕ} (R : RealMaps F a a') (Rf : FinMaps F a a') (T : Finset (Pl F)) (m : ℕ)
    (f : Fin m → SInf F (Fin a' × Fin (a + a'))) (φ : Fin m → ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ) :
    R.Pi ⊗[ℂ] (⨂[ℂ] v : T, Rf.Pi v) :=
  ∑ j, R.p' (f j) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => Rf.p' v (φ j v))

def ImgSet {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (R : RealMaps F a a') (Rf : FinMaps F a a') (T : Finset (Pl F))
    (S : Submodule ℂ ((Fin a' × Fin (a + a') → AF F) → ℂ)) : Set (R.Pi ⊗[ℂ] (⨂[ℂ] v : T, Rf.Pi v)) :=
  {x | ∃ Ψ ∈ S, ∃ (m : ℕ) (f : Fin m → SInf F (Fin a' × Fin (a + a'))) (φ : Fin m → ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ),
    DecOn B G.M' T Ψ m f φ ∧ imgOn R Rf T m f φ = x}

end GlobalTheory.ThK.CycGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
section
noncomputable section

namespace GlobalTheory.IndLine

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Fin

variable {n d n₁ d₁ : ℕ} {Y : Spc F E n} {W : Spc F E d} {Y₁ : Spc F E n₁} {W₁ : Spc F E d₁}

structure IsIndMap (v : Pl F) (om : Rep σ Y W) (om₁ : Rep σ Y₁ W₁) {P P₁ : Type} [AddCommGroup P] [Module ℂ P]
    [AddCommGroup P₁] [Module ℂ P₁] (p : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] P)
    (p₁ : ((Fin n₁ × Fin d₁ → Fv F v) → ℂ) →ₗ[ℂ] P₁) (H' : Plane E d d₁) (χ : Chr F E) (z : ℝ)
    (A : P →ₗ[ℂ] (UA σ W.J → P₁)) : Prop where
  right : ∀ g ∈ UAt σ W (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
    Acts (evFin F v) (om (1, g)) φ φ₁ → ∀ h ∈ UAt σ W (evFin F v), A (p φ₁) h = A (p φ) (h * g)
  unip : ∀ u ∈ unip σ W H', u ∈ UAt σ W (evFin F v) → ∀ x, ∀ h ∈ UAt σ W (evFin F v), A x (u * h) = A x h
  levi : ∀ (t : (AE F E)ˣ) (h₁ : UA σ W₁.J) (m : UA σ W.J), IsLevi H' t h₁ m → m ∈ UAt σ W (evFin F v) →
    h₁ ∈ UAt σ W₁ (evFin F v) → ∀ φ ∈ SB (Fin n₁ × Fin d₁ → Fv F v), ∀ φ₁ ∈ SB (Fin n₁ × Fin d₁ → Fv F v),
    Acts (evFin F v) (om₁ (1, h₁)) φ φ₁ → ∀ x, ∀ h ∈ UAt σ W (evFin F v), A x h = p₁ φ →
      A x (m * h) = ((χ t : ℂ) * (((absE F E t : ℝ) ^ z : ℝ) : ℂ)) • p₁ φ₁

def IndLineFin (v : Pl F) (om : Rep σ Y W) (om₁ : Rep σ Y₁ W₁) {P P₁ : Type} [AddCommGroup P] [Module ℂ P]
    [AddCommGroup P₁] [Module ℂ P₁] (p : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] P)
    (p₁ : ((Fin n₁ × Fin d₁ → Fv F v) → ℂ) →ₗ[ℂ] P₁) (H' : Plane E d d₁) (χ : Chr F E) (z : ℝ) : Prop :=
  ∀ A A' : P →ₗ[ℂ] (UA σ W.J → P₁), IsIndMap v om om₁ p p₁ H' χ z A → IsIndMap v om om₁ p p₁ H' χ z A' →
    (∀ x, ∀ h ∈ UAt σ W (evFin F v), A x h = 0) ∨ ∃ c : ℂ, ∀ x, ∀ h ∈ UAt σ W (evFin F v), A' x h = c • A x h

end Fin

section Inf

variable {n d n₁ d₁ : ℕ} {Y : Spc F E n} {W : Spc F E d} {Y₁ : Spc F E n₁} {W₁ : Spc F E d₁}

structure IsFrobInf (B : Base F E) (M : Model σ Y W) (M₁ : Model σ Y₁ W₁) (om : Rep σ Y W) (om₁ : Rep σ Y₁ W₁)
    {P P₁ : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup P₁] [Module ℂ P₁]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (p₁ : SInf F (Fin n₁ × Fin d₁) →ₗ[ℂ] P₁) (H' : Plane E d d₁) (χ : Chr F E)
    (z : ℝ) (φ : P →ₗ[ℂ] P₁) : Prop where
  unip : ∀ γ ∈ Lines σ W, (∀ s, γ s ∈ unip σ W H') → ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
    ActsD (evI F) (fun s => om (1, γ (Multiplicative.ofAdd s))) f f₁ → φ (p f₁) = 0
  lie : ∀ γ ∈ Lines σ W, ∀ γ₁ ∈ Lines σ W₁, ∀ t : Multiplicative ℝ →* (AE F E)ˣ, (∀ s, IsLevi H' (t s) (γ₁ s) (γ s)) →
    ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (fun s => om (1, γ (Multiplicative.ofAdd s))) f f₁ →
    ∀ g ∈ M₁.Pol B.ψ B.emb, ∀ g₁ : SInf F (Fin n₁ × Fin d₁),
    ActsD (evI F) (fun s => om₁ (1, γ₁ (Multiplicative.ofAdd s))) g g₁ → φ (p f) = p₁ g → ∀ c : ℂ,
    HasDerivAt (fun s : ℝ => (χ (t (Multiplicative.ofAdd s)) : ℂ) *
      (((absE F E (t (Multiplicative.ofAdd s)) : ℝ) ^ z : ℝ) : ℂ)) c 0 →
      φ (p f₁) = p₁ g₁ + c • φ (p f)
  cpt : ∀ k ∈ KInf σ W B.emb, ∀ (t : (AE F E)ˣ) (k₁ : UA σ W₁.J), IsLevi H' t k₁ k → k₁ ∈ KInf σ W₁ B.emb →
    ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) f f₁ →
    ∀ g ∈ M₁.Pol B.ψ B.emb, ∀ g₁ : SInf F (Fin n₁ × Fin d₁), Acts (evI F) (om₁ (1, k₁)) g g₁ → φ (p f) = p₁ g →
      φ (p f₁) = ((χ t : ℂ) * (((absE F E t : ℝ) ^ z : ℝ) : ℂ)) • p₁ g₁

def IndLineInf (B : Base F E) (M : Model σ Y W) (M₁ : Model σ Y₁ W₁) (om : Rep σ Y W) (om₁ : Rep σ Y₁ W₁)
    {P P₁ : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup P₁] [Module ℂ P₁]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (p₁ : SInf F (Fin n₁ × Fin d₁) →ₗ[ℂ] P₁) (H' : Plane E d d₁) (χ : Chr F E)
    (z : ℝ) : Prop :=
  ∀ φ φ' : P →ₗ[ℂ] P₁, IsFrobInf B M M₁ om om₁ p p₁ H' χ z φ → IsFrobInf B M M₁ om om₁ p p₁ H' χ z φ' →
    φ = 0 ∨ ∃ c : ℂ, φ' = c • φ

end Inf

end GlobalTheory.IndLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModuleRankOneLeftStatement
section
open Matrix GlobalTheory.TorFin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_module_rank_one_left : ∀ (n : ℕ) (A : Type) [Ring A] [Algebra ℂ A] (ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A), IsLieRep ρ → ∀ v φ : Fin n → ℂ, φ ⬝ᵥ v = 1 → IsIntMod (invAlg ρ) (leftIdl ρ {Y | ∃ u, φ ⬝ᵥ u = 0 ∧ Y = vecMulVec u φ}) (ρ (vecMulVec v φ)) := by
  first | exact @GlobalTheory.rho_vecMulVec_isIntMod_invAlg | exact GlobalTheory.rho_vecMulVec_isIntMod_invAlg | (intros; apply GlobalTheory.rho_vecMulVec_isIntMod_invAlg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPolarisedTopFormDbarExactEqZero
section
set_option autoImplicit false

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem integral_mixTop_mdbar_eq_zero : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (S : Finset (Fin n)) (U K : Set (V n)) (θ : Fin n → Fin n → V n → Matrix r r ℂ) (j : Fin n) (c : ℝ), IsOpen U → IsCompact K → K ⊆ U → (∀ v ∈ U, ∀ a ∈ S, ‖v a‖ ≤ 1 / 2) → (∀ i a, ∀ v ∈ offHyp S U, MContDiffAt 2 (θ i a) v) → (∀ a, ∀ v ∈ offHyp S U, v ∉ K → θ j a v = 0) → (∀ v ∈ offHyp S U, v ∈ K → ∀ a p q, ‖θ j a v p q‖ * poinWt S v a ≤ c) → (∀ v ∈ offHyp S U, v ∈ K → ∀ i a b p q, ‖mdbar (θ i a) v (coordVec b) p q‖ * (poinWt S v a * poinWt S v b) ≤ c) → IntegrableOn (fun v => mixTop fun i a b => mdbar (θ i a) v (coordVec b)) (offHyp S U) ∧ ∫ v in offHyp S U, (mixTop fun i a b => mdbar (θ i a) v (coordVec b)) = 0 := by
  intro n r _ _ S U K θ j c hU hK hKU hS hθ h0 hb hd
  have key : ∀ (p : Fin n → r) (π u : Equiv.Perm (Fin n)),
      IntegrableOn (fun v => (Matrix.of fun i b => mdbar (θ i (u i)) v (coordVec b) (p i) (p (π i))).det)
        (offHyp S U) ∧
      ∫ v in offHyp S U, (Matrix.of fun i b => mdbar (θ i (u i)) v (coordVec b) (p i) (p (π i))).det = 0 := by
    intro p π u
    exact GlobalTheory.T.integral_antiholomorphicJacobian_eq_zero_poincareGrowth S U K (fun i x => θ i (u i) x (p i) (p (π i))) j u c hU hK hKU hS
      (fun i v hv => (hθ i (u i) v hv (p i) (p (π i))).contDiffWithinAt)
      (fun v hv hvK => by simp [h0 (u j) v hv hvK])
      (fun v hv hvK => hb v hv hvK (u j) _ _)
      (fun v hv hvK i b => hd v hv hvK i (u i) b (p i) (p (π i)))
  have hI : ∀ (p : Fin n → r) (π u : Equiv.Perm (Fin n)),
      Integrable (fun v => ((Equiv.Perm.sign π : ℤ) : ℂ) * ((Equiv.Perm.sign u : ℤ) : ℂ) *
        (Matrix.of fun i b => mdbar (θ i (u i)) v (coordVec b) (p i) (p (π i))).det)
        (volume.restrict (offHyp S U)) := fun p π u => Integrable.const_mul (key p π u).1 _
  have hI2 : ∀ (p : Fin n → r) (π : Equiv.Perm (Fin n)),
      Integrable (fun v => ∑ u : Equiv.Perm (Fin n), ((Equiv.Perm.sign π : ℤ) : ℂ) * ((Equiv.Perm.sign u : ℤ) : ℂ) *
        (Matrix.of fun i b => mdbar (θ i (u i)) v (coordVec b) (p i) (p (π i))).det)
        (volume.restrict (offHyp S U)) := fun p π => integrable_finset_sum _ fun u _ => hI p π u
  have hI3 : ∀ (p : Fin n → r),
      Integrable (fun v => ∑ π : Equiv.Perm (Fin n), ∑ u : Equiv.Perm (Fin n),
        ((Equiv.Perm.sign π : ℤ) : ℂ) * ((Equiv.Perm.sign u : ℤ) : ℂ) *
        (Matrix.of fun i b => mdbar (θ i (u i)) v (coordVec b) (p i) (p (π i))).det)
        (volume.restrict (offHyp S U)) := fun p => integrable_finset_sum _ fun π _ => hI2 p π
  unfold mixTop
  refine ⟨Integrable.const_mul (integrable_finset_sum _ fun p _ => hI3 p) _, ?_⟩
  rw [integral_const_mul, integral_finset_sum _ fun p _ => hI3 p]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun p _ => ?_)
  rw [integral_finset_sum _ fun π _ => hI2 p π]
  refine Finset.sum_eq_zero fun π _ => ?_
  rw [integral_finset_sum _ fun u _ => hI p π u]
  refine Finset.sum_eq_zero fun u _ => ?_
  rw [integral_const_mul, (key p π u).2, mul_zero]

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralUnipotentRadicalConjToSquareInertPlaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralUnipotentRadical_conj_to_square_inertPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (d : ℕ) (W : Spc F E d) (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ n ∈ GlobalTheory.InertDbl.NabD σ W v, ∃ s ∈ GlobalTheory.InertDbl.ParD σ W v, s * n * s⁻¹ = n * n := by
  first | exact @GlobalTheory.InertConjSq.conj_sq | exact GlobalTheory.InertConjSq.conj_sq | (intros; apply GlobalTheory.InertConjSq.conj_sq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTwoSmulMemAdelicLatticeAtFinitePlaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inv_two_smul_mem_adelicLatticeAtFinitePlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (W : Spc F E d)
    (v : Pl F), (2 : 𝓞 F) ∉ v.asIdeal → ∀ z ∈ GlobalTheory.InertSph.latAt W v, (⅟(2 : AF F)) • z ∈ GlobalTheory.InertSph.latAt W v := by
  first | exact @GlobalTheory.InertSph.invTwo_smul_mem_latAt | exact GlobalTheory.InertSph.invTwo_smul_mem_latAt | (intros; apply GlobalTheory.InertSph.invTwo_smul_mem_latAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspW
section
noncomputable section

namespace GlobalTheory.ThKLiftCusp

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def kern {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (om : Rep σ X W)
    (Ψ Φ : (Fin n × Fin d → AF F) → ℂ) (h h' : UA σ W.J) : ℂ :=
  ∫ g in M.dom, theta om Ψ g h * (starRingEnd ℂ) (theta om Φ g h') ∂M.μ

variable (σ) in

def formA {d : ℕ} (J : Matrix (Fin d) (Fin d) E) (x y : Fin d → AE F E) : AE F E :=
  x ⬝ᵥ incM F J *ᵥ fun i => cA σ (y i)

variable (σ) in

def unipSp {d j : ℕ} (W : Spc F E d) (Y : Matrix (Fin d) (Fin j) E) : Subgroup (UA σ W.J) :=
  Subgroup.closure {u | mat u * incM F Y = incM F Y ∧
    (∀ z, (∀ k, formA σ W.J z (incV F fun i => Y i k) = 0) → ∃ a, mat u *ᵥ z = z + incM F Y *ᵥ a) ∧
    ∀ z k, formA σ W.J (mat u *ᵥ z - z) (incV F fun i => Y i k) = 0}

def IsCuspW {d : ℕ} (W : Spc F E d) (f : UA σ W.J → ℂ) : Prop :=
  ∀ (j : ℕ) (Y : Matrix (Fin d) (Fin j) E), 1 ≤ j → Function.Injective Y.mulVec →
    (∀ k l, form σ W.J (fun i => Y i k) (fun i => Y i l) = 0) →
    ∀ (μ : Measure (unipSp σ W Y)) (𝓕 : Set (unipSp σ W Y)), μ.IsHaarMeasure →
      IsFundamentalDomain ((ratU σ W.J).subgroupOf (unipSp σ W Y)) 𝓕 μ → μ 𝓕 = 1 →
      ∀ h, ∫ u in 𝓕, f (u.1 * h) ∂μ = 0

end GlobalTheory.ThKLiftCusp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLeviLeviElt
section
noncomputable section

namespace GlobalTheory.ThKCtFin

open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (σ : E →ₐ[F] E) in

def leviElt {d d₁ : ℕ} (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (t : (AE F E)ˣ) : UA σ W.J := by
  classical
  exact if h : ∃ m : UA σ W.J, IsLevi (W₁ := W₁) H' t 1 m then h.choose else 1

theorem isLevi_leviElt {σ : E →ₐ[F] E} {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H' : Plane E d d₁} {t : (AE F E)ˣ}
    (h : ∃ m : UA σ W.J, IsLevi (W₁ := W₁) H' t 1 m) : IsLevi (W₁ := W₁) H' t 1 (leviElt σ W W₁ H' t) := by
  classical
  rw [leviElt, dif_pos h]
  exact h.choose_spec

variable (σ : E →ₐ[F] E) in

def ctLevi {d d₁ : ℕ} (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (μ : Measure (unip σ W H'))
    (𝓕 : Set (unip σ W H')) (f : UA σ W.J → ℂ) (h : UA σ W.J) (t : (AE F E)ˣ) : ℂ :=
  ∫ u in 𝓕, f (u.1 * (leviElt σ W W₁ H' t * h)) ∂μ

theorem ctLevi_apply {σ : E →ₐ[F] E} {d d₁ : ℕ} (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁)
    (μ : Measure (unip σ W H')) (𝓕 : Set (unip σ W H')) (f : UA σ W.J → ℂ) (h : UA σ W.J) (t : (AE F E)ˣ) :
    ctLevi σ W W₁ H' μ 𝓕 f h t = ∫ u in 𝓕, f (u.1 * (leviElt σ W W₁ H' t * h)) ∂μ := rfl

example {σ : E →ₐ[F] E} {d d₁ : ℕ} (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) :
    IsLevi (σ := σ) (W := W) (W₁ := W₁) H' 1 1 (leviElt σ W W₁ H' 1) :=
  isLevi_leviElt ⟨1, by refine ⟨?_, ?_, ?_⟩ <;> simp [mat]⟩

end GlobalTheory.ThKCtFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieDerivativeLeOfBoundOnFiniteDirectionsStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieDerivative_le_of_bound_on_finiteDirections : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), ∃ (B : Finset (Lie E a)) (C : ℝ), 0 ≤ C ∧ ∀ (ψ : GA E a → ℂ) (g : GA E a) (X : Lie E a) (M : ℝ), (∀ Y ∈ B, ‖lieD Y ψ g‖ ≤ M) → 0 ≤ M → ‖lieD X ψ g‖ ≤ C * ‖X‖ * M := by
  first | exact @GlobalTheory.CuspRapid.lieD_le_of_basis | exact GlobalTheory.CuspRapid.lieD_le_of_basis | (intros; apply GlobalTheory.CuspRapid.lieD_le_of_basis <;> assumption)
end

