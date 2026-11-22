import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PlaneStrongApproxProduct

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReflectionsGenerateSubgroup
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.SaGen.PairList

open Matrix

variable {R : Type} [CommRing R] {M : ℕ}

def wv (c : R →+* R) (Jm : Matrix (Fin M) (Fin M) R) (a : Fin M → R) : Fin M → R :=
  fun j => ∑ i, c (a i) * Jm i j

theorem qr_eq (c : R →+* R) (Jm : Matrix (Fin M) (Fin M) R) (a : Fin M → R) (k : R) :
    qr c Jm a k = 1 + k • vecMulVec a (wv c Jm a) := rfl

theorem hform_eq (c : R →+* R) (Jm : Matrix (Fin M) (Fin M) R) (x y : Fin M → R) :
    Formalism.UG.hform c Jm x y = wv c Jm x ⬝ᵥ y := by
  simp only [Formalism.UG.hform, wv, dotProduct, Finset.sum_mul]
  exact Finset.sum_comm

theorem mat_mul_vmv (A : Matrix (Fin M) (Fin M) R) (u v : Fin M → R) :
    A * vecMulVec u v = vecMulVec (A *ᵥ u) v := by
  ext i j
  simp only [Matrix.mul_apply, vecMulVec_apply, mulVec, dotProduct, Finset.sum_mul, mul_assoc]

theorem vmv_mul_mat (A : Matrix (Fin M) (Fin M) R) (u v : Fin M → R) :
    vecMulVec u v * A = vecMulVec u (v ᵥ* A) := by
  ext i j
  simp only [Matrix.mul_apply, vecMulVec_apply, vecMul, dotProduct, Finset.mul_sum, mul_assoc]

theorem vmv_mul_vmv (u v x y : Fin M → R) :
    vecMulVec u v * vecMulVec x y = (v ⬝ᵥ x) • vecMulVec u y := by
  ext i j
  simp only [Matrix.mul_apply, vecMulVec_apply, dotProduct, Matrix.smul_apply, smul_eq_mul, Finset.sum_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

theorem qr_mul (c : R →+* R) (Jm : Matrix (Fin M) (Fin M) R) (a : Fin M → R) (k₁ k₂ : R) :
    qr c Jm a k₁ * qr c Jm a k₂ = qr c Jm a (k₁ + k₂ + k₁ * k₂ * Formalism.UG.hform c Jm a a) := by
  simp only [qr_eq]
  have h := vmv_mul_vmv a (wv c Jm a) a (wv c Jm a)
  rw [← hform_eq] at h
  rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, smul_mul_smul_comm, h]
  module

theorem qr_zero (c : R →+* R) (Jm : Matrix (Fin M) (Fin M) R) (a : Fin M → R) : qr c Jm a 0 = 1 := by
  simp [qr_eq]

theorem det_qr (c : R →+* R) (Jm : Matrix (Fin M) (Fin M) R) (a : Fin M → R) (k : R) :
    (qr c Jm a k).det = 1 + k * Formalism.UG.hform c Jm a a := by
  have h : k • vecMulVec a (wv c Jm a) =
      replicateCol Unit (k • a) * replicateRow Unit (wv c Jm a) := by
    rw [← vecMulVec_eq]
    ext i j
    simp [vecMulVec_apply, mul_assoc]
  rw [qr_eq, h, det_one_add_replicateCol_mul_replicateRow, hform_eq, dotProduct_smul, smul_eq_mul]

theorem wv_mulVec (c : R →+* R) (Jm : Matrix (Fin M) (Fin M) R) (g : GL (Fin M) R)
    (hg : g ∈ Formalism.UG.UJ c Jm) (a : Fin M → R) :
    wv c Jm ((g : Matrix (Fin M) (Fin M) R) *ᵥ a) = wv c Jm a ᵥ* ((g⁻¹ : GL (Fin M) R) : Matrix (Fin M) (Fin M) R) := by
  have h1 : Formalism.UG.cT c (g : Matrix (Fin M) (Fin M) R) * Jm =
      Jm * ((g⁻¹ : GL (Fin M) R) : Matrix (Fin M) (Fin M) R) := by
    have hg' : Formalism.UG.cT c (g : Matrix (Fin M) (Fin M) R) * Jm * (g : Matrix (Fin M) (Fin M) R) = Jm := hg
    calc _ = Formalism.UG.cT c (g : Matrix (Fin M) (Fin M) R) * Jm * ((g : Matrix (Fin M) (Fin M) R) *
            ((g⁻¹ : GL (Fin M) R) : Matrix (Fin M) (Fin M) R)) := by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, hg']
  have h2 : ∀ x : Fin M → R, wv c Jm x = (fun i => c (x i)) ᵥ* Jm := fun x => by
    ext j; simp [wv, vecMul, dotProduct]
  have h3 : (fun i => c (((g : Matrix (Fin M) (Fin M) R) *ᵥ a) i)) =
      (fun i => c (a i)) ᵥ* Formalism.UG.cT c (g : Matrix (Fin M) (Fin M) R) := by
    ext i
    simp [mulVec, vecMul, dotProduct, Formalism.UG.cT, map_sum, mul_comm]
  rw [h2, h2, h3, vecMul_vecMul, h1, vecMul_vecMul]

theorem conj_qr (c : R →+* R) (Jm : Matrix (Fin M) (Fin M) R) (g : GL (Fin M) R)
    (hg : g ∈ Formalism.UG.UJ c Jm) (a : Fin M → R) (k : R) :
    (g : Matrix (Fin M) (Fin M) R) * qr c Jm a k * ((g⁻¹ : GL (Fin M) R) : Matrix (Fin M) (Fin M) R) =
      qr c Jm ((g : Matrix (Fin M) (Fin M) R) *ᵥ a) k := by
  rw [qr_eq, qr_eq, wv_mulVec c Jm g hg, mul_add, add_mul, Matrix.mul_one, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, Matrix.mul_smul, Matrix.smul_mul, mat_mul_vmv, vmv_mul_mat]

theorem hform_mulVec (c : R →+* R) (Jm : Matrix (Fin M) (Fin M) R) (g : GL (Fin M) R)
    (hg : g ∈ Formalism.UG.UJ c Jm) (a : Fin M → R) :
    Formalism.UG.hform c Jm ((g : Matrix (Fin M) (Fin M) R) *ᵥ a) ((g : Matrix (Fin M) (Fin M) R) *ᵥ a) =
      Formalism.UG.hform c Jm a a := by
  rw [hform_eq, hform_eq, wv_mulVec c Jm g hg, ← dotProduct_mulVec, mulVec_mulVec, ← Units.val_mul,
    inv_mul_cancel, Units.val_one, one_mulVec]

theorem hform_self_fixed (c : R →+* R) (hc : ∀ x, c (c x) = x) (Jm : Matrix (Fin M) (Fin M) R)
    (hJ : ∀ i j, c (Jm j i) = Jm i j) (a : Fin M → R) :
    c (Formalism.UG.hform c Jm a a) = Formalism.UG.hform c Jm a a := by
  simp only [Formalism.UG.hform, map_sum, map_mul, hc, hJ]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem qr_unitary (c : R →+* R) (hc : ∀ x, c (c x) = x) (Jm : Matrix (Fin M) (Fin M) R)
    (hJ : ∀ i j, c (Jm j i) = Jm i j) (a : Fin M → R) (k : R)
    (hk : k + c k + c k * k * Formalism.UG.hform c Jm a a = 0) :
    Formalism.UG.cT c (qr c Jm a k) * Jm * qr c Jm a k = Jm := by
  set w := wv c Jm a with hw
  set u := Jm *ᵥ a with hu
  have hcT : Formalism.UG.cT c (qr c Jm a k) = 1 + c k • vecMulVec u (fun i => c (a i)) := by
    ext i j
    have hcw : c (w i) = u i := by
      simp only [hw, hu, wv, map_sum, map_mul, hc, hJ, mulVec, dotProduct]
      exact Finset.sum_congr rfl fun l _ => mul_comm _ _
    by_cases hij : i = j
    · subst hij
      simp [Formalism.UG.cT, qr_eq, ← hw, vecMulVec_apply, hcw, mul_assoc, mul_comm]
    · have hji : j ≠ i := fun h => hij h.symm
      simp [Formalism.UG.cT, qr_eq, ← hw, vecMulVec_apply, hcw, Matrix.one_apply, hij, hji, mul_assoc, mul_comm]
  have hw' : (fun i => c (a i)) ᵥ* Jm = w := by
    ext j; simp [hw, wv, vecMul, dotProduct]
  have h1 : vecMulVec u (fun i => c (a i)) * Jm = vecMulVec u w := by rw [vmv_mul_mat, hw']
  have h2 : Jm * vecMulVec a w = vecMulVec u w := by rw [mat_mul_vmv]
  have h3 : vecMulVec u w * vecMulVec a w = Formalism.UG.hform c Jm a a • vecMulVec u w := by
    rw [vmv_mul_vmv, hw, ← hform_eq]
  rw [hcT, qr_eq, ← hw, add_mul, one_mul, Matrix.smul_mul, h1, add_mul, mul_add, Matrix.mul_one, Matrix.mul_smul,
    h2, Matrix.smul_mul, mul_add, Matrix.mul_one, Matrix.mul_smul, h3]
  have : Jm + k • vecMulVec u w + c k • (vecMulVec u w + k • Formalism.UG.hform c Jm a a • vecMulVec u w)
      = Jm + (k + c k + c k * k * Formalism.UG.hform c Jm a a) • vecMulVec u w := by module
  rw [this, hk, zero_smul, add_zero]

theorem num_cond (c : R →+* R) {n k l : R} (hn : IsUnit n) (hcn : c n = n) (hl : l * c l = 1)
    (hk : k * n = l - 1) : k + c k + c k * k * n = 0 := by
  have h1 : c k * n = c l - 1 := by
    have := congrArg c hk
    rwa [map_mul, hcn, map_sub, map_one] at this
  apply hn.mul_right_cancel
  calc (k + c k + c k * k * n) * n = k * n + c k * n + (c k * n) * (k * n) := by ring
    _ = l * c l - 1 := by rw [hk, h1]; ring
    _ = 0 * n := by rw [hl]; ring

theorem tau_exists (c : R →+* R) (hc : ∀ x, c (c x) = x) (Jm : Matrix (Fin M) (Fin M) R)
    (hJ : ∀ i j, c (Jm j i) = Jm i j) (a₀ : Fin M → R) (n' : R)
    (hn' : n' * Formalism.UG.hform c Jm a₀ a₀ = 1) (μ : R) (hμ : μ * c μ = 1) :
    ∃ g : GL (Fin M) R, g ∈ Formalism.UG.UJ c Jm ∧
      (g : Matrix (Fin M) (Fin M) R) = qr c Jm a₀ ((μ - 1) * n') ∧
      ((g⁻¹ : GL (Fin M) R) : Matrix (Fin M) (Fin M) R) = qr c Jm a₀ ((c μ - 1) * n') := by
  have hz : (μ - 1) * n' + (c μ - 1) * n' + (μ - 1) * n' * ((c μ - 1) * n') * Formalism.UG.hform c Jm a₀ a₀ = 0 := by
    linear_combination n' * hμ + n' * (μ - 1) * (c μ - 1) * hn'
  have hz' : (c μ - 1) * n' + (μ - 1) * n' + (c μ - 1) * n' * ((μ - 1) * n') * Formalism.UG.hform c Jm a₀ a₀ = 0 := by
    linear_combination n' * hμ + n' * (μ - 1) * (c μ - 1) * hn'
  have hu : IsUnit (Formalism.UG.hform c Jm a₀ a₀) := IsUnit.of_mul_eq_one n' (by rw [mul_comm]; exact hn')
  refine ⟨⟨qr c Jm a₀ ((μ - 1) * n'), qr c Jm a₀ ((c μ - 1) * n'), ?_, ?_⟩, ?_, rfl, rfl⟩
  · rw [qr_mul, hz, qr_zero]
  · rw [qr_mul, hz', qr_zero]
  · refine qr_unitary c hc Jm hJ a₀ _ (num_cond c hu (hform_self_fixed c hc Jm hJ a₀) hμ ?_)
    linear_combination (μ - 1) * hn'

theorem prod_claim (c : R →+* R) (hc : ∀ x, c (c x) = x) (Jm : Matrix (Fin M) (Fin M) R)
    (hJ : ∀ i j, c (Jm j i) = Jm i j) (a₀ : Fin M → R) (n' : R)
    (hn' : n' * Formalism.UG.hform c Jm a₀ a₀ = 1) (H : Subgroup (GL (Fin M) R))
    (hH : ∀ y ∈ Formalism.UG.UJ c Jm, IsQPair c Jm (y : Matrix (Fin M) (Fin M) R) → y ∈ H)
    (l : List (GL (Fin M) R))
    (hl : ∀ y ∈ l, y ∈ Formalism.UG.UJ c Jm ∧ IsQR c Jm (y : Matrix (Fin M) (Fin M) R)) :
    ∃ h ∈ H, (h : Matrix (Fin M) (Fin M) R).det = 1 ∧ ∃ μ : R, μ * c μ = 1 ∧
      ∃ g ∈ Formalism.UG.UJ c Jm, (g : Matrix (Fin M) (Fin M) R) = qr c Jm a₀ ((μ - 1) * n') ∧ l.prod = h * g := by
  have hu : IsUnit (Formalism.UG.hform c Jm a₀ a₀) := IsUnit.of_mul_eq_one n' (by rw [mul_comm]; exact hn')
  induction l using List.reverseRecOn with
  | nil =>
    refine ⟨1, H.one_mem, by simp, 1, by simp, 1, one_mem _, ?_, by simp⟩
    simp [qr_zero]
  | append_singleton l y ih =>
    obtain ⟨h, hhH, hdet, μ, hμ, g, hgU, hg, hprod⟩ := ih (fun z hz => hl z (List.mem_append_left _ hz))
    obtain ⟨hyU, a, lam, k, ha, hlam, hk, hy⟩ := hl y (by simp)
    obtain ⟨gl, hglU, hgl, hgli⟩ := tau_exists c hc Jm hJ a₀ n' hn' lam hlam
    have hBU : g * y * gl⁻¹ * g⁻¹ ∈ Formalism.UG.UJ c Jm :=
      mul_mem (mul_mem (mul_mem hgU hyU) (inv_mem hglU)) (inv_mem hgU)
    have hBmat : ((g * y * gl⁻¹ * g⁻¹ : GL (Fin M) R) : Matrix (Fin M) (Fin M) R) =
        qr c Jm ((g : Matrix (Fin M) (Fin M) R) *ᵥ a) k *
          qr c Jm ((g : Matrix (Fin M) (Fin M) R) *ᵥ a₀) ((c lam - 1) * n') := by
      rw [← conj_qr c Jm g hgU, ← conj_qr c Jm g hgU, ← hy, ← hgli]
      have : g * y * gl⁻¹ * g⁻¹ = (g * y * g⁻¹) * (g * gl⁻¹ * g⁻¹) := by group
      rw [this]
      simp only [Units.val_mul]
    have hk' : k * Formalism.UG.hform c Jm ((g : Matrix (Fin M) (Fin M) R) *ᵥ a) ((g : Matrix (Fin M) (Fin M) R) *ᵥ a) = lam - 1 := by
      rw [hform_mulVec c Jm g hgU]; exact hk
    have hkb : (c lam - 1) * n' * Formalism.UG.hform c Jm ((g : Matrix (Fin M) (Fin M) R) *ᵥ a₀) ((g : Matrix (Fin M) (Fin M) R) *ᵥ a₀) = c lam - 1 := by
      rw [hform_mulVec c Jm g hgU]
      linear_combination (c lam - 1) * hn'
    have hBH : g * y * gl⁻¹ * g⁻¹ ∈ H := by
      refine hH _ hBU ⟨_, _, lam, k, (c lam - 1) * n', ?_, ?_, hlam, hk', hkb, hBmat⟩
      · rw [hform_mulVec c Jm g hgU]; exact ha
      · rw [hform_mulVec c Jm g hgU]; exact hu
    have hBdet : ((g * y * gl⁻¹ * g⁻¹ : GL (Fin M) R) : Matrix (Fin M) (Fin M) R).det = 1 := by
      rw [hBmat, Matrix.det_mul, det_qr, det_qr, hk', hkb]
      linear_combination hlam
    refine ⟨h * (g * y * gl⁻¹ * g⁻¹), mul_mem hhH hBH, ?_, μ * lam, ?_, g * gl, mul_mem hgU hglU, ?_, ?_⟩
    · rw [Units.val_mul, Matrix.det_mul, hdet, hBdet, one_mul]
    · rw [map_mul]
      linear_combination (lam * c lam) * hμ + hlam
    · rw [Units.val_mul, hg, hgl, qr_mul]
      congr 1
      linear_combination n' * (μ - 1) * (lam - 1) * hn'
    · rw [List.prod_append, hprod, List.prod_singleton]
      group

theorem pair_of_list : ∀ {R : Type} [CommRing R] (c : R →+* R), (∀ x, c (c x) = x) → ∀ {M : ℕ} (Jm : Matrix (Fin M) (Fin M) R), (∀ i j, c (Jm j i) = Jm i j) → ∀ a₀ : Fin M → R, IsUnit (Formalism.UG.hform c Jm a₀ a₀) → ∀ H : Subgroup (GL (Fin M) R), (∀ y ∈ Formalism.UG.UJ c Jm, IsQPair c Jm (y : Matrix (Fin M) (Fin M) R) → y ∈ H) → ∀ l : List (GL (Fin M) R), (∀ y ∈ l, y ∈ Formalism.UG.UJ c Jm ∧ IsQR c Jm (y : Matrix (Fin M) (Fin M) R)) → ((l.prod : GL (Fin M) R) : Matrix (Fin M) (Fin M) R).det = 1 → l.prod ∈ H := by
  intro R _ c hc M Jm hJ a₀ ha₀ H hH l hl hdet
  obtain ⟨n', hn'⟩ := ha₀.exists_left_inv
  obtain ⟨h, hhH, hdh, μ, hμ, g, hgU, hg, hprod⟩ := prod_claim c hc Jm hJ a₀ n' hn' H hH l hl
  have hμ1 : μ = 1 := by
    rw [hprod, Units.val_mul, Matrix.det_mul, hdh, one_mul, hg, det_qr] at hdet
    linear_combination hdet - (μ - 1) * hn'
  have hg1 : g = 1 := by
    apply Units.ext
    rw [hg, hμ1, sub_self, zero_mul, qr_zero, Units.val_one]
  rw [hprod, hg1, mul_one]
  exact hhH

end GlobalTheory.CompanionTheory.SaGen.PairList
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpecialSupportOfLocalLift
section
noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.SaGen

section Component

variable {F E K : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [Field K] [Algebra F K]
  [TopologicalSpace K]

def projB (P : PlaceMap F K) : AF F ⊗[F] E →ₐ[F] K ⊗[F] E :=
  Algebra.TensorProduct.map P.proj (AlgHom.id F E)

theorem projB_sigR (P : PlaceMap F K) (σ : E →ₐ[F] E) (y : AF F ⊗[F] E) :
    projB P (sigR (AF F) σ y) = sigR K σ (projB P y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [projB, sigR]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem projB_inclR (P : PlaceMap F K) (e : E) : projB P (inclR (AF F) e) = inclR K e := by
  simp [projB, inclR]

theorem iB_projB (P : PlaceMap F K) (y : AF F ⊗[F] E) :
    iB P (projB P y) = algebraMap (AF F) (AF F ⊗[F] E) (P.inj 1) * y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp [projB, iB, P.inj_proj, Algebra.TensorProduct.algebraMap_apply]
  | add x y hx hy => simp only [map_add, hx, hy, mul_add]

theorem cT_map_projB (P : PlaceMap F K) (σ : E →ₐ[F] E) {M : ℕ}
    (A : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) :
    Formalism.UG.cT (sigR K σ) (A.map (projB P)) = (Formalism.UG.cT (sigR (AF F) σ) A).map (projB P) := by
  ext i j
  simp [Formalism.UG.cT, projB_sigR]

theorem JR_map_projB (P : PlaceMap F K) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    (JR (F := F) (AF F) J).map (projB P) = JR (F := F) K J := by
  ext i j
  simp [JR, projB_inclR]

end Component

theorem exists_lift_of_mem_supp : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E),
    ∀ {K : Type} [NontriviallyNormedField K] [Algebra F K] (P : PlaceMap F K) (L : HA K σ J →* HA (AF F) σ J),
    IsLift P σ J L → ∀ g ∈ SUSupp σ J (P.inj 1), ∃ x : HA K σ J,
      ((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)).det = 1 ∧ L x = g := by
  intro F E _ _ _ _ _ σ _ M J K _ _ P L hL g hg
  obtain ⟨hdet, hsupp⟩ := hg
  have hdet' := StrongApprox.mem_SUAdelic.1 hdet
  set G : Matrix (Fin M) (Fin M) (AF F ⊗[F] E) := ((HA.mat (AF F) σ J g).1 : _) with hG
  let X : GL (Fin M) (K ⊗[F] E) := Formalism.UG.bc (projB P).toRingHom (HA.mat (AF F) σ J g)
  have hXG : (X : Matrix (Fin M) (Fin M) (K ⊗[F] E)) = G.map (projB P) := rfl
  have hg0 : Formalism.UG.cT (sigR (AF F) σ) G * JR (F := F) (AF F) J * G = JR (F := F) (AF F) J := g.2
  have hX : X ∈ HR K σ J := by
    change Formalism.UG.cT (sigR K σ) (X : Matrix (Fin M) (Fin M) (K ⊗[F] E)) * JR (F := F) K J * (X : Matrix (Fin M) (Fin M) (K ⊗[F] E)) = JR (F := F) K J
    have h1 := congrArg (fun A => (projB P).toRingHom.mapMatrix A) hg0
    simp only [map_mul] at h1
    rw [hXG, cT_map_projB, ← JR_map_projB P J]
    exact h1
  let x : HA K σ J := (⟨X, hX⟩ : HR K σ J)
  have hxm : ((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)) = G.map (projB P) := rfl
  refine ⟨x, ?_, ?_⟩
  · rw [hxm]
    have h2 := RingHom.map_det (projB P).toRingHom G
    rw [hdet'] at h2
    simpa using h2.symm
  · have hm : ((HA.mat (AF F) σ J (L x)).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) = G := by
      ext i j
      have h3 := hL x i j
      have h4 : (((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)) - 1) i j = projB P ((G - 1) i j) := by
        rw [hxm]
        by_cases hij : i = j
        · subst hij
          simp
        · simp [Matrix.one_apply_ne hij]
      rw [h4, iB_projB, hsupp i j] at h3
      exact sub_left_injective h3
    exact Subtype.ext (Units.ext hm)

end GlobalTheory.CompanionTheory.SaGen
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpecialUnitarySupportProduct
section
noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.SaGen.Supp

open GlobalTheory.CompanionTheory.Sa2Prod

section Ring

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

theorem trunc_mul_trunc {c d : R} (h : c * d = 0) {A : Matrix n n R} (hA : (c + d) • (A - 1) = A - 1) :
    trunc c A * trunc d A = A := by
  have e : trunc c A * trunc d A = 1 + (c + d) • (A - 1) + (c * d) • ((A - 1) * (A - 1)) := by
    unfold trunc
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, add_smul, smul_add]
    rw [mul_comm d c]
    abel
  rw [e, h, zero_smul, add_zero, hA]
  abel

end Ring

section Idem

variable {F : Type} [Field F] [NumberField F]

theorem idem_self {S₁ : Finset (InfinitePlace F)} {S₂ : Finset (HeightOneSpectrum (𝓞 F))} {a : AF F}
    (ha : IsPlacesIdem S₁ S₂ a) : a * a = a := by
  refine adele_ext (funext fun w => ?_) (finAdele_ext fun v => ?_)
  · rw [map_mul]
    change fstA F a w * fstA F a w = fstA F a w
    by_cases h : w ∈ S₁
    · rw [ha.1 w h, one_mul]
    · rw [ha.2.1 w h, zero_mul]
  · rw [map_mul, map_mul]
    by_cases h : v ∈ S₂
    · rw [ha.2.2.1 v h, one_mul]
    · rw [ha.2.2.2 v h, zero_mul]

theorem idem_orth {A₁ B₁ : Finset (InfinitePlace F)} {A₂ B₂ : Finset (HeightOneSpectrum (𝓞 F))} {a b : AF F}
    (ha : IsPlacesIdem A₁ A₂ a) (hb : IsPlacesIdem B₁ B₂ b) (h₁ : Disjoint A₁ B₁) (h₂ : Disjoint A₂ B₂) :
    a * b = 0 := by
  refine adele_ext (funext fun w => ?_) (finAdele_ext fun v => ?_)
  · rw [map_mul, map_zero]
    change fstA F a w * fstA F b w = 0
    by_cases h : w ∈ A₁
    · rw [hb.2.1 w (Finset.disjoint_left.1 h₁ h), mul_zero]
    · rw [ha.2.1 w h, zero_mul]
  · rw [map_mul, map_mul, map_zero, map_zero]
    by_cases h : v ∈ A₂
    · rw [hb.2.2.2 v (Finset.disjoint_left.1 h₂ h), mul_zero]
    · rw [ha.2.2.2 v h, zero_mul]

theorem idem_eq_add [DecidableEq (InfinitePlace F)] [DecidableEq (HeightOneSpectrum (𝓞 F))]
    {A₁ B₁ : Finset (InfinitePlace F)} {A₂ B₂ : Finset (HeightOneSpectrum (𝓞 F))} {a b δ : AF F}
    (ha : IsPlacesIdem A₁ A₂ a) (hb : IsPlacesIdem B₁ B₂ b) (h₁ : Disjoint A₁ B₁) (h₂ : Disjoint A₂ B₂)
    (hδ : IsPlacesIdem (A₁ ∪ B₁) (A₂ ∪ B₂) δ) : δ = a + b := by
  refine adele_ext (funext fun w => ?_) (finAdele_ext fun v => ?_)
  · rw [map_add]
    change fstA F δ w = fstA F a w + fstA F b w
    by_cases h : w ∈ A₁
    · rw [hδ.1 w (Finset.mem_union_left _ h), ha.1 w h, hb.2.1 w (Finset.disjoint_left.1 h₁ h), add_zero]
    · by_cases h' : w ∈ B₁
      · rw [hδ.1 w (Finset.mem_union_right _ h'), ha.2.1 w h, hb.1 w h', zero_add]
      · rw [hδ.2.1 w (by simp [h, h']), ha.2.1 w h, hb.2.1 w h', add_zero]
  · rw [map_add, map_add]
    by_cases h : v ∈ A₂
    · rw [hδ.2.2.1 v (Finset.mem_union_left _ h), ha.2.2.1 v h, hb.2.2.2 v (Finset.disjoint_left.1 h₂ h), add_zero]
    · by_cases h' : v ∈ B₂
      · rw [hδ.2.2.1 v (Finset.mem_union_right _ h'), ha.2.2.2 v h, hb.2.2.1 v h', zero_add]
      · rw [hδ.2.2.2 v (by simp [h, h']), ha.2.2.2 v h, hb.2.2.2 v h', add_zero]

theorem idem_empty {a : AF F} (ha : IsPlacesIdem (∅ : Finset (InfinitePlace F))
    (∅ : Finset (HeightOneSpectrum (𝓞 F))) a) : a = 0 := by
  refine adele_ext (funext fun w => ?_) (finAdele_ext fun v => ?_)
  · rw [map_zero]
    exact ha.2.1 w (Finset.notMem_empty w)
  · rw [map_zero, map_zero]
    exact ha.2.2.2 v (Finset.notMem_empty v)

end Idem

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem supp_split (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {a b : AF F}
    (ha : a * a = a) (hb : b * b = b) (hab : a * b = 0) {g : HA (AF F) σ J} (hg : g ∈ SUSupp σ J (a + b)) :
    ∃ x ∈ SUSupp σ J a, ∃ y ∈ SUSupp σ J b, g = x * y := by
  have ha' : algebraMap (AF F) (AF F ⊗[F] E) a * algebraMap (AF F) (AF F ⊗[F] E) a =
      algebraMap (AF F) (AF F ⊗[F] E) a := by rw [← map_mul, ha]
  have hb' : algebraMap (AF F) (AF F ⊗[F] E) b * algebraMap (AF F) (AF F ⊗[F] E) b =
      algebraMap (AF F) (AF F ⊗[F] E) b := by rw [← map_mul, hb]
  refine ⟨truncHA σ J ha' g, truncHA_mem σ J ha' hg.1, truncHA σ J hb' g, truncHA_mem σ J hb' hg.1, ?_⟩
  refine Subtype.ext (Units.ext ?_)
  refine (trunc_mul_trunc (c := algebraMap (AF F) (AF F ⊗[F] E) a) (d := algebraMap (AF F) (AF F ⊗[F] E) b)
    (by rw [← map_mul, hab, map_zero]) ?_).symm
  ext i j
  have := hg.2 i j
  rw [map_add] at this
  rw [Matrix.smul_apply, smul_eq_mul]
  exact this

theorem supp_le_of_disjoint [DecidableEq (InfinitePlace F)] [DecidableEq (HeightOneSpectrum (𝓞 F))]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (N : Subgroup (HA (AF F) σ J))
    {A₁ B₁ : Finset (InfinitePlace F)} {A₂ B₂ : Finset (HeightOneSpectrum (𝓞 F))} {a b δ : AF F}
    (ha : IsPlacesIdem A₁ A₂ a) (hb : IsPlacesIdem B₁ B₂ b) (h₁ : Disjoint A₁ B₁) (h₂ : Disjoint A₂ B₂)
    (hδ : IsPlacesIdem (A₁ ∪ B₁) (A₂ ∪ B₂) δ) (hNa : SUSupp σ J a ⊆ N) (hNb : SUSupp σ J b ⊆ N) :
    SUSupp σ J δ ⊆ N := by
  intro g hg
  rw [idem_eq_add ha hb h₁ h₂ hδ] at hg
  obtain ⟨x, hx, y, hy, rfl⟩ := supp_split σ J (idem_self ha) (idem_self hb) (idem_orth ha hb h₁ h₂) hg
  exact N.mul_mem (hNa hx) (hNb hy)

theorem supp_zero_le (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (N : Subgroup (HA (AF F) σ J)) :
    SUSupp σ J (0 : AF F) ⊆ N := by
  intro g hg
  have h : g = 1 := by
    refine Subtype.ext (Units.ext ?_)
    ext i j
    have := hg.2 i j
    rw [map_zero, zero_mul] at this
    exact (sub_eq_zero.1 this.symm)
  rw [h]
  exact N.one_mem

theorem supp_le_of_single : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (N : Subgroup (HA (AF F) σ J))
    {T₁ : Finset (InfinitePlace F)} {T₂ : Finset (HeightOneSpectrum (𝓞 F))} {δ : AF F},
    IsPlacesIdem T₁ T₂ δ → (∀ w ∈ T₁, ∀ e : AF F, IsPlacesIdem {w} ∅ e → SUSupp σ J e ⊆ N) →
    (∀ v ∈ T₂, ∀ e : AF F, IsPlacesIdem ∅ {v} e → SUSupp σ J e ⊆ N) → SUSupp σ J δ ⊆ N := by
  intro F E _ _ _ _ _ σ M J N T₁ T₂ δ hδ h₁ h₂
  classical
  have base : ∀ (S : Finset (HeightOneSpectrum (𝓞 F))), (∀ v ∈ S, ∀ e : AF F, IsPlacesIdem ∅ {v} e → SUSupp σ J e ⊆ N) →
      ∀ d : AF F, IsPlacesIdem ∅ S d → SUSupp σ J d ⊆ N := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _ d hd
      rw [idem_empty hd]
      exact supp_zero_le σ J N
    | insert v s hv ih =>
      intro hS d hd
      obtain ⟨e, he⟩ := StrongApprox.exists_isPlacesIdem (F := F) ∅ {v}
      obtain ⟨d', hd'⟩ := StrongApprox.exists_isPlacesIdem (F := F) ∅ s
      refine supp_le_of_disjoint σ J N he hd' (Finset.disjoint_empty_left _)
        (Finset.disjoint_singleton_left.2 hv) ?_ (hS v (Finset.mem_insert_self v s) e he)
        (ih (fun u hu => hS u (Finset.mem_insert_of_mem hu)) d' hd')
      rwa [Finset.empty_union, ← Finset.insert_eq]
  have main : ∀ (S : Finset (InfinitePlace F)), (∀ w ∈ S, ∀ e : AF F, IsPlacesIdem {w} ∅ e → SUSupp σ J e ⊆ N) →
      ∀ d : AF F, IsPlacesIdem S T₂ d → SUSupp σ J d ⊆ N := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _ d hd
      exact base T₂ h₂ d hd
    | insert w s hw ih =>
      intro hS d hd
      obtain ⟨e, he⟩ := StrongApprox.exists_isPlacesIdem (F := F) {w} ∅
      obtain ⟨d', hd'⟩ := StrongApprox.exists_isPlacesIdem (F := F) s T₂
      refine supp_le_of_disjoint σ J N he hd' (Finset.disjoint_singleton_left.2 hw)
        (Finset.disjoint_empty_left _) ?_ (hS w (Finset.mem_insert_self w s) e he)
        (ih (fun u hu => hS u (Finset.mem_insert_of_mem hu)) d' hd')
      rwa [Finset.empty_union, ← Finset.insert_eq]
  exact main T₁ h₁ δ hδ

end Main

end GlobalTheory.CompanionTheory.SaGen.Supp
end
end

