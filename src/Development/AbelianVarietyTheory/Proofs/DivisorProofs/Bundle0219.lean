import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0114
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0155
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0167
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0156
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0158
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0091

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisElementDvdOfFormallyUnramified
section
open scoped TensorProduct

namespace GlobalTheory.GoodEtale

theorem galElt_dvd_of_unramified : ∀ (R C O : Type) [CommRing R] [CommRing C] [Algebra R C] [CommRing O] [Algebra R O]
    [Algebra.FormallyUnramified O (O ⊗[R] C)] [Algebra.EssFiniteType O (O ⊗[R] C)]
    (G : Type) [Group G] [DecidableEq G] (act : G →* (C ≃ₐ[R] C)) (b : R) (n : ℕ) (x y : Fin n → C),
      (∀ g, ∑ i, x i * act g (y i) = if g = 1 then algebraMap R C b else 0) →
    ∀ σ : C →ₐ[R] O, Function.Injective (GlobalTheory.GoodEtale.galMap act σ) →
    ∀ h : G, ∃ m' : O ⊗[R] C, GlobalTheory.GoodEtale.galElt act σ x y h = algebraMap R O b • m' := by
  intro R C O _ _ _ _ _ _ _ G _ _ act b n x y hxy σ hinj h
  obtain ⟨t, ht1, ht2⟩ := (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := O) (S := O ⊗[R] C)).mp inferInstance
  let τ : O ⊗[R] C →ₐ[O] O := (Pi.evalAlgHom O (fun _ : G => O) h).comp (galMap act σ)
  let ψ : (O ⊗[R] C) ⊗[O] (O ⊗[R] C) →ₐ[O] O ⊗[R] C :=
    Algebra.TensorProduct.lift (AlgHom.id O _) ((Algebra.ofId O (O ⊗[R] C)).comp τ) (fun _ _ => Commute.all _ _)
  have hψ : ∀ a c, ψ (a ⊗ₜ c) = a * algebraMap O (O ⊗[R] C) (τ c) := by
    intro a c; simp [ψ]
  set e := ψ t with he

  have hi : ∀ s, s * e = algebraMap O (O ⊗[R] C) (τ s) * e := by
    intro s
    have := congrArg ψ (ht1 s)
    rw [map_mul, map_sub, hψ, hψ, map_zero] at this
    simp only [map_one, one_mul, mul_one] at this
    rw [← he] at this
    rw [sub_mul, sub_eq_zero] at this
    exact this.symm

  have hii : τ e = 1 := by
    have hcomp : τ.comp ψ = τ.comp (Algebra.TensorProduct.lmul' O) := by
      apply Algebra.TensorProduct.ext'
      intro a c
      simp only [AlgHom.comp_apply, hψ, map_mul, AlgHom.commutes, Algebra.TensorProduct.lmul'_apply_tmul]
      simp only [Algebra.algebraMap_self, RingHom.id_apply]
    have := congrArg (fun f => f t) hcomp
    simp only [AlgHom.comp_apply] at this
    rw [he, this, ht2, map_one]

  have hfix : galElt act σ x y h * e = galElt act σ x y h := by
    apply hinj
    rw [map_mul, galMap_galElt act σ x y b hxy h]
    funext g
    by_cases hg : g = h
    · subst hg
      have : galMap act σ e g = τ e := rfl
      simp [this, hii]
    · simp [Pi.single_apply, hg]
  refine ⟨e, ?_⟩
  rw [← hfix]
  simp only [galElt, Finset.sum_mul]
  have hterm : ∀ i, σ (x i) ⊗ₜ[R] act h⁻¹ (y i) * e = algebraMap O (O ⊗[R] C) (σ (x i) * σ (y i)) * e := by
    intro i
    have hsplit : σ (x i) ⊗ₜ[R] act h⁻¹ (y i) = algebraMap O (O ⊗[R] C) (σ (x i)) * ((1 : O) ⊗ₜ[R] act h⁻¹ (y i)) := by
      simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
    rw [hsplit, mul_assoc, hi, ← mul_assoc, ← map_mul]
    congr 3
    have : τ ((1 : O) ⊗ₜ[R] act h⁻¹ (y i)) = σ (act h (act h⁻¹ (y i))) := by
      simp [τ, galMap_tmul]
    rw [this]
    congr 2
    rw [← AlgEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one, AlgEquiv.one_apply]
  simp_rw [hterm, ← Finset.sum_mul, ← map_sum, ← map_mul, ← map_sum]
  have h1 := hxy 1
  simp only [map_one, AlgEquiv.one_apply, if_true] at h1
  rw [h1, AlgHom.commutes, Algebra.smul_def]

end GlobalTheory.GoodEtale
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisTwistedNormGLBasicProperties
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

noncomputable section

namespace GlobalTheory.Shin.NrmBasic

section General

variable {G Γ : Type} [Group G] [Group Γ] (φ : Γ →* MulAut G) (s : Γ)

theorem nrmG_zero (δ : G) : nrmG φ s 0 δ = 1 := by
  simp [nrmG]

theorem nrmG_succ (l : ℕ) (δ : G) : nrmG φ s (l + 1) δ = nrmG φ s l δ * φ (s ^ l) δ := by
  simp [nrmG, List.range_succ, List.map_append, List.prod_append]

theorem nrmG_twConj (l : ℕ) (δ y : G) :
    nrmG φ s l (y⁻¹ * δ * φ s y) = y⁻¹ * nrmG φ s l δ * φ (s ^ l) y := by
  induction l with
  | zero => simp [nrmG_zero]
  | succ l ih =>
    rw [nrmG_succ, nrmG_succ, ih]
    have h1 : φ (s ^ l) (y⁻¹ * δ * φ s y) = (φ (s ^ l) y)⁻¹ * φ (s ^ l) δ * φ (s ^ (l + 1)) y := by
      rw [map_mul, map_mul, map_inv, pow_succ, map_mul, MulAut.mul_apply]
    rw [h1]
    group

theorem mul_map_nrmG (l : ℕ) (δ : G) :
    δ * φ s (nrmG φ s l δ) = nrmG φ s l δ * φ (s ^ l) δ := by
  induction l with
  | zero => simp [nrmG_zero]
  | succ l ih =>
    rw [nrmG_succ, map_mul, ← mul_assoc, ih, pow_succ', map_mul, MulAut.mul_apply]

theorem nrmG_mul (l : ℕ) (δ ε : G) (h : ∀ i j : ℕ, Commute (φ (s ^ i) δ) (φ (s ^ j) ε)) :
    nrmG φ s l (δ * ε) = nrmG φ s l δ * nrmG φ s l ε := by
  induction l with
  | zero => simp [nrmG_zero]
  | succ l ih =>
    rw [nrmG_succ, nrmG_succ, nrmG_succ, ih, map_mul]
    have hc : Commute (nrmG φ s l ε) (φ (s ^ l) δ) := by
      unfold nrmG
      apply Commute.list_prod_left
      intro x hx
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
      exact (h l i).symm
    rw [mul_assoc, mul_assoc, ← mul_assoc (nrmG φ s l ε), hc.eq, mul_assoc]

end General

section Fields

variable {F F' : Type} [Field F] [Field F'] [Algebra F F'] [Finite F']

theorem pow_finrank_eq_one (s : F' ≃ₐ[F] F') : s ^ Module.finrank F F' = 1 := by
  haveI : Finite F := Finite.of_injective _ (algebraMap F F').injective
  rw [← IsGalois.card_aut_eq_finrank]
  exact pow_card_eq_one'

theorem fixed_iff (s : F' ≃ₐ[F] F') (hs : ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) (x : F') :
    s x = x ↔ x ∈ Set.range (algebraMap F F') := by
  haveI : Finite F := Finite.of_injective _ (algebraMap F F').injective
  constructor
  · intro hx
    rw [← IntermediateField.mem_bot, ← IsGalois.fixedField_top, IntermediateField.mem_fixedField_iff]
    intro t _
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hs t)
    have h1 : ∀ m : ℕ, (s ^ m) x = x := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => rw [pow_succ, AlgEquiv.mul_apply, hx, ih]
    have h2 : ∀ m : ℕ, (s⁻¹ ^ m) x = x := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [pow_succ, AlgEquiv.mul_apply]
        have : s⁻¹ x = x := by
          conv_lhs => rw [← hx]
          exact s.symm_apply_apply x
        rw [this, ih]
    cases k with
    | ofNat m => simpa using h1 m
    | negSucc m => rw [zpow_negSucc, ← inv_pow]; exact h2 (m + 1)
  · rintro ⟨a, rfl⟩
    exact s.commutes a

end Fields

theorem main : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ n : ℕ, (∀ x : GL (Fin n) F', galAct F F' n s x = x ↔ ∃ y, incl F F' n y = x) ∧ Function.Injective (incl F F' n) ∧ (∀ δ y : GL (Fin n) F', nrm s (y⁻¹ * δ * galAct F F' n s y) = y⁻¹ * nrm s δ * y) ∧ (∀ δ : GL (Fin n) F', δ * galAct F F' n s (nrm s δ) = nrm s δ * δ) ∧ ∀ δ ε : GL (Fin n) F', (∀ t u : F' ≃ₐ[F] F', Commute (galAct F F' n t δ) (galAct F F' n u ε)) → nrm s (δ * ε) = nrm s δ * nrm s ε := by
  intro F F' _ _ _ _ s hs n
  have hl := pow_finrank_eq_one s
  have hinj : Function.Injective (algebraMap F F') := (algebraMap F F').injective
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x
    constructor
    · intro hx
      have he : ∀ i j, s ((x : Matrix (Fin n) (Fin n) F') i j) = (x : Matrix (Fin n) (Fin n) F') i j := by
        intro i j
        have := congrArg (fun z : GL (Fin n) F' => (z : Matrix (Fin n) (Fin n) F') i j) hx
        simpa [galAct_apply, gal] using this
      choose M0 hM using fun i j => (fixed_iff s hs _).1 (he i j)
      let M : Matrix (Fin n) (Fin n) F := Matrix.of M0
      have hdet : (algebraMap F F') (M.det) = (x : Matrix (Fin n) (Fin n) F').det := by
        rw [RingHom.map_det]
        congr 1
        ext i j
        exact hM i j
      have hu : IsUnit M := by
        rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
        intro h0
        have : (x : Matrix (Fin n) (Fin n) F').det = 0 := by rw [← hdet, h0, map_zero]
        exact (Matrix.GeneralLinearGroup.det_ne_zero x) this
      refine ⟨hu.unit, ?_⟩
      ext i j
      simp [incl, gal, M, hM]
    · rintro ⟨y, rfl⟩
      ext i j
      simp [galAct_apply, gal, incl]
  · intro a b hab
    ext i j
    have := congrArg (fun z : GL (Fin n) F' => (z : Matrix (Fin n) (Fin n) F') i j) hab
    exact hinj (by simpa [incl, gal] using this)
  · intro δ y
    unfold nrm
    rw [nrmG_twConj, hl, map_one, MulAut.one_apply]
  · intro δ
    unfold nrm
    rw [mul_map_nrmG, hl, map_one, MulAut.one_apply]
  · intro δ ε h
    unfold nrm
    exact nrmG_mul _ _ _ _ _ fun i j => h _ _

end GlobalTheory.Shin.NrmBasic

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisTwistedNormGLDiagonalBlocks
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

noncomputable section

namespace GlobalTheory.ShinBlock

open GlobalTheory.Shin

variable {K : Type} [Field K]

theorem tl_eq {a b : ℕ} (M : Matrix (Fin (a + b)) (Fin (a + b)) K) :
    tl a M = M.submatrix (Fin.castAdd b) (Fin.castAdd b) := by
  ext i j
  simp only [tl, ent, Matrix.submatrix_apply]
  rw [dif_pos ⟨by omega, by omega⟩]
  rfl

theorem br_eq {a b : ℕ} (M : Matrix (Fin (a + b)) (Fin (a + b)) K) :
    br a b M = M.submatrix (Fin.natAdd a) (Fin.natAdd a) := by
  ext i j
  simp only [br, ent, Matrix.submatrix_apply]
  rw [dif_pos ⟨by omega, by omega⟩]
  rfl

theorem inPar_mul {a n : ℕ} {x y : GL (Fin n) K} (hx : InPar a x) (hy : InPar a y) :
    InPar a (x * y) := by
  intro i j hj hi
  rw [Units.val_mul, Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hk : (k : ℕ) < a
  · rw [hx i k hk hi, zero_mul]
  · rw [hy k j hj (by omega), mul_zero]

theorem inPar_one {a n : ℕ} : InPar a (1 : GL (Fin n) K) := by
  intro i j hj hi
  rw [Units.val_one, Matrix.one_apply_ne]
  intro h; subst h; omega

theorem inPar_inv {a n : ℕ} {x : GL (Fin n) K} (hx : InPar a x) : InPar a x⁻¹ := by
  have hB : Matrix.BlockTriangular (x : Matrix (Fin n) (Fin n) K)
      (fun i : Fin n => if a ≤ (i : ℕ) then 1 else 0) := by
    intro i j hij
    simp only at hij
    split_ifs at hij with h1 h2 <;> first | omega | exact hx i j (by omega) (by omega)
  haveI : Invertible (x : Matrix (Fin n) (Fin n) K) := x.invertible
  have := Matrix.blockTriangular_inv_of_blockTriangular hB
  intro i j hj hi
  rw [Matrix.coe_units_inv]
  exact this (by simp only; rw [if_pos hi, if_neg (by omega)]; exact Nat.zero_lt_one)

theorem tl_mul {a b : ℕ} {x y : GL (Fin (a + b)) K} (hy : InPar a y) :
    tl a (x * y).val = tl a x.val * tl a y.val := by
  rw [tl_eq, tl_eq, tl_eq]
  ext i j
  simp only [Matrix.submatrix_apply, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_add]
  have : ∑ k : Fin b, x.val (Fin.castAdd b i) (Fin.natAdd a k) *
      y.val (Fin.natAdd a k) (Fin.castAdd b j) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    rw [hy _ _ (by simp) (by simp), mul_zero]
  rw [this, add_zero]

theorem br_mul {a b : ℕ} {x y : GL (Fin (a + b)) K} (hx : InPar a x) :
    br a b (x * y).val = br a b x.val * br a b y.val := by
  rw [br_eq, br_eq, br_eq]
  ext i j
  simp only [Matrix.submatrix_apply, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_add]
  have : ∑ k : Fin a, x.val (Fin.natAdd a i) (Fin.castAdd b k) *
      y.val (Fin.castAdd b k) (Fin.natAdd a j) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    rw [hx _ _ (by simp) (by simp), zero_mul]
  rw [this, zero_add]

theorem tl_one {a b : ℕ} : tl a (1 : GL (Fin (a + b)) K).val = 1 := by
  rw [tl_eq, Units.val_one]
  exact Matrix.submatrix_one _ (Fin.castAdd_injective a b)

theorem br_one {a b : ℕ} : br a b (1 : GL (Fin (a + b)) K).val = 1 := by
  rw [br_eq, Units.val_one]
  exact Matrix.submatrix_one _ (Fin.natAdd_injective b a)

theorem isUnit_tl {a b : ℕ} {x : GL (Fin (a + b)) K} (hx : InPar a x) : IsUnit (tl a x.val) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  apply Matrix.isUnit_det_of_right_inverse (B := tl a x⁻¹.val)
  rw [← tl_mul (inPar_inv hx), mul_inv_cancel, tl_one]

theorem isUnit_br {a b : ℕ} {x : GL (Fin (a + b)) K} (hx : InPar a x) : IsUnit (br a b x.val) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  apply Matrix.isUnit_det_of_right_inverse (B := br a b x⁻¹.val)
  rw [← br_mul hx, mul_inv_cancel, br_one]

theorem coe_tlG {a b : ℕ} {x : GL (Fin (a + b)) K} (hx : InPar a x) :
    (tlG a x).val = tl a x.val := by
  unfold tlG toG
  rw [dif_pos (isUnit_tl hx)]
  rfl

theorem coe_brG {a b : ℕ} {x : GL (Fin (a + b)) K} (hx : InPar a x) :
    (brG a b x).val = br a b x.val := by
  unfold brG toG
  rw [dif_pos (isUnit_br hx)]
  rfl

theorem gal_val {K' : Type} [Field K'] (t : K →+* K') {n : ℕ} (x : GL (Fin n) K) :
    (gal t n x).val = x.val.map t := rfl

theorem inPar_gal {K' : Type} [Field K'] (t : K →+* K') {a n : ℕ} {x : GL (Fin n) K} (hx : InPar a x) :
    InPar a (gal t n x) := by
  intro i j hj hi
  rw [gal_val, Matrix.map_apply, hx i j hj hi, map_zero]

theorem tl_map {K' : Type} [Field K'] (t : K →+* K') (a : ℕ) {n : ℕ} (M : Matrix (Fin n) (Fin n) K) :
    tl a (M.map t) = (tl a M).map t := by
  ext i j
  simp only [tl, ent, Matrix.map_apply]
  split_ifs <;> simp

theorem br_map {K' : Type} [Field K'] (t : K →+* K') (a b : ℕ) {n : ℕ} (M : Matrix (Fin n) (Fin n) K) :
    br a b (M.map t) = (br a b M).map t := by
  ext i j
  simp only [br, ent, Matrix.map_apply]
  split_ifs <;> simp

theorem tlG_gal {K' : Type} [Field K'] (t : K →+* K') {a b : ℕ} {x : GL (Fin (a + b)) K} (hx : InPar a x) :
    tlG a (gal t (a + b) x) = gal t a (tlG a x) := by
  ext1
  rw [coe_tlG (inPar_gal t hx), gal_val, gal_val, coe_tlG hx, tl_map]

theorem brG_gal {K' : Type} [Field K'] (t : K →+* K') {a b : ℕ} {x : GL (Fin (a + b)) K} (hx : InPar a x) :
    brG a b (gal t (a + b) x) = gal t b (brG a b x) := by
  ext1
  rw [coe_brG (inPar_gal t hx), gal_val, gal_val, coe_brG hx, br_map]

theorem tlG_mul {a b : ℕ} {x y : GL (Fin (a + b)) K} (hx : InPar a x) (hy : InPar a y) :
    tlG a (x * y) = tlG a x * tlG a y := by
  ext1
  rw [coe_tlG (inPar_mul hx hy), tl_mul hy, Units.val_mul, coe_tlG hx, coe_tlG hy]

theorem brG_mul {a b : ℕ} {x y : GL (Fin (a + b)) K} (hx : InPar a x) (hy : InPar a y) :
    brG a b (x * y) = brG a b x * brG a b y := by
  ext1
  rw [coe_brG (inPar_mul hx hy), br_mul hx, Units.val_mul, coe_brG hx, coe_brG hy]

theorem tlG_one {a b : ℕ} : tlG a (1 : GL (Fin (a + b)) K) = 1 := by
  ext1
  rw [coe_tlG inPar_one, tl_one, Units.val_one]

theorem brG_one {a b : ℕ} : brG a b (1 : GL (Fin (a + b)) K) = 1 := by
  ext1
  rw [coe_brG inPar_one, br_one, Units.val_one]

theorem prod_blocks {a b : ℕ} (l : List (GL (Fin (a + b)) K)) (hl : ∀ x ∈ l, InPar a x) :
    InPar a l.prod ∧ tlG a l.prod = (l.map (tlG a)).prod ∧ brG a b l.prod = (l.map (brG a b)).prod := by
  induction l with
  | nil => exact ⟨inPar_one, tlG_one, brG_one⟩
  | cons x l ih =>
    obtain ⟨h1, h2, h3⟩ := ih (fun y hy => hl y (List.mem_cons_of_mem x hy))
    have hx := hl x List.mem_cons_self
    simp only [List.prod_cons, List.map_cons]
    exact ⟨inPar_mul hx h1, by rw [tlG_mul hx h1, h2], by rw [brG_mul hx h1, h3]⟩

theorem nrm_blocks : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'),
    (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (a b n : ℕ), n = a + b →
    ∀ (γ : GL (Fin n) F) (δ : GL (Fin n) F'), InPar a γ → InPar a δ → nrm s δ = incl F F' n γ →
    nrm s (tlG a δ) = incl F F' a (tlG a γ) ∧ nrm s (brG a b δ) = incl F F' b (brG a b γ) := by
  intro F F' _ _ _ _ s _ a b n hn γ δ hγ hδ h
  subst hn
  have hall : ∀ x ∈ (List.range (Module.finrank F F')).map (fun i => galAct F F' (a + b) (s ^ i) δ), InPar a x := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact inPar_gal _ hδ
  obtain ⟨-, h2, h3⟩ := prod_blocks _ hall
  have hn : nrm s δ = ((List.range (Module.finrank F F')).map (fun i => galAct F F' (a + b) (s ^ i) δ)).prod := rfl
  refine ⟨?_, ?_⟩
  · have e : nrm s (tlG a δ) = (((List.range (Module.finrank F F')).map
        (fun i => galAct F F' (a + b) (s ^ i) δ)).map (tlG a)).prod := by
      unfold nrm nrmG
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      simp only [Function.comp_apply, galAct_apply]
      exact (tlG_gal _ hδ).symm
    rw [e, ← h2, ← hn, h]
    exact tlG_gal _ hγ
  · have e : nrm s (brG a b δ) = (((List.range (Module.finrank F F')).map
        (fun i => galAct F F' (a + b) (s ^ i) δ)).map (brG a b)).prod := by
      unfold nrm nrmG
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      simp only [Function.comp_apply, galAct_apply]
      exact (brG_gal _ hδ).symm
    rw [e, ← h3, ← hn, h]
    exact brG_gal _ hγ

end GlobalTheory.ShinBlock
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HTransABTwoZero
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.HeckeTwo

open MeasureTheory

def hTransAB (a b : ℕ) (σ : ℂ) (ν y : ℝ) : ℂ :=
  ∫ t : ℝ, ((t : ℂ) + (y : ℂ) * I)⁻¹ ^ a * ((starRingEnd ℂ) ((t : ℂ) + (y : ℂ) * I))⁻¹ ^ b *
    ((‖(t : ℂ) + (y : ℂ) * I‖ : ℝ) : ℂ) ^ (-2 * σ) * Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ)))

theorem hTransAB_two_zero (σ : ℂ) (ν y : ℝ) : hTransAB 2 0 σ ν y = hTrans σ ν y := by
  unfold hTransAB hTrans phi
  congr 1; funext t
  simp only [pow_zero, mul_one]

variable {F : Type} [Field F] [NumberField F]

def termQ (σ : ℂ) (b ν : F) (q : Emb F → ℕ) (z : Emb F → ℂ) : ℂ :=
  ∏ τ : Emb F, (Complex.exp (2 * (Real.pi : ℂ) * I * ((τ ν * τ b * (z τ).re : ℝ) : ℂ)) *
    iteratedDeriv (q τ) (hTrans σ (τ ν)) (τ b * (z τ).im))

theorem termQ_zero (σ : ℂ) (b ν : F) (z : Emb F → ℂ) : termQ σ b ν 0 z = fTerm σ z b ν := by
  unfold termQ fTerm
  simp only [Pi.zero_apply, iteratedDeriv_zero]

end GlobalTheory.HeckeTwo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtOfContinuousRealToComplexExponentialStatement
section
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_of_continuous_real_to_complex_exponential : ∀ (χ : ℝ → ℂ), Continuous χ → (∀ s t, χ (s + t) = χ s * χ t) → χ 0 = 1 → ∀ s, HasDerivAt χ (deriv χ 0 * χ s) s := by
  first | exact @GlobalTheory.hasDerivAt_of_continuous_additive_to_mul | exact GlobalTheory.hasDerivAt_of_continuous_additive_to_mul | (intros; apply GlobalTheory.hasDerivAt_of_continuous_additive_to_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionOfLevelCoeffAndFunctionUniqueStatement
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasQExpansionOfLevel_coeff_and_function_unique : (∀ (N : ℕ) (f : ℍ → ℂ) (a b : ℕ → ℂ), 0 < N → HasQ N f a → HasQ N f b → a = b) ∧ (∀ (N : ℕ) (f g : ℍ → ℂ) (a : ℕ → ℂ), HasQ N f a → HasQ N g a → f = g) := by
  first | exact @GlobalTheory.QFam.hasQ_unique_both | exact GlobalTheory.QFam.hasQ_unique_both | (intros; apply GlobalTheory.QFam.hasQ_unique_both <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionOfLevelLinearOperationsStatement
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasQExpansionOfLevel_linear_operations : ∀ (N : ℕ), (∀ f g a b, HasQ N f a → HasQ N g b → HasQ N (fun τ => f τ + g τ) (fun n => a n + b n)) ∧ (∀ f g a b, HasQ N f a → HasQ N g b → HasQ N (fun τ => f τ - g τ) (fun n => a n - b n)) ∧ (∀ (c : ℂ) f a, HasQ N f a → HasQ N (fun τ => c * f τ) (fun n => c * a n)) ∧ (∀ c : ℂ, HasQ N (fun _ => c) (fun n => if n = 0 then c else 0)) ∧ (∀ (κ : Type) (s : Finset κ) (f : κ → ℍ → ℂ) (a : κ → ℕ → ℂ), (∀ k ∈ s, HasQ N (f k) (a k)) → HasQ N (fun τ => ∑ k ∈ s, f k τ) (fun n => ∑ k ∈ s, a k n)) := by
  first | exact @GlobalTheory.QFam.hasQ_linear | exact GlobalTheory.QFam.hasQ_linear | (intros; apply GlobalTheory.QFam.hasQ_linear <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionOfLevelMulOfPosLevelStatement
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasQExpansionOfLevel_mul_of_pos_level : ∀ (N : ℕ) (f g : ℍ → ℂ) (a b : ℕ → ℂ), 0 < N → HasQ N f a → HasQ N g b → HasQ N (fun τ => f τ * g τ) (conv a b) := by
  first | exact @GlobalTheory.QFam.hasQ_mul_conv | exact GlobalTheory.QFam.hasQ_mul_conv | (intros; apply GlobalTheory.QFam.hasQ_mul_conv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumGaussianConvolutionSeriesTermIntegralStatement
section
open MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_gaussianConvolutionSeriesTerm_integral : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (b c : ℝ), 0 < b → 0 < c → ∀ (h : SchwartzMap E ℂ) (y : E),
    HasSum (fun k => GlobalTheory.ConvSeries.term b c h k y)
      (∫ a, Complex.exp (-((b * ‖a‖ ^ 2 : ℝ) : ℂ)) * h a * Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ))) := by
  first | exact @GlobalTheory.ConvSeries.hasSum_term_integral | exact GlobalTheory.ConvSeries.hasSum_term_integral | (intros; apply GlobalTheory.ConvSeries.hasSum_term_integral <;> assumption)
end

