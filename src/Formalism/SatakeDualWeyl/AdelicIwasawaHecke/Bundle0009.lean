import Formalism.SatakeDualWeyl.Bundle0003
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0007

-- bundled from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bridge
section
noncomputable section

open Matrix

namespace Formalism.UG.P

theorem glEquiv_apply' {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n]
    (g : GL n K) (x : n → K) : Formalism.UG.glEquiv g x = (g : Matrix n n K) *ᵥ x := by
  first
  | rfl
  | simp [LinearMap.GeneralLinearGroup.generalLinearEquiv, Matrix.GeneralLinearGroup.toLin, Matrix.toLin'_apply]

theorem hform_eq_dot {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A)
    (J : Matrix n n A) (x y : n → A) : Formalism.UG.hform σ J x y = (σ ∘ x) ⬝ᵥ (J *ᵥ y) := by
  unfold Formalism.UG.hform
  first
  | simp only [dotProduct, mulVec, Function.comp_apply, Finset.mul_sum, mul_assoc]
  | simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem hform_mulVec {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A)
    (J M : Matrix n n A) (x y : n → A) :
    Formalism.UG.hform σ J (M *ᵥ x) (M *ᵥ y) = Formalism.UG.hform σ (Formalism.UG.cT σ M * J * M) x y := by
  rw [hform_eq_dot, hform_eq_dot]
  unfold Formalism.UG.cT
  have h1 : (⇑σ ∘ (M *ᵥ x)) = (M.map σ) *ᵥ (⇑σ ∘ x) := by
    funext i
    first
    | exact RingHom.map_mulVec σ M x i
    | simp [mulVec, dotProduct, map_sum, map_mul]
  rw [h1, mulVec_mulVec, ← vecMul_transpose (M.map ⇑σ) (⇑σ ∘ x), ← dotProduct_mulVec, mulVec_mulVec,
    Matrix.mul_assoc]

theorem hform_single {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
    (σ : A →+* A) (J : Matrix n n A) (i j : n) :
    Formalism.UG.hform σ J (Pi.single i 1) (Pi.single j 1) = J i j := by
  rw [hform_eq_dot]
  have hs : (⇑σ ∘ Pi.single i (1 : A)) = Pi.single i 1 := by
    funext k
    by_cases hk : k = i
    · subst hk
      simp
    · simp [Pi.single_apply, hk]
  rw [hs]
  simp [mulVec_single]

theorem hform_gram {K : Type} [Field K] [StarRing K] {n : Type} [Fintype n] [DecidableEq n]
    (h : (n → K) →ₗ⋆[K] (n → K) →ₗ[K] K) (x y : n → K) :
    h x y = Formalism.UG.hform (starRingEnd K) (Formalism.UG.gram h) x y := by
  have hx : ∀ v : n → K, v = ∑ i, v i • (Pi.single i 1 : n → K) := by
    intro v
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hx x, hx y]
  simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, map_smul, smul_eq_mul,
    Finset.mul_sum]
  unfold Formalism.UG.hform Formalism.UG.gram
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  simp only [RingHom.id_apply]
  ring

theorem hermitian_lattice_correspondence_holds : Formalism.UG.HermBridge := by
  intro K _ _ n _ _ h g
  unfold Formalism.UG.UJ HermitianLatticesTheory.isom
  constructor
  · intro hg x y
    have hg' : Formalism.UG.cT (starRingEnd K) (g : Matrix n n K) * Formalism.UG.gram h * (g : Matrix n n K)
        = Formalism.UG.gram h := hg
    show h (Formalism.UG.glEquiv g x) (Formalism.UG.glEquiv g y) = h x y
    rw [glEquiv_apply', glEquiv_apply', hform_gram h ((g : Matrix n n K) *ᵥ x) ((g : Matrix n n K) *ᵥ y),
      hform_gram h x y, hform_mulVec, hg']
  · intro hg
    have hg' : ∀ x y : n → K, h (Formalism.UG.glEquiv g x) (Formalism.UG.glEquiv g y) = h x y := hg
    show Formalism.UG.cT (starRingEnd K) (g : Matrix n n K) * Formalism.UG.gram h * (g : Matrix n n K)
        = Formalism.UG.gram h
    ext i j
    have := hg' (Pi.single i 1) (Pi.single j 1)
    rw [glEquiv_apply', glEquiv_apply',
      hform_gram h ((g : Matrix n n K) *ᵥ Pi.single i 1) ((g : Matrix n n K) *ᵥ Pi.single j 1),
      hform_gram h (Pi.single i 1) (Pi.single j 1), hform_mulVec, hform_single, hform_single] at this
    exact this

theorem hermitian_correspondence_surjective_holds : Formalism.UG.HermBridgeSurj := by
  intro K _ _ n _ _ h u _
  refine ⟨Matrix.GeneralLinearGroup.toLin.symm
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv K (n → K)).symm u), ?_⟩
  unfold Formalism.UG.glEquiv
  simp

theorem stabilizer_group_map_holds : Formalism.UG.StabGmap := by
  intro K _ R _ _ n _ _ Λ g
  unfold Formalism.UG.stabGL HermitianLatticesTheory.gmap
  show (∀ x : n → K, x ∈ Λ ↔ (g : Matrix n n K) *ᵥ x ∈ Λ) ↔ _
  constructor
  · intro hg
    ext y
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      show Formalism.UG.glEquiv g x ∈ Λ
      rw [glEquiv_apply']
      exact (hg x).mp hx
    · intro hy
      refine ⟨(Formalism.UG.glEquiv g).symm y, ?_, ?_⟩
      · rw [hg, ← glEquiv_apply']
        simpa using hy
      · show Formalism.UG.glEquiv g ((Formalism.UG.glEquiv g).symm y) = y
        simp
  · intro hg x
    constructor
    · intro hx
      rw [← hg, Submodule.mem_map]
      exact ⟨x, hx, glEquiv_apply' g x⟩
    · intro hx
      rw [← hg, Submodule.mem_map] at hx
      obtain ⟨z, hz, hzx⟩ := hx
      have hzx' : Formalism.UG.glEquiv g z = (g : Matrix n n K) *ᵥ x := hzx
      have hzx'' : Formalism.UG.glEquiv g z = Formalism.UG.glEquiv g x := by
        rw [hzx', glEquiv_apply']
      rw [← (Formalism.UG.glEquiv g).injective hzx'']
      exact hz

end Formalism.UG.P
end
end

-- bundled from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FIwasawaB
section
open Formalism.UG Matrix

namespace Formalism.UG.P

section FIwasawaMat

variable {L : Type} [Field L] (σ : L →+* L) {n : ℕ}

def fIwasawaP (π : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) L :=
  Matrix.of fun i j => if π i = j then 1 else 0

theorem permMatrix_mulVec₂ (π : Equiv.Perm (Fin n)) (w : Fin n → L) :
    fIwasawaP π *ᵥ w = fun i => w (π i) := by
  funext i
  simp [fIwasawaP, Matrix.mulVec, dotProduct]

theorem permMatrix_mul_apply₂ (π : Equiv.Perm (Fin n)) (M : Matrix (Fin n) (Fin n) L) (i j : Fin n) :
    (fIwasawaP π * M : Matrix (Fin n) (Fin n) L) i j = M (π i) j := by
  simp [fIwasawaP, Matrix.mul_apply]

theorem permMatrix_isUnitary_of_commute_rev (π : Equiv.Perm (Fin n)) (hπ : ∀ i, π (Fin.rev i) = Fin.rev (π i)) :
    fIwasawaUn σ (fIwasawaP (L := L) π) := by
  apply fIwasawa_un_of_isometry
  intro x y
  simp only [fIwasawaH, permMatrix_mulVec₂, hπ]
  exact Equiv.sum_comp π (fun k => σ (x (Fin.rev k)) * y k)

def fIwasawaE (e z : Fin n → L) (c : L) : Matrix (Fin n) (Fin n) L :=
  Matrix.of fun i j => (if i = j then 1 else 0) + z i * σ (e (Fin.rev j)) - e i * σ (z (Fin.rev j)) +
    c * e i * σ (e (Fin.rev j))

theorem fIwasawa_E_mulVec (e z : Fin n → L) (c : L) (w : Fin n → L) :
    fIwasawaE σ e z c *ᵥ w = w + fIwasawaH σ e w • z - fIwasawaH σ z w • e +
      (c * fIwasawaH σ e w) • e := by
  funext i
  simp only [fIwasawaE, fIwasawaH, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.add_apply,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, add_mul, sub_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Finset.mul_sum, Finset.sum_mul]
  ring_nf

theorem fIwasawa_E_un (hσ : ∀ x, σ (σ x) = x) (e z : Fin n → L) (c : L)
    (hee : fIwasawaH σ e e = 0) (hez : fIwasawaH σ e z = 0)
    (hc : c + σ c + fIwasawaH σ z z = 0) : fIwasawaUn σ (fIwasawaE σ e z c) := by
  have Hal : ∀ x x' y : Fin n → L, fIwasawaH σ (x + x') y = fIwasawaH σ x y + fIwasawaH σ x' y := by
    intro x x' y
    simp [fIwasawaH, add_mul, Finset.sum_add_distrib]
  have Hsl : ∀ x x' y : Fin n → L, fIwasawaH σ (x - x') y = fIwasawaH σ x y - fIwasawaH σ x' y := by
    intro x x' y
    simp [fIwasawaH, sub_mul, Finset.sum_sub_distrib]
  have Hml : ∀ (t : L) (x y : Fin n → L), fIwasawaH σ (t • x) y = σ t * fIwasawaH σ x y := by
    intro t x y
    simp [fIwasawaH, Finset.mul_sum, mul_assoc]
  have Har : ∀ x y y' : Fin n → L, fIwasawaH σ x (y + y') = fIwasawaH σ x y + fIwasawaH σ x y' := by
    intro x y y'
    simp [fIwasawaH, mul_add, Finset.sum_add_distrib]
  have Hsr : ∀ x y y' : Fin n → L, fIwasawaH σ x (y - y') = fIwasawaH σ x y - fIwasawaH σ x y' := by
    intro x y y'
    simp [fIwasawaH, mul_sub, Finset.sum_sub_distrib]
  have Hmr : ∀ (t : L) (x y : Fin n → L), fIwasawaH σ x (t • y) = t * fIwasawaH σ x y := by
    intro t x y
    simp only [fIwasawaH, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have Hsym : ∀ x y : Fin n → L, fIwasawaH σ y x = σ (fIwasawaH σ x y) := by
    intro x y
    simp only [fIwasawaH, map_sum, map_mul, hσ]
    exact (Fintype.sum_equiv Fin.revPerm _ _ fun j => by simp [mul_comm]).symm
  apply fIwasawa_un_of_isometry
  intro w w'
  rw [fIwasawa_E_mulVec, fIwasawa_E_mulVec]
  simp only [Hal, Hsl, Hml, Har, Hsr, Hmr, map_mul]
  simp only [Hsym z w, Hsym e w, Hsym e z, hez, hee, map_zero]
  linear_combination (σ (fIwasawaH σ e w) * fIwasawaH σ e w') * hc

end FIwasawaMat

section FIwasawaInt

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) {n : ℕ}

def fIwasawaInt (M : Matrix (Fin n) (Fin n) L) : Prop := ∀ i j, Valued.v (M i j) ≤ 1

theorem fIwasawa_int_mul (A B : Matrix (Fin n) (Fin n) L) (hA : fIwasawaInt A) (hB : fIwasawaInt B) :
    fIwasawaInt (A * B) := by
  intro i j
  rw [Matrix.mul_apply]
  exact Valuation.map_sum_le _ fun k _ => by rw [map_mul]; exact mul_le_one' (hA i k) (hB k j)

theorem fIwasawa_int_one : fIwasawaInt (1 : Matrix (Fin n) (Fin n) L) := by
  intro i j
  rw [Matrix.one_apply]
  split_ifs <;> simp

theorem fIwasawa_int_inv (hσv : ∀ x, Valued.v (σ x) = Valued.v x) (M : Matrix (Fin n) (Fin n) L)
    (hM : fIwasawaInt M) : fIwasawaInt (fIwasawaInv σ M) := by
  have hJ : fIwasawaInt (antiJ L n) := by
    intro i j
    simp only [antiJ]
    split_ifs <;> simp
  have hcT : fIwasawaInt (cT σ M) := by
    intro i j
    simp only [cT, Matrix.transpose_apply, Matrix.map_apply]
    rw [hσv]
    exact hM j i
  unfold fIwasawaInv
  exact fIwasawa_int_mul _ _ (fIwasawa_int_mul _ _ hJ hcT) hJ

theorem fIwasawa_int_P (π : Equiv.Perm (Fin n)) : fIwasawaInt (fIwasawaP (L := L) π) := by
  intro i j
  simp only [fIwasawaP, Matrix.of_apply]
  split_ifs <;> simp

theorem fIwasawa_int_E (hσv : ∀ x, Valued.v (σ x) = Valued.v x) (e z : Fin n → L) (c : L)
    (he : ∀ i, Valued.v (e i) ≤ 1) (hz : ∀ i, Valued.v (z i) ≤ 1) (hc : Valued.v c ≤ 1) :
    fIwasawaInt (fIwasawaE σ e z c) := by
  intro i j
  simp only [fIwasawaE, Matrix.of_apply]
  have h1 : Valued.v (if i = j then (1 : L) else 0) ≤ 1 := by split_ifs <;> simp
  refine Valuation.map_add_le _ (Valuation.map_sub_le _ (Valuation.map_add_le _ h1 ?_) ?_) ?_
  · rw [map_mul, hσv]
    exact mul_le_one' (hz i) (he _)
  · rw [map_mul, hσv]
    exact mul_le_one' (he i) (hz _)
  · rw [map_mul, map_mul, hσv]
    exact mul_le_one' (mul_le_one' hc (he i)) (he _)

theorem fIwasawa_mk_mem_K (hσv : ∀ x, Valued.v (σ x) = Valued.v x) (M : Matrix (Fin n) (Fin n) L)
    (hM : fIwasawaUn σ M) (hI : fIwasawaInt M) : fIwasawaMk σ M hM ∈ KU σ n := by
  have hinvI := fIwasawa_int_inv σ hσv M hI
  rw [KU, Subgroup.mem_subgroupOf]
  refine Subgroup.mem_inf.2 ⟨(fIwasawaMk σ M hM).2, ?_⟩
  let A : Matrix (Fin n) (Fin n) (intL L) := Matrix.of fun i j => ⟨M i j, hI i j⟩
  let B : Matrix (Fin n) (Fin n) (intL L) := Matrix.of fun i j => ⟨fIwasawaInv σ M i j, hinvI i j⟩
  have hinj : Function.Injective
      (RingHom.mapMatrix (intL L).subtype : Matrix (Fin n) (Fin n) (intL L) →+* Matrix (Fin n) (Fin n) L) :=
    fun X Y h => by
      ext i j
      exact congrFun (congrFun h i) j
  have hA : RingHom.mapMatrix (intL L).subtype A = M := by ext i j; rfl
  have hB : RingHom.mapMatrix (intL L).subtype B = fIwasawaInv σ M := by ext i j; rfl
  have hAB : A * B = 1 := hinj (by rw [map_mul, hA, hB, map_one, fIwasawa_mul_inv σ M hM])
  have hBA : B * A = 1 := hinj (by rw [map_mul, hA, hB, map_one, fIwasawa_inv_mul σ M hM])
  refine ⟨⟨A, B, hAB, hBA⟩, ?_⟩
  apply Units.ext
  show RingHom.mapMatrix (intL L).subtype A = _
  rw [hA]
  exact (fIwasawa_mk_val σ M hM).symm

theorem fIwasawa_K_int (k : GU σ n) (hk : k ∈ KU σ n) :
    fIwasawaInt (((k : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) := by
  intro i j
  have h1 := Subgroup.mem_subgroupOf.1 hk
  obtain ⟨k', hk'⟩ := (Subgroup.mem_inf.1 h1).2
  rw [← hk']
  show Valued.v (((k' : Matrix (Fin n) (Fin n) (intL L)) i j : intL L) : L) ≤ 1
  exact (k' i j).2

end FIwasawaInt

end Formalism.UG.P
end

