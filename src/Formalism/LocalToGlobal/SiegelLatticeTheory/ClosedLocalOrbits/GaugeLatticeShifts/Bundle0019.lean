import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0016
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0014

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfH
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ScalarFramePf

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc
open PI.ScalarPairDr.W (mem_orth hT_swap orth_orth finrank_orth fvec_castSucc fvec_last mem_orth_Xplus
  X_le_orth_Xplus mem_ThPairs hT_add_left hT_sub_left hT_smul_left)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lat

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem exists_hos : ∃ _P : HeightOneSpectrum (𝓞 E), True := by
  obtain ⟨p, hp0, hp⟩ := Ring.not_isField_iff_exists_prime.1 (NumberField.RingOfIntegers.not_isField E)
  exact ⟨⟨p, hp, hp0⟩, trivial⟩

theorem X_le_spanE_of_conv (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (g : ℕ) (hc : IsFixedConv Λ g F) :
    Xsp F ≤ spanE S (XLam Λ F) := by
  obtain ⟨P, -⟩ := exists_hos (E := E)
  have := P.isPrime
  obtain ⟨c, hc0, -, heq⟩ := hc.1 P
  rw [Xsp, FlagG.X, Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  have h1 : c a • F.fl.e a ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ F) := by
    rw [heq]
    exact ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact Submodule.subset_span ⟨a, rfl⟩⟩
  obtain ⟨s, hs, hsx⟩ := h1
  have hs0 : (algebraMap (𝓞 E) E s) ≠ 0 := by
    intro h
    apply hs
    have : s = 0 := (FaithfulSMul.algebraMap_injective (𝓞 E) E) (by rw [h, map_zero])
    rw [this]
    exact P.asIdeal.zero_mem
  have hmem : s • (c a • F.fl.e a) ∈ spanE S (XLam Λ F) := Submodule.subset_span hsx
  have e : F.fl.e a = ((algebraMap (𝓞 E) E s) * c a)⁻¹ • (s • (c a • F.fl.e a)) := by
    rw [algebra_compatible_smul E s, smul_smul, smul_smul, mul_assoc, inv_mul_cancel₀ (mul_ne_zero hs0 (hc0 a)),
      one_smul]
  rw [SetLike.mem_coe, e]
  exact Submodule.smul_mem _ _ hmem

theorem Xs_fvec (F : FlagG S r T) : Xs (S := S) F.fvec = F.X := by
  have h : (fun a : Fin r => F.fvec a.castSucc) = F.e := funext fun a => fvec_castSucc F a
  show Submodule.span E (Set.range fun a : Fin r => F.fvec a.castSucc) = _
  rw [h]
  rfl

theorem Xflag_top (F : LFlag S r T) : Xflag F r = Xsp F := by
  rw [Xflag, FlagG.Xa, Xsp, FlagG.X]
  congr 1
  ext v
  simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_range]
  constructor
  · rintro ⟨i, -, rfl⟩; exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩; exact ⟨i, i.2, rfl⟩

theorem hT_X_X (F : FlagG S r T) {x y : S.V} (hx : x ∈ F.X) (hy : y ∈ F.X) : S.hT x y = 0 := by
  have key : ∀ w : S.V, (∀ a, S.hT (F.e a) w = 0) → ∀ x ∈ F.X, S.hT x w = 0 := by
    intro w hw x hx
    have hx' : x ∈ Submodule.span E (Set.range F.e) := hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem x h =>
      obtain ⟨a, rfl⟩ := h
      exact hw a
    | zero =>
      have h0 := hT_sub_left (S := S) w w w
      rwa [sub_self, sub_self] at h0
    | add x y _ _ ihx ihy => rw [hT_add_left, ihx, ihy, add_zero]
    | smul c x _ ihx => rw [hT_smul_left, ihx, mul_zero]
  refine key y (fun a => ?_) x hx
  rw [hT_swap]
  have h1 : S.hT y (F.e a) = 0 := key (F.e a) (fun b => F.e_iso b a) y hy
  rw [h1, star_zero]

theorem hT_z_X (F : FlagG S r T) {y : S.V} (hy : y ∈ F.X) : S.hT F.z y = 0 := by
  have key : ∀ w : S.V, (∀ a, S.hT (F.e a) w = 0) → ∀ x ∈ F.X, S.hT x w = 0 := by
    intro w hw x hx
    have hx' : x ∈ Submodule.span E (Set.range F.e) := hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem x h =>
      obtain ⟨a, rfl⟩ := h
      exact hw a
    | zero =>
      have h0 := hT_sub_left (S := S) w w w
      rwa [sub_self, sub_self] at h0
    | add x y _ _ ihx ihy => rw [hT_add_left, ihx, ihy, add_zero]
    | smul c x _ ihx => rw [hT_smul_left, ihx, mul_zero]
  rw [hT_swap, key F.z F.z_orth y hy, star_zero]

theorem hT_X_alt (F : FlagG S r T) {x : S.V} (hx : x ∈ F.X) : S.hT x F.z = 0 := by
  have key : ∀ w : S.V, (∀ a, S.hT (F.e a) w = 0) → ∀ x ∈ F.X, S.hT x w = 0 := by
    intro w hw x hx
    have hx' : x ∈ Submodule.span E (Set.range F.e) := hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem x h =>
      obtain ⟨a, rfl⟩ := h
      exact hw a
    | zero =>
      have h0 := hT_sub_left (S := S) w w w
      rwa [sub_self, sub_self] at h0
    | add x y _ _ ihx ihy => rw [hT_add_left, ihx, ihy, add_zero]
    | smul c x _ ihx => rw [hT_smul_left, ihx, mul_zero]
  exact key F.z F.z_orth x hx

theorem theta_eq (Λ : Submodule (𝓞 E) S.V) (k : ℕ) (F : LFlag S r T) (F' F'' : LFlag S r T')
    (β : S.V ≃ₗ[E] S.V) (hn : finrank E S.V = k + 2 * r + 1)
    (hd1 : finrank E (UUE Λ F F') = 2 * r + 2) (hd2 : finrank E (UUE Λ F F'') = 2 * r + 2)
    (hU1 : UUE Λ F F' = Submodule.span E (Set.range (Sum.elim F.fl.fvec F'.fl.fvec)))
    (hG' : Gval F F' ≠ 0) (hs : s0 Λ F F' F'' β k = 1) :
    Th Λ F F' F'' β = Hp Λ F F' ∧ Th'' Λ F F' F'' β = Hp Λ F F'' := by
  have hH1 : finrank E (Hp Λ F F') + 1 = k := by
    have := finrank_orth S (UUE Λ F F')
    rw [Hp]
    omega
  have hH2 : finrank E (Hp Λ F F'') + 1 = k := by
    have := finrank_orth S (UUE Λ F F'')
    rw [Hp]
    omega
  have hTh : finrank E (Th Λ F F' F'' β) + 1 = k := by
    unfold s0 at hs
    omega
  have hThle : Th Λ F F' F'' β ≤ Hp Λ F F' := by
    rintro x ⟨p, hp, rfl⟩
    exact ((mem_ThPairs Λ F F' F'' β p).1 hp).1
  refine ⟨Submodule.eq_of_le_of_finrank_eq hThle (by omega), ?_⟩
  have hTh''le : Th'' Λ F F' F'' β ≤ Hp Λ F F'' := by
    rintro x ⟨p, hp, rfl⟩
    exact ((mem_ThPairs Λ F F' F'' β p).1 hp).2.1
  refine Submodule.eq_of_le_of_finrank_eq hTh''le ?_
  let f := (LinearMap.snd E S.V S.V).comp (ThPairs Λ F F' F'' β).subtype
  have hker : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro p hp
    have hm := (mem_ThPairs Λ F F' F'' β p.1).1 p.2
    have h2 : p.1.2 = 0 := hp
    have hx1 : p.1.1 ∈ F.fl.X := by
      have := hm.2.2.1
      rwa [h2, sub_zero] at this
    have h1 : p.1.1 = 0 := by
      refine PI.ScalarPairDr.W.eq_zero_of_orth F.fl F'.fl hG' hx1 fun b => ?_
      have hm1 := hm.1
      rw [Hp, mem_orth] at hm1
      exact hm1 _ (by rw [hU1]; exact Submodule.subset_span ⟨Sum.inr b, rfl⟩)
    exact Subtype.ext (Prod.ext h1 h2)
  have hrange : LinearMap.range f = Th'' Λ F F' F'' β := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
    rfl
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  rw [hker, hrange, finrank_bot] at h1
  have h2 : finrank E (Th Λ F F' F'' β) ≤ finrank E (ThPairs Λ F F' F'' β) :=
    Submodule.finrank_map_le _ _
  have h3 := Submodule.finrank_mono hTh''le
  omega

theorem ylift_tr (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' F'' : LFlag S r T') (β : S.V ≃ₗ[E] S.V)
    (hTh : Th Λ F F' F'' β = Hp Λ F F') {y : S.V} (hy : y ∈ UUE Λ F F'') (hyo : y ∈ orth S (Xplus F)) :
    y ∈ UUE Λ F F' := by
  rw [← orth_orth S (UUE Λ F F'), mem_orth]
  intro v hv
  have hv' : v ∈ Th Λ F F' F'' β := by rw [hTh]; exact hv
  obtain ⟨p, hp, rfl⟩ := hv'
  have hm := (mem_ThPairs Λ F F' F'' β p).1 hp
  have e1 : S.hT p.2 y = 0 := by
    have := (mem_orth S).1 hm.2.1 _ hy
    rw [hT_swap, this, star_zero]
  have e2 : S.hT (p.1 - p.2) y = 0 := (mem_orth S).1 hyo _ (Submodule.mem_sup_left hm.2.2.1)
  have : p.1 = (p.1 - p.2) + p.2 := by abel
  show S.hT p.1 y = 0
  rw [this, hT_add_left, e1, e2, add_zero]

theorem ylift_tr' (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' F'' : LFlag S r T') (β : S.V ≃ₗ[E] S.V)
    (hTh : Th'' Λ F F' F'' β = Hp Λ F F'') {y : S.V} (hy : y ∈ UUE Λ F F') (hyo : y ∈ orth S (Xplus F)) :
    y ∈ UUE Λ F F'' := by
  rw [← orth_orth S (UUE Λ F F''), mem_orth]
  intro v hv
  have hv' : v ∈ Th'' Λ F F' F'' β := by rw [hTh]; exact hv
  obtain ⟨p, hp, rfl⟩ := hv'
  have hm := (mem_ThPairs Λ F F' F'' β p).1 hp
  have e1 : S.hT p.1 y = 0 := by
    have := (mem_orth S).1 hm.1 _ hy
    rw [hT_swap, this, star_zero]
  have e2 : S.hT (p.1 - p.2) y = 0 := (mem_orth S).1 hyo _ (Submodule.mem_sup_left hm.2.2.1)
  have : p.2 = p.1 - (p.1 - p.2) := by abel
  show S.hT p.2 y = 0
  rw [this, hT_sub_left, e1, e2, sub_zero]

theorem ylift_beta (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' F'' : LFlag S r T') (β : S.V ≃ₗ[E] S.V)
    (hiso : ∀ x y, S.hT (β x) (β y) = S.hT x y) (hX : ∀ x ∈ Xsp F'', β.symm x ∈ Xsp F')
    (hTh : Th'' Λ F F' F'' β = Hp Λ F F'') {y : S.V} (hy : y ∈ UUE Λ F F') (hyo : y ∈ orth S (Xsp F')) :
    β y ∈ UUE Λ F F'' := by
  rw [← orth_orth S (UUE Λ F F''), mem_orth]
  intro v hv
  have hv' : v ∈ Th'' Λ F F' F'' β := by rw [hTh]; exact hv
  obtain ⟨p, hp, rfl⟩ := hv'
  have hm := (mem_ThPairs Λ F F' F'' β p).1 hp
  have e1 : S.hT (β p.1) (β y) = 0 := by
    rw [hiso]
    have := (mem_orth S).1 hm.1 _ hy
    rw [hT_swap, this, star_zero]
  have e2 : S.hT (β p.1 - p.2) (β y) = 0 := by
    have h := hX _ hm.2.2.2
    have : β p.1 - p.2 = β (β.symm (β p.1 - p.2)) := (β.apply_symm_apply _).symm
    rw [this, hiso]
    exact (mem_orth S).1 hyo _ h
  have : p.2 = β p.1 - (β p.1 - p.2) := by abel
  show S.hT p.2 (β y) = 0
  rw [this, hT_sub_left, e1, e2, sub_zero]

end Lat

end Formalism.L2.SG.Pf.ScalarFramePf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StepPtRepPfA
section
noncomputable section

open Matrix Formalism.MainNotions.S

namespace Formalism.L2.SG.RealObj.InfCut.PtRepPf

open Formalism.L2.SG.HidaSetting

section Calc

variable {n : ℕ} (ε : Fin n → Bool)

theorem hJ_apply (x y : Fin n → ℂ) :
    hJ ε x y = ∑ i, star (x i) * ((if ε i then 1 else -1) * y i) := by
  simp [hJ, Formalism.REAL.Jm, dotProduct, mulVec_diagonal]

theorem hJ_conj (x y : Fin n → ℂ) : star (hJ ε x y) = hJ ε y x := by
  rw [hJ_apply, hJ_apply, star_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : ε i <;> simp [h] <;> ring

theorem hJ_add_right (x y y' : Fin n → ℂ) : hJ ε x (y + y') = hJ ε x y + hJ ε x y' := by
  simp only [hJ, mulVec_add, dotProduct_add]

theorem hJ_add_left (x x' y : Fin n → ℂ) : hJ ε (x + x') y = hJ ε x y + hJ ε x' y := by
  simp only [hJ, star_add, add_dotProduct]

theorem hJ_sub_right (x y y' : Fin n → ℂ) : hJ ε x (y - y') = hJ ε x y - hJ ε x y' := by
  simp only [hJ, mulVec_sub, dotProduct_sub]

theorem hJ_smul_right (c : ℂ) (x y : Fin n → ℂ) : hJ ε x (c • y) = c * hJ ε x y := by
  simp only [hJ, mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem hJ_smul_left (c : ℂ) (x y : Fin n → ℂ) : hJ ε (c • x) y = star c * hJ ε x y := by
  simp only [hJ, star_smul, smul_dotProduct, smul_eq_mul]

theorem hJ_zero_right (x : Fin n → ℂ) : hJ ε x 0 = 0 := by simp [hJ]

theorem hJ_zero_left (y : Fin n → ℂ) : hJ ε 0 y = 0 := by simp [hJ]

def formB : (Fin n → ℂ) →ₗ⋆[ℂ] (Fin n → ℂ) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun x y => hJ ε x y)
    (fun x x' y => hJ_add_left ε x x' y)
    (fun c x y => by rw [hJ_smul_left, smul_eq_mul, starRingEnd_apply])
    (fun x y y' => hJ_add_right ε x y y')
    (fun c x y => by rw [hJ_smul_right, smul_eq_mul, RingHom.id_apply])

theorem formB_apply (x y : Fin n → ℂ) : formB ε x y = hJ ε x y := rfl

theorem hJ_sum_right {ι : Type*} (s : Finset ι) (x : Fin n → ℂ) (y : ι → Fin n → ℂ) :
    hJ ε x (∑ i ∈ s, y i) = ∑ i ∈ s, hJ ε x (y i) := by
  simp only [← formB_apply, map_sum]

theorem hJ_sum_left {ι : Type*} (s : Finset ι) (x : ι → Fin n → ℂ) (y : Fin n → ℂ) :
    hJ ε (∑ i ∈ s, x i) y = ∑ i ∈ s, hJ ε (x i) y := by
  simp only [← formB_apply, map_sum, LinearMap.sum_apply]

theorem hJ_mulVec (A : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) :
    hJ ε (A *ᵥ x) (A *ᵥ y) = star x ⬝ᵥ ((Aᴴ * Formalism.REAL.Jm ε * A) *ᵥ y) := by
  unfold hJ
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]

theorem hJ_UJ (g : Formalism.REAL.UJ ε) (x y : Fin n → ℂ) :
    hJ ε (uMat g *ᵥ x) (uMat g *ᵥ y) = hJ ε x y := by
  rw [hJ_mulVec, show (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε from g.2]
  rfl

theorem mat_eq_of_mulVec {A B : Matrix (Fin n) (Fin n) ℂ} (h : ∀ v, A *ᵥ v = B *ᵥ v) : A = B := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [mulVec_single_one] using this

theorem inUJ_of_iso (A : Matrix (Fin n) (Fin n) ℂ) (h : ∀ x y, hJ ε (A *ᵥ x) (A *ᵥ y) = hJ ε x y) :
    Formalism.REAL.inUJ ε A := by
  unfold Formalism.REAL.inUJ
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  rw [hJ_mulVec] at this
  unfold hJ at this
  simpa [mulVec_single_one] using this

theorem eq_zero_of_hJ (d : Fin n → ℂ) (h : ∀ x, hJ ε x d = 0) : d = 0 := by
  funext i
  have h1 := h (Pi.single i 1)
  rw [hJ_apply, Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)] at h1
  by_cases hi : ε i <;> simp_all

theorem li_of_pair {ι : Type*} [Fintype ι] [DecidableEq ι] (s d : ι → Fin n → ℂ) (M : Matrix ι ι ℂ)
    (hM : IsUnit M.det) (h : ∀ j i, hJ ε (d j) (s i) = M j i) : LinearIndependent ℂ s := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hMc : M *ᵥ c = 0 := by
    funext j
    have := congrArg (hJ ε (d j)) hc
    rw [hJ_sum_right, hJ_zero_right] at this
    simp only [hJ_smul_right, h] at this
    simpa [mulVec, dotProduct, mul_comm] using this
  have h0 : c = 0 := by
    have := congrArg (fun v => M⁻¹ *ᵥ v) hMc
    simpa [mulVec_mulVec, nonsing_inv_mul _ hM] using this
  intro i
  simp [h0]

theorem expand_of_dual {ι : Type*} [Fintype ι] [DecidableEq ι] (φ d : ι → Fin n → ℂ)
    (hcard : Fintype.card ι = n) (hd : ∀ j i, hJ ε (d j) (φ i) = if j = i then 1 else 0)
    (v : Fin n → ℂ) : v = ∑ i, hJ ε (d i) v • φ i := by
  have hli : LinearIndependent ℂ d := li_of_pair ε d φ 1 (by simp) (fun j i => by
    rw [← hJ_conj, hd, one_apply]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Ne.symm hij])
  have hspan := hli.span_eq_top_of_card_eq_finrank' (by rw [hcard, Module.finrank_fin_fun])
  rw [← sub_eq_zero]
  apply eq_zero_of_hJ ε
  intro x
  have hx : x ∈ Submodule.span ℂ (Set.range d) := by rw [hspan]; trivial
  refine Submodule.span_induction (p := fun x _ => hJ ε x (v - ∑ i, hJ ε (d i) v • φ i) = 0)
    ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨j, rfl⟩
    rw [hJ_sub_right, hJ_sum_right]
    simp only [hJ_smul_right, hd, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      sub_self]
  · exact hJ_zero_left ε _
  · intro x y _ _ hx hy; rw [hJ_add_left, hx, hy, add_zero]
  · intro c x _ hx; rw [hJ_smul_left, hx, mul_zero]

end Calc

section Witt

variable {n : ℕ} (ε : Fin n → Bool)

theorem wittFam {ι : Type*} [Fintype ι] (s t : ι → Fin n → ℂ) (hs : LinearIndependent ℂ s)
    (ht : LinearIndependent ℂ t) (hG : ∀ i j, hJ ε (t i) (t j) = hJ ε (s i) (s j)) :
    ∃ g : Formalism.REAL.UJ ε, ∀ i, uMat g *ᵥ s i = t i := by
  classical
  let U := Submodule.span ℂ (Set.range s)
  let bs : Module.Basis ι ℂ U := Module.Basis.span hs
  let f : U →ₗ[ℂ] (Fin n → ℂ) := bs.constr ℂ t
  have hf : ∀ i, f (bs i) = t i := fun i => bs.constr_basis ℂ t i
  have hsum : ∀ x : U, (x : Fin n → ℂ) = ∑ i, bs.repr x i • s i := by
    intro x
    have := congrArg (fun y : U => (y : Fin n → ℂ)) (bs.sum_repr x)
    simp only [Submodule.coe_sum, Submodule.coe_smul, bs] at this
    refine this.symm.trans (Finset.sum_congr rfl fun i _ => ?_)
    congr 1
    exact congrArg Subtype.val (Module.Basis.span_apply hs i)
  have hfsum : ∀ x : U, f x = ∑ i, bs.repr x i • t i := by
    intro x
    have := congrArg f (bs.sum_repr x)
    rw [map_sum] at this
    simp only [map_smul, hf] at this
    exact this.symm
  have e1 : ∀ x : U, Finsupp.linearCombination ℂ t (bs.repr x) = f x := fun x => by
    rw [hfsum, Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    intro i; simp
  have finj : Function.Injective f := by
    intro x y hxy
    apply bs.repr.injective
    exact (show Function.Injective (Finsupp.linearCombination ℂ t) from ht) (by rw [e1, e1, hxy])
  have hiso : ∀ x y : U, formB ε (f x) (f y) = formB ε (x : Fin n → ℂ) y := by
    intro x y
    simp only [formB_apply, hfsum, hsum, hJ_sum_left, hJ_sum_right, hJ_smul_left, hJ_smul_right, hG]
  have hnd : ∀ x, (∀ y, formB ε x y = 0) → x = 0 := by
    intro x hx
    apply eq_zero_of_hJ ε
    intro y
    rw [← hJ_conj ε x y, ← formB_apply, hx y, star_zero]
  obtain ⟨g, hgiso, hgext⟩ := witt_extension_theorem ℂ (Fin n → ℂ) (formB ε)
    (fun x y => hJ_conj ε x y) hnd U f finj hiso
  let A : Matrix (Fin n) (Fin n) ℂ := LinearMap.toMatrix' (g : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))
  let Ai : Matrix (Fin n) (Fin n) ℂ := LinearMap.toMatrix' (g.symm : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))
  have hA : ∀ v, A *ᵥ v = g v := fun v => LinearMap.toMatrix'_mulVec _ v
  have hAi : ∀ v, Ai *ᵥ v = g.symm v := fun v => LinearMap.toMatrix'_mulVec _ v
  have h1 : A * Ai = 1 := mat_eq_of_mulVec fun v => by
    rw [← mulVec_mulVec, hAi, hA, one_mulVec, LinearEquiv.apply_symm_apply]
  have h2 : Ai * A = 1 := mat_eq_of_mulVec fun v => by
    rw [← mulVec_mulVec, hA, hAi, one_mulVec, LinearEquiv.symm_apply_apply]
  have hmem : Formalism.REAL.inUJ ε A := inUJ_of_iso ε A fun x y => by
    rw [hA, hA, ← formB_apply, hgiso, formB_apply]
  refine ⟨⟨⟨A, Ai, h1, h2⟩, hmem⟩, fun i => ?_⟩
  show A *ᵥ s i = t i
  rw [hA]
  have := hgext (bs i)
  rw [Module.Basis.span_apply] at this
  rw [this, ← Module.Basis.span_apply hs i]
  exact hf i

end Witt

section Rot

variable {n : ℕ} (ε : Fin n → Bool)

def rotM (ω : Fin n → ℂ) (φ : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => (if i = j then 1 else 0) + (φ - 1) * ω i * (star (ω j) * (if ε j then 1 else -1))

theorem rotM_mulVec (ω : Fin n → ℂ) (φ : ℂ) (v : Fin n → ℂ) :
    rotM ε ω φ *ᵥ v = v + ((φ - 1) * hJ ε ω v) • ω := by
  funext i
  simp only [rotM, mulVec, dotProduct, of_apply, add_mul, Finset.sum_add_distrib, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    hJ_apply]
  congr 1
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by split_ifs <;> ring

theorem rotM_mul (ω : Fin n → ℂ) (hω : hJ ε ω ω = 1) (α β : ℂ) (hab : α * β = 1) :
    rotM ε ω α * rotM ε ω β = 1 := mat_eq_of_mulVec fun v => by
  rw [← mulVec_mulVec, rotM_mulVec, rotM_mulVec, hJ_add_right, hJ_smul_right, hω, one_mulVec, add_assoc,
    ← add_smul]
  have e : ∀ c : ℂ, c = 0 → v + c • ω = v := fun c hc => by rw [hc, zero_smul, add_zero]
  apply e
  linear_combination (hJ ε ω v) * hab

theorem rotM_iso (ω : Fin n → ℂ) (hω : hJ ε ω ω = 1) (φ : ℂ) (hφ : star φ * φ = 1) (x y : Fin n → ℂ) :
    hJ ε (rotM ε ω φ *ᵥ x) (rotM ε ω φ *ᵥ y) = hJ ε x y := by
  simp only [rotM_mulVec, hJ_add_left, hJ_add_right, hJ_smul_left, hJ_smul_right, hω, star_mul', star_sub,
    star_one]
  rw [← hJ_conj ε ω x]
  linear_combination (star (hJ ε ω x) * hJ ε ω y) * hφ

def rotU (ω : Fin n → ℂ) (hω : hJ ε ω ω = 1) (φ : ℂ) (hφ : star φ * φ = 1) : Formalism.REAL.UJ ε :=
  ⟨⟨rotM ε ω φ, rotM ε ω (star φ), rotM_mul ε ω hω _ _ (by rw [mul_comm]; exact hφ),
    rotM_mul ε ω hω _ _ hφ⟩, inUJ_of_iso ε _ (rotM_iso ε ω hω φ hφ)⟩

theorem rotU_mulVec (ω : Fin n → ℂ) (hω : hJ ε ω ω = 1) (φ : ℂ) (hφ : star φ * φ = 1) (v : Fin n → ℂ) :
    uMat (rotU ε ω hω φ hφ) *ᵥ v = v + ((φ - 1) * hJ ε ω v) • ω :=
  rotM_mulVec ε ω φ v

end Rot

end Formalism.L2.SG.RealObj.InfCut.PtRepPf
end
end

