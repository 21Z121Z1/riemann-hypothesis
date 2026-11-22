import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0007
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0014
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0015
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0016
import GroundTheory.GlobalFields.Artin.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormSmulLeOneOfPrimitiveBoundedPowers

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeElementaryDivisors
section
open IsDedekindDomain NumberField

namespace GlobalTheory.LatticeMinuscule

open Matrix

variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {n : ℕ}

theorem map_mulVec_algebraMap (M : Matrix (Fin n) (Fin n) R) (z : Fin n → R) :
    (M.map (algebraMap R K)).mulVec (fun i => algebraMap R K (z i))
      = fun i => algebraMap R K (M.mulVec z i) := by
  funext i
  rw [RingHom.map_mulVec]
  rfl

theorem exists_frame [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K]
    (Λ : Submodule R (Fin n → K)) (hfg : Λ.FG)
    (hsp : Submodule.span K (Λ : Set (Fin n → K)) = ⊤) :
    ∃ C : Matrix (Fin n) (Fin n) K, IsUnit C.det ∧
      ∀ y, y ∈ Λ ↔ ∃ z : Fin n → R, y = C.mulVec (fun i => algebraMap R K (z i)) := by
  haveI : Submodule.IsLattice K Λ := ⟨hfg, hsp⟩
  have hr : Module.finrank R Λ = n := by
    rw [Submodule.IsLattice.finrank_of_pi K Λ, Fintype.card_fin]
  let b : Module.Basis (Fin n) R Λ := Module.finBasisOfFinrankEq R Λ hr
  have key : ∀ z : Fin n → R,
      ((Pi.basisFun K (Fin n)).toMatrix (b.extendOfIsLattice K)).mulVec
        (fun i => algebraMap R K (z i)) = ((∑ j, z j • b j : Λ) : Fin n → K) := by
    intro z
    funext i
    simp [Matrix.mulVec, dotProduct, Module.Basis.toMatrix_apply, Algebra.smul_def, mul_comm]
  refine ⟨(Pi.basisFun K (Fin n)).toMatrix (b.extendOfIsLattice K), ?_, fun y => ⟨?_, ?_⟩⟩
  · rw [← Module.Basis.det_apply]; exact Module.Basis.isUnit_det _ _
  · intro hy
    refine ⟨b.repr ⟨y, hy⟩, ?_⟩
    rw [key, b.sum_repr]
  · rintro ⟨z, rfl⟩
    rw [key]
    exact Subtype.prop _

theorem exists_mul_eq (Λ : Submodule R (Fin n → K)) (C : Matrix (Fin n) (Fin n) K)
    (hC : ∀ y, y ∈ Λ ↔ ∃ z : Fin n → R, y = C.mulVec (fun i => algebraMap R K (z i)))
    (a : Matrix (Fin n) (Fin n) K) (ha : ∀ y ∈ Λ, a.mulVec y ∈ Λ) :
    ∃ M : Matrix (Fin n) (Fin n) R, a * C = C * M.map (algebraMap R K) := by
  have h : ∀ j : Fin n, ∃ z : Fin n → R,
      a.mulVec (C.mulVec (fun i => algebraMap R K ((Pi.single j 1 : Fin n → R) i)))
        = C.mulVec (fun i => algebraMap R K (z i)) :=
    fun j => (hC _).mp (ha _ ((hC _).mpr ⟨_, rfl⟩))
  choose z hz using h
  refine ⟨Matrix.of fun i j => z j i, ?_⟩
  ext i j
  have h1 := congrFun (hz j) i
  have h2 : (fun i => algebraMap R K ((Pi.single j 1 : Fin n → R) i)) = Pi.single j 1 := by
    funext k
    by_cases hk : k = j
    · subst hk; simp
    · simp [hk]
  rw [h2, Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at h1
  exact h1

theorem exists_mul_unit_iff (C : Matrix (Fin n) (Fin n) K) (P : Matrix (Fin n) (Fin n) R)
    (hP : IsUnit P.det) (y : Fin n → K) :
    (∃ z : Fin n → R, y = C.mulVec (fun i => algebraMap R K (z i))) ↔
      ∃ z : Fin n → R,
        y = (C * P.map (algebraMap R K)).mulVec (fun i => algebraMap R K (z i)) := by
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨P⁻¹.mulVec z, ?_⟩
    rw [← Matrix.mulVec_mulVec, map_mulVec_algebraMap, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ hP, Matrix.one_mulVec]
  · rintro ⟨z, rfl⟩
    exact ⟨P.mulVec z, by rw [← Matrix.mulVec_mulVec, map_mulVec_algebraMap]⟩

open IsDedekindDomain NumberField in
open Matrix in
variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {n : ℕ} in
theorem _root_.GlobalTheory.LatticeMinuscule.lattice_elementary_divisors (R K : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (ϖ : R)
    (hϖ : Irreducible ϖ) (n k : ℕ) (hk : k ≤ n) (Λ : Submodule R (Fin n → K)) (hfg : Λ.FG)
    (hsp : Submodule.span K (Λ : Set (Fin n → K)) = ⊤) (a a' : Matrix (Fin n) (Fin n) K)
    (haa : a * a' = 1) (h1 : ∀ y ∈ Λ, a.mulVec y ∈ Λ)
    (h2 : ∀ y ∈ Λ, ∃ z ∈ Λ, algebraMap R K ϖ • y = a.mulVec z) (u : Rˣ)
    (hdet : a.det = algebraMap R K ϖ ^ k * algebraMap R K (u : R)) :
    ∃ B : Matrix (Fin n) (Fin n) K,
      (∀ y, y ∈ Λ ↔ ∃ z : Fin n → R, y = B.mulVec (fun i => algebraMap R K (z i))) ∧
      (∀ y, (∃ x ∈ Λ, y = a'.mulVec x) ↔ ∃ z : Fin n → R, y = B.mulVec (fun i =>
        algebraMap R K ϖ ^ (if i.1 < n - k then (0 : ℤ) else -1) * algebraMap R K (z i))) := by
  classical
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hϖ0 : algebraMap R K ϖ ≠ 0 := (map_ne_zero_iff _ hinj).mpr hϖ.ne_zero
  haveI : Module.Finite R Λ := Module.Finite.iff_fg.mpr hfg
  haveI : Module.Free R Λ := Module.free_of_finite_type_torsion_free'
  let b := Module.Free.chooseBasis R Λ
  have hli : LinearIndependent K (fun i => (b i : Fin n → K)) :=
    (LinearIndependent.iff_fractionRing R K).mp
      (b.linearIndependent.map' Λ.subtype (Submodule.ker_subtype Λ))
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex R Λ) = n := by
    have hspan : ⊤ ≤ Submodule.span K (Set.range fun i => (b i : Fin n → K)) := by
      rw [← hsp, Submodule.span_le]
      intro x hx
      rw [← show ((⟨x, hx⟩ : Λ) : Fin n → K) = x from rfl, ← b.sum_repr ⟨x, hx⟩,
        Submodule.coe_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [Submodule.coe_smul, ← algebraMap_smul K]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have h := Module.finrank_eq_card_basis (Module.Basis.mk hli hspan)
    rw [Module.finrank_fin_fun] at h
    exact h.symm
  let b' := b.reindex (Fintype.equivFinOfCardEq hcard)
  let B0 : Matrix (Fin n) (Fin n) K := Matrix.of fun i j => (b' j : Fin n → K) i
  have key : ∀ z : Fin n → R, B0 *ᵥ (fun i => algebraMap R K (z i)) =
      ((b'.equivFun.symm z : Λ) : Fin n → K) := by
    intro z; ext i
    simp [B0, Matrix.mulVec, dotProduct, Module.Basis.equivFun_symm_apply, Submodule.coe_sum,
      Finset.sum_apply, Algebra.smul_def, mul_comm]
  have memL : ∀ y, y ∈ Λ ↔ ∃ z : Fin n → R, y = B0 *ᵥ (fun i => algebraMap R K (z i)) := by
    intro y; constructor
    · intro hy; refine ⟨b'.equivFun ⟨y, hy⟩, ?_⟩; rw [key, LinearEquiv.symm_apply_apply]
    · rintro ⟨z, rfl⟩; rw [key]; exact Subtype.prop _
  have keyinj : ∀ z w : Fin n → R, B0 *ᵥ (fun i => algebraMap R K (z i)) =
      B0 *ᵥ (fun i => algebraMap R K (w i)) → z = w := by
    intro z w h; rw [key, key] at h; exact b'.equivFun.symm.injective (Subtype.coe_injective h)
  have hmap : ∀ (N : Matrix (Fin n) (Fin n) R) (z : Fin n → R),
      N.map (algebraMap R K) *ᵥ (fun i => algebraMap R K (z i)) =
        fun i => algebraMap R K ((N *ᵥ z) i) := by
    intro N z; funext i; exact (RingHom.map_mulVec (algebraMap R K) N z i).symm
  have h1' : ∀ j, ∃ z : Fin n → R,
      a *ᵥ (b' j : Fin n → K) = B0 *ᵥ (fun i => algebraMap R K (z i)) :=
    fun j => (memL _).1 (h1 _ (b' j).2)
  choose zM hzM using h1'
  let M : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => zM j i
  have haB : a * B0 = B0 * M.map (algebraMap R K) := by
    ext i j
    have := congrFun (hzM j) i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, B0, M] using this
  have h2' : ∀ j, ∃ z : Fin n → R, algebraMap R K ϖ • (b' j : Fin n → K) =
      a *ᵥ (B0 *ᵥ (fun i => algebraMap R K (z i))) := by
    intro j
    obtain ⟨x, hx, hxe⟩ := h2 _ (b' j).2
    obtain ⟨z, rfl⟩ := (memL x).1 hx
    exact ⟨z, hxe⟩
  choose zM' hzM' using h2'
  let M' : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => zM' j i
  have hMM : M * M' = ϖ • (1 : Matrix (Fin n) (Fin n) R) := by
    ext i j
    have h := hzM' j
    rw [Matrix.mulVec_mulVec, haB, ← Matrix.mulVec_mulVec, hmap] at h
    have hl : algebraMap R K ϖ • (b' j : Fin n → K) =
        B0 *ᵥ (fun i => algebraMap R K ((ϖ • Pi.single j (1 : R) : Fin n → R) i)) := by
      rw [key, map_smul, Module.Basis.equivFun_symm_apply]
      simp [Pi.single_apply, algebraMap_smul]
    have h3 := congrFun (keyinj _ _ (hl.symm.trans h)) i
    rw [show (M * M') i j = (M *ᵥ zM' j) i from rfl, ← h3]
    simp [Matrix.one_apply, Pi.single_apply]
  have hsurj : Function.Surjective B0.mulVec := by
    intro y
    have hy : y ∈ Submodule.span K (Λ : Set (Fin n → K)) := hsp ▸ Submodule.mem_top
    have hle : Submodule.span K (Λ : Set (Fin n → K)) ≤ LinearMap.range (Matrix.mulVecLin B0) := by
      rw [Submodule.span_le]
      intro x hx
      obtain ⟨z, rfl⟩ := (memL x).1 hx
      exact ⟨_, rfl⟩
    obtain ⟨w, hw⟩ := hle hy
    exact ⟨w, hw⟩
  have hB0 : B0.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det B0).mp (Matrix.mulVec_surjective_iff_isUnit.mp hsurj)).ne_zero
  have hdetM : Associated M.det (ϖ ^ k) := by
    have h := congrArg Matrix.det haB
    have hdm : (M.map (algebraMap R K)).det = algebraMap R K M.det := (RingHom.map_det _ _).symm
    rw [Matrix.det_mul, Matrix.det_mul, mul_comm, hdet, hdm, ← map_pow, ← map_mul] at h
    have h' := hinj (mul_left_cancel₀ hB0 h)
    exact ⟨u⁻¹, by rw [← h', mul_assoc, Units.mul_inv, mul_one]⟩
  obtain ⟨P, Q, hP, hQ, hMQ⟩ :=
    _root_.GlobalTheory.SmithBetween.smith_between R ϖ hϖ n k hk M M' hMM hdetM
  have haa' : a' * a = 1 := mul_eq_one_comm.mp haa
  have hE : ∀ z : Fin n → R, a *ᵥ ((B0 * Q.map (algebraMap R K)) *ᵥ (fun i =>
      algebraMap R K ϖ ^ (if i.1 < n - k then (0 : ℤ) else -1) * algebraMap R K (z i))) =
        B0 *ᵥ (fun i => algebraMap R K ((P *ᵥ z) i)) := by
    intro z
    have hdw : ((Matrix.diagonal fun i : Fin n => if i.1 < n - k then (1 : R) else ϖ).map
        (algebraMap R K)) *ᵥ (fun i =>
          algebraMap R K ϖ ^ (if i.1 < n - k then (0 : ℤ) else -1) * algebraMap R K (z i)) =
        fun i => algebraMap R K (z i) := by
      rw [Matrix.diagonal_map (map_zero _)]
      funext i
      rw [Matrix.mulVec_diagonal]
      by_cases hi : i.1 < n - k <;> simp [hi, hϖ0]
    rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, haB, Matrix.mul_assoc, ← Matrix.map_mul, hMQ,
      Matrix.map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hdw, hmap]
  refine ⟨B0 * Q.map (algebraMap R K), fun y => ?_, fun y => ?_⟩
  · rw [memL]
    constructor
    · rintro ⟨z, rfl⟩
      refine ⟨Q⁻¹ *ᵥ z, ?_⟩
      rw [← Matrix.mulVec_mulVec, hmap, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv Q hQ,
        Matrix.one_mulVec]
    · rintro ⟨z, rfl⟩
      exact ⟨Q *ᵥ z, by rw [← Matrix.mulVec_mulVec, hmap]⟩
  · constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨z, rfl⟩ := (memL x).1 hx
      refine ⟨P⁻¹ *ᵥ z, ?_⟩
      have h := hE (P⁻¹ *ᵥ z)
      have hz : P *ᵥ (P⁻¹ *ᵥ z) = z := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv P hP, Matrix.one_mulVec]
      rw [hz] at h
      rw [← h, Matrix.mulVec_mulVec, haa', Matrix.one_mulVec]
    · rintro ⟨z, rfl⟩
      refine ⟨_, (memL _).2 ⟨P *ᵥ z, rfl⟩, ?_⟩
      rw [← hE z, Matrix.mulVec_mulVec, haa', Matrix.one_mulVec]

end GlobalTheory.LatticeMinuscule
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LineHyperplaneCut
section
open scoped TensorProduct
open GlobalTheory.EigenSplit

namespace GlobalTheory.EigenLine

variable {K : Type} [Field K] {O : Type} [CommRing O] {L : Type} [AddCommGroup L] [Module K L]

theorem action_one_tmul (ρ : O →+* Module.End K L) (a : O) :
    tensorAction ρ ((1 : K) ⊗ₜ[ℤ] a) = ρ a := by
  ext x
  simp

theorem action_mem (ρ : O →+* Module.End K L) (P : Submodule K L)
    (hP : ∀ a, ∀ x ∈ P, ρ a x ∈ P) (t : K ⊗[ℤ] O) : ∀ x ∈ P, tensorAction ρ t x ∈ P := by
  induction t using TensorProduct.induction_on with
  | zero => intro x _; simp
  | tmul r a => intro x hx; rw [tensorAction_tmul]; exact P.smul_mem _ (hP a x hx)
  | add s t hs ht =>
    intro x hx
    rw [map_add, LinearMap.add_apply]
    exact P.add_mem (hs x hx) (ht x hx)

theorem action_eigen_right (ρ : O →+* Module.End K L) (χ : O →+* K) (ε : K ⊗[ℤ] O)
    (hε : ∀ a, ε * ((1 : K) ⊗ₜ[ℤ] a) = χ a • ε) (a : O) (x : L) :
    tensorAction ρ ε (ρ a x) = χ a • tensorAction ρ ε x := by
  have h := congrArg (fun t => tensorAction ρ t x) (hε a)
  simpa only [map_mul, Module.End.mul_apply, action_one_tmul, map_smul,
    LinearMap.smul_apply] using h

theorem action_eigen_left (ρ : O →+* Module.End K L) (χ : O →+* K) (ε : K ⊗[ℤ] O)
    (hε : ∀ a, ε * ((1 : K) ⊗ₜ[ℤ] a) = χ a • ε) (a : O) (x : L) :
    ρ a (tensorAction ρ ε x) = χ a • tensorAction ρ ε x := by
  have h := congrArg (fun t => tensorAction ρ t x) ((mul_comm _ _).trans (hε a))
  simpa only [map_mul, Module.End.mul_apply, action_one_tmul, map_smul,
    LinearMap.smul_apply] using h

noncomputable def twist (c : O →+* O) : K ⊗[ℤ] O →ₐ[ℤ] K ⊗[ℤ] O :=
  Algebra.TensorProduct.map (AlgHom.id ℤ K) c.toIntAlgHom

theorem twist_twist (c : O →+* O) (hcc : ∀ a, c (c a) = a) (t : K ⊗[ℤ] O) :
    twist c (twist c t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul r a => simp [twist, hcc]
  | add s t hs ht => simp only [map_add, hs, ht]

theorem form_action (ρ : O →+* Module.End K L) (c : O →+* O) (B : LinearMap.BilinForm K L)
    (hadj : ∀ a x y, B x (ρ a y) = B (ρ (c a) x) y) (t : K ⊗[ℤ] O) (x y : L) :
    B x (tensorAction ρ t y) = B (tensorAction ρ (twist c t) x) y := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul r a => simp [twist, hadj]
  | add s t hs ht => simp only [map_add, LinearMap.add_apply, hs, ht]

theorem finrank_ker_add_one {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : V →ₗ[K] K) (hf : f ≠ 0) :
    Module.finrank K (LinearMap.ker f) + 1 = Module.finrank K V := by
  obtain ⟨y, hy⟩ : ∃ y, f y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf (LinearMap.ext h)
  have htop : LinearMap.range f = ⊤ := by
    refine LinearMap.range_eq_top.2 fun k => ⟨(k / f y) • y, ?_⟩
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hy]
  have h := LinearMap.finrank_range_add_finrank_ker f
  rw [htop, finrank_top, Module.finrank_self] at h
  omega

theorem line_hyperplane_cut (K : Type) [Field K] (O : Type) [CommRing O] (L : Type)
    [AddCommGroup L] [Module K L]
    [FiniteDimensional K L] (ρ : O →+* Module.End K L) (c : O →+* O) (B : LinearMap.BilinForm K L)
    (χ : O →+* K) (ε : K ⊗[ℤ] O) (M M' : Submodule K L) (n₀ : L)
    (hcc : ∀ a, c (c a) = a) (hadj : ∀ a x y, B x (ρ a y) = B (ρ (c a) x) y)
    (hnd : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hε : ∀ a, ε * ((1 : K) ⊗ₜ[ℤ] a) = χ a • ε) (hε0 : ε ≠ 0) (hMM : IsCompl M M')
    (hM : ∀ a, ∀ x ∈ M, ρ a x ∈ M) (hM' : ∀ a, ∀ x ∈ M', ρ a x ∈ M')
    (hspan : M = Submodule.span K (Set.range fun a => ρ a n₀))
    (hinj : ∀ t : K ⊗[ℤ] O, tensorAction ρ t n₀ = 0 → t = 0) :
    Module.finrank K ↥(M ⊓ LinearMap.range (tensorAction ρ ε)) = 1 ∧
    Module.finrank K ↥(B.orthogonal M ⊓ LinearMap.range (tensorAction ρ ε)) + 1 =
      Module.finrank K ↥(LinearMap.range (tensorAction ρ ε)) := by
  set T := tensorAction ρ ε with hT
  set E := LinearMap.range T with hE
  have hn₀ : n₀ ∈ M := by
    rw [hspan]
    exact Submodule.subset_span ⟨1, by simp⟩
  have hTn : T n₀ ≠ 0 := fun h => hε0 (hinj ε h)

  have hTM : ∀ m ∈ M, T m ∈ K ∙ T n₀ := by
    intro m hm
    rw [hspan] at hm
    induction hm using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      have : T (ρ a n₀) = χ a • T n₀ := action_eigen_right ρ χ ε hε a n₀
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  have hline : M ⊓ E = K ∙ T n₀ := by
    apply le_antisymm
    · rintro x ⟨hxM, z, rfl⟩
      have hz : z ∈ M ⊔ M' := by rw [hMM.sup_eq_top]; trivial
      obtain ⟨m, hm, m', hm', rfl⟩ := Submodule.mem_sup.1 hz
      have h1 : T m' ∈ M' := action_mem ρ M' hM' ε m' hm'
      have h2 : T m ∈ M := action_mem ρ M hM ε m hm
      have h3 : T m' ∈ M := by
        have : T m' = T (m + m') - T m := by rw [map_add]; abel
        rw [this]
        exact M.sub_mem hxM h2
      have h4 : T m' = 0 := by
        have : T m' ∈ M ⊓ M' := ⟨h3, h1⟩
        rwa [hMM.inf_eq_bot, Submodule.mem_bot] at this
      rw [map_add, h4, add_zero]
      exact hTM m hm
    · rw [Submodule.span_singleton_le_iff_mem]
      exact ⟨action_mem ρ M hM ε n₀ hn₀, n₀, rfl⟩
  refine ⟨by rw [hline]; exact finrank_span_singleton hTn, ?_⟩

  let f : E →ₗ[K] K := (B n₀).comp E.subtype
  have hf : f ≠ 0 := by
    have h1 : twist c ε ≠ 0 := by
      intro h
      apply hε0
      rw [← twist_twist c hcc ε, h, map_zero]
    have h2 : tensorAction ρ (twist c ε) n₀ ≠ 0 := fun h => h1 (hinj _ h)
    obtain ⟨z, hz⟩ : ∃ z, B (tensorAction ρ (twist c ε) n₀) z ≠ 0 := by
      by_contra h
      push_neg at h
      exact h2 (hnd _ h)
    intro h0
    apply hz
    rw [← form_action ρ c B hadj]
    exact LinearMap.congr_fun h0 ⟨T z, z, rfl⟩
  have hmap : (LinearMap.ker f).map E.subtype = B.orthogonal M ⊓ E := by
    ext x
    constructor
    · rintro ⟨⟨y, hy⟩, hyk, rfl⟩
      refine ⟨?_, hy⟩
      change y ∈ B.orthogonal M
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro n hn
      have hy0 : B n₀ y = 0 := hyk
      rw [hspan] at hn
      induction hn using Submodule.span_induction with
      | mem n hn =>
        obtain ⟨a, rfl⟩ := hn
        obtain ⟨z, rfl⟩ := hy
        have h1 := hadj (c a) n₀ (T z)
        rw [hcc] at h1
        show B (ρ a n₀) (T z) = 0
        rw [← h1, action_eigen_left ρ χ ε hε, map_smul, hy0, smul_zero]
      | zero => simp [LinearMap.BilinForm.IsOrtho]
      | add u v _ _ hu hv =>
        simp only [LinearMap.BilinForm.IsOrtho, map_add, LinearMap.add_apply] at *
        rw [hu, hv, add_zero]
      | smul r u _ hu =>
        simp only [LinearMap.BilinForm.IsOrtho, map_smul, LinearMap.smul_apply] at *
        rw [hu, smul_zero]
    · rintro ⟨hx, hxE⟩
      refine ⟨⟨x, hxE⟩, ?_, rfl⟩
      have hx' : x ∈ B.orthogonal M := hx
      rw [LinearMap.BilinForm.mem_orthogonal_iff] at hx'
      exact hx' n₀ hn₀
  rw [← hmap, Submodule.finrank_map_subtype_eq]
  exact finrank_ker_add_one f hf

end GlobalTheory.EigenLine
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalizationAtPrimeIsDiscreteValuationRingOfHeig
section
namespace GlobalTheory

theorem localizationAtPrime_isDiscreteValuationRing_of_height_eq_one :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      (q : Ideal A) [q.IsPrime], q.height = 1 → IsDiscreteValuationRing (Localization.AtPrime q) := by
  intro A _ _ _ _ q _ hq
  exact isDiscreteValuationRing_of_height_eq_one q hq (Localization.AtPrime q)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalizationMaximalIdealMapStatement
section
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localization_maximal_ideal_map : ∀ (B S : Type) [CommRing B] [IsLocalRing B] [CommRing S] [Algebra B S] (J q : Ideal S) [q.IsMaximal], J ≤ (IsLocalRing.maximalIdeal B).map (algebraMap B S) → (IsLocalRing.maximalIdeal B).map (algebraMap B S) ≤ q → Algebra.FormallyUnramified B (S ⧸ J) → Module.Finite B (S ⧸ J) → (IsLocalRing.maximalIdeal B).map ((algebraMap S (Localization.AtPrime q)).comp (algebraMap B S)) = IsLocalRing.maximalIdeal (Localization.AtPrime q) := by
  first | exact @GlobalTheory.map_maximalIdeal_localization_eq_of_formallyUnramified_quotient | exact GlobalTheory.map_maximalIdeal_localization_eq_of_formallyUnramified_quotient | (intros; apply GlobalTheory.map_maximalIdeal_localization_eq_of_formallyUnramified_quotient <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalizationResidueFiniteUnramStatement
section
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localization_residue_finite_unram : ∀ (B S : Type) [CommRing B] [CommRing S] [Algebra B S] (J q : Ideal S) [q.IsMaximal], J ≤ q → Algebra.FormallyUnramified B (S ⧸ J) → Module.Finite B (S ⧸ J) → ((IsLocalRing.residue (Localization.AtPrime q)).comp ((algebraMap S (Localization.AtPrime q)).comp (algebraMap B S))).Finite ∧ ((IsLocalRing.residue (Localization.AtPrime q)).comp ((algebraMap S (Localization.AtPrime q)).comp (algebraMap B S))).FormallyUnramified := by
  first | exact @GlobalTheory.residue_atMaximal_finite_formallyUnramified | exact GlobalTheory.residue_atMaximal_finite_formallyUnramified | (intros; apply GlobalTheory.residue_atMaximal_finite_formallyUnramified <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocallyBoundedOffCoordinateHyperplanesStatement
section
open Metric Filter Topology Set
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locally_bounded_off_coordinate_hyperplanes : (∀ (H : ℂ → ℂ) (r C : ℝ) (N : ℕ), 0 < r → DifferentiableOn ℂ H (Metric.ball (0 : ℂ) r \ {0}) → (∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 → ‖Complex.exp (2 * Real.pi * Complex.I * H t)‖ * ‖t‖ ^ N ≤ C) → ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (Metric.ball (0 : ℂ) r) ∧ ∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 → G t = H t) → ∀ (n a : ℕ) (ρ : ℝ) (Φ : (Fin n → ℂ) → ℂ) (m : Fin n → ℕ), 0 < ρ → DifferentiableOn ℂ Φ {z | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → ‖Complex.exp (2 * Real.pi * Complex.I * Φ z)‖ * ∏ k, ‖z k‖ ^ m k ≤ 1) → ∀ z₀ ∈ Metric.ball (0 : Fin n → ℂ) ρ, ∃ V ∈ nhds z₀, ∃ M : ℝ, ∀ z ∈ V, z ∈ Metric.ball (0 : Fin n → ℂ) ρ → (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → ‖Φ z‖ ≤ M := by
  first | exact @GlobalTheory.HyperplaneLocBound.locally_bounded | exact GlobalTheory.HyperplaneLocBound.locally_bounded | (intros; apply GlobalTheory.HyperplaneLocBound.locally_bounded <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSpanMapOfEvalMemOfNeZeroStatement
section
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_map_of_eval_mem_of_ne_zero : ∀ (k : Type) [Field k] [Infinite k] (σ τ : Type) (M : Submodule k (MvPolynomial σ k)) (D : MvPolynomial τ k), D ≠ 0 → ∀ P : MvPolynomial σ (MvPolynomial τ k), (∀ y : τ → k, MvPolynomial.eval y D ≠ 0 → MvPolynomial.map (MvPolynomial.eval y) P ∈ M) → P ∈ Submodule.span (MvPolynomial τ k) (MvPolynomial.map (algebraMap k (MvPolynomial τ k)) '' (M : Set (MvPolynomial σ k))) := by
  first | exact @GlobalTheory.mem_span_map_of_eval_mem | exact GlobalTheory.mem_span_map_of_eval_mem | (intros; apply GlobalTheory.mem_span_map_of_eval_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoCharOfMulPolyDivPowStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_zpow_of_multiplicative_of_pow_mul_eq_eval : ∀ (χ : ℂ → ℂ), (∀ s t : ℂ, s ≠ 0 → t ≠ 0 → χ (s * t) = χ s * χ t) → χ 1 = 1 → ∀ (N : ℕ) (p : Polynomial ℂ), (∀ t : ℂ, t ≠ 0 → t ^ N * χ t = p.eval t) → ∃ k : ℤ, ∀ t : ℂ, t ≠ 0 → χ t = t ^ k := by
  first | exact @GlobalTheory.mono_char_of_mul_poly_div_pow | exact GlobalTheory.mono_char_of_mul_poly_div_pow | (intros; apply GlobalTheory.mono_char_of_mul_poly_div_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MvPolynomialClearDenominatorsEvalStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mvPolynomial_clear_denominators_eval : ∀ {K : Type} [Field K] {ι τ : Type} (F : MvPolynomial ι K) (P D : ι → MvPolynomial τ K), ∃ G M : MvPolynomial τ K, ∀ y : τ → K, (∀ i, MvPolynomial.eval y (D i) ≠ 0) → MvPolynomial.eval y M ≠ 0 ∧ MvPolynomial.eval y G = MvPolynomial.eval y M * MvPolynomial.eval (fun i => MvPolynomial.eval y (P i) / MvPolynomial.eval y (D i)) F := by
  first | exact @GlobalTheory.clearDenominators | exact GlobalTheory.clearDenominators | (intros; apply GlobalTheory.clearDenominators <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NatCastMulCoeffCharpolyRev
section
namespace GlobalTheory

theorem natCast_mul_coeff_charpolyRev {R : Type} [CommRing R] {m : ℕ}
    (M : Matrix (Fin m) (Fin m) R) (k : ℕ) :
    (k : R) * M.charpolyRev.coeff k =
      -∑ i ∈ Finset.range k, (M ^ (i + 1)).trace * M.charpolyRev.coeff (k - 1 - i) := by
  rcases k with _ | j
  · simp
  · have h := congrArg (PowerSeries.coeff j) (GroundTheory.Global.coe_derivative_charpolyRev M)
    rw [Polynomial.coeff_coe, Polynomial.coeff_derivative, neg_mul, map_neg,
      PowerSeries.coeff_mul, ← Finset.Nat.sum_antidiagonal_swap,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
    simp only [Prod.swap_prod_mk, PowerSeries.coeff_mk, Polynomial.coeff_coe] at h
    have e : ∀ i ∈ Finset.range (j + 1), j + 1 - 1 - i = j - i := fun i _ => by omega
    rw [Finset.sum_congr rfl fun i hi => by rw [e i hi], mul_comm, Nat.cast_succ, h]
    exact congrArg Neg.neg (Finset.sum_congr rfl fun i _ => mul_comm _ _)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDetOfRealLeFactorialMulPowStatement
section
open Matrix
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_det_ofReal_le_factorial_mul_pow : ∀ (g : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (M : ℝ), 0 ≤ M → Y.PosSemidef → (M • (1 : Matrix (Fin g) (Fin g) ℝ) - Y).PosSemidef → ‖(Y.map Complex.ofReal).det‖ ≤ (g.factorial : ℝ) * M ^ g := by
  first | exact @GlobalTheory.det_map_ofReal_norm_le | exact GlobalTheory.det_map_ofReal_norm_le | (intros; apply GlobalTheory.det_map_ofReal_norm_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormSmulLeOneOfPrimitiveBoundedPowersStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_smul_le_one_of_primitive_bounded_powers : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] (p : ℕ) [Fact p.Prime], ‖(p : C)‖ = (p : ℝ)⁻¹ → ∀ (B₁ B₂ : Type) [CommRing B₁] [Algebra C B₁] [CommRing B₂] [Algebra C B₂] (N₁ : B₁ → ℝ) (N₂ : B₂ → ℝ) (Δ i j : B₁ →ₐ[C] B₂), (∀ (c : C) x, N₁ (c • x) = ‖c‖ * N₁ x) → (∀ (c : C) x, N₂ (c • x) = ‖c‖ * N₂ x) → (∀ x, 0 ≤ N₁ x) → (∀ x, 0 ≤ N₂ x) → (∀ x y, N₂ (x + y) ≤ max (N₂ x) (N₂ y)) → (∀ x y, N₂ (x * y) ≤ N₂ x * N₂ y) → (∀ x, N₂ (Δ x) ≤ N₁ x) → (∀ x y, N₂ (i x * j y) = N₁ x * N₁ y) → ∀ y : B₁, (∃ K : ℝ, ∀ k : ℕ, N₁ (y ^ k) ≤ K) → N₂ (Δ y - i y - j y) ≤ 1 → ∀ a : C, ‖a‖ ≤ (p : ℝ) ^ (-(1 / ((p : ℝ) - 1))) → N₁ (a • y) ≤ 1 := by
  first | exact @GlobalTheory.NearlyPrimitive.norm_smul_le_one | exact GlobalTheory.NearlyPrimitive.norm_smul_le_one | (intros; apply GlobalTheory.NearlyPrimitive.norm_smul_le_one <;> assumption)
end

