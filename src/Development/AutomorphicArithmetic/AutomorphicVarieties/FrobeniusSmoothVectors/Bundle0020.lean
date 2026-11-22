import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0005
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0015
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0010
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0018
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0001
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0045
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ContMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0013

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpGlift
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

section Av

variable {O C' C : Type} [CommRing O] [CommRing C'] [Algebra O C'] [CommRing C] [Algebra O C]

private def av (h : O) (σ' : C' →ₐ[O] C') (j : ZMod 2) (x : C') : C' := h • (x + sg C' j * σ' x)

private theorem sg_map (p : C' →ₐ[O] C) (j : ZMod 2) : p (sg C' j) = sg C j := by
  simp [sg]

private theorem av_zero (h : O) (σ' : C' →ₐ[O] C') (j : ZMod 2) : av h σ' j 0 = 0 := by
  simp [av]

variable [IsLocalRing O] [IsCO O C']

variable [IsCO O C]

end Av

private theorem sg_sub_eq_mul {R : Type} [CommRing R] (j k : ZMod 2) : sg R (j - k) = sg R j * sg R k := by
  obtain rfl | rfl : j = 0 ∨ j = 1 := by revert j; decide
  all_goals obtain rfl | rfl : k = 0 ∨ k = 1 := by revert k; decide
  all_goals simp [sg, show (0:ZMod 2) - 1 = 1 from rfl, show (1:ZMod 2) - 1 = 0 from rfl, ZMod.val_one]

private theorem sg_mul_self_eq_one {R : Type} [CommRing R] (j : ZMod 2) : sg R j * sg R j = 1 := by
  unfold sg
  rw [← pow_add, ← two_mul, pow_mul]
  simp

private theorem grM_iff_map_eq_diagonal_mul_mul_diagonal {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (σ : R →ₐ[O] R)
    (α β : Fin 3 → ZMod 2) (M : Matrix (Fin 3) (Fin 3) R) :
    GrM σ α β M ↔ M.map σ = Matrix.diagonal (fun a => sg R (α a)) * M * Matrix.diagonal (fun b => sg R (β b)) := by
  constructor
  · intro hM
    ext a b
    have e : σ (M a b) = sg R (α a - β b) * M a b := hM a b
    simp only [Matrix.map_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, e, sg_sub_eq_mul]
    ring
  · intro hM a b
    have e := congrFun (congrFun hM a) b
    simp only [Matrix.map_apply, Matrix.mul_diagonal, Matrix.diagonal_mul] at e
    show σ (M a b) = sg R (α a - β b) * M a b
    rw [e, sg_sub_eq_mul]
    ring

private theorem diagonal_sg_mul_diagonal_sg_mul_cancel {R : Type} [CommRing R] (α : Fin 3 → ZMod 2) (X : Matrix (Fin 3) (Fin 3) R) :
    Matrix.diagonal (fun a => sg R (α a)) * (Matrix.diagonal (fun a => sg R (α a)) * X) = X := by
  rw [← Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
  simp only [sg_mul_self_eq_one]
  rw [Matrix.diagonal_one, Matrix.one_mul]

private theorem grM_mul_of_grM_of_grM {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (σ : R →ₐ[O] R)
    (α β γ : Fin 3 → ZMod 2) (M N : Matrix (Fin 3) (Fin 3) R) (hM : GrM σ α β M) (hN : GrM σ β γ N) :
    GrM σ α γ (M * N) := by
  rw [grM_iff_map_eq_diagonal_mul_mul_diagonal] at hM hN ⊢
  have e : (M * N).map σ = M.map σ * N.map σ := Matrix.map_mul (f := (σ : R →+* R))
  rw [e, hM, hN]
  simp only [Matrix.mul_assoc, diagonal_sg_mul_diagonal_sg_mul_cancel]

private theorem grM_gl_inv_of_grM {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (σ : R →ₐ[O] R)
    (α β : Fin 3 → ZMod 2) (g : GL (Fin 3) R) (hg : GrM σ α β (g : Matrix (Fin 3) (Fin 3) R)) :
    GrM σ β α ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := by
  rw [grM_iff_map_eq_diagonal_mul_mul_diagonal] at hg ⊢
  set G : Matrix (Fin 3) (Fin 3) R := (g : Matrix (Fin 3) (Fin 3) R) with hG
  set Gi : Matrix (Fin 3) (Fin 3) R := ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) with hGi
  have hGiG : Gi * G = 1 := by rw [hG, hGi]; simp
  have hGGi : G * Gi = 1 := by rw [hG, hGi]; simp
  have e : (Gi * G).map σ = Gi.map σ * G.map σ := Matrix.map_mul (f := (σ : R →+* R))
  have e1 : Gi.map σ * G.map σ = 1 := by
    rw [← e, hGiG]
    simp
  have key : Matrix.diagonal (fun a => sg R (α a)) * G * Matrix.diagonal (fun b => sg R (β b)) *
      (Matrix.diagonal (fun b => sg R (β b)) * Gi * Matrix.diagonal (fun a => sg R (α a))) = 1 := by
    simp only [Matrix.mul_assoc, diagonal_sg_mul_diagonal_sg_mul_cancel]
    rw [← Matrix.mul_assoc G, hGGi, Matrix.one_mul, Matrix.diagonal_mul_diagonal]
    simp only [sg_mul_self_eq_one]
    exact Matrix.diagonal_one
  calc Gi.map σ
      = Gi.map σ * (G.map σ *
        (Matrix.diagonal (fun b => sg R (β b)) * Gi * Matrix.diagonal (fun a => sg R (α a)))) := by
        rw [hg, key, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, e1, Matrix.one_mul]

private theorem av_mem_evp_of_involutive {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (h : O) (σ' : R →ₐ[O] R)
    (hinv : ∀ y, σ' (σ' y) = y) (j : ZMod 2) (x : R) : av h σ' j x ∈ evp σ' j := by
  show σ' (av h σ' j x) = sg R j * av h σ' j x
  simp only [av, map_smul, map_add, map_mul, hinv, sg_map σ' j]
  rw [mul_smul_comm]
  congr 1
  linear_combination (-(σ' x)) * sg_mul_self_eq_one (R := R) j

private theorem map_av_eq_map_of_map_mem_evp {O C' C : Type} [CommRing O] [CommRing C'] [Algebra O C'] [CommRing C] [Algebra O C]
    (p : C' →ₐ[O] C) (σ' : C' →ₐ[O] C') (σ : C →ₐ[O] C) (hcomm : ∀ y, p (σ' y) = σ (p y)) (h : O) (hh : h * 2 = 1)
    (j : ZMod 2) (x : C') (hx : p x ∈ evp σ j) : p (av h σ' j x) = p x := by
  have hx' : σ (p x) = sg C j * p x := hx
  simp only [av, map_smul, map_add, map_mul, hcomm, hx', sg_map p j]
  rw [Algebra.smul_def]
  have h2 : algebraMap O C h * 2 = 1 := by
    rw [← map_ofNat (algebraMap O C) 2, ← map_mul, hh, map_one]
  linear_combination (p x) * h2 + (algebraMap O C h * p x) * sg_mul_self_eq_one (R := C) j

private theorem isUnit_of_isUnit_algHom_map_of_isCO {O C' C : Type} [CommRing O] [IsLocalRing O] [CommRing C'] [Algebra O C'] [IsCO O C']
    [CommRing C] [Algebra O C] [IsCO O C] (p : C' →ₐ[O] C) (x : C') (hx : IsUnit (p x)) : IsUnit x := by
  by_contra hx'
  have hxm : x ∈ maximalIdeal C' := (IsLocalRing.mem_maximalIdeal x).mpr hx'
  obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) (R := C) (p x)
  have hau : IsUnit (algebraMap O C a) := by
    by_contra hna
    have h1 : algebraMap O C a ∈ maximalIdeal C := (IsLocalRing.mem_maximalIdeal _).mpr hna
    have h2 : p x ∈ maximalIdeal C := by simpa using Ideal.add_mem _ ha h1
    exact ((IsLocalRing.mem_maximalIdeal _).mp h2) hx
  haveI := IsCO.isLocalHom (O := O) (R := C)
  obtain ⟨u, rfl⟩ := isUnit_of_map_unit (algebraMap O C) a hau
  have h1 : IsUnit (1 - algebraMap O C' ↑u⁻¹ * x) :=
    IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ ((IsLocalRing.mem_maximalIdeal _).mp (Ideal.mul_mem_left _ _ hxm))
  have h2 := h1.map p
  have h3 : p (1 - algebraMap O C' ↑u⁻¹ * x) = -(algebraMap O C ↑u⁻¹ * (p x - algebraMap O C ↑u)) := by
    rw [map_sub, map_one, map_mul, AlgHom.commutes]
    have : algebraMap O C ↑u⁻¹ * algebraMap O C ↑u = 1 := by rw [← map_mul, Units.inv_mul, map_one]
    linear_combination (-1 : C) * this
  rw [h3] at h2
  have h4 : -(algebraMap O C ↑u⁻¹ * (p x - algebraMap O C ↑u)) ∈ maximalIdeal C :=
    (Ideal.neg_mem_iff _).mpr (Ideal.mul_mem_left _ _ ha)
  exact ((IsLocalRing.mem_maximalIdeal _).mp h4) h2

private theorem av_sub_av_mem_maximalIdeal_pow {O C' : Type} [CommRing O] [IsLocalRing O] [CommRing C'] [Algebra O C'] [IsCO O C']
    (h : O) (σ' : C' →ₐ[O] C') (hinv : ∀ y, σ' (σ' y) = y) (j : ZMod 2) (N : ℕ) (x y : C')
    (hxy : x - y ∈ maximalIdeal C' ^ N) : av h σ' j x - av h σ' j y ∈ maximalIdeal C' ^ N := by
  have hm : Ideal.map σ' (maximalIdeal C') ≤ maximalIdeal C' := by
    rw [Ideal.map_le_iff_le_comap]
    intro z hz
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hz
    intro hu
    apply hz
    have := hu.map σ'
    rwa [hinv] at this
  have hmN : Ideal.map σ' (maximalIdeal C' ^ N) ≤ maximalIdeal C' ^ N := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono hm N
  have hσ : σ' (x - y) ∈ maximalIdeal C' ^ N := hmN (Ideal.mem_map_of_mem _ hxy)
  have e : av h σ' j x - av h σ' j y = algebraMap O C' h * ((x - y) + sg C' j * σ' (x - y)) := by
    simp only [av, Algebra.smul_def, map_sub]
    ring
  rw [e]
  exact Ideal.mul_mem_left _ _ (Ideal.add_mem _ hxy (Ideal.mul_mem_left _ _ hσ))

private theorem adicCont_av_comp {Γ O C' : Type} [TopologicalSpace Γ] [CommRing O] [IsLocalRing O] [CommRing C']
    [Algebra O C'] [IsCO O C'] (h : O) (σ' : C' →ₐ[O] C') (hinv : ∀ y, σ' (σ' y) = y) (j : ZMod 2) (f : Γ → C')
    (hf : AdicCont (maximalIdeal C') f) : AdicCont (maximalIdeal C') (fun s => av h σ' j (f s)) := by
  intro N
  have hs := Ideal.Quotient.mk_surjective (I := maximalIdeal C' ^ N)
  have e : (fun g => Ideal.Quotient.mk (maximalIdeal C' ^ N) (av h σ' j (f g))) =
      (fun q => Ideal.Quotient.mk (maximalIdeal C' ^ N) (av h σ' j (Function.surjInv hs q))) ∘
        (fun g => Ideal.Quotient.mk (maximalIdeal C' ^ N) (f g)) := by
    funext g
    simp only [Function.comp]
    rw [Ideal.Quotient.eq]
    apply av_sub_av_mem_maximalIdeal_pow h σ' hinv j N
    rw [← Ideal.Quotient.eq]
    exact (Function.surjInv_eq hs _).symm
  rw [e]
  exact (hf N).comp _

private theorem exists_gl_eq_av_entries_and_map_eq {O C' C : Type} [CommRing O] [IsLocalRing O] [CommRing C'] [Algebra O C'] [IsCO O C']
    [CommRing C] [Algebra O C] [IsCO O C] (p : C' →ₐ[O] C) (σ' : C' →ₐ[O] C') (σ : C →ₐ[O] C)
    (hcomm : ∀ y, p (σ' y) = σ (p y)) (h : O) (hh : h * 2 = 1) (α β : Fin 3 → ZMod 2) (X : GL (Fin 3) C')
    (hX : GrM σ α β ((X : Matrix (Fin 3) (Fin 3) C').map p)) :
    ∃ Y : GL (Fin 3) C', (Y : Matrix (Fin 3) (Fin 3) C') =
        Matrix.of (fun a b => av h σ' (α a - β b) ((X : Matrix (Fin 3) (Fin 3) C') a b)) ∧
      Matrix.GeneralLinearGroup.map (p : C' →+* C) Y = Matrix.GeneralLinearGroup.map (p : C' →+* C) X := by
  set M : Matrix (Fin 3) (Fin 3) C' := Matrix.of (fun a b => av h σ' (α a - β b) ((X : Matrix (Fin 3) (Fin 3) C') a b)) with hM
  have hmap : M.map p = (X : Matrix (Fin 3) (Fin 3) C').map p := by
    ext a b
    exact map_av_eq_map_of_map_mem_evp p σ' σ hcomm h hh _ _ (hX a b)
  have hXu : IsUnit (X : Matrix (Fin 3) (Fin 3) C').det := (Matrix.isUnit_iff_isUnit_det _).mp X.isUnit
  have hdet : IsUnit M.det := by
    apply isUnit_of_isUnit_algHom_map_of_isCO p
    rw [AlgHom.map_det, AlgHom.mapMatrix_apply, hmap, ← AlgHom.mapMatrix_apply, ← AlgHom.map_det]
    exact hXu.map p
  refine ⟨Matrix.nonsingInvUnit M hdet, rfl, ?_⟩
  exact Units.ext hmap

theorem UpperTheory.V.Fr.ep_glift :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O], IsUnit (2 : O) → ∀ (C' : Type) [CommRing C'] [Algebra O C'] [IsCO O C'] (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (p : C' →ₐ[O] C) (σ' : C' →ₐ[O] C') (σ : C →ₐ[O] C), (∀ y, σ' (σ' y) = y) → (∀ y, p (σ' y) = σ (p y)) → ∀ (B : Box F 3 C) (π : F.V → Fin 3 → ZMod 2), B.Gr σ π → SetLift p B → ∃ D : SetLift p B, D.Gr σ' π := by
  intro l _ k _ F O _ _ _ _ h2 C' _ _ _ C _ _ _ p σ' σ hinv hcomm B π hB D
  obtain ⟨h, hh⟩ : ∃ h : O, h * 2 = 1 := ⟨_, h2.val_inv_mul⟩
  have gr_r : ∀ s, GrM σ pq pq ((D.r s : Matrix (Fin 3) (Fin 3) C').map p) := by
    intro s
    have e : (D.r s : Matrix (Fin 3) (Fin 3) C').map p = ((B.r s).left : Matrix (Fin 3) (Fin 3) C) := by
      rw [← D.r_map s]
      rfl
    rw [e]
    exact hB.r s
  have gr_g : ∀ v, GrM σ (π v) pq ((D.g v : Matrix (Fin 3) (Fin 3) C').map p) := by
    intro v
    have e : (D.g v : Matrix (Fin 3) (Fin 3) C').map p = ((B.g v : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) := by
      rw [← D.g_map v]
      rfl
    rw [e]
    exact hB.g v
  have gr_t : ∀ v s, GrM σ (π v) (π v) ((D.t v s : Matrix (Fin 3) (Fin 3) C').map p) := by
    intro v s
    have e : (D.t v s : Matrix (Fin 3) (Fin 3) C').map p =
        ((B.g v * (B.r (F.loc v s)).left * (B.g v)⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) := by
      rw [← D.t_map v s]
      rfl
    rw [e, Units.val_mul, Units.val_mul]
    exact grM_mul_of_grM_of_grM σ _ _ _ _ _ (grM_mul_of_grM_of_grM σ _ _ _ _ _ (hB.g v) (hB.r _)) (grM_gl_inv_of_grM σ _ _ _ (hB.g v))
  choose r' hr' hr'm using fun s => exists_gl_eq_av_entries_and_map_eq p σ' σ hcomm h hh pq pq (D.r s) (gr_r s)
  choose g' hg' hg'm using fun v => exists_gl_eq_av_entries_and_map_eq p σ' σ hcomm h hh (π v) pq (D.g v) (gr_g v)
  choose t' ht' ht'm using fun v s => exists_gl_eq_av_entries_and_map_eq p σ' σ hcomm h hh (π v) (π v) (D.t v s) (gr_t v s)
  refine ⟨⟨r', ?_, fun s => (hr'm s).trans (D.r_map s), g', fun v => (hg'm v).trans (D.g_map v), t', ?_, ?_,
    fun v s => (ht'm v s).trans (D.t_map v s)⟩, ⟨?_, ?_, ?_⟩⟩
  · intro i j
    simp only [hr', Matrix.of_apply]
    exact adicCont_av_comp h σ' hinv _ (fun s => (D.r s : Matrix (Fin 3) (Fin 3) C') i j) (D.r_cont i j)
  · intro v i j
    simp only [ht', Matrix.of_apply]
    exact adicCont_av_comp h σ' hinv _ (fun s => (D.t v s : Matrix (Fin 3) (Fin 3) C') i j) (D.t_cont v i j)
  · intro v s i j hij
    rw [ht', Matrix.of_apply, D.t_tri v s i j hij]
    exact av_zero h σ' _
  · intro s a b
    rw [hr', Matrix.of_apply]
    exact av_mem_evp_of_involutive h σ' hinv _ _
  · intro v a b
    rw [hg', Matrix.of_apply]
    exact av_mem_evp_of_involutive h σ' hinv _ _
  · intro v s a b
    rw [ht', Matrix.of_apply]
    exact av_mem_evp_of_involutive h σ' hinv _ _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.GgMapOfGL
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem lc_of_ker {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H]
    (f : G →* H) (h : IsOpen (f.ker : Set G)) : IsLocallyConstant f :=
  _root_.UpperTheory.Reformulated.B.LocallyConstantOfKernel.lc_of_ker f h

private theorem res_dual (O : Type) [CommRing O] [IsLocalRing O] [IsCO O (DualNumber (ResidueField O))]
    (x : DualNumber (ResidueField O)) : res O (DualNumber (ResidueField O)) x = x.fst := by
  obtain ⟨a, ha⟩ := residue_surjective x.fst
  have h1 : x - algebraMap O _ a ∈ maximalIdeal (DualNumber (ResidueField O)) := by
    rw [mem_maximalIdeal, mem_nonunits_iff, TrivSqZeroExt.isUnit_iff_isUnit_fst, isUnit_iff_ne_zero, not_not,
      TrivSqZeroExt.fst_sub, ← ha]
    exact sub_self _
  have h2 := (res_eq_zero_iff O _ _).2 h1
  rw [map_sub, AlgHom.commutes, sub_eq_zero] at h2
  rw [h2, ← ha]
  rfl

private theorem of_unique {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {n : ℕ} {C : Type}
    [CommRing C] {B : Box F n C} {ρ ρ' : NRep F n C} (h : B.Of ρ) (h' : B.Of ρ') : ρ = ρ' := by
  have e : ρ.r = ρ'.r := MonoidHom.ext fun s => (h.res s).symm.trans (h'.res s)
  refine NRep.ext e (funext fun v => funext fun i => MonoidHom.ext fun s => Units.ext ?_)
  rw [← h.psi, ← h'.psi, e]

private theorem conj_mat {m : ℕ} {C : Type} [CommRing C] (h : GL (Fin m) C) (x : GG m C) (hx : x.right = 1) :
    (GG.ofGL h * x * (GG.ofGL h)⁻¹).left = h * x.left * h⁻¹ := by
  rw [← map_inv]
  simp [hx]

private theorem gg_map_ofGL {m : ℕ} {C C' : Type} [CommRing C] [CommRing C'] (f : C →+* C') (h : GL (Fin m) C) :
    GG.map f (GG.ofGL h) = GG.ofGL (GeneralLinearGroup.map f h) := rfl

private theorem dual_mul {K : Type} [Field K] (a : DualNumber K) (c : K) :
    (TrivSqZeroExt.inr (a.fst * c) : DualNumber K) = a * TrivSqZeroExt.inr c := by
  ext <;> simp [mul_comm]

private theorem dual_fst {K : Type} [Field K] {m : ℕ} (X : Matrix (Fin m) (Fin m) K) (i j : Fin m) :
    ((1 + X.map (TrivSqZeroExt.inr : K → DualNumber K)) i j).fst = (1 : Matrix (Fin m) (Fin m) K) i j := by
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

private theorem dual_snd {K : Type} [Field K] {m : ℕ} (X A : Matrix (Fin m) (Fin m) K) :
    ((1 + X.map (TrivSqZeroExt.inr : K → DualNumber K)) * A.map (TrivSqZeroExt.inl : K → DualNumber K)).map
      TrivSqZeroExt.snd = X * A := by
  ext i j
  rw [Matrix.add_mul, Matrix.one_mul]
  simp [Matrix.mul_apply, TrivSqZeroExt.snd_sum]

theorem UpperTheory.V.Fr.pr_tor :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (ρ : NRep F n R) (B : Box F n R), ρ.Univ O → B.Of ρ → B.Cont (maximalIdeal R) → (ρ.bar O).Good → thetaLie (lieT (ResidueField O) n) = lieT (ResidueField O) n → ∃ D ∈ Tan O R, ∀ s, B.tanCo O D s = (B.bar O).ad s (lieT _ n) - lieT _ n := by
  intro l _ k _ _ F C₀ n hF O _ _ R _ _ _ ρ B hU hB hC _ hT
  haveI := (co_res O).2
  let K := ResidueField O
  let C := DualNumber K
  let μ : K →+ C := (TrivSqZeroExt.inrHom K K).toAddMonoidHom
  let ι : K →+* C := (TrivSqZeroExt.inlHom K K)
  have hμ : IsSq O μ := by
    refine ⟨fun a c => ?_, fun c => ?_⟩
    · rw [res_dual]
      exact dual_mul a c
    · rw [← res_eq_zero_iff O, res_dual]
      rfl
  have hres : (res O C : C →+* K).comp ι = RingHom.id K := RingHom.ext fun a => res_dual O _
  obtain ⟨e, e1, e2, e3, -, e5⟩ := pr_sqz O C n μ hμ
  set T := lieT K n with hTdef
  let B₀ : Box F n C := (B.bar O).map ι
  have hB₀ : B₀.bar O = B.bar O := by
    show ((B.bar O).map ι).map _ = _
    rw [Box.map_map, hres]
    rfl
  have hr₀ : ∀ s, GG.map (res O C : C →+* K) (B₀.r s) = (B.bar O).r s := fun s => by
    rw [← hB₀]; rfl
  let h := e (-T)
  have hinv : h⁻¹ = e T := by rw [e3, neg_neg]
  have hloc : ∀ s : F.G0, (B₀.r s).right = 1 := fun s => (B₀.nu s).trans s.2
  let B' : Box F n C :=
    { r := conjBy h B₀.r
      nu := fun s => by
        show (GG.ofGL h * B₀.r s * (GG.ofGL h)⁻¹).right = _
        rw [← map_inv]
        simp [B₀.nu]
      g := fun v => B₀.g v * h⁻¹
      tri := fun v s => by
        have : (conjBy h B₀.r (F.loc v s)).left = h * (B₀.r (F.loc v s)).left * h⁻¹ :=
          conj_mat h _ (hloc (F.loc0 v s))
        have h2 := B₀.tri v s
        unfold GG.mat at h2 ⊢
        rw [this, ← Units.val_mul, ← Units.val_mul]
        rw [← Units.val_mul, ← Units.val_mul] at h2
        convert h2 using 2
        group }
  have hform : ∀ s, B'.r s = GG.ofGL (e ((B.bar O).ad s T - T)) * B₀.r s := fun s => by
    show GG.ofGL h * B₀.r s * (GG.ofGL h)⁻¹ = _
    rw [← map_inv, hinv, mul_assoc, e5, hr₀, ← mul_assoc, ← map_mul, ← e2, neg_add_eq_sub]
    rfl
  have hmat : ∀ s, (B'.r s).mat = (1 + ((B.bar O).ad s T - T).map μ) * ((B.bar O).r s).mat.map ι := fun s => by
    rw [hform, ← e1]
    simp [GG.mat]
    rfl
  have hbar : B.bar O |>.Of (ρ.bar O) := hB.map _
  have hc : (B'.r F.c).mat = 1 := by
    have h1 : (B.bar O).ad F.c T = T := by
      have hl : ((B.bar O).r F.c).left = 1 := Units.ext hbar.atc
      have hd : ((B.bar O).r F.c).right ≠ 1 := by
        rw [(B.bar O).nu, hF.del_c]; decide
      show ((B.bar O).r F.c).adFun T = T
      unfold GG.adFun GG.mat
      rw [hl, if_neg hd, hT]
      simp
    rw [hmat, h1, hbar.atc, sub_self, Matrix.map_one _ (map_zero ι) (map_one ι), Matrix.map_zero _ (map_zero μ)]
    simp
  have hdiagE : ∀ a : K, ((e (a • T) : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) =
      Matrix.diagonal fun i => 1 + μ (a * (w n i : K)) := fun a => by
    rw [e1]
    ext1 i j
    by_cases hij : i = j
    · subst hij; simp [hTdef, lieT]
    · simp [hTdef, lieT, hij]
  have hd : ∀ i j, i ≠ j → ((B'.r F.g0).mat - (B'.r (F.star F.g0)).mat) i j = 0 := fun i j hij => by
    have h1 : ∀ s : F.G0, (B'.r s).mat = (h : Matrix (Fin n) (Fin n) C) * ((ρ.bar O).r s).map ι *
        ((h⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) := fun s => by
      rw [← hbar.res]
      exact congrArg Units.val (conj_mat h _ (hloc s))
    have h2 := (ρ.bar O).diag i j hij
    rw [h1, h1, ← Matrix.sub_mul, ← Matrix.mul_sub, hinv, ← one_smul K T, hdiagE, Matrix.mul_diagonal]
    have h3 : h = e ((-1 : K) • T) := by rw [neg_one_smul]
    rw [h3, hdiagE, Matrix.diagonal_mul, Matrix.sub_apply, Matrix.map_apply, Matrix.map_apply, ← map_sub,
      ← Matrix.sub_apply, h2]
    simp
  have hcont : B'.Cont (maximalIdeal C) := fun i j N => by
    have h1 := lc_of_ker _ (pr_open hF O R B hC).1
    exact h1.comp fun x => Ideal.Quotient.mk _ ((GG.ofGL h * GG.map ι x * (GG.ofGL h)⁻¹).mat i j)
  obtain ⟨ρ', hρ', hc'⟩ := pr_ofbox hF C _ B' hc hd hcont
  have hh : GeneralLinearGroup.map (res O C : C →+* K) h = 1 := by
    apply Units.ext
    ext i j
    show res O C ((e (-T) : Matrix (Fin n) (Fin n) C) i j) = _
    rw [e1, res_dual]
    exact dual_fst _ i j
  have hB' : B'.bar O = B.bar O := by
    rw [← hB₀]
    refine Box.ext (MonoidHom.ext fun s => ?_) (funext fun v => ?_)
    · show GG.map _ (GG.ofGL h * B₀.r s * (GG.ofGL h)⁻¹) = GG.map _ (B₀.r s)
      rw [map_mul, map_mul, map_inv, gg_map_ofGL, hh]
      simp
    · show GeneralLinearGroup.map _ (B₀.g v * h⁻¹) = GeneralLinearGroup.map _ (B₀.g v)
      rw [map_mul, map_inv, hh]
      simp
  have hρb : ρ'.bar O = ρ.bar O := of_unique (hB' ▸ hρ'.map _) hbar
  obtain ⟨D, hD, hD'⟩ := pr_dof hF O R ρ B hU hB ρ' B'.r hc' hρb B'.nu hc hρ'.res
  refine ⟨D, hD, fun s => ?_⟩
  have h1 : (B'.r s).mat.map TrivSqZeroExt.snd = ((B.bar O).ad s T - T) * ((B.bar O).r s).mat := by
    rw [hmat]
    exact dual_snd _ _
  have h2 := (hD' s).symm.trans h1
  exact (Units.mul_left_inj ((B.bar O).r s).left).1 h2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.IsInternalCongr
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem isInternal_congr {ι M σ σ' : Type} [DecidableEq ι] [AddCommMonoid M] [SetLike σ M]
    [AddSubmonoidClass σ M] [SetLike σ' M] [AddSubmonoidClass σ' M] (A : ι → σ) (A' : ι → σ')
    (h : ∀ i x, x ∈ A' i ↔ x ∈ A i) (hA : DirectSum.IsInternal A) : DirectSum.IsInternal A' := by
  let e : ∀ i, A' i ≃+ A i := fun i =>
    { toFun := fun x => ⟨x.1, (h i _).1 x.2⟩
      invFun := fun x => ⟨x.1, (h i _).2 x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  let E : DirectSum ι (fun i => A' i) ≃+ DirectSum ι (fun i => A i) := DFinsupp.mapRange.addEquiv e
  have hE : DirectSum.coeAddMonoidHom A' = (DirectSum.coeAddMonoidHom A).comp E.toAddMonoidHom := by
    refine DirectSum.addHom_ext fun i x => ?_
    have h1 : E (DirectSum.of (fun i => A' i) i x) = DirectSum.of (fun i => A i) i (e i x) :=
      DFinsupp.mapRange_single (hf := fun i => (e i).map_zero)
    show _ = DirectSum.coeAddMonoidHom A (E (DirectSum.of (fun i => A' i) i x))
    rw [h1, DirectSum.coeAddMonoidHom_of, DirectSum.coeAddMonoidHom_of]
    rfl
  unfold DirectSum.IsInternal
  rw [hE]
  exact hA.comp E.bijective

private theorem gr_transfer (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O ℤ R)
    (hz : ∀ s, W.z s ∈ maximalIdeal R) (B A : Subalgebra O R) [Algebra B A]
    (halg : ∀ b : B, ((algebraMap B A b : A) : R) = b) (gr : ℤ → Submodule B A)
    (hB : ∀ y, y ∈ B ↔ y ∈ W.part 0) (hA : A = W.A) (hgr : ∀ j (a : A), a ∈ gr j ↔ (a : R) ∈ W.part j) :
    DirectSum.IsInternal gr ∧ SetLike.GradedMonoid gr ∧ gr 0 = 1 ∧ (∀ j, (gr j).FG) ∧ Algebra.FiniteType B A ∧
      IsNoetherianRing A := by
  subst hA
  obtain ⟨h1, h2, h3⟩ := gr_noeth O ℤ R W hz
  have h0 : ∀ a : W.A, a ∈ W.gr 0 → ∃ b : B, algebraMap B W.A b = a := fun a ha =>
    ⟨⟨a, (hB _).2 ha⟩, Subtype.ext (halg _)⟩
  refine ⟨isInternal_congr W.gr gr hgr (gr_internal O ℤ R W), ?_, ?_, fun j => ?_, ?_, h1⟩
  · exact
      { one_mem := (hgr _ _).2 (SetLike.GradedOne.one_mem : (1 : R) ∈ W.part 0)
        mul_mem := fun _ _ _ _ ha hb => (hgr _ _).2 (SetLike.mul_mem_graded ((hgr _ _).1 ha) ((hgr _ _).1 hb)) }
  · ext a
    rw [Submodule.mem_one, hgr]
    refine ⟨h0 a, ?_⟩
    rintro ⟨b, rfl⟩
    rw [halg]
    exact (hB _).1 b.2
  · obtain ⟨s, hs, hs'⟩ := h3 j
    refine ⟨s, le_antisymm (Submodule.span_le.2 fun a ha => (hgr _ _).2 (hs a ha)) fun a ha => ?_⟩
    have ha' : a ∈ W.gr j := (hgr _ _).1 ha
    rw [hs'] at ha'
    refine Submodule.mul_induction_on ha' (fun x hx y hy => ?_) fun x y hx hy => add_mem hx hy
    obtain ⟨b, rfl⟩ := h0 x hx
    rw [← Algebra.smul_def]
    refine Submodule.smul_mem _ _ ?_
    induction hy using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span hy
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | smul c y _ hy =>
      obtain ⟨b, hb⟩ := h0 _ (SetLike.algebraMap_mem_graded W.gr c)
      rw [Algebra.smul_def, ← hb, ← Algebra.smul_def]
      exact Submodule.smul_mem _ _ hy
  · obtain ⟨s, hs⟩ := h2.out
    refine ⟨⟨s, ?_⟩⟩
    rw [eq_top_iff]
    intro a ht
    clear ht
    have ha : a ∈ Algebra.adjoin (W.gr 0) (s : Set W.A) := by rw [hs]; trivial
    induction ha using Algebra.adjoin_induction with
    | mem y hy => exact Algebra.subset_adjoin hy
    | algebraMap r =>
      obtain ⟨b, hb⟩ := h0 r.1 r.2
      have : algebraMap (W.gr 0) W.A r = algebraMap B W.A b := hb.symm
      rw [this]
      exact Subalgebra.algebraMap_mem _ b
    | add a b _ _ ha hb => exact add_mem ha hb
    | mul a b _ _ ha hb => exact mul_mem ha hb

theorem UpperTheory.V.Fr.gr_A :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, DirectSum.IsInternal S.gr ∧ SetLike.GradedMonoid S.gr ∧ S.gr 0 = 1 ∧ (∀ j, (S.gr j).FG) ∧ Algebra.FiniteType S.B S.A ∧ IsNoetherianRing S.A ∧ ∀ g i j, S.u.r g i j ∈ S.gr (w n i - w n j) := by
  intro l _ O _ _ _ _ F C₀ n hF hn S
  obtain ⟨W, hz, hr, hB, hA, hgr⟩ := UpperTheory.V.Fr.wpres hF hn S
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := gr_transfer O S.R W hz S.B S.A (fun _ => rfl) S.gr hB hA hgr
  exact ⟨h1, h2, h3, h4, h5, h6, fun g i j => (hgr _ _).2 (hr g i j)⟩
end

