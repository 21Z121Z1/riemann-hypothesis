import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeSizeContinuity.Bundle0001
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsDual
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.ArchIneq
section
noncomputable section

open Matrix

namespace PI.UnitaryGroupMassFormula.LCG

theorem archimedean_inequality : ArchIneq := by
  intro n k A C D κ hκ hA hker
  have hGdet := (PI.UnitaryGroupMassFormula.LSC.determinant_monotone n k D 1 1 zero_le_one (by intro w; simp)).1
  obtain ⟨G, hG⟩ : ∃ G : Matrix (Fin k) (Fin k) ℂ, G = Dᴴ * D := ⟨_, rfl⟩
  rw [← hG] at hGdet ⊢
  have hGh : Gᴴ = G := by
    rw [hG, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have him : G.det.im = 0 := by
    have hstar : star G.det = G.det := by rw [← Matrix.det_conjTranspose, hGh]
    have h1 := congrArg Complex.im hstar
    simp only [Complex.star_def, Complex.conj_im] at h1
    linarith
  by_cases hg : G.det = 0
  · rw [hg, Complex.zero_re, mul_zero]
    exact mul_nonneg (pow_nonneg hκ k) (sq_nonneg _)
  · have hGu : IsUnit G.det := isUnit_iff_ne_zero.mpr hg
    obtain ⟨X, hX⟩ : ∃ X : Matrix (Fin n) (Fin k) ℂ, X = D * G⁻¹ * Dᴴ * C := ⟨_, rfl⟩
    have hAP : A * (D * G⁻¹ * Dᴴ) = A := by
      apply Matrix.ext_of_mulVec_single
      intro j
      have h1 : Dᴴ *ᵥ ((Pi.single j 1 : Fin n → ℂ) - (D * G⁻¹ * Dᴴ) *ᵥ Pi.single j 1) = 0 := by
        have h3 : Dᴴ * (D * G⁻¹ * Dᴴ) = G * G⁻¹ * Dᴴ := by
          rw [hG]
          simp only [Matrix.mul_assoc]
        rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, h3, Matrix.mul_nonsing_inv G hGu, Matrix.one_mul, sub_self]
      have h2 := hker _ h1
      rw [Matrix.mulVec_sub, sub_eq_zero] at h2
      rw [← Matrix.mulVec_mulVec, ← h2]
    have hAX : A * X = A * C := by
      rw [hX, ← Matrix.mul_assoc, hAP]
    have hdm := (PI.UnitaryGroupMassFormula.LSC.determinant_monotone n k X A κ hκ hA).2
    rw [hAX] at hdm
    have hXh : Xᴴ = Cᴴ * D * G⁻¹ * Dᴴ := by
      rw [hX]
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_nonsing_inv,
        hGh, Matrix.mul_assoc]
    have hXX : Xᴴ * X = Cᴴ * D * G⁻¹ * (Dᴴ * C) := by
      rw [hXh, hX]
      have hGG : G⁻¹ * (Dᴴ * D) = 1 := by
        rw [← hG]
        exact Matrix.nonsing_inv_mul G hGu
      calc Cᴴ * D * G⁻¹ * Dᴴ * (D * G⁻¹ * Dᴴ * C) = Cᴴ * D * (G⁻¹ * (Dᴴ * D)) * G⁻¹ * (Dᴴ * C) := by
            simp only [Matrix.mul_assoc]
        _ = Cᴴ * D * G⁻¹ * (Dᴴ * C) := by rw [hGG, Matrix.mul_one]
    have hdetX : (Xᴴ * X).det = star (Dᴴ * C).det * (Dᴴ * C).det / G.det := by
      have hCD : Cᴴ * D = (Dᴴ * C)ᴴ := by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      rw [hXX, Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', hCD,
        Matrix.det_conjTranspose]
      ring
    have h5 : (Xᴴ * X).det * G.det = star (Dᴴ * C).det * (Dᴴ * C).det := by
      rw [hdetX, div_mul_cancel₀ _ hg]
    have hval : (Xᴴ * X).det.re * G.det.re = ‖(Dᴴ * C).det‖ ^ 2 := by
      have h6 := congrArg Complex.re h5
      rw [Complex.mul_re, him, mul_zero, sub_zero] at h6
      rw [h6, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
      ring
    calc (((A * C)ᴴ * (A * C)).det).re * G.det.re ≤ κ ^ k * (Xᴴ * X).det.re * G.det.re :=
          mul_le_mul_of_nonneg_right hdm hGdet
      _ = κ ^ k * ‖(Dᴴ * C).det‖ ^ 2 := by rw [mul_assoc, hval]

end PI.UnitaryGroupMassFormula.LCG
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.Choose
section
noncomputable section

open NumberField Matrix

namespace PI.UnitaryGroupMassFormula.LCG

namespace ChooseW

section Gen

variable {K : Type*} [Field K] {n : ℕ}

lemma ann_range (δ : Matrix (Fin n) (Fin n) K) (a : Fin n → K)
    (ha : ∀ z, δ *ᵥ z = 0 → a ⬝ᵥ z = 0) : ∃ t, a = t ᵥ* δ := by
  let ℓ : Module.Dual K (Fin n → K) :=
    { toFun := fun z => a ⬝ᵥ z
      map_add' := fun x y => dotProduct_add a x y
      map_smul' := fun c x => by simp [dotProduct_smul] }
  have hmem : ℓ ∈ (LinearMap.ker δ.mulVecLin).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro z hz
    exact ha z (by simpa using hz)
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hmem
  obtain ⟨φ, hφ⟩ := hmem
  refine ⟨fun j => φ (fun r => if j = r then 1 else 0), ?_⟩
  funext i
  have h1 := LinearMap.congr_fun hφ (fun r => if i = r then 1 else 0)
  rw [LinearMap.dualMap_apply] at h1
  have h2 : ℓ (fun r => if i = r then 1 else 0) = a i := by
    simp [ℓ, dotProduct]
  rw [h2, LinearMap.pi_apply_eq_sum_univ φ] at h1
  rw [← h1]
  simp [Matrix.vecMul, dotProduct, Matrix.mulVec, mul_comm]

lemma scaled_li {ι : Type*} {V : Type*} [AddCommGroup V] [Module K V] (d : ι → V)
    (hli : LinearIndependent K d) (m : ι → K) (hm : ∀ c, m c ≠ 0) :
    LinearIndependent K (fun c => m c • d c) := by
  have := hli.units_smul (fun c => Units.mk0 (m c) (hm c))
  convert this using 1
  funext c
  simp [Units.smul_def]

lemma scaled_span {ι : Type*} {V : Type*} [AddCommGroup V] [Module K V] (d : ι → V) (m : ι → K)
    (hm : ∀ c, m c ≠ 0) :
    Submodule.span K (Set.range d) ≤ Submodule.span K (Set.range fun c => m c • d c) := by
  rw [Submodule.span_le]
  rintro _ ⟨c, rfl⟩
  have : d c = (m c)⁻¹ • (m c • d c) := by rw [smul_smul, inv_mul_cancel₀ (hm c), one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)

lemma basis_range (A : Matrix (Fin n) (Fin n) K) (k : ℕ) (hk : A.rank = k) :
    ∃ z : Fin k → Fin n → K, LinearIndependent K (fun c => A *ᵥ z c) ∧
      ∀ w, A *ᵥ w ∈ Submodule.span K (Set.range fun c => A *ᵥ z c) := by
  let R := LinearMap.range A.mulVecLin
  let bas := Module.finBasisOfFinrankEq K R hk
  have hz : ∀ c, ∃ z, A *ᵥ z = (bas c : Fin n → K) := fun c => by
    obtain ⟨z, hz⟩ := LinearMap.mem_range.mp (bas c).2
    exact ⟨z, by simpa using hz⟩
  choose z hz using hz
  have hspan : Submodule.span K (Set.range fun c => (bas c : Fin n → K)) = R := by
    rw [show (fun c => (bas c : Fin n → K)) = R.subtype ∘ bas from rfl, Set.range_comp,
      ← Submodule.map_span, bas.span_eq, Submodule.map_top, Submodule.range_subtype]
  refine ⟨z, ?_, ?_⟩
  · simp only [hz]
    exact bas.linearIndependent.map' R.subtype (Submodule.ker_subtype R)
  · intro w
    simp only [hz]
    rw [hspan]
    exact LinearMap.mem_range.mpr ⟨w, by simp⟩

lemma rank_pos (δ : Matrix (Fin n) (Fin n) K) (hδ : δ ≠ 0) : 1 ≤ δ.rank := by
  by_contra h
  have h0 : δ.rank = 0 := by omega
  have hbot : LinearMap.range δ.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp h0
  have hz : Matrix.toLin' δ = 0 := by
    rw [Matrix.toLin'_apply']
    exact LinearMap.range_eq_bot.mp hbot
  exact hδ (Matrix.toLin'.injective (by rw [hz, map_zero]))

end Gen

section Star

variable {E : Type*} [Field E] [StarRing E] {n : ℕ}

def sv (w : Fin n → E) : Fin n → E := fun i => starRingEnd E (w i)

lemma sv_sv (w : Fin n → E) : sv (sv w) = w := by
  funext i; simp [sv]

lemma star_li {k : ℕ} (v : Fin k → Fin n → E) (h : LinearIndependent E v) :
    LinearIndependent E (fun a => sv (v a)) := by
  rw [Fintype.linearIndependent_iff] at h ⊢
  intro g hg i
  have h0 : ∑ a, starRingEnd E (g a) • v a = 0 := by
    funext j
    have := congrArg (starRingEnd E) (congrFun hg j)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sv, map_sum, map_mul,
      starRingEnd_self_apply, map_zero, Pi.zero_apply] at this ⊢
    rw [← this]
  have := h _ h0 i
  simpa using this

lemma star_span {k : ℕ} (v : Fin k → Fin n → E) (w : Fin n → E)
    (hw : sv w ∈ Submodule.span E (Set.range v)) :
    w ∈ Submodule.span E (Set.range fun a => sv (v a)) := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun E).mp hw
  refine (Submodule.mem_span_range_iff_exists_fun E).mpr ⟨fun a => starRingEnd E (c a), ?_⟩
  rw [← sv_sv w, ← hc]
  funext j
  simp [sv, Finset.sum_apply, map_sum, map_mul]

end Star

lemma scale {E : Type} [Field E] [NumberField E] {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E))
    (hΛ : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) (w : Fin n → E) :
    ∃ m : ℤ, m ≠ 0 ∧ (m : E) • w ∈ Λ := by
  classical
  have hw : w ∈ Submodule.span E (Λ : Set (Fin n → E)) := hΛ ▸ Submodule.mem_top
  obtain ⟨N, f, g, hfg⟩ := Submodule.mem_span_set'.mp hw
  obtain ⟨y, hy, hint⟩ := exists_integral_multiples ℤ ℚ (L := E) (Finset.univ.image f)
  refine ⟨y, hy, ?_⟩
  rw [← hfg, Finset.smul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hi : IsIntegral ℤ ((y : E) * f i) := by
    have := hint (f i) (Finset.mem_image_of_mem f (Finset.mem_univ i))
    simpa [zsmul_eq_mul] using this
  rw [smul_smul]
  have := Λ.smul_mem (⟨(y : E) * f i, hi⟩ : 𝓞 E) (g i).2
  convert this using 1
  exact (algebraMap_smul E _ _).symm

lemma hf_eq (I : Formalism.MainNotions.S.AutInst) (w z : Fin I.n → I.E) : hf I w z = (sv w ᵥ* I.J) ⬝ᵥ z := by
  simp only [hf, Formalism.UG.hform, dotProduct, vecMul, Finset.sum_mul, sv]
  rw [Finset.sum_comm]

end ChooseW

open ChooseW in
theorem choice_of_generators : Choose := by
  intro I y δ hδ
  obtain ⟨Λ, _, hΛs, hΛ0⟩ := PI.UnitaryGroupMassFormula.LSC.lattice_isometry I y
  have hΛ : PI.LatCountG.latSet I y = (Λ : Set (Fin I.n → I.E)) := hΛ0
  have hJ : IsUnit I.J.det := isUnit_iff_ne_zero.mpr I.J_det
  set k := δ.rank with hk
  have hk1 : 1 ≤ k := rank_pos δ hδ

  obtain ⟨z, hzli, hzsp⟩ := basis_range δ k hk.symm
  have hsc : ∀ c, ∃ m : ℤ, m ≠ 0 ∧ ((m : I.E) • z c) ∈ Λ := fun c => scale Λ hΛs (z c)
  choose mu hmu0 hmuΛ using hsc

  set B : Matrix (Fin I.n) (Fin I.n) I.E := (δ * I.J⁻¹)ᵀ with hB
  have hBr : B.rank = k := by
    rw [hB, Matrix.rank_transpose, Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.isUnit_nonsing_inv_det I.J hJ)]
  obtain ⟨t, htli, htsp⟩ := basis_range B k hBr
  have hsc' : ∀ a, ∃ m : ℤ, m ≠ 0 ∧ ((m : I.E) • sv (B *ᵥ t a)) ∈ Λ := fun a => scale Λ hΛs _
  choose mb hmb0 hmbΛ using hsc'
  have hmu0' : ∀ c, ((mu c : ℤ) : I.E) ≠ 0 := fun c => Int.cast_ne_zero.mpr (hmu0 c)
  have hmb0' : ∀ a, ((mb a : ℤ) : I.E) ≠ 0 := fun a => Int.cast_ne_zero.mpr (hmb0 a)

  have hperpB : ∀ s w, δ *ᵥ w = 0 → ((B *ᵥ s) ᵥ* I.J) ⬝ᵥ w = 0 := by
    intro s w hw
    rw [hB, Matrix.mulVec_transpose, Matrix.vecMul_vecMul, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hJ, Matrix.mul_one, ← Matrix.dotProduct_mulVec, hw, dotProduct_zero]
  refine ⟨k, fun c => ((mu c : ℤ) : I.E) • z c, fun a => ((mb a : ℤ) : I.E) • sv (B *ᵥ t a), hk1,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c; rw [hΛ]; exact hmuΛ c
  · simp only [Matrix.mulVec_smul]
    exact scaled_li (fun c => δ *ᵥ z c) hzli (fun c => ((mu c : ℤ) : I.E)) hmu0'
  · intro w
    simp only [Matrix.mulVec_smul]
    exact scaled_span (fun c => δ *ᵥ z c) (fun c => ((mu c : ℤ) : I.E)) hmu0' (hzsp w)
  · intro a; rw [hΛ]; exact hmbΛ a
  · exact scaled_li (fun a => sv (B *ᵥ t a)) (star_li (fun a => B *ᵥ t a) htli)
      (fun a => ((mb a : ℤ) : I.E)) hmb0'
  · intro a w hw
    rw [hf_eq]
    have hs : sv (((mb a : ℤ) : I.E) • sv (B *ᵥ t a)) = ((mb a : ℤ) : I.E) • (B *ᵥ t a) := by
      funext i; simp [sv]
    rw [hs, Matrix.smul_vecMul, smul_dotProduct, hperpB _ _ hw, smul_zero]
  · intro w hw
    have hann : ∀ z', δ *ᵥ z' = 0 → (sv w ᵥ* I.J) ⬝ᵥ z' = 0 := fun z' hz' => by
      rw [← hf_eq]; exact hw z' hz'
    obtain ⟨s, hs⟩ := ann_range δ _ hann
    have hsv : sv w = B *ᵥ s := by
      have : sv w = (sv w ᵥ* I.J) ᵥ* I.J⁻¹ := by
        rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hJ, Matrix.vecMul_one]
      rw [this, hs, Matrix.vecMul_vecMul, hB, Matrix.mulVec_transpose]
    have h1 : sv w ∈ Submodule.span I.E (Set.range fun a => B *ᵥ t a) := hsv ▸ htsp s
    exact scaled_span (fun a => sv (B *ᵥ t a)) (fun a => ((mb a : ℤ) : I.E)) hmb0'
      (star_span (fun a => B *ᵥ t a) w h1)

end PI.UnitaryGroupMassFormula.LCG
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.DualIncl
section
noncomputable section

open NumberField Matrix TensorProduct

namespace PI.UnitaryGroupMassFormula.LCG

namespace DualI

open Formalism.UG Formalism.UG.P

abbrev AA (I : Formalism.MainNotions.S.AutInst) : Type := I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F

abbrev SS (I : Formalism.MainNotions.S.AutInst) : Subring (AA I) := Formalism.MainNotions.S.IntAf I.F I.E

abbrev iA (I : Formalism.MainNotions.S.AutInst) : I.E →+* AA I := Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)

theorem sig_eq (I : Formalism.MainNotions.S.AutInst) :
    ((I.cm.sig : I.E →ₐ[I.F] I.E) : I.E →+* I.E) = starRingEnd I.E := rfl

theorem mem_latSet (I : Formalism.MainNotions.S.AutInst) (y : I.GA) (u : Fin I.n → I.E) :
    u ∈ PI.LatCountG.latSet I y ↔
      (((y.2 : GL (Fin I.n) (AA I))⁻¹ : GL (Fin I.n) (AA I)) : Matrix (Fin I.n) (Fin I.n) (AA I)) *ᵥ
        (fun i => iA I (u i)) ∈ latS (F := I.F) (Formalism.MainNotions.S.Af I.F) (SS I) I.L := by
  unfold PI.LatCountG.latSet
  rw [Set.mem_setOf_eq, PI.UnitaryGroupMassFormula.LSC.LatIs.lamAf_eq I]
  rfl

theorem hform_smul_right {A : Type} [CommRing A] {n : Type} [Fintype n] (τ : A →+* A)
    (J : Matrix n n A) (a : A) (w x : n → A) : hform τ J w (a • x) = a * hform τ J w x := by
  unfold hform
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hform_add_right {A : Type} [CommRing A] {n : Type} [Fintype n] (τ : A →+* A)
    (J : Matrix n n A) (w x x' : n → A) : hform τ J w (x + x') = hform τ J w x + hform τ J w x' := by
  unfold hform
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hform_sub_right {A : Type} [CommRing A] {n : Type} [Fintype n] (τ : A →+* A)
    (J : Matrix n n A) (w x x' : n → A) : hform τ J w (x - x') = hform τ J w x - hform τ J w x' := by
  unfold hform
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem hform_zero_right {A : Type} [CommRing A] {n : Type} [Fintype n] (τ : A →+* A)
    (J : Matrix n n A) (w : n → A) : hform τ J w 0 = 0 := by
  unfold hform
  simp

theorem pair_int (I : Formalism.MainNotions.S.AutInst) (w : Fin I.n → I.E) (hw : w ∈ I.L)
    (x : Fin I.n → AA I) (hx : x ∈ latS (F := I.F) (Formalism.MainNotions.S.Af I.F) (SS I) I.L) :
    hform (sigR I.cm.sig (Formalism.MainNotions.S.Af I.F)) (I.J.map (iA I)) (fun i => iA I (w i)) x ∈ SS I := by
  unfold latS at hx
  induction hx using Submodule.span_induction with
  | mem x h =>
    obtain ⟨l, hl, rfl⟩ := h
    exact csDual_span I.cm.sig I.J I.L l ((I.L_dual l).mp hl) (fun i => iA I (w i))
      (Submodule.subset_span ⟨w, hw, rfl⟩)
  | zero =>
    rw [hform_zero_right]
    exact (SS I).zero_mem
  | add x y _ _ hx hy =>
    rw [hform_add_right]
    exact (SS I).add_mem hx hy
  | smul a x _ hx =>
    rw [Subring.smul_def, hform_smul_right]
    exact (SS I).mul_mem a.2 hx

end DualI

open DualI Formalism.UG Formalism.UG.P in
theorem dual_lattice_inclusion : DualIncl := by
  intro I y u hu
  have hfin : Module.Finite (𝓞 I.E) I.L := Module.Finite.iff_fg.mpr I.L_fg
  have hdet : IsUnit I.J.det := isUnit_iff_ne_zero.mpr I.J_det
  set g : GL (Fin I.n) (AA I) := (y.2 : GL (Fin I.n) (AA I)) with hg
  have hU : cT (sigR I.cm.sig (Formalism.MainNotions.S.Af I.F)) (g : Matrix (Fin I.n) (Fin I.n) (AA I)) * I.J.map (iA I) *
      (g : Matrix (Fin I.n) (Fin I.n) (AA I)) = I.J.map (iA I) := y.2.2

  have hu' : ∀ w ∈ Formalism.UG.CS.globLat g I.L, hform ((I.cm.sig : I.E →ₐ[I.F] I.E) : I.E →+* I.E) I.J w u ∈
      (algebraMap (𝓞 I.E) I.E).range := by
    intro w hw
    apply hu w
    rw [mem_latSet]
    exact hw
  obtain ⟨z, hz⟩ : ∃ z, z = ((g⁻¹ : GL (Fin I.n) (AA I)) : Matrix (Fin I.n) (Fin I.n) (AA I)) *ᵥ
      (fun i => iA I (u i)) := ⟨_, rfl⟩
  have hxz : (fun i => iA I (u i)) = (g : Matrix (Fin I.n) (Fin I.n) (AA I)) *ᵥ z := by
    rw [hz, mulVec_mulVec, Units.mul_inv, one_mulVec]

  have hw : ∀ w ∈ latS (F := I.F) (Formalism.MainNotions.S.Af I.F) (SS I) I.L,
      hform (sigR I.cm.sig (Formalism.MainNotions.S.Af I.F)) (I.J.map (iA I)) w z ∈ SS I := by
    intro w hw
    have hu2 := (span_recovery_of_integral_adelic_approx csGlob_intAdApprox I.F I.E (Fin I.n) I.L hfin I.L_span g
      ((g : Matrix (Fin I.n) (Fin I.n) (AA I)) *ᵥ w)).2
      (by rwa [mulVec_mulVec, Units.inv_mul, one_mulVec])
    have := csDual_span I.cm.sig I.J (Formalism.UG.CS.globLat g I.L) u hu' _ hu2
    rwa [hxz, hform_mulVec, hU] at this
  obtain ⟨c, hc, hlow⟩ := adelstabL_lower (F := I.F) I.L I.L_span
  obtain ⟨m, hm0, hm⟩ := adelstabL_den (fun p : Fin I.n × Fin I.n => (I.J⁻¹) p.1 p.2)
  have hi : ∀ i, levelafC I.E c * ((I.J.map (iA I)) *ᵥ z) i ∈ SS I := by
    intro i
    have h1 := hw _ (hlow (Pi.single i (1 : AA I)) (fun k => by
      rw [Pi.single_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _))
    have h2 : (fun k => levelafC I.E c * (Pi.single i (1 : AA I) : Fin I.n → _) k) =
        levelafC I.E c • (Pi.single i (1 : AA I) : Fin I.n → _) := by
      funext k; simp [Pi.smul_apply]
    rwa [h2, csDual_hform_smul_left, csDual_sig_C, sf_single] at h1
  have hinv : (I.J⁻¹).map (iA I) * I.J.map (iA I) = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul I.J hdet, Matrix.map_one _ (map_zero _) (map_one _)]
  have hz2 : (I.J⁻¹).map (iA I) *ᵥ ((I.J.map (iA I)) *ᵥ z) = z := by
    rw [mulVec_mulVec, hinv, one_mulVec]
  have hv : ∀ k, levelafC I.E c * iA I (m : I.E) * z k ∈ SS I := by
    intro k
    have := csDual_expand (F := I.F) (I.J⁻¹) ((I.J.map (iA I)) *ᵥ z) (levelafC I.E c) (iA I (m : I.E)) k
    rw [hz2] at this
    rw [this]
    refine sum_mem fun i _ => mul_mem ?_ (hi i)
    rw [← map_mul]
    exact adelstabL_incl_int (F := I.F) _ (hm (k, i))

  set D : 𝓞 I.F := c * (m : 𝓞 I.F) with hD
  have hD0 : D ≠ 0 := mul_ne_zero hc (Int.cast_ne_zero.2 hm0)
  have hmC : levelafC I.E ((m : 𝓞 I.F)) = iA I (m : I.E) := by
    rw [← adelstab_incl_C, map_intCast]
  have hDl : levelafC I.E D = levelafC I.E c * iA I (m : I.E) := by
    rw [hD, levelafC_mul, hmC]
  have hDE : algebraMap (𝓞 I.F) I.E D ≠ 0 := adelstab_algebraMap_ne_zero (F := I.F) (E := I.E) D hD0
  have happ : ∀ k, ∃ b : 𝓞 I.E, ∃ t ∈ SS I, levelafC I.E D * z k =
      iA I (algebraMap (𝓞 I.E) I.E b) + levelafC I.E (D * c) * t := by
    intro k
    obtain ⟨b, t, ht, hbt⟩ := csGlob_approx (F := I.F) (E := I.E) csGlob_intAdApprox (D * c)
      (mul_ne_zero hD0 hc) (levelafC I.E D * z k) (by rw [hDl]; exact hv k)
    exact ⟨b, t, ht, hbt⟩
  choose b t ht hbt using happ
  set v : Fin I.n → I.E := fun k => algebraMap (𝓞 I.E) I.E (b k) * (algebraMap (𝓞 I.F) I.E D)⁻¹ with hvdef
  have hq : iA I ((algebraMap (𝓞 I.F) I.E D)⁻¹) * levelafC I.E D = 1 := by
    rw [← adelstab_incl_C, ← map_mul, inv_mul_cancel₀ hDE, map_one]
  have hzk : ∀ k, z k = iA I (v k) + levelafC I.E c * t k := by
    intro k
    have h1 := hbt k
    rw [levelafC_mul D c] at h1
    have h3 : iA I (v k) = iA I (algebraMap (𝓞 I.E) I.E (b k)) * iA I ((algebraMap (𝓞 I.F) I.E D)⁻¹) := by
      rw [hvdef]; exact map_mul _ _ _
    rw [h3]
    linear_combination iA I ((algebraMap (𝓞 I.F) I.E D)⁻¹) * h1 - z k * hq + (levelafC I.E c * t k) * hq
  have hct : (fun k => levelafC I.E c * t k) ∈ latS (F := I.F) (Formalism.MainNotions.S.Af I.F) (SS I) I.L := hlow _ ht
  have hzv : (fun k => iA I (v k)) = z - (fun k => levelafC I.E c * t k) := by
    funext k
    rw [Pi.sub_apply, hzk k]
    ring

  have hvL : v ∈ I.L := by
    rw [I.L_dual v]
    intro w hwL
    have hint : IsIntegral ℤ (Formalism.UG.hform (starRingEnd I.E) I.J w v) := by
      apply csGlob_int (F := I.F)
      rw [← sig_eq, ← csDual_hform_incl, hzv, hform_sub_right]
      exact sub_mem (hw _ (Submodule.subset_span ⟨w, hwL, rfl⟩)) (pair_int I w hwL _ hct)
    exact ⟨⟨_, hint⟩, rfl⟩
  rw [mem_latSet]
  show ((g⁻¹ : GL (Fin I.n) (AA I)) : Matrix (Fin I.n) (Fin I.n) (AA I)) *ᵥ (fun i => iA I (u i)) ∈ _
  rw [← hz]
  have hz3 : z = (fun k => iA I (v k)) + (fun k => levelafC I.E c * t k) := by
    rw [hzv]; abel
  rw [hz3]
  exact add_mem (Submodule.subset_span ⟨v, hvL, rfl⟩) hct

end PI.UnitaryGroupMassFormula.LCG
end
end

