import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0006

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplFirstRow
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PSymplFirstRow

theorem intVec_ne_zero {ι : Type*} {v : ι → ℤ} (hv : v ≠ 0) : intVec v ≠ 0 := by
  intro h
  apply hv
  funext i
  have := congrFun h i
  simpa [intVec] using this

end PSymplFirstRow

theorem SymplFirstRow.proof (h1 : SymplMinExists.Statement) (h2 : SymplMinBound.Statement)
    (h3 : SymplOrbit.Statement) (h4 : SymplShortPrim.Statement) (h5 : SymplGramMem.Statement) :
    SymplFirstRow.Statement := by
  intro n G hG hpd
  obtain ⟨ρsq, hleast⟩ := h1 (Fin (n + 1) ⊕ Fin (n + 1)) G hpd
  have hdet : G.det = 1 := SymplecticGroup.det_eq_one hG
  have hbound := h2 (Fin (n + 1) ⊕ Fin (n + 1)) G hpd hdet ρsq hleast
  obtain ⟨v, hv0, hvρ⟩ := hleast.1
  refine ⟨ρsq, hleast, ?_, ?_, ?_⟩
  · rw [hvρ]
    have := hpd.dotProduct_mulVec_pos (PSymplFirstRow.intVec_ne_zero hv0)
    simpa [qf] using this
  · simp only [Fintype.card_sum, Fintype.card_fin] at hbound
    push_cast at hbound
    linarith
  · have hmin : ∀ u : Fin (n + 1) ⊕ Fin (n + 1) → ℤ, u ≠ 0 →
        qf G (intVec v) ≤ qf G (intVec u) := by
      intro u hu
      rw [← hvρ]
      exact hleast.2 ⟨u, hu, rfl⟩
    obtain ⟨P, hP, m, hm⟩ := h3 n v
    have hrow : ∃ P' ∈ symplecticGroup (Fin (n + 1)) ℤ, P' (Sum.inl 0) = v := by
      rcases h4 _ G hpd v (P (Sum.inl 0)) m hm hv0 hmin with h | h
      · exact ⟨P, hP, by rw [hm, h, one_smul]⟩
      · refine ⟨-P, SymplecticGroup.neg_mem hP, ?_⟩
        rw [hm, h, neg_one_smul]
        rfl
    obtain ⟨P', hP', hP'v⟩ := hrow
    refine ⟨P', hP', ?_⟩
    rw [(h5 (n + 1) P' G hP' hG hpd).2.2.2 (Sum.inl 0), hP'v, hvρ]

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplGramMem
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PSymplGramMem

lemma det_map_cast {n : ℕ} {P : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ}
    (hP : P ∈ symplecticGroup (Fin n) ℤ) : (P.map (Int.cast : ℤ → ℝ)).det = 1 := by
  have h := SymplecticGroup.det_eq_one (SymplecticGroup.map_mem hP (Int.castRingHom ℝ))
  simpa using h

lemma gram_diag {l : Type*} [Fintype l] (P : Matrix l l ℤ) (G : Matrix l l ℝ) (x : l) :
    symplGram P G x x = qf G (intVec (P x)) := by
  unfold symplGram qf intVec
  rw [Matrix.mul_mul_apply]
  rfl

end PSymplGramMem

open PSymplGramMem in

theorem SymplGramMem.proof : SymplGramMem.Statement := by
  intro n P G hP hG hGpd
  set P' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ := P.map (Int.cast : ℤ → ℝ) with hP'
  have hP'mem : P' ∈ symplecticGroup (Fin n) ℝ := SymplecticGroup.map_mem hP (Int.castRingHom ℝ)
  refine ⟨?_, ?_, ?_, fun x => gram_diag P G x⟩
  · exact Submonoid.mul_mem _ (Submonoid.mul_mem _ hP'mem hG) (SymplecticGroup.transpose_mem hP'mem)
  · have hdet : IsUnit P'.det := by rw [det_map_cast hP]; exact isUnit_one
    have hinj : Function.Injective P'.vecMul :=
      vecMul_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr hdet)
    have h := hGpd.mul_mul_conjTranspose_same hinj
    rwa [conjTranspose_eq_transpose_of_trivial] at h
  · intro Q
    unfold symplGram
    have hmap : (Q * P).map (Int.cast : ℤ → ℝ) = Q.map (Int.cast : ℤ → ℝ) * P.map (Int.cast : ℤ → ℝ) :=
      Matrix.map_mul (f := Int.castRingHom ℝ)
    rw [hmap, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplMinBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PSymplMinBound

theorem prod_sqrt_eq_one {ι : Type} [Fintype ι] (lam : ι → ℝ) (hlam : ∀ i, 0 < lam i)
    (hprod : ∏ i, lam i = 1) : ∏ i, Real.sqrt (lam i) = 1 := by
  have hnn : 0 ≤ ∏ i, Real.sqrt (lam i) := Finset.prod_nonneg fun i _ => Real.sqrt_nonneg _
  have hsq : (∏ i, Real.sqrt (lam i)) ^ 2 = 1 := by
    rw [← Finset.prod_pow]
    simp_rw [Real.sq_sqrt (hlam _).le]
    exact hprod
  nlinarith [hsq, hnn]

theorem exists_lt (h2 : SymplMinkowskiBox.Statement) {ι : Type} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (O : Matrix ι ι ℝ) (lam : ι → ℝ) (hlam : ∀ i, 0 < lam i) (hO : |O.det| = 1)
    (hprod : ∏ i, lam i = 1) (c : ℝ) (hc : 1 < c) :
    ∃ v : ι → ℤ, v ≠ 0 ∧
      ∑ i, lam i * (O *ᵥ intVec v) i ^ 2 < (Fintype.card ι : ℝ) * c ^ 2 := by
  have hc0 : 0 < c := by linarith
  have ha : ∀ i, 0 < c / Real.sqrt (lam i) := fun i => div_pos hc0 (Real.sqrt_pos.2 (hlam i))
  have hpa : 1 < ∏ i, c / Real.sqrt (lam i) := by
    rw [Finset.prod_div_distrib, prod_sqrt_eq_one lam hlam hprod, div_one, Finset.prod_const,
      Finset.card_univ]
    exact one_lt_pow₀ hc Fintype.card_ne_zero
  obtain ⟨v, hv, hbox⟩ := h2 ι O (fun i => c / Real.sqrt (lam i)) hO ha hpa
  refine ⟨v, hv, ?_⟩
  have hlt : ∀ i ∈ (Finset.univ : Finset ι), lam i * (O *ᵥ intVec v) i ^ 2 < c ^ 2 := by
    intro i _
    have hs := Real.sqrt_pos.2 (hlam i)
    have h1 : |(O *ᵥ intVec v) i| * Real.sqrt (lam i) < c := (lt_div_iff₀ hs).1 (hbox i)
    have h2' : (|(O *ᵥ intVec v) i| * Real.sqrt (lam i)) ^ 2 < c ^ 2 :=
      pow_lt_pow_left₀ h1 (mul_nonneg (abs_nonneg _) hs.le) two_ne_zero
    rw [mul_pow, sq_abs, Real.sq_sqrt (hlam i).le] at h2'
    linarith
  calc ∑ i, lam i * (O *ᵥ intVec v) i ^ 2 < ∑ _i : ι, c ^ 2 :=
        Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty hlt
    _ = (Fintype.card ι : ℝ) * c ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end PSymplMinBound

theorem SymplMinBound.proof (h1 : SymplQuadDiag.Statement) (h2 : SymplMinkowskiBox.Statement) :
    SymplMinBound.Statement := by
  intro ι _ _ G hG hdet m hm
  obtain ⟨w, hw, -⟩ := hm.1
  have hne : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact hw (funext fun i => (IsEmpty.false i).elim)
  obtain ⟨O, lam, hlam, hO, hprod, hq⟩ := h1 ι G hG
  rw [hdet] at hprod
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have key : ∀ c : ℝ, 1 < c → m < (Fintype.card ι : ℝ) * c ^ 2 := by
    intro c hc
    obtain ⟨v, hv, hlt⟩ := PSymplMinBound.exists_lt h2 O lam hlam hO hprod c hc
    have hmv : m ≤ qf G (intVec v) := hm.2 ⟨v, hv, rfl⟩
    rw [hq] at hmv
    linarith
  by_contra hcon
  rw [not_le] at hcon
  set N : ℝ := (Fintype.card ι : ℝ) with hNdef
  set t : ℝ := (m / N + 1) / 2 with htdef
  have hmN : 1 < m / N := by rw [lt_div_iff₀ hN]; linarith
  have ht : 1 < t := by rw [htdef]; linarith
  have hsqrt : 1 < Real.sqrt t := by
    rw [Real.lt_sqrt zero_le_one]; linarith
  have hk := key (Real.sqrt t) hsqrt
  rw [Real.sq_sqrt (by linarith)] at hk
  have : N * t = (m + N) / 2 := by
    rw [htdef]; field_simp
  linarith

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplMinExists
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PSymplMinExists

variable {ι : Type} [Fintype ι]

theorem qf_smul (G : Matrix ι ι ℝ) (c : ℝ) (x : ι → ℝ) : qf G (c • x) = c ^ 2 * qf G x := by
  simp only [qf, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

theorem continuous_qf (G : Matrix ι ι ℝ) : Continuous (qf G) :=
  continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)

theorem exists_lower [DecidableEq ι] [Nonempty ι] (G : Matrix ι ι ℝ) (hG : G.PosDef) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ x : ι → ℝ, μ * ‖x‖ ^ 2 ≤ qf G x := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hpos : ∀ x : ι → ℝ, x ≠ 0 → 0 < qf G x := fun x hx => by
    simpa [qf] using hG.dotProduct_mulVec_pos hx
  have hK : IsCompact (Metric.sphere (0 : ι → ℝ) 1) := isCompact_sphere 0 1
  have hne : (Metric.sphere (0 : ι → ℝ) 1).Nonempty :=
    ⟨Pi.single i₀ 1, by simp [Pi.norm_single]⟩
  obtain ⟨u, hu, hmin⟩ := hK.exists_isMinOn hne (continuous_qf G).continuousOn
  refine ⟨qf G u, hpos u ?_, fun x => ?_⟩
  · rintro rfl
    simp at hu
  · by_cases hx : x = 0
    · subst hx
      simp [qf]
    · have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have hy : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : ι → ℝ) 1 := by
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
      have h1 : qf G u ≤ qf G (‖x‖⁻¹ • x) := isMinOn_iff.mp hmin _ hy
      calc qf G u * ‖x‖ ^ 2 ≤ qf G (‖x‖⁻¹ • x) * ‖x‖ ^ 2 := by gcongr
        _ = qf G x := by
          rw [qf_smul]
          field_simp

end PSymplMinExists

theorem SymplMinExists.proof (h1 : SymplQuadDiag.Statement) : SymplMinExists.Statement := by
  intro ι _ _ _ G hG
  obtain ⟨μ, hμ, hlow⟩ := PSymplMinExists.exists_lower G hG
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  set v₀ : ι → ℤ := Pi.single i₀ 1 with hv₀def
  set M₀ : ℝ := qf G (intVec v₀) with hM₀
  set R : ℤ := ⌈M₀ / μ⌉ with hR
  set S : Set (ι → ℤ) := {v | v ≠ 0 ∧ qf G (intVec v) ≤ M₀} with hS
  have hbox : S ⊆ Set.Icc (fun _ => -R) (fun _ => R) := by
    rintro v ⟨-, hq⟩
    have hb : ∀ i, |(v i : ℝ)| ≤ M₀ / μ := by
      intro i
      have hi : |(v i : ℝ)| ≤ ‖intVec v‖ := by
        have := norm_le_pi_norm (intVec v) i
        simpa [intVec, Real.norm_eq_abs] using this
      have hsq : |(v i : ℝ)| ≤ |(v i : ℝ)| ^ 2 := by
        rcases eq_or_ne (v i) 0 with h | h
        · simp [h]
        · have h' : (1 : ℝ) ≤ |(v i : ℝ)| := by
            rw [← Int.cast_abs]
            exact_mod_cast Int.one_le_abs h
          nlinarith
      have hsq2 : |(v i : ℝ)| ^ 2 ≤ ‖intVec v‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hi 2
      rw [le_div_iff₀ hμ]
      calc |(v i : ℝ)| * μ ≤ μ * ‖intVec v‖ ^ 2 := by nlinarith
        _ ≤ qf G (intVec v) := hlow _
        _ ≤ M₀ := hq
    have hc : ∀ i, |v i| ≤ R := by
      intro i
      have : ((|v i| : ℤ) : ℝ) ≤ (R : ℝ) := by
        rw [Int.cast_abs]
        exact (hb i).trans (Int.le_ceil _)
      exact_mod_cast this
    refine ⟨fun i => ?_, fun i => ?_⟩
    · exact (abs_le.mp (hc i)).1
    · exact (abs_le.mp (hc i)).2
  have hfin : S.Finite := (Set.finite_Icc _ _).subset hbox
  have hv₀ : v₀ ∈ S := by
    refine ⟨fun h => ?_, le_rfl⟩
    have := congrFun h i₀
    simp [v₀] at this
  obtain ⟨w, hwS, hwmin⟩ := Set.exists_min_image S (fun v => qf G (intVec v)) hfin ⟨v₀, hv₀⟩
  refine ⟨qf G (intVec w), ⟨w, hwS.1, rfl⟩, ?_⟩
  rintro t ⟨v, hv, rfl⟩
  by_cases hvS : qf G (intVec v) ≤ M₀
  · exact hwmin v ⟨hv, hvS⟩
  · exact hwS.2.trans (le_of_lt (not_le.mp hvS))

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplMinkowskiBox
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix MeasureTheory

namespace PSymplMinkowskiBox

theorem box_neg {ι : Type} [Fintype ι] (A : Matrix ι ι ℝ) (a : ι → ℝ) (x : ι → ℝ)
    (hx : ∀ i, |(A *ᵥ x) i| < a i) : ∀ i, |(A *ᵥ (-x)) i| < a i := by
  intro i
  rw [mulVec_neg, Pi.neg_apply, abs_neg]
  exact hx i

theorem box_convex {ι : Type} [Fintype ι] (A : Matrix ι ι ℝ) (a : ι → ℝ) :
    Convex ℝ {x : ι → ℝ | ∀ i, |(A *ᵥ x) i| < a i} := by
  intro x hx y hy s t hs ht hst i
  have hlt : s • |(A *ᵥ x) i| + t • |(A *ᵥ y) i| ∈ Set.Iio (a i) :=
    convex_Iio (a i) (hx i) (hy i) hs ht hst
  rw [Set.mem_Iio, smul_eq_mul, smul_eq_mul] at hlt
  rw [mulVec_add, mulVec_smul, mulVec_smul, Pi.add_apply, Pi.smul_apply, Pi.smul_apply,
    smul_eq_mul, smul_eq_mul]
  calc |s * (A *ᵥ x) i + t * (A *ᵥ y) i| ≤ |s * (A *ᵥ x) i| + |t * (A *ᵥ y) i| := abs_add_le _ _
    _ = s * |(A *ᵥ x) i| + t * |(A *ᵥ y) i| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hs, abs_of_nonneg ht]
    _ < a i := hlt

theorem volume_fundamentalDomain_basisFun (ι : Type) [Fintype ι] :
    volume (ZSpan.fundamentalDomain (Pi.basisFun ℝ ι)) = 1 := by
  rw [ZSpan.fundamentalDomain_pi_basisFun, volume_pi, Measure.pi_pi]
  simp [Real.volume_Ico]

end PSymplMinkowskiBox

open PSymplMinkowskiBox in

theorem SymplMinkowskiBox.proof (h1 : SymplBoxVolume.Statement) : SymplMinkowskiBox.Statement := by
  intro ι _ _ A a hdet ha hprod
  have hdet0 : A.det ≠ 0 := by
    intro h
    rw [h, abs_zero] at hdet
    exact zero_ne_one hdet
  set s : Set (ι → ℝ) := {x | ∀ i, |(A *ᵥ x) i| < a i} with hs
  have hvol : volume s = ENNReal.ofReal (2 ^ Fintype.card ι * ∏ i, a i) := by
    rw [hs, h1 ι A a hdet0 ha, hdet, div_one, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ]
  have hP : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  have hbig : volume (ZSpan.fundamentalDomain (Pi.basisFun ℝ ι)) * 2 ^ Module.finrank ℝ (ι → ℝ) <
      volume s := by
    rw [volume_fundamentalDomain_basisFun, one_mul, Module.finrank_fintype_fun_eq_card, hvol,
      ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_pow (by norm_num),
      ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    exact lt_mul_of_one_lt_right hP hprod
  have : Countable (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))).toAddSubgroup := by
    change Countable (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι)))
    infer_instance
  obtain ⟨x, hx0, hxs⟩ := MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    (L := (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))).toAddSubgroup)
    (ZSpan.isAddFundamentalDomain (Pi.basisFun ℝ ι) volume)
    (fun y hy => box_neg A a y hy) (box_convex A a) hbig
  have hint : ∀ i, ∃ z : ℤ, (z : ℝ) = (x : ι → ℝ) i := by
    intro i
    obtain ⟨z, hz⟩ := ((Pi.basisFun ℝ ι).mem_span_iff_repr_mem ℤ (x : ι → ℝ)).mp x.2 i
    exact ⟨z, by simpa using hz⟩
  choose v hv using hint
  have hxv : intVec v = (x : ι → ℝ) := funext hv
  refine ⟨v, ?_, fun i => ?_⟩
  · rintro rfl
    apply hx0
    ext i
    rw [← hv i]
    simp
  · rw [hxv]
    exact hxs i

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplOmegaMem
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PSymplOmegaMem

theorem mul_J_mul_transpose_apply {R : Type*} [CommRing R] {l : Type*} [Fintype l]
    [DecidableEq l] (M : Matrix (l ⊕ l) (l ⊕ l) R) (x y : l ⊕ l) :
    (M * J l R * Mᵀ) x y = symplOmega (M x) (M y) := by
  rw [symplOmega, dotProduct_mulVec, Matrix.mul_apply]
  rfl

end PSymplOmegaMem

theorem SymplOmegaMem.proof : SymplOmegaMem.Statement := by
  intro R _ l _ _ M
  rw [SymplecticGroup.mem_iff]
  constructor
  · intro h x y
    rw [← PSymplOmegaMem.mul_J_mul_transpose_apply, h]
  · intro h
    ext x y
    rw [PSymplOmegaMem.mul_J_mul_transpose_apply, h]

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplOrbit
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PSymplOrbit

theorem smul_symplCons {R : Type*} [CommRing R] {n : ℕ} (m p q : R) (w : Fin n ⊕ Fin n → R) :
    m • symplCons p q w = symplCons (m * p) (m * q) (m • w) := by
  funext x
  rcases x with i | i <;> refine Fin.cases ?_ (fun j => ?_) i <;> simp [symplCons]

theorem symplCons_one_zero {R : Type*} [CommRing R] {n : ℕ} :
    symplCons (1 : R) 0 (0 : Fin n ⊕ Fin n → R) = Pi.single (Sum.inl 0) 1 := by
  funext x
  rcases x with i | i <;> refine Fin.cases ?_ (fun j => ?_) i <;>
    simp [symplCons, Fin.succ_ne_zero]

end PSymplOrbit

open PSymplOrbit in

theorem SymplOrbit.proof (h1 : SymplExtMem.Statement) (h2 : SymplExtVecMul.Statement)
    (h3 : SymplTwoRow.Statement) (h4 : SymplGcd.Statement) (h5 : SymplCons.Statement) :
    SymplOrbit.Statement := by
  intro n
  induction n with
  | zero =>
    intro v
    obtain ⟨c, a', b', x, y, ha, hb, hxy⟩ := h4 (v (Sum.inl 0)) (v (Sum.inr 0))
    have hE := h1 ℤ 0 a' b' (-y) x 1 (by linarith) (Submonoid.one_mem _)
    refine ⟨_, hE, c, ?_⟩
    have htail : symplTail v = 0 := funext fun z => z.elim (fun i => i.elim0) (fun i => i.elim0)
    have hrow : symplExt a' b' (-y) x (1 : Matrix (Fin 0 ⊕ Fin 0) (Fin 0 ⊕ Fin 0) ℤ) (Sum.inl 0) =
        symplCons a' b' 0 :=
      rfl
    rw [hrow, smul_symplCons, ← ha, ← hb, smul_zero, ← htail]
    exact ((h5 ℤ 0).1 v).symm
  | succ n ih =>
    intro v
    obtain ⟨Q, hQ, m', hw⟩ := ih (symplTail v)
    obtain ⟨c, a', b', x, y, ha, hb, hxy⟩ := h4 (v (Sum.inl 0)) (v (Sum.inr 0))
    obtain ⟨k, c'', d'', x', y', hc, hm, hxy'⟩ := h4 c m'
    obtain ⟨P₂, hP₂, hrow₂⟩ := h3 n c'' d'' x' y' hxy'
    have hE₁ := h1 ℤ (n + 1) a' b' (-y) x 1 (by linarith) (Submonoid.one_mem _)
    have hE₂ := h1 ℤ (n + 1) 1 0 0 1 Q (by ring) hQ
    refine ⟨P₂ * symplExt 1 0 0 1 Q * symplExt a' b' (-y) x 1,
      Submonoid.mul_mem _ (Submonoid.mul_mem _ hP₂ hE₂) hE₁, k, ?_⟩
    have e1 : symplCons c 0 (symplTail v) ᵥ* symplExt a' b' (-y) x 1 = v := by
      rw [h2, vecMul_one]
      simp only [zero_mul, add_zero]
      rw [← ha, ← hb]
      exact (h5 ℤ (n + 1)).1 v
    have e2 : symplCons c 0 (symplCons m' 0 0) ᵥ* symplExt 1 0 0 1 Q = symplCons c 0 (symplTail v) := by
      rw [h2]
      simp only [mul_one, mul_zero, add_zero]
      congr 1
      have hs : symplCons m' 0 (0 : Fin n ⊕ Fin n → ℤ) = m' • symplCons 1 0 0 := by
        rw [smul_symplCons]; simp
      rw [hs, smul_vecMul, symplCons_one_zero, single_one_vecMul, hw]
      rfl
    have e3 : k • P₂ (Sum.inl 0) = symplCons c 0 (symplCons m' 0 0) := by
      rw [hrow₂, hc, hm, smul_symplCons, smul_symplCons]
      simp
    rw [mul_apply_eq_vecMul, mul_apply_eq_vecMul, ← smul_vecMul, ← smul_vecMul, e3, e2, e1]

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplReduceStep
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

namespace PSymplReduceStep

theorem symplExt_map {n : ℕ} (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ) :
    (symplExt (1 : ℤ) 0 0 1 Q).map (Int.cast : ℤ → ℝ) =
      symplExt 1 0 0 1 (Q.map (Int.cast : ℤ → ℝ)) := by
  ext x y
  rcases x with i | i <;> rcases y with j | j <;>
    cases i using Fin.cases <;> cases j using Fin.cases <;> simp [symplExt, symplCons]

theorem schur_toBlocks {n : ℕ} (K : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ) :
    (Matrix.of fun i j : Fin n => K.toBlocks₁₁ i.succ j.succ -
        K.toBlocks₁₁ i.succ 0 * K.toBlocks₁₁ 0 j.succ / K.toBlocks₁₁ 0 0) =
      (symplReduce K).toBlocks₁₁ := by
  ext i j
  simp [symplReduce, Matrix.toBlocks₁₁]

end PSymplReduceStep

theorem SymplReduceStep.proof (h1 : SymplExtMem.Statement) (h2 : SymplReduceConj.Statement)
    (h3 : SymplDetSchur.Statement) : SymplReduceStep.Statement := by
  intro n H Q hH hQ
  refine ⟨symplExt 1 0 0 1 Q, h1 ℤ n 1 0 0 1 Q (by norm_num) hQ, ?_⟩
  obtain ⟨he, hred⟩ := h2 n H (Q.map (Int.cast : ℤ → ℝ))
  rw [symplGram, PSymplReduceStep.symplExt_map]
  generalize symplExt 1 0 0 1 (Q.map (Int.cast : ℤ → ℝ)) * H *
    (symplExt 1 0 0 1 (Q.map (Int.cast : ℤ → ℝ)))ᵀ = K at he hred ⊢
  refine ⟨he, ?_⟩
  have hk0 : K.toBlocks₁₁ 0 0 = H (Sum.inl 0) (Sum.inl 0) := he
  rw [h3 n K.toBlocks₁₁ (hk0 ▸ hH), PSymplReduceStep.schur_toBlocks, hred, hk0]
  rfl

end

end GroundTheory.Heights₂.Heights
end

