import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0028
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEquivOfRetractions
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0028
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0023
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0030
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSmulRatTupEq
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct ENNReal Matrix

namespace GlobalTheory.LocalWittND

theorem exists_gl {K S : Type} [Field K] [CommRing S] (s : S →+* S) (hs : ∀ x, s (s x) = x)
    (h2 : (2 : S) ≠ 0) (hS : IsField S ∨ ∃ φ : S ≃+* K × K, ∀ x, φ (s x) = (φ x).swap)
    {n a : ℕ} (J : Matrix (Fin n) (Fin n) S) (hJ : ∀ i j, s (J j i) = J i j) (hd : IsUnit J.det)
    (X Y : Matrix (Fin n) (Fin a) S) (hX : IsUnit (Formalism.UG.cT s X * J * X).det)
    (hXY : Formalism.UG.cT s Y * J * Y = Formalism.UG.cT s X * J * X) :
    ∃ γ : GL (Fin n) S, Formalism.UG.cT s γ.1 * J * γ.1 = J ∧ γ.1 * X = Y := by
  have key : ∀ {m : ℕ} (Z : Matrix (Fin n) (Fin m) S),
      Zᵀ * Jᵀ * Z.map s = (Formalism.UG.cT s Z * J * Z)ᵀ := by
    intro m Z
    simp only [Formalism.UG.cT, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  have hX' : IsUnit (Xᵀ * Jᵀ * X.map s).det := by rw [key, Matrix.det_transpose]; exact hX
  have hXY' : Yᵀ * Jᵀ * Y.map s = Xᵀ * Jᵀ * X.map s := by rw [key, key, hXY]
  have : ∃ γ : Matrix (Fin n) (Fin n) S, γᵀ * Jᵀ * γ.map s = Jᵀ ∧ γ * X = Y := by
    rcases hS with hF | ⟨φ, hφ⟩
    · letI := hF.toField
      obtain ⟨γ, h1, h3⟩ := GlobalTheory.HermWitt.exists_gl_isometry_mul_eq_of_det_ne_zero (c := s)
        h2 hs (G := Jᵀ) (fun i j => hJ i j) (X := X) (Y := Y) hX'.ne_zero hXY'
      exact ⟨γ, h1, h3⟩
    · exact GlobalTheory.HermTuple.exists_matrix_split s φ hφ Jᵀ (fun i j => hJ i j)
        (by rwa [Matrix.det_transpose]) X Y hX' hXY'
  obtain ⟨γ, h1, h3⟩ := this
  rw [key] at h1
  have h4 := Matrix.transpose_injective h1
  have hγ : IsUnit γ.det := by
    rw [← h4, Matrix.det_mul] at hd
    exact isUnit_of_mul_isUnit_right hd
  obtain ⟨G, hG⟩ := (Matrix.isUnit_iff_isUnit_det γ).2 hγ
  exact ⟨G, by rw [hG]; exact h4, by rw [hG]; exact h3⟩

theorem gram_eq {S : Type} [CommRing S] (s : S →+* S) {n a : ℕ} (J : Matrix (Fin n) (Fin n) S)
    (Z : Fin a → Fin n → S) :
    (Matrix.of fun k l => Formalism.UG.hform s J (Z k) (Z l)) =
      Formalism.UG.cT s (Matrix.of Z)ᵀ * J * (Matrix.of Z)ᵀ := by
  ext k l
  simp only [Formalism.UG.hform, Formalism.UG.cT, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Matrix.of_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem gramR_ratTup {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (σ : E →ₐ[F] E) {n a : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (X : Fin a → Fin n → E) :
    gramR R σ J (ratTup (F := F) R X) = (gramE σ J X).map (inclR (F := F) R) := by
  ext k l
  simp only [gramR, gramE, hR, hE, Formalism.UG.hform, map_sum, map_mul, ratTup, JR, Matrix.map_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 2

theorem invol_of_isCMExt {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : (∀ a, σ (σ a) = a) ∧ ∃ a, σ a ≠ a := by
  obtain ⟨-, hE, -, hσ⟩ := h
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  refine ⟨fun a => τ.injective (by rw [hσ, hσ, star_star]), ?_⟩
  by_contra hc
  push Not at hc
  refine IsTotallyComplex.complexEmbedding_not_isReal τ ?_
  rw [ComplexEmbedding.isReal_iff]
  ext x
  have := hσ τ x
  rw [hc] at this
  exact this.symm

theorem exists_smul_eq_field {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (K : Type) [Field K] [Algebra F K]
    {n a : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J)
    (X Y : Fin a → Fin n → K ⊗[F] E) (hX : IsUnit (gramR K σ J X).det)
    (hXY : gramR K σ J Y = gramR K σ J X) : ∃ g : HA K σ J, g • X = Y := by
  obtain ⟨hi, hne⟩ := invol_of_isCMExt hcm
  have hS := (GlobalTheory.quadBaseChange_isField_or_split F E K σ hcm.2.2.1 hi hne).1
  have hg : ∀ Z : Fin a → Fin n → K ⊗[F] E, gramR K σ J Z = _ :=
    fun Z => gram_eq (sigR K σ) (JR K J) Z
  have h2 : (2 : K ⊗[F] E) ≠ 0 := by
    have : inclR (F := F) K (2 : E) ≠ 0 := by
      rw [map_ne_zero]; exact two_ne_zero
    rwa [map_ofNat] at this
  obtain ⟨γ, h1, h3⟩ := exists_gl (sigR K σ)
    (fun x => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul k e => exact congrArg (k ⊗ₜ[F] ·) (hi e)
      | add x y hx hy => simp only [map_add, hx, hy])
    h2 hS (JR K J)
    (fun i j => by
      show (1 : K) ⊗ₜ[F] σ (J j i) = (1 : K) ⊗ₜ[F] J i j
      rw [hJ.1])
    (by
      have := (hJ.2.isUnit).map (inclR (F := F) K)
      rwa [RingHom.map_det] at this)
    (Matrix.of X)ᵀ (Matrix.of Y)ᵀ (by rw [← hg]; exact hX) (by rw [← hg, ← hg]; exact hXY)
  refine ⟨(⟨γ, h1⟩ : HR K σ J), ?_⟩
  funext k i
  exact congrFun (congrFun h3 i) k

theorem exists_smul_ratTup_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (a : ℕ) (X0 : Fin a → Fin n → E), (gramE σ J X0).det ≠ 0 → ∀ y : Fin a → Fin n → Fv F v ⊗[F] E, gramR (Fv F v) σ J y = (gramE σ J X0).map (inclR (Fv F v)) → ∃ g : HA (Fv F v) σ J, g • ratTup (Fv F v) X0 = y := by
  intro F E _ _ _ _ _ σ hcm n J hJ v a X0 hX y hy
  refine exists_smul_eq_field hcm (Fv F v) hJ _ _ ?_ (by rw [hy, gramR_ratTup])
  have := hX.isUnit.map (inclR (F := F) (Fv F v))
  rw [gramR_ratTup]
  rwa [RingHom.map_det] at this

end GlobalTheory.LocalWittND
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameLatticeGramDetAndMinorsOrbitInvariant
section
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.FrameGram

theorem submatrix_mul_upper {E : Type} [CommRing E] {N m : ℕ} (hm : m ≤ N) {ι : Type} (f : ι → Fin N)
    (M B : Matrix (Fin N) (Fin N) E) (hB : ∀ i j, j < i → B i j = 0) :
    (M * B).submatrix f (Fin.castLE hm) =
      M.submatrix f (Fin.castLE hm) * B.submatrix (Fin.castLE hm) (Fin.castLE hm) := by
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  symm
  refine Fintype.sum_of_injective (Fin.castLE hm) (Fin.castLE_injective hm) _ _ ?_ fun _ => rfl
  intro i hi
  rw [hB, mul_zero]
  by_contra h
  apply hi
  have h1 : (i : ℕ) ≤ b := not_lt.1 h
  exact ⟨⟨i, by omega⟩, rfl⟩

theorem det_sub_upper {E : Type} [CommRing E] {N m : ℕ} (hm : m ≤ N)
    (B : Matrix (Fin N) (Fin N) E) (hB : ∀ i j, j < i → B i j = 0) (h1 : ∀ i, B i i = 1) :
    (B.submatrix (Fin.castLE hm) (Fin.castLE hm)).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · simp [h1]
  · intro i j hij
    exact hB _ _ hij

theorem lead_mul_upper {E : Type} [CommRing E] {N : ℕ} (M B : Matrix (Fin N) (Fin N) E)
    (hB : ∀ i j, j < i → B i j = 0) (h1 : ∀ i, B i i = 1) (l : Fin (N + 1)) :
    lead (M * B) l = lead M l := by
  unfold lead
  rw [submatrix_mul_upper _ _ _ _ hB, Matrix.det_mul, det_sub_upper _ _ hB h1, mul_one]

theorem lead_transpose {E : Type} [CommRing E] {N : ℕ} (M : Matrix (Fin N) (Fin N) E)
    (l : Fin (N + 1)) : lead M.transpose l = lead M l := by
  unfold lead
  rw [← Matrix.det_transpose]
  rfl

theorem lead_lower_mul {E : Type} [CommRing E] {N : ℕ} (M B : Matrix (Fin N) (Fin N) E)
    (hB : ∀ i j, j < i → B i j = 0) (h1 : ∀ i, B i i = 1) (l : Fin (N + 1)) :
    lead (B.transpose * M) l = lead M l := by
  rw [← lead_transpose, Matrix.transpose_mul, Matrix.transpose_transpose, lead_mul_upper _ _ hB h1,
    lead_transpose]

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem hf_sum_left (L : LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) {ι : Type} [Fintype ι]
    (α : ι → E) (g : ι → Fin n → E) (y : Fin n → E) :
    hf L H (∑ i, α i • g i) y = ∑ i, α i * hf L H (g i) y := by
  change GlobalTheory.FrameBasic.hfL L H y _ = _
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul]; rfl

theorem gram_change (L : LocE F E) {n : ℕ} {H : Matrix (Fin n) (Fin n) E} (h : IsHerm L H)
    {ι : Type} [Fintype ι] (u u' v v' : ι → Fin n → E) (P P' : Matrix ι ι E)
    (hv : ∀ j, v j = ∑ i, P i j • u i) (hv' : ∀ j, v' j = ∑ i, P' i j • u' i) :
    (Matrix.of fun a b => hf L H (v' b) (v a)) =
      (P.map L.cj).transpose * (Matrix.of fun a b => hf L H (u' b) (u a)) * P' := by
  ext a b
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  rw [hv', hf_sum_left]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm, GlobalTheory.FrameBasic.hf_conj L h, hv, hf_sum_left, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← GlobalTheory.FrameBasic.hf_conj L h]

theorem det_conj (L : LocE F E) {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι E) :
    (A.map L.cj).transpose.det = L.cj A.det := by
  rw [Matrix.det_transpose]
  exact (AlgEquiv.map_det L.cj A).symm

theorem span_frames {V : Type} [AddCommGroup V] [Module E V] {ι : Type} (g g' : ι → V) (t : F)
    (ht : t ≠ 0) :
    Submodule.span E (Set.range (Sum.elim g fun i => algebraMap F E t⁻¹ • (g' i - g i))) =
      Submodule.span E (Set.range g) ⊔ Submodule.span E (Set.range g') := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i | i, rfl⟩
    · exact Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)
    · exact Submodule.smul_mem _ _ (Submodule.sub_mem _
        (Submodule.mem_sup_right (Submodule.subset_span ⟨i, rfl⟩))
        (Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)))
  · rw [sup_le_iff, Submodule.span_le, Submodule.span_le]
    constructor
    · rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨Sum.inl i, rfl⟩
    · rintro _ ⟨i, rfl⟩
      have e : g' i = algebraMap F E t • (algebraMap F E t⁻¹ • (g' i - g i)) + g i := by
        rw [smul_smul, ← map_mul, mul_inv_cancel₀ ht, map_one, one_smul, sub_add_cancel]
      rw [e]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr i, rfl⟩))
        (Submodule.subset_span ⟨Sum.inl i, rfl⟩)

theorem vE_const [IsNonarchimedeanLocalField F] [CharZero F] (L : LocE F E) (r k : ℕ)
    (S : Frames L r k) (c : F) (hc : c ≠ 0) (m : ℕ) :
    vE L S.ϖ (algebraMap F E ((-1) ^ (r + 1) * c * S.th⁻¹ ^ m)) =
      vE L S.ϖ (algebraMap F E c) - m * S.vth := by
  obtain ⟨hadd, hϖ, -, -⟩ := GlobalTheory.UnramVal.vE_valuation L S.ϖ S.ϖ_irr
  have hth : S.th ≠ 0 := (GlobalTheory.FrameBasic.main L r k S).2.2.2.2.2.1
  have h1 : vE L S.ϖ (algebraMap F E 1) = 0 := by
    have := hadd 1 1 one_ne_zero one_ne_zero
    rw [mul_one] at this
    omega
  have hn : vE L S.ϖ (algebraMap F E (-1)) = 0 := by
    have := hadd (-1) (-1) (by simp) (by simp)
    rw [neg_mul_neg, mul_one] at this
    omega
  have ht : vE L S.ϖ (algebraMap F E S.th) = S.vth := by
    unfold Frames.th Frames.vth
    split_ifs
    · exact hϖ
    · exact h1
  have hti : vE L S.ϖ (algebraMap F E S.th⁻¹) = -S.vth := by
    have := hadd S.th S.th⁻¹ hth (inv_ne_zero hth)
    rw [mul_inv_cancel₀ hth] at this
    omega
  have hpow : ∀ x : F, x ≠ 0 → ∀ j : ℕ,
      vE L S.ϖ (algebraMap F E (x ^ j)) = j * vE L S.ϖ (algebraMap F E x) := by
    intro x hx j
    induction j with
    | zero => rw [pow_zero, h1]; simp
    | succ j ih => rw [pow_succ, hadd _ _ (pow_ne_zero _ hx) hx, ih]; push_cast; ring
  rw [hadd _ _ (mul_ne_zero (pow_ne_zero _ (by simp)) hc) (pow_ne_zero _ (inv_ne_zero hth)),
    hadd _ _ (pow_ne_zero _ (by simp)) hc, hpow _ (by simp), hpow _ (inv_ne_zero hth), hn, hti]
  ring

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ n ∈ S.N, ∀ n' ∈ S.N', (∃ c : F, c ≠ 0 ∧ vE L S.ϖ (algebraMap F E c) = S.a ∧ (Matrix.of fun a b => S.h (Sum.elim (fun i => n (S.f i)) (fun i => algebraMap F E S.th⁻¹ • (n' (S.f' i) - n (S.f i))) b) (Sum.elim (fun i => n (S.f i)) (fun i => algebraMap F E S.th⁻¹ • (n' (S.f' i) - n (S.f i))) a)).det = algebraMap F E c) ∧ (∀ l, lead (Matrix.of fun a b => S.h (n' (S.f' b)) (n (S.f a))) l = S.D l) ∧ Submodule.span E (Set.range (Sum.elim (fun i => n (S.f i)) (fun i => algebraMap F E S.th⁻¹ • (n' (S.f' i) - n (S.f i))))) = S.ME := by
  intro F _ _ _ _ _ E _ _ _ L r k S n hn n' hn'
  obtain ⟨⟨s, ⟨hs0, hs1⟩, hs⟩, hsp, -⟩ := (GlobalTheory.HL.frame_unipotent_unitriangular L r k S S.f S.es (Or.inl ⟨rfl, rfl⟩)).2 n hn
  obtain ⟨⟨s', ⟨hs0', hs1'⟩, hs'⟩, hsp', -⟩ :=
    (GlobalTheory.HL.frame_unipotent_unitriangular L r k S S.f' S.es' (Or.inr ⟨rfl, rfl⟩)).2 n' hn'
  obtain ⟨-, -, ⟨c, hc0, hc⟩, -, -, hth, -⟩ := GlobalTheory.FrameBasic.main L r k S
  have hlead : ∀ l, lead (Matrix.of fun a b => S.h (n' (S.f' b)) (n (S.f a))) l = S.D l := by
    intro l
    have e := gram_change L S.herm.1 S.f S.f' _ _ s s' hs hs'
    unfold Frames.h
    rw [e, lead_mul_upper _ _ hs0' hs1', lead_lower_mul]
    · rfl
    · intro i j hij; rw [Matrix.map_apply, hs0 i j hij, map_zero]
    · intro i; rw [Matrix.map_apply, hs1, map_one]
  refine ⟨⟨(-1) ^ (r + 1) * c * S.th⁻¹ ^ (2 * (r + 1)),
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by simp)) hc0) (pow_ne_zero _ (inv_ne_zero hth)),
    ?_, ?_⟩, hlead, ?_⟩
  · rw [vE_const L r k S c hc0, Frames.a, hc]
    push_cast; ring
  · set Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
      Matrix.of fun a b => S.h (n' (S.f' b)) (n (S.f a)) with hZ
    set t : E := algebraMap F E S.th⁻¹ with ht
    let P : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) E :=
      Matrix.fromBlocks 1 (Matrix.diagonal fun _ => -t) 0 (Matrix.diagonal fun _ => t)
    have hP : ∀ j, (Sum.elim (fun i => n (S.f i)) (fun i => t • (n' (S.f' i) - n (S.f i)))) j =
        ∑ i, P i j • (Sum.elim (fun i => n (S.f i)) (fun i => n' (S.f' i))) i := by
      rintro (j | j)
      · simp [P, Fintype.sum_sum_type, Matrix.one_apply]
      · simp [P, Fintype.sum_sum_type, Matrix.diagonal_apply, smul_sub]
        abel
    have hPd : P.det = t ^ (r + 1) := by
      simp [P, Matrix.det_fromBlocks_zero₂₁]
    have e := gram_change L S.herm.1 _ _ _ _ P P hP hP
    have hG : (Matrix.of fun a b => hf L S.Hm
        ((Sum.elim (fun i => n (S.f i)) (fun i => n' (S.f' i))) b)
        ((Sum.elim (fun i => n (S.f i)) (fun i => n' (S.f' i))) a)) =
        Matrix.fromBlocks (Matrix.single (Fin.last r) (Fin.last r) (-(algebraMap F E S.T))) Z
          (Z.map L.cj).transpose
          (Matrix.single (Fin.last r) (Fin.last r) (-(algebraMap F E S.T'))) := by
      ext (a | a) (b | b)
      · have := hn.1.1 (S.f b) (S.f a)
        simp only [Matrix.of_apply, Sum.elim_inl, Matrix.fromBlocks_apply₁₁, this, S.gram,
          Matrix.single_apply, eq_comm, and_comm]
      · rfl
      · exact GlobalTheory.FrameBasic.hf_conj L S.herm.1 _ _
      · have := hn'.1.1 (S.f' b) (S.f' a)
        simp only [Matrix.of_apply, Sum.elim_inr, Matrix.fromBlocks_apply₂₂, this, S.gram',
          Matrix.single_apply, eq_comm, and_comm]
    have hD1 : Z.det = S.D (Fin.last (r + 1)) := hlead (Fin.last (r + 1))
    have hD0 : (Z.submatrix Fin.castSucc Fin.castSucc).det = S.D (Fin.last r).castSucc :=
      hlead (Fin.last r).castSucc
    have e2 : ((Z.map L.cj).transpose.submatrix Fin.castSucc Fin.castSucc) =
      ((Z.submatrix Fin.castSucc Fin.castSucc).map L.cj).transpose := rfl
    have hct : L.cj t = t := L.cj.commutes _
    unfold Frames.h
    rw [e, Matrix.det_mul, Matrix.det_mul, det_conj, hPd, hG, GlobalTheory.HL.det_gram_two_frames, e2,
      det_conj, det_conj, hD1, hD0, ← map_mul (algebraMap F E), map_pow, hct]
    change _ * (_ * S.G) * _ = _
    rw [hc, map_mul, map_mul, map_pow, map_pow, map_neg, map_one, ← ht]
    ring
  · have hu : {i : Fin (r + 1) | (i : ℕ) < r + 1} = Set.univ := by
      ext i; simpa using i.2
    rw [span_frames _ _ _ hth, Frames.ME, ← hsp, ← hsp']
    simp only [Frames.spanTo, hu, Set.image_univ]

end GlobalTheory.FrameGram
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalFrameStabilizerActsUnitriangular
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

noncomputable section
namespace GlobalTheory.HL.StTri

theorem descend {E R : Type} [Field E] [CommRing R] [Nontrivial R] (ι : E →+* R) {n m : ℕ}
    (w : Fin m → Fin n → E) (s : Set (Fin m)) (v : Fin n → E)
    (h : (fun i => ι (v i)) ∈ Submodule.span R ((fun a i => ι (w a i)) '' s)) :
    v ∈ Submodule.span E (w '' s) := by
  letI : Algebra E R := ι.toAlgebra
  have hinj : Function.Injective (Algebra.linearMap E R) := ι.injective
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap E R)
    (LinearMap.ker_eq_bot.mpr hinj)
  have hg1 : ∀ c : E, g (ι c) = c := fun c => LinearMap.congr_fun hg c
  have hgm : ∀ (a : R) (c : E), g (a * ι c) = c * g a := by
    intro a c
    have : a * ι c = c • a := by rw [Algebra.smul_def, mul_comm]; rfl
    rw [this, map_smul, smul_eq_mul]
  rw [Finsupp.mem_span_image_iff_linearCombination] at h
  obtain ⟨l, hl, hv⟩ := h
  rw [Finsupp.mem_span_image_iff_linearCombination]
  refine ⟨Finsupp.mapRange g (map_zero g) l, ?_, ?_⟩
  · rw [Finsupp.mem_supported'] at hl ⊢
    intro i hi
    simp [hl i hi]
  · funext k
    have hk := congrFun hv k
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at hk ⊢
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hk ⊢
    rw [← hg1 (v k), ← hk, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hgm, Finsupp.mapRange_apply, mul_comm]

theorem hf_smul_right {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) (c : E) :
    hf L Hm x (c • y) = L.cj c * hf L Hm x y := by
  simp only [hf, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hf_add_right {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (x y z : Fin n → E) :
    hf L Hm x (y + z) = hf L Hm x y + hf L Hm x z := by
  simp only [hf, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

theorem loc_step {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] {L : LocE F E} {r k : ℕ} (S : Frames L r k) (g : Fin (r + 1) → S.V)
    (hg : ∀ b : Fin (r + 1), (b : ℕ) < r → hf L S.Hm (g (Fin.last r)) (g b) = 0)
    (x : S.GLV) (hx : x ∈ S.Nof g) (j : Fin (r + 1)) : x (g j) - g j ∈ S.spanTo g j := by
  unfold Frames.Nof at hx
  rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_iInf] at hx
  obtain ⟨⟨_, hU⟩, hP⟩ := hx
  by_cases hj : (j : ℕ) < r
  · have h1 := (hU ⟨j, hj⟩).2 (g j) (Submodule.subset_span ⟨j, by simp, rfl⟩)
    simpa using h1
  · have hjr : (j : ℕ) = r := by omega
    have hjl : j = Fin.last r := Fin.ext hjr
    have hmem : g (Fin.last r) ∈ perp L S.Hm (S.spanTo g r) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨b, hb, rfl⟩ := hy
        exact hg b hb
      | zero => simp [hf]
      | add y z _ _ hy hz => rw [hf_add_right, hy, hz, add_zero]
      | smul c y _ hy => rw [hf_smul_right, hy, mul_zero]
    have h2 := hP.2 _ hmem
    rw [hjl]
    simpa [Frames.spanTo] using h2

theorem frame_tri {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} (A : Places F E sig) {r n : ℕ} (p : HeightOneSpectrum (𝓞 F))
    (x : (Fin n → E) ≃ₗ[E] (Fin n → E))
    (xp : (Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep)) (hext : A.Ext p x xp)
    (gG : Fin (r + 1) → Fin n → E) (gS : Fin (r + 1) → Fin n → (A.loc p).Ep)
    (u : Fin (r + 1) → (A.loc p).Ep) (hu : ∀ a, IsUnit (u a)) (heq : ∀ a, u a • gS a = A.bc p (gG a))
    (hstep : ∀ j : Fin (r + 1), xp (gS j) - gS j ∈ Submodule.span (A.loc p).Ep (gS '' {i | (i : ℕ) < j})) :
    ∃ s : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) ∧
      ∀ j, x (gG j) = ∑ i, s i j • gG i := by
  haveI : Nontrivial (A.loc p).Ep :=
    Module.nontrivial_of_finrank_pos (R := (A.loc p).Fp) (by rw [(A.loc p).rank]; norm_num)
  have key : ∀ j : Fin (r + 1), x (gG j) - gG j ∈ Submodule.span E (gG '' {i | (i : ℕ) < j}) := by
    intro j
    apply descend (A.loc p).ιE gG
    have e1 : (fun i => (A.loc p).ιE ((x (gG j) - gG j) i)) = u j • (xp (gS j) - gS j) := by
      rw [smul_sub, ← map_smul, heq, hext]
      funext i
      simp [Places.bc]
    rw [e1]
    refine Submodule.smul_mem _ _ ?_
    refine (Submodule.span_le.mpr ?_) (hstep j)
    rintro _ ⟨i, hi, rfl⟩
    have h3 : gS i = ((hu i).unit⁻¹ : ((A.loc p).Ep)ˣ) • A.bc p (gG i) := by
      rw [← heq, Units.smul_def, smul_smul, (hu i).val_inv_mul, one_smul]
    rw [h3]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  have key2 : ∀ j : Fin (r + 1), ∃ l : Fin (r + 1) →₀ E,
      l ∈ Finsupp.supported E E {i : Fin (r + 1) | (i : ℕ) < j} ∧
      Finsupp.linearCombination E gG l = x (gG j) - gG j := fun j =>
    (Finsupp.mem_span_image_iff_linearCombination E).mp (key j)
  choose l hl hl' using key2
  have hz : ∀ i j : Fin (r + 1), ¬ ((i : ℕ) < j) → l j i = 0 := fun i j h =>
    (Finsupp.mem_supported' _ _).mp (hl j) i h
  refine ⟨Matrix.of fun i j => if i = j then 1 else l j i, ⟨fun i j hij => ?_, fun i => ?_⟩, fun j => ?_⟩
  · have hne : i ≠ j := fun h => by subst h; exact lt_irrefl _ hij
    simp only [Matrix.of_apply, if_neg hne]
    exact hz i j (by rw [Fin.lt_def] at hij; omega)
  · simp
  · have hjj : l j j = 0 := hz j j (lt_irrefl _)
    have hsplit : ∀ i, (if i = j then (1 : E) else l j i) = (if i = j then 1 else 0) + l j i := by
      intro i
      by_cases h : i = j
      · subst h; simp [hjj]
      · simp [h]
    have hlc := hl' j
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at hlc
    simp only [Matrix.of_apply, hsplit, add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, hlc]
    abel

theorem stab_unitriangular : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), ∀ x ∈ G.St, ∃ s s' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) ∧ ((∀ i j, j < i → s' i j = 0) ∧ (∀ i, s' i i = 1)) ∧ (∀ j, x (G.f j) = ∑ i, s i j • G.f i) ∧ ∀ j, x (G.f' j) = ∑ i, s' i j • G.f' i := by
  intro F E _ _ _ _ _ sig A r k G x hx
  obtain ⟨p⟩ : Nonempty (HeightOneSpectrum (𝓞 F)) := by
    obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 F)
    exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField F)⟩⟩
  obtain ⟨xp, hxp, hext⟩ := (show ∀ p, ∃ g' ∈ (G.S p).St, A.Ext p x g' from hx) p
  have hxp' := Subgroup.mem_inf.mp hxp
  have hunit : ∀ a : Fin (r + 1), IsUnit (algebraMap (A.loc p).Fp (A.loc p).Ep
      (((G.c p : (A.loc p).Fp)) ^ (r - (a : ℕ)))) := fun a =>
    ((G.c p).isUnit.pow _).map _
  obtain ⟨s, hs, hsx⟩ := frame_tri A p x xp hext G.f (G.S p).f _ hunit (G.f_eq p)
    (loc_step (G.S p) (G.S p).f (fun b hb => by
      rw [(G.S p).gram]
      have : b ≠ Fin.last r := fun h => by subst h; simp at hb
      simp [this]) xp hxp'.1)
  obtain ⟨s', hs', hsx'⟩ := frame_tri A p x xp hext G.f' (G.S p).f' _ hunit (G.f'_eq p)
    (loc_step (G.S p) (G.S p).f' (fun b hb => by
      rw [(G.S p).gram']
      have : b ≠ Fin.last r := fun h => by subst h; simp at hb
      simp [this]) xp hxp'.2)
  exact ⟨s, s', hs, hs', hsx, hsx'⟩

end GlobalTheory.HL.StTri
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HmUnit
section
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc

namespace GlobalTheory.HL.StdPlace

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

def coordLat {L : LocE F E} {r k : ℕ} (S : Frames L r k) : Submodule L.O S.V :=
  Submodule.span L.O (Set.range fun i => (Pi.single i 1 : S.V))

structure Good {L : LocE F E} {r k : ℕ} (S : Frames L r k) : Prop where
  gg : S.gg = false
  Hm_int : IsIntM L S.Hm
  Hm_unit : ∃ y ∈ L.O, S.Hm.det * y = 1
  f_int : ∀ a i, S.f a i ∈ L.O
  f'_int : ∀ a i, S.f' a i ∈ L.O
  es_int : ∀ a i, S.es a i ∈ L.O
  es'_int : ∀ a i, S.es' a i ∈ L.O
  G_unit : S.G ∈ L.O ∧ ∃ y ∈ L.O, S.G * y = 1
  D_unit : ∀ l, S.D l ≠ 0 → S.D l ∈ L.O ∧ ∃ y ∈ L.O, S.D l * y = 1

end GlobalTheory.HL.StdPlace
end
end

