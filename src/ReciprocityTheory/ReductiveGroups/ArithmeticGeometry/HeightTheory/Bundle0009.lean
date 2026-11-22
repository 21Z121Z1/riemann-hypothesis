import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0006

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AevalElimEqRenameLinearSubstitution
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

noncomputable def hTX5 {κ : Type} [Fintype κ] (f : MvPolynomial κ K) : ℝ :=
  ((∑ᶠ w : FinitePlace K, Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs w f)) +
      ∑ σ : K →+* ℂ, ReciprocityTheory.MultiplicativeHeights.torusMean (MvPolynomial.map σ f)) / (Module.finrank ℚ K : ℝ)

noncomputable def bilinearSubstitution {D N : ℕ} (f : KTp K D N) :
    MvPolynomial ((Fin (D + 2) × Fin (N + 1)) ⊕ Fin (D + 2)) K :=
  MvPolynomial.aeval (fun t : TVar D N =>
    MvPolynomial.X (Sum.inr 0) * MvPolynomial.X (Sum.inl (t.1.succ, t.2)) -
      MvPolynomial.X (Sum.inr t.1.succ) * MvPolynomial.X (Sum.inl (0, t.2))) f

section Gen

variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S] {P I : Type*} [Fintype P]
  [Fintype I]

theorem aeval_elim_mul_of_xhom (f : P → S) (g : I → S) (t : S) (n : ℕ) (Q : MvPolynomial (P ⊕ I) R)
    (hQ : ∀ s ∈ Q.support, ∑ i, s (Sum.inr i) = n) :
    MvPolynomial.aeval (Sum.elim f (fun i => t * g i)) Q =
      t ^ n * MvPolynomial.aeval (Sum.elim f g) Q := by
  conv_lhs => rw [Q.as_sum]
  conv_rhs => rw [Q.as_sum]
  simp only [map_sum, MvPolynomial.aeval_monomial, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp), Fintype.prod_sum_type,
    Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    hQ s hs]
  ring

end Gen

namespace Data

variable (d : Data K ι Ω WT A)

noncomputable def affineCoord (c : ι) (j : Fin (d.N + 1)) : Ω c :=
  ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c)

noncomputable def linearSubstitution (c : ι) :
    MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K →ₐ[K]
      MvPolynomial (Fin (d.D + 2) × Fin (d.N + 1)) (Ω c) :=
  MvPolynomial.aeval fun v =>
    match v with
    | Sum.inl p => MvPolynomial.X p
    | Sum.inr i => ∑ j, MvPolynomial.X (i, j) * MvPolynomial.C (d.affineCoord c j)

noncomputable def scaledSubstitution (c : ι) :
    MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K →ₐ[K]
      MvPolynomial (Option (Fin (d.D + 2) × Fin (d.N + 1))) (Ω c) :=
  MvPolynomial.aeval fun v =>
    match v with
    | Sum.inl p => MvPolynomial.X (some p)
    | Sum.inr i => MvPolynomial.X none *
        ∑ j, MvPolynomial.X (some (i, j)) * MvPolynomial.C (d.affineCoord c j)

theorem scaledSubstitution_eq (c : ι) : d.scaledSubstitution c = MvPolynomial.aeval (Sum.elim (fun p => MvPolynomial.X (some p))
    (fun i => MvPolynomial.X none *
      ∑ j, MvPolynomial.X (some (i, j)) * MvPolynomial.C (d.affineCoord c j))) := by
  unfold scaledSubstitution
  congr 1
  funext v
  cases v <;> rfl

theorem aeval_elim_eq_rename_linearSubstitution (c : ι)
    (Q : MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K) :
    MvPolynomial.aeval (Sum.elim (fun p => (MvPolynomial.X (some p) :
        MvPolynomial (Option (Fin (d.D + 2) × Fin (d.N + 1))) (Ω c)))
      (fun i => ∑ j, MvPolynomial.X (some (i, j)) * MvPolynomial.C (d.affineCoord c j))) Q =
      MvPolynomial.rename some (d.linearSubstitution c Q) := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp [linearSubstitution, MvPolynomial.algebraMap_eq]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    cases v <;> simp [linearSubstitution, map_mul, hp, map_sum]

theorem scaledSubstitution_of_homogeneous (c : ι) (n : ℕ)
    (Q : MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K)
    (hQ : ∀ s ∈ Q.support, ∑ i, s (Sum.inr i) = n) :
    d.scaledSubstitution c Q = MvPolynomial.X none ^ n * MvPolynomial.rename some (d.linearSubstitution c Q) := by
  rw [scaledSubstitution_eq, aeval_elim_mul_of_xhom _ _ _ n Q hQ, aeval_elim_eq_rename_linearSubstitution]

theorem eq_zero_of_xhom_zero (c : ι)
    (Q : MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K)
    (hQ : ∀ s ∈ Q.support, ∑ i, s (Sum.inr i) = 0) (h : d.linearSubstitution c Q = 0) : Q = 0 := by
  have hvars : (↑Q.vars : Set ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2))) ⊆ Set.range Sum.inl := by
    intro x hx
    rw [Finset.mem_coe, MvPolynomial.mem_vars] at hx
    obtain ⟨s, hs, hxs⟩ := hx
    cases x with
    | inl p => exact ⟨p, rfl⟩
    | inr i =>
      exfalso
      have h0 := (Finset.sum_eq_zero_iff.mp (hQ s hs)) i (Finset.mem_univ _)
      exact (Finsupp.mem_support_iff.mp hxs) h0
  obtain ⟨Q0, rfl⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range Q Sum.inl Sum.inl_injective hvars
  have hmap : ∀ q : MvPolynomial (Fin (d.D + 2) × Fin (d.N + 1)) K,
      MvPolynomial.aeval (fun p => (MvPolynomial.X p : MvPolynomial (Fin (d.D + 2) × Fin (d.N + 1)) (Ω c))) q =
        MvPolynomial.map (algebraMap K (Ω c)) q := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C a => simp [MvPolynomial.algebraMap_eq]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p v hp => simp [map_mul, hp]
  have e : d.linearSubstitution c (MvPolynomial.rename Sum.inl Q0) = MvPolynomial.map (algebraMap K (Ω c)) Q0 := by
    rw [← hmap, linearSubstitution, MvPolynomial.aeval_rename]
    rfl
  rw [e] at h
  have hQ0 : Q0 = 0 := MvPolynomial.map_injective _ (algebraMap K (Ω c)).injective (by rw [h, map_zero])
  rw [hQ0, map_zero]

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscDefs
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

noncomputable def unif (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : 𝓞 K :=
  open Classical in
  if h : ∃ ϖ : 𝓞 K, ϖ ∈ la.asIdeal ∧ ϖ ∉ la.asIdeal ^ 2 then h.choose else 0

noncomputable def gOrd (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (q : KTf K d.D d.N) : ℤ :=
  open Classical in
  if h : ∃ m : ℤ, ∃ u : Op d.D d.N la, IsUnit u ∧
      q = (algebraMap K (KTf K d.D d.N) ((unif la : 𝓞 K) : K)) ^ m * OpToKT d.D d.N la u
  then h.choose else 0

noncomputable def De (hd : d.AxH 𝒜) (h : d.S1) : KTf K d.D d.N :=
  Matrix.det (Matrix.of fun k l : Fin d.del => ∑ c,
    letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
    Algebra.trace (KTf K d.D d.N) (OmS (Ω c) d.D d.N)
      (d.bvecG hd.sel hd.a4.choose k c * d.bvecG hd.sel hd.a4.choose l c))

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HNormDefs
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

noncomputable def tOf (z : ReciprocityTheory.MultiplicativeHeights.BlockSphere d.D (d.N + 1)) : Fin d.D → Fin (d.N + 1) → ℂ :=
  fun i j => ReciprocityTheory.MultiplicativeHeights.spherePoint (z i) j

noncomputable def evT (sg : K →+* ℂ) (t0 : Fin (d.N + 1) → ℂ) (t : Fin d.D → Fin (d.N + 1) → ℂ)
    (q : KTp K d.D d.N) : ℂ :=
  MvPolynomial.eval₂ sg (fun v : TVar d.D d.N => Fin.cases (t0 v.2) (fun i => t i v.2) v.1) q

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.OffBaseSubstitution
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

namespace FractionFieldVariableLift

def eT (D N : ℕ) : TVar D N ≃ Fin (N + 1) ⊕ {v : TVar D N // v.1 ≠ 0} where
  toFun v := if h : v.1 = 0 then Sum.inl v.2 else Sum.inr ⟨v, h⟩
  invFun := Sum.elim (fun j => ((0 : Fin (D + 1)), j)) Subtype.val
  left_inv v := by
    by_cases h : v.1 = 0
    · simp only [h, dite_true, Sum.elim_inl]; exact Prod.ext h.symm rfl
    · simp [h]
  right_inv s := by
    rcases s with j | ⟨v, hv⟩
    · simp
    · simp [hv]

noncomputable def eS (D N : ℕ) (j0 : Fin (N + 1)) :
    SVar D N ≃ Fin (N + 1) ⊕ ({i : Fin (D + 1) // i ≠ 0} × Fin N) where
  toFun s := match s with
    | Sum.inl _ => Sum.inl j0
    | Sum.inr p => if h : p.1 = 0 then Sum.inl (j0.succAbove p.2) else Sum.inr (⟨p.1, h⟩, p.2)
  invFun t := match t with
    | Sum.inl j => if h : j = j0 then Sum.inl () else Sum.inr (0, (Fin.exists_succAbove_eq h).choose)
    | Sum.inr q => Sum.inr (q.1.1, q.2)
  left_inv s := by
    rcases s with u | ⟨i, k⟩
    · simp
    · by_cases h : i = 0
      · subst h
        have hne : j0.succAbove k ≠ j0 := Fin.succAbove_ne j0 k
        simp only [dite_true, hne, dite_false]
        congr
        exact Fin.succAbove_right_injective (Fin.exists_succAbove_eq hne).choose_spec
      · simp [h]
  right_inv t := by
    rcases t with j | ⟨⟨i, hi⟩, k⟩
    · by_cases h : j = j0
      · subst h; simp
      · simp only [h, dite_false, dite_true]
        exact congrArg Sum.inl (Fin.exists_succAbove_eq h).choose_spec
    · simp [hi]

noncomputable def hL (K : Type) [Field K] (D N : ℕ) :
    KTp K D N ≃+* MvPolynomial (Fin (N + 1)) (MvPolynomial {v : TVar D N // v.1 ≠ 0} K) :=
  (MvPolynomial.renameEquiv K (eT D N)).toRingEquiv.trans (MvPolynomial.sumRingEquiv K _ _)

noncomputable def hE (Ω : Type) [Field Ω] (D N : ℕ) (j0 : Fin (N + 1)) :
    MvPolynomial (SVar D N) Ω ≃+*
      MvPolynomial (Fin (N + 1)) (MvPolynomial ({i : Fin (D + 1) // i ≠ 0} × Fin N) Ω) :=
  (MvPolynomial.renameEquiv Ω (eS D N j0)).toRingEquiv.trans (MvPolynomial.sumRingEquiv Ω _ _)

variable {K : Type} [Field K] {Ω : Type} [Field Ω] {D N : ℕ}

theorem hL_C (r : K) : hL K D N (MvPolynomial.C r) = MvPolynomial.C (MvPolynomial.C r) := by
  simp [hL, MvPolynomial.sumRingEquiv_C, MvPolynomial.sumRingEquiv_X_inl, MvPolynomial.sumRingEquiv_X_inr]

theorem hL_X (v : TVar D N) : hL K D N (MvPolynomial.X v) =
    if h : v.1 = 0 then MvPolynomial.X v.2 else MvPolynomial.C (MvPolynomial.X ⟨v, h⟩) := by
  by_cases h : v.1 = 0
  · simp [hL, eT, h, MvPolynomial.sumRingEquiv_C, MvPolynomial.sumRingEquiv_X_inl, MvPolynomial.sumRingEquiv_X_inr]
  · simp [hL, eT, h, MvPolynomial.sumRingEquiv_C, MvPolynomial.sumRingEquiv_X_inl, MvPolynomial.sumRingEquiv_X_inr]

theorem hL_rename (p : MvPolynomial {v : TVar D N // v.1 ≠ 0} K) :
    hL K D N (MvPolynomial.rename Subtype.val p) = MvPolynomial.C p := by
  induction p using MvPolynomial.induction_on with
  | C a => rw [MvPolynomial.rename_C, hL_C]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  | mul_X p n hp => rw [map_mul, map_mul, hp, MvPolynomial.rename_X, hL_X, dif_neg n.2, map_mul]

theorem hE_C (j0 : Fin (N + 1)) (r : Ω) :
    hE Ω D N j0 (MvPolynomial.C r) = MvPolynomial.C (MvPolynomial.C r) := by
  simp [hE, MvPolynomial.sumRingEquiv_C, MvPolynomial.sumRingEquiv_X_inl, MvPolynomial.sumRingEquiv_X_inr]

end FractionFieldVariableLift

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]

namespace Data

variable (d : Data K ι Ω WT A)

noncomputable def offBaseSubstitution (c : ι) :
    MvPolynomial {v : TVar d.D d.N // v.1 ≠ 0} K →ₐ[K]
      MvPolynomial ({i : Fin (d.D + 1) // i ≠ 0} × Fin d.N) (Ω c) :=
  MvPolynomial.aeval fun v =>
    Fin.succAboveCases (α := fun _ => MvPolynomial ({i : Fin (d.D + 1) // i ≠ 0} × Fin d.N) (Ω c))
      (d.jc c) (-∑ k, MvPolynomial.X (⟨v.1.1, v.2⟩, k) * MvPolynomial.C (d.x c k))
      (fun k => MvPolynomial.X (⟨v.1.1, v.2⟩, k)) v.1.2

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.OrthogonalProjectorMulVecConjugate
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open Matrix NumberField ComplexConjugate NumberField.ComplexEmbedding
open scoped ComplexOrder Kronecker

section Gram

variable {K : Type} [Field K] [NumberField K] {r k m : ℕ}

theorem embeddingColumns_conjugate (σ : K →+* ℂ) (b : Fin k → Fin r → K) :
    hBm (conjugate σ) b = (hBm σ b).map (starRingEnd ℂ) := by
  ext l j
  simp [hBm, NumberField.ComplexEmbedding.conjugate_coe_eq]

private lemma map_star_inv {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    A⁻¹.map (starRingEnd ℂ) = (A.map (starRingEnd ℂ))⁻¹ := by
  have h : ∀ M : Matrix (Fin n) (Fin n) ℂ, M.map (starRingEnd ℂ) = Mᴴᵀ := by
    intro M
    ext i j
    simp [conjTranspose_apply]
  rw [h, h, ← transpose_nonsing_inv, conjTranspose_nonsing_inv]

theorem orthogonalProjector_conjugate (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b) :
    hPm (conjugate σ) b = (hPm σ b).map (starRingEnd ℂ) := by
  unfold hPm
  rw [embeddingColumns_conjugate σ b]
  have h1 : ((hBm σ b).map (starRingEnd ℂ))ᴴ = (hBm σ b)ᴴ.map (starRingEnd ℂ) := by
    ext i j
    simp [conjTranspose_apply]
  rw [h1, ← Matrix.map_mul, ← map_star_inv, Matrix.map_sub _ (map_sub _),
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_mul, Matrix.map_mul]

theorem orthogonalProjector_mulVec_conjugate (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b)
    (x : Fin r → K) :
    (hPm (conjugate σ) b *ᵥ fun l => (conjugate σ) (x l)) = star (hPm σ b *ᵥ fun l => σ (x l)) := by
  rw [orthogonalProjector_conjugate σ hb]
  ext i
  simp [Matrix.mulVec, dotProduct, NumberField.ComplexEmbedding.conjugate_coe_eq, map_sum,
    mul_comm]

theorem conj_sum_projected_inner (b : Fin k → Fin r → K) (hb : LinearIndependent K b) (a a' : K)
    (x y : Fin r → K) :
    conj (∑ σ : K →+* ℂ, conj (σ a) * σ a' *
        (star (hPm σ b *ᵥ fun l => σ (x l)) ⬝ᵥ (hPm σ b *ᵥ fun l => σ (y l)))) =
      ∑ σ : K →+* ℂ, conj (σ a) * σ a' *
        (star (hPm σ b *ᵥ fun l => σ (x l)) ⬝ᵥ (hPm σ b *ᵥ fun l => σ (y l))) := by
  rw [map_sum]
  have hinv : Function.Involutive (NumberField.ComplexEmbedding.conjugate (K := K)) := by
    intro σ
    ext z
    simp [NumberField.ComplexEmbedding.conjugate_coe_eq]
  refine Fintype.sum_bijective _ hinv.bijective _ _ (fun σ => ?_)
  rw [orthogonalProjector_mulVec_conjugate σ hb x, orthogonalProjector_mulVec_conjugate σ hb y,
    NumberField.ComplexEmbedding.conjugate_coe_eq, NumberField.ComplexEmbedding.conjugate_coe_eq]
  simp [dotProduct, map_sum, mul_comm, mul_left_comm]

theorem quotientGram_conjTranspose (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b)
    (c : Fin m → Fin r → K) : (ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c)ᴴ = ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c := by
  unfold ReciprocityTheory.MultiplicativeHeights.quotGramC
  simp only [gramMatrix_eq_embeddingColumns, crossGram_eq_embeddingColumns, conjTranspose_sub, conjTranspose_mul,
    conjTranspose_conjTranspose, conjTranspose_nonsing_inv, Matrix.mul_assoc]

theorem quotientGram_det_re_eq (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b)
    (c : Fin m → Fin r → K) :
    (((ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c).det.re : ℝ) : ℂ) = (ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c).det := by
  have h := quotientGram_conjTranspose σ hb c
  have h2 : star (ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c).det = (ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c).det := by
    rw [← det_conjTranspose, h]
  exact Complex.conj_eq_iff_re.mp h2

end Gram

section GramDet

variable {K : Type} [Field K] [NumberField K] {r k m : ℕ}

noncomputable def hwv (b : Fin k → Fin r → K) (c : Fin m → Fin r → K) :
    Fin m × Module.Free.ChooseBasisIndex ℤ (𝓞 K) → EuclideanSpace ℝ (hIdx K r) :=
  fun p => hpv b (integralBasis K p.2 • c p.1)

theorem det_gram_projectedLatticeVectors (b : Fin k → Fin r → K) (hb : LinearIndependent K b)
    (c : Fin m → Fin r → K) :
    (gram ℝ (hwv b c)).det =
      |(discr K : ℝ)| ^ m * ∏ σ : K →+* ℂ, (ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c).det.re := by
  classical
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) = Fintype.card (K →+* ℂ) := by
    rw [NumberField.Embeddings.card, ← NumberField.RingOfIntegers.rank,
      Module.finrank_eq_card_chooseBasisIndex]
  obtain ⟨e⟩ : Nonempty (Module.Free.ChooseBasisIndex ℤ (𝓞 K) ≃ (K →+* ℂ)) :=
    ⟨Fintype.equivOfCardEq hcard⟩
  obtain ⟨Ω, hΩ⟩ : ∃ Ω : Matrix (Module.Free.ChooseBasisIndex ℤ (𝓞 K))
      (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) ℂ, Ω = Matrix.of fun q p => e q (integralBasis K p) :=
    ⟨_, rfl⟩

  have hent : ∀ j p j' p', ((gram ℝ (hwv b c) (j, p) (j', p') : ℝ) : ℂ) =
      ∑ q, star (Ω q p) * ReciprocityTheory.MultiplicativeHeights.quotGramC 1 (e q) b c j j' * Ω q p' := by
    intro j p j' p'
    rw [Matrix.gram_apply]
    simp only [hwv]
    rw [inner_projectedVector_smul, Complex.conj_eq_iff_re.mp (conj_sum_projected_inner b hb _ _ _ _)]
    symm
    refine Fintype.sum_equiv e _ _ (fun q => ?_)
    rw [quotientGram_eq_projector (e q) hb c j j', hΩ]
    simp only [Matrix.of_apply]
    rw [show star ((e q) (integralBasis K p)) = conj ((e q) (integralBasis K p)) from rfl]
    ring
  have hmat : (gram ℝ (hwv b c)).map Complex.ofRealHom =
      ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ Ω)ᴴ *
        Matrix.blockDiagonal (fun q => ReciprocityTheory.MultiplicativeHeights.quotGramC 1 (e q) b c) *
        ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ Ω) := by
    ext ⟨j, p⟩ ⟨j', p'⟩
    rw [Matrix.map_apply, Complex.ofRealHom_eq_coe, hent]
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
      Matrix.kroneckerMap_apply, Matrix.blockDiagonal_apply, Matrix.one_apply, ite_mul, mul_ite,
      Finset.sum_ite_eq, Finset.sum_ite_eq', apply_ite (starRingEnd ℂ), map_zero]
  have hdet : ((gram ℝ (hwv b c)).det : ℂ) =
      star ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ Ω).det *
        (Matrix.blockDiagonal (fun q => ReciprocityTheory.MultiplicativeHeights.quotGramC 1 (e q) b c)).det *
        ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ Ω).det := by
    have h := RingHom.map_det Complex.ofRealHom (gram ℝ (hwv b c))
    rw [Complex.ofRealHom_eq_coe] at h
    rw [h, RingHom.mapMatrix_apply, hmat, det_mul, det_mul, det_conjTranspose]
  have hT : ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ Ω).det = Ω.det ^ m := by
    simp [Matrix.det_kronecker]
  have hdisc : Ω.det ^ 2 = (discr K : ℂ) := by
    have h1 := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ (integralBasis K)
      (e.trans (RingHom.equivRatAlgHom K ℂ))
    rw [← NumberField.coe_discr] at h1
    have h2 : Algebra.embeddingsMatrixReindex ℚ ℂ (integralBasis K)
        (e.trans (RingHom.equivRatAlgHom K ℂ)) = Ωᵀ := by
      ext i j
      simp [Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix, hΩ, RingHom.equivRatAlgHom]
    rw [h2, det_transpose] at h1
    rw [← h1]
    simp
  have hnorm : star Ω.det * Ω.det = ((|(discr K : ℝ)| : ℝ) : ℂ) := by
    rw [show star Ω.det = conj Ω.det from rfl, Complex.conj_mul', ← Complex.ofReal_pow, ← norm_pow,
      hdisc, Complex.norm_intCast]
  apply Complex.ofReal_injective
  rw [hdet, hT, Matrix.det_blockDiagonal]
  push_cast
  rw [← Equiv.prod_comp e (fun σ => (((ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c).det.re : ℝ) : ℂ))]
  simp_rw [quotientGram_det_re_eq _ hb c]
  rw [star_pow, ← hnorm]
  ring

end GramDet

end ReciprocityTheory.ChartRestriction.G.T0
end

