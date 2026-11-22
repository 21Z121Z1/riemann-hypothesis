import Development.WeilBound.CoreStatements.VolumeEquality.Bundle0006
import Development.WeilBound.CoreStatements.EqualVolumeCompactOpens.RmulScalOne
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0165
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SkewHermitianFormExists
import Development.WeilBound.CoreStatements.VolumeEquality.Bundle0012
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PIntNumBaseChange
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0013

-- bundled from Development.WeilBound.CoreStatements.VolumeEquality.BallVolModel
section
noncomputable section

namespace SheetDecomposition

open NumberField Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.Dict
  GlobalTheory.CompanionTheory.Ar.Cusp.DictMeas GlobalTheory.CompanionTheory.Ar.Cmp PositivityTheory.EqVol

theorem qconj_eq {E : Type} [Field E] [NumberField E] [IsCMField E] (x : E) :
    GroundTheory.Automorphic.conj (maximalRealSubfield E) E x = IsCMField.complexConj E x :=
  HermTrace.quadConj_eq_complexConj x

theorem sesq_eq_herm {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}
    (h : GroundTheory.Automorphic.HermitianForm (maximalRealSubfield E) E (Fin N → E)) (r : E) (x y : Fin N → E) :
    herm (r • (GroundTheory.Automorphic.gram h.toSesq (Pi.basisFun E (Fin N)))ᵀ) x y = r * h.toSesq y x := by
  rw [GroundTheory.Automorphic.sesq_eq_sum h.toSesq (Pi.basisFun E (Fin N)), herm, Finset.sum_comm]
  simp only [Finset.mul_sum, qconj_eq, Pi.basisFun_repr, Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul, cc]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem sgI_sq (j j' : ℕ) : sgI j j' * sgI j j' = 1 := by
  simp [sgI, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

theorem stdModel_of (h : StdZ) : StdModel := by
  intro E _ _ _ Ψ _ _ j j' n g Λ _ _ H F ξ c₀ hc₀ hξ
  obtain ⟨C⟩ := GlobalTheory.T.exists_lattice_embedding E Ψ j j' n g Λ H F
  obtain ⟨A, hA, Z, hbij, hmeas, hZ⟩ := h E Ψ j j' n g Λ F C
  obtain ⟨τ₀⟩ := ‹Nonempty Ψ›
  have hc := C.c_pos
  have hc₀' : (c₀ : ℂ) ≠ 0 := by exact_mod_cast hc₀.ne'
  have hξ0 : ξ ≠ 0 := fun h0 => by
    have := hξ τ₀
    rw [h0, map_zero] at this
    exact mul_ne_zero Complex.I_ne_zero hc₀' this.symm
  set r : E := C.xi / ξ with hr
  have hsr : ∀ τ, embOf (F.σ τ) r = ((C.c / c₀ * C.eps τ : ℝ) : ℂ) := fun τ => by
    rw [hr, map_div₀, C.xi_eq, hξ]
    push_cast
    field_simp
  have heps : ∀ τ, C.eps τ ≠ 0 := fun τ h0 => by
    have := C.eps_sq τ
    rw [h0] at this
    norm_num at this
  have hsr0 : ∀ τ, embOf (F.σ τ) r ≠ 0 := fun τ => by
    rw [hsr]
    exact_mod_cast mul_ne_zero (div_pos hc hc₀).ne' (heps τ)
  have hr0 : r ≠ 0 := fun h0 => hsr0 τ₀ (by rw [h0, map_zero])
  have hcr : cc r = r := (embOf (F.σ τ₀)).injective (by
    rw [cc, IsCMField.complexEmbedding_complexConj, hsr, Complex.conj_ofReal])
  set g₀ := GroundTheory.Automorphic.gram C.h.toSesq (Pi.basisFun E (Fin (j + j'))) with hg₀
  have hGs : ∀ τ, ((r • g₀ᵀ).map (embOf (F.σ τ)))ᵀ = embOf (F.σ τ) r • C.gr τ := fun τ => by
    ext a b
    simp [LatEmb.gr, hg₀]
  have hGs' : ∀ τ, ((r • g₀ᵀ).map (embOf (F.σ τ)))ᵀ = ((C.c / c₀ : ℝ) : ℂ) • C.sgr τ := fun τ => by
    rw [hGs, hsr, LatEmb.sgr, smul_smul, Complex.ofReal_mul]
  let e : Λ →ₗ[𝓞 E] (Fin (j + j') → E) :=
    { toFun := C.e, map_add' := C.e.map_add, map_smul' := fun a x => C.e_smul a x }
  let k : ℝ := Real.sqrt (c₀ / C.c)
  have hk : 0 < k := Real.sqrt_pos.2 (div_pos hc₀ hc)
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hkk : (k : ℂ) * ((C.c / c₀ : ℝ) : ℂ) * k = 1 := by
    have : k * (C.c / c₀) * k = 1 := by
      have h1 : k * k = c₀ / C.c := Real.mul_self_sqrt (div_pos hc₀ hc).le
      rw [mul_right_comm, h1]
      field_simp
    exact_mod_cast this
  have hl : ∀ τ, C.cinv (A τ) τ * A τ = 1 := fun τ => by
    rw [LatEmb.cinv, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (A τ)ᴴ, hA, sgI_sq]
  have hrr : ∀ τ, A τ * C.cinv (A τ) τ = 1 := fun τ =>
    (Matrix.mul_eq_one_comm_of_equiv finSumFinEquiv).1 (hl τ)
  have hform : ∀ x y, ((F.form x y : ℤ) : ℚ) = EFf (-ξ) (r • g₀ᵀ) (e x) (e y) := fun x y => by
    rw [C.form_eq, EFf, hg₀, sesq_eq_herm, neg_neg, ← mul_assoc, hr, mul_div_cancel₀ _ hξ0]
    rfl
  refine ⟨r • g₀ᵀ, e, fun τ => (k : ℂ) • A τ, fun τ => (k : ℂ)⁻¹ • C.cinv (A τ) τ, Z, fun a b => ?_, ?_, C.e_inj, ⟨?_, ?_⟩,
    hform, fun τ => ⟨?_, ?_, ?_⟩, hbij, hmeas, fun γ hγ δ hδ t ht t' ht' => ?_⟩
  · have h1 : cc (g₀ b a) = g₀ a b := by
      rw [cc, ← qconj_eq]
      exact C.h.isSymm.eq _ _
    show cc (r * g₀ b a) = r * g₀ a b
    rw [← h1]
    conv_rhs => rw [← hcr]
    exact map_mul (IsCMField.complexConj E) _ _
  · rw [det_smul, det_transpose]
    exact mul_ne_zero (pow_ne_zero _ hr0) (GroundTheory.Automorphic.isUnit_det_gram C.h _).ne_zero
  · have := (F.R 0).fin
    have : Module.Finite (𝓞 E) Λ := Module.Finite.of_restrictScalars_finite ℤ _ _
    exact Module.Finite.iff_fg.1 inferInstance
  · exact C.integral.isLattice.span_eq_top
  · rw [hGs', conjTranspose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul,
      hA, smul_smul, smul_smul]
    have : star (k : ℂ) * (k : ℂ) * ((C.c / c₀ : ℝ) : ℂ) = 1 := by
      rw [Complex.star_def, Complex.conj_ofReal, mul_right_comm, hkk]
    rw [this, one_smul]
  · rw [Matrix.smul_mul, Matrix.mul_smul, hl, smul_smul, inv_mul_cancel₀ hk', one_smul]
  · rw [Matrix.smul_mul, Matrix.mul_smul, hrr, smul_smul, mul_inv_cancel₀ hk', one_smul]
  · have hγ' : (γ : Matrix (Fin (j + j')) (Fin (j + j')) E)ᵀ * (r • g₀ᵀ) *
        (γ : Matrix (Fin (j + j')) (Fin (j + j')) E).map (ccH E) = r • g₀ᵀ := hγ
    have hrho : rho (fun τ => embOf (F.σ τ)) (fun τ => (k : ℂ) • A τ) (fun τ => (k : ℂ)⁻¹ • C.cinv (A τ) τ) γ =
        rho (fun τ => embOf (F.σ τ)) A (fun τ => C.cinv (A τ) τ) γ := by
      funext τ
      simp only [rho]
      rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hk', one_smul]
    rw [hrho]
    refine hZ γ δ hδ (fun x y => ?_) (fun τ => ?_) t ht t' ht'
    · have h1 := hform (δ x) (δ y)
      rw [hδ, hδ, EFf, herm_mulVec', hγ', ← EFf, ← hform] at h1
      exact_mod_cast h1
    · have h1 := congrArg (fun M => (M.map (embOf (F.σ τ)))ᵀ) hγ'
      have h2 : (((γ : Matrix (Fin (j + j')) (Fin (j + j')) E).map (ccH E)).map (embOf (F.σ τ)))ᵀ =
          ((γ : Matrix (Fin (j + j')) (Fin (j + j')) E).map (embOf (F.σ τ)))ᴴ := by
        ext a b
        exact IsCMField.complexEmbedding_complexConj E (embOf (F.σ τ)) ((γ : Matrix (Fin (j + j')) (Fin (j + j')) E) b a)
      simp only [Matrix.map_mul, transpose_mul] at h1
      rw [hGs, h2, ← Matrix.transpose_map, transpose_transpose, Matrix.smul_mul, Matrix.mul_smul] at h1
      rw [Matrix.mul_assoc]
      exact smul_right_injective _ (hsr0 τ) h1

end SheetDecomposition
end
end

-- bundled from Development.WeilBound.CoreStatements.VolumeEquality.DegPushFibA
section
noncomputable section

namespace SheetDecomposition.Fib

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal pointConeMap intNum)

theorem ker_map {σ τ : Type} (k : Type) [Field k] [Algebra ℚ k] (g : σ → MvPolynomial τ ℚ) :
    RingHom.ker (aeval (fun s => map (algebraMap ℚ k) (g s)) : MvPolynomial σ k →ₐ[k] MvPolynomial τ k) =
      (RingHom.ker (aeval g : MvPolynomial σ ℚ →ₐ[ℚ] MvPolynomial τ ℚ)).map (map (algebraMap ℚ k)) := by
  classical
  have hc : ∀ f : MvPolynomial σ ℚ, (aeval (fun s => map (algebraMap ℚ k) (g s)) : MvPolynomial σ k →ₐ[k] MvPolynomial τ k)
      (map (algebraMap ℚ k) f) = map (algebraMap ℚ k) (aeval g f) := fun f => by
    induction f using MvPolynomial.induction_on with
    | C a => simp [algebraMap_eq]
    | add f g hf hg => simp only [map_add, hf, hg]
    | mul_X f i hf => simp only [map_mul, hf, map_X, aeval_X]
  refine le_antisymm (fun f hf => ?_) (Ideal.map_le_iff_le_comap.2 fun f hf => ?_)
  · let b := Module.Basis.ofVectorSpace ℚ k
    let T : Finset _ := f.support.biUnion fun m => (b.repr (coeff m f)).support
    let F : _ → MvPolynomial σ ℚ := fun i => ∑ m ∈ f.support, monomial m (b.repr (coeff m f) i)
    have hf' : f = ∑ i ∈ T, C (b i) * map (algebraMap ℚ k) (F i) := by
      conv_lhs => rw [f.as_sum]
      simp only [F, map_sum, Finset.mul_sum, map_monomial, C_mul_monomial]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun m hm => ?_
      rw [← map_sum (monomial m)]
      congr 1
      conv_lhs => rw [← b.linearCombination_repr (coeff m f), Finsupp.linearCombination_apply,
        Finsupp.sum_of_support_subset _ (Finset.subset_biUnion_of_mem (fun m => (b.repr (coeff m f)).support) hm)
          (fun i a => a • b i) (fun _ _ => zero_smul _ _)]
      exact Finset.sum_congr rfl fun i _ => by rw [Algebra.smul_def, mul_comm]
    have h0 : ∑ i ∈ T, C (b i) * map (algebraMap ℚ k) (aeval g (F i)) = 0 := by
      rw [RingHom.mem_ker, hf'] at hf
      simpa only [map_sum, map_mul, hc, aeval_C, algebraMap_eq] using hf
    have h1 : ∀ i ∈ T, aeval g (F i) = 0 := fun i hi => by
      ext m
      have := congrArg (coeff m) h0
      simp only [coeff_sum, coeff_C_mul, coeff_map, coeff_zero] at this
      refine linearIndependent_iff'.1 b.linearIndependent T (fun i => coeff m (aeval g (F i))) ?_ i hi
      rw [← this]
      exact Finset.sum_congr rfl fun i _ => by rw [Algebra.smul_def, mul_comm]
    rw [hf']
    exact Ideal.sum_mem _ fun i hi => Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (h1 i hi))
  · rw [Ideal.mem_comap, RingHom.mem_ker, hc, (RingHom.mem_ker.1 hf : aeval g f = 0), map_zero]

variable {S : Type} {r : S → ℕ} {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω]

abbrev Ent (r : S → ℕ) : Type := Σ s, {lk : Fin (r s) × Fin (r s) // lk.2 < lk.1}

def genU (r : S → ℕ) (s : S) : Matrix (Fin (r s)) (Fin (r s)) (MvPolynomial (Ent r) ℚ) := fun l m =>
  if h : m < l then X ⟨s, ⟨(l, m), h⟩⟩ else if l = m then 1 else 0

def genMinor (r : S → ℕ) (x : Σ b : (Σ s, Fin (r s)), PlIx r b) : MvPolynomial (Ent r) ℚ :=
  Matrix.det (Matrix.of fun a b : Fin (x.1.2 + 1) => genU r x.1.1 (x.2 a) (Fin.castLE x.1.2.2 b))

def genCone (r : S → ℕ) (x : Σ b : (Σ s, Fin (r s)), PlIx r b) : MvPolynomial ((Σ s, Fin (r s)) ⊕ Ent r) ℚ :=
  rename Sum.inr (genMinor r x) * X (Sum.inl x.1)

def uNum (r : S → ℕ) {n : ℕ} (a : Fin n → (Σ s, Fin (r s)) → ℤ) : ℤ :=
  @intNum _ (fun _ _ => Classical.propDecidable _) (PlIx r) ℚ _
    (RingHom.ker (aeval (genCone r) : MvPolynomial _ ℚ →ₐ[ℚ] MvPolynomial _ ℚ)) n a

theorem plPt_eq [Algebra ℚ Ω] (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) (h1 : ∀ s m, u s m m = 1)
    (h0 : ∀ s l m, l < m → u s l m = 0) (x) :
    plPt u x = aeval (fun q : Ent r => u q.1 q.2.1.1 q.2.1.2) (genMinor r x) := by
  have e : ∀ s l m, aeval (fun q : Ent r => u q.1 q.2.1.1 q.2.1.2) (genU r s l m) = u s l m := fun s l m => by
    unfold genU
    split_ifs with h h'
    · simp
    · subst h'; simp [h1]
    · rw [map_zero, h0 s l m (lt_of_le_of_ne (not_lt.1 h) h')]
  unfold plPt genMinor
  rw [AlgHom.map_det]
  congr 1
  ext a b
  exact (e _ _ _).symm

theorem pointIdeal_plPt [CharZero k] (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) {d : ℕ} (h : IsGenU k u d) :
    pointIdeal k (plPt u) =
      (RingHom.ker (aeval (genCone r) : MvPolynomial _ ℚ →ₐ[ℚ] MvPolynomial _ ℚ)).map (map (algebraMap ℚ k)) := by
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
  let φ : MvPolynomial (Ent r) k →ₐ[k] Ω := aeval fun q : Ent r => u q.1 q.2.1.1 q.2.1.2
  have hφ : Function.Injective φ := h.2.2.1
  let Θ : MvPolynomial ((Σ s, Fin (r s)) ⊕ Ent r) k →+* MvPolynomial (Σ s, Fin (r s)) Ω :=
    (map φ.toRingHom).comp (sumAlgEquiv k _ _).toRingHom
  have hΘ : Function.Injective Θ := (map_injective _ hφ).comp (sumAlgEquiv k _ _).injective
  have hr : ∀ f : MvPolynomial (Ent r) ℚ, Θ (map (algebraMap ℚ k) (rename Sum.inr f)) =
      C (aeval (fun q : Ent r => u q.1 q.2.1.1 q.2.1.2) f) := fun f => by
    induction f using MvPolynomial.induction_on with
    | C a => simp [Θ, φ]
    | add f g hf hg => simp only [map_add, hf, hg]
    | mul_X f i hf => simp only [map_mul, hf]; simp [Θ, φ]
  have key : (pointConeMap k (plPt u) : MvPolynomial _ k →+* MvPolynomial _ Ω) = Θ.comp
      (aeval (fun s => map (algebraMap ℚ k) (genCone r s)) : MvPolynomial _ k →ₐ[k] MvPolynomial _ k).toRingHom := by
    refine ringHom_ext (fun a => ?_) fun x => ?_
    · simp [pointConeMap, Θ, φ, algebraMap_eq]
    · simp only [pointConeMap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X, RingHom.comp_apply, genCone, map_mul, hr, plPt_eq u h.1 h.2.1]
      simp [Θ]
  rw [← ker_map]
  ext f
  rw [pointIdeal, RingHom.mem_ker, RingHom.mem_ker, ← map_eq_zero_iff Θ hΘ]
  exact (RingHom.congr_fun key f).congr_left

theorem inum_plPt [Fintype S] [CharZero k] (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) {d : ℕ} (h : IsGenU k u d) {n : ℕ}
    (a : Fin n → (Σ s, Fin (r s)) → ℤ) : inum k (plPt u) a = uNum r a := by
  unfold inum uNum
  rw [pointIdeal_plPt u h]
  exact (@GroundTheory.Heights₂.Heights.FieldNumbers.IntNumBaseChange.intersectionNumber_baseChange.1 ℚ _ k _ _ _ _ (fun _ _ => Classical.propDecidable _)
    (PlIx r) _ _).2 n a

def rowIx {n : ℕ} (m l : Fin n) : Fin (m + 1) → Fin n := fun a => if a = Fin.last m then l else Fin.castLE m.2 a

theorem plPt_row (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) (h1 : ∀ s m, u s m m = 1)
    (h0 : ∀ s l m, l < m → u s l m = 0) (s : S) (m l : Fin (r s)) : plPt u ⟨⟨s, m⟩, rowIx m l⟩ = u s l m := by
  unfold plPt
  rw [Matrix.det_of_isLowerTriangular]
  · rw [Fin.prod_univ_castSucc, Finset.prod_eq_one, one_mul]
    · simp only [Matrix.of_apply, rowIx, if_true]
      rfl
    · intro a _
      simp only [Matrix.of_apply, rowIx, if_neg (Fin.castSucc_lt_last a).ne, h1]
  · intro a b hab
    have hab' : a < b := hab
    simp only [Matrix.of_apply, rowIx, if_neg (hab'.trans_le (Fin.le_last b)).ne]
    exact h0 _ _ _ hab'

theorem plPt_ne (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) (h1 : ∀ s m, u s m m = 1)
    (h0 : ∀ s l m, l < m → u s l m = 0) (b) : ∃ i, plPt u ⟨b, i⟩ ≠ 0 :=
  ⟨rowIx b.2 b.2, by rw [show b = ⟨b.1, b.2⟩ from rfl, plPt_row u h1 h0, h1]; exact one_ne_zero⟩

theorem fnField_plPt [Fintype S] (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) (h1 : ∀ s m, u s m m = 1)
    (h0 : ∀ s l m, l < m → u s l m = 0) : fnField k (plPt u) =
      IntermediateField.adjoin k (Set.range fun q : Σ s, Fin (r s) × Fin (r s) => u q.1 q.2.1 q.2.2) := by
  refine le_antisymm (IntermediateField.adjoin_le_iff.2 ?_) (IntermediateField.adjoin_le_iff.2 ?_)
  · have : ∀ x, plPt u x ∈ IntermediateField.adjoin k
        (Set.range fun q : Σ s, Fin (r s) × Fin (r s) => u q.1 q.2.1 q.2.2) := fun x => by
      unfold plPt
      rw [Matrix.det_apply']
      exact sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun a _ =>
        IntermediateField.subset_adjoin _ _ ⟨⟨_, _, _⟩, rfl⟩)
    rintro _ ⟨p, q, -, rfl⟩
    exact div_mem (this p) (this q)
  · rintro _ ⟨⟨s, l, m⟩, rfl⟩
    refine IntermediateField.subset_adjoin _ _ ⟨⟨⟨s, m⟩, rowIx m l⟩, ⟨⟨s, m⟩, rowIx m m⟩, rfl, ?_⟩
    rw [plPt_row u h1 h0, plPt_row u h1 h0, h1, div_one]

theorem vdeg_plDeg [Fintype S] (O : ValuationSubring Ω) (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) (b : Σ s, Fin (r s)) :
    vdeg O (plPt u) (plDeg b) = (Finset.univ.sup fun i => O.valuation (plPt u ⟨b, i⟩))⁻¹ := by
  unfold vdeg
  rw [Finset.prod_eq_single b (fun b' _ h => by simp [plDeg, h]) (by simp)]
  simp [plDeg]

theorem trdeg_eq [Fintype S] (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) {d : ℕ} (h : IsGenU k u d) :
    Algebra.trdeg k Ω = Nat.card (Ent r) := by
  obtain ⟨h1, h0, hi, hd, hf⟩ := h
  have e : IntermediateField.adjoin k (Set.range fun q : Σ s, Fin (r s) × Fin (r s) => u q.1 q.2.1 q.2.2) =
      IntermediateField.adjoin k (Set.range fun q : Ent r => u q.1 q.2.1.1 q.2.1.2) := by
    refine le_antisymm (IntermediateField.adjoin_le_iff.2 ?_) (IntermediateField.adjoin.mono _ _ _ ?_)
    · rintro _ ⟨⟨s, l, m⟩, rfl⟩
      rcases lt_trichotomy l m with h | h | h
      · simp only [h0 s l m h]; exact zero_mem _
      · subst h; simp only [h1]; exact one_mem _
      · exact IntermediateField.subset_adjoin _ _ ⟨⟨s, (l, m), h⟩, rfl⟩
    · rintro _ ⟨⟨s, ⟨l, m⟩, h⟩, rfl⟩
      exact ⟨⟨s, l, m⟩, rfl⟩
  rw [e] at hf
  have := Module.finite_of_finrank_pos (hf ▸ hd)
  have hb : IsTranscendenceBasis k fun q : Ent r => u q.1 q.2.1.1 q.2.1.2 :=
    hi.isTranscendenceBasis_iff_isAlgebraic.2 (IntermediateField.isAlgebraic_adjoin_iff_top.1 inferInstance)
  rw [← hb.cardinalMk_eq_trdeg]
  exact (Nat.cast_card).symm

end SheetDecomposition.Fib
end
end

-- bundled from Development.WeilBound.CoreStatements.VolumeEquality.DegPushNumEq
section
noncomputable section

namespace SheetDecomposition

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI.I4 GroundTheory.Heights₂.Heights

variable {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] {K : Type} [Fintype K] {ι : K → Type} [∀ b, Fintype (ι b)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ b, Fintype (ι' b)]

theorem inum_eq_zero_of_valEq_zero (h3 : UnitZero) {z : (Σ b, ι b) → Ω} {d : ℕ} (hz : IsPt k z d) (ht : fnField k z = ⊤)
    (a : Fin d → K → ℤ) (i : Fin d) (h : ValEq k z (a i) z 0) : inum k z a = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by have := i.pos; omega⟩
  have key : inum k z a = inum k z (a ∘ Equiv.swap i (Fin.last n)) := by
    unfold inum NumbersDVR.intNum
    rw [FieldNumbers.mixedDiff_comp_perm]
  rw [key, ← Fin.snoc_init_self (a ∘ Equiv.swap i (Fin.last n))]
  apply h3 k Ω K ι z n _ _ hz ht
  show ValEq k z (a (Equiv.swap i (Fin.last n) (Fin.last n))) z 0
  rw [Equiv.swap_apply_right]
  exact h

theorem inum_update (h1 : PtDim) (h3 : UnitZero) {z : (Σ b, ι b) → Ω} {d : ℕ} (hz : IsPt k z d) (ht : fnField k z = ⊤)
    (a : Fin d → K → ℤ) (i : Fin d) (b : K → ℤ) (h : ValEq k z b z (a i)) : inum k z (Function.update a i b) = inum k z a := by
  classical
  obtain ⟨hprime, hdim, -⟩ := h1 k Ω K ι z d hz
  have hadd := FieldNumbers.IntNumAdd.full k K ι (NumbersDVR.pointIdeal k z) hprime.multiHomog hprime.relevant d hdim
    a i (b - a i) (a i)
  rw [sub_add_cancel, Function.update_eq_self] at hadd
  have hz0 : inum k z (Function.update a i (b - a i)) = 0 := by
    apply inum_eq_zero_of_valEq_zero h3 hz ht _ i
    rw [Function.update_self]
    obtain ⟨ρ, hρ, hO⟩ := h
    refine ⟨ρ, hρ, fun O hk => ?_⟩
    have e := hO O hk
    have hne : ∀ c : K, (Finset.univ.sup fun j : ι c => O.valuation (z ⟨c, j⟩)) ≠ 0 := by
      intro c h0
      obtain ⟨j, hj⟩ := hz.1 c
      have hle : O.valuation (z ⟨c, j⟩) ≤ 0 :=
        h0 ▸ Finset.le_sup (f := fun j : ι c => O.valuation (z ⟨c, j⟩)) (Finset.mem_univ j)
      exact hj ((Valuation.zero_iff _).mp (le_antisymm hle zero_le'))
    have hv : vdeg O z (b - a i) * vdeg O z (a i) = vdeg O z b := by
      unfold vdeg
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun c _ => ?_
      rw [Pi.sub_apply, ← zpow_add₀ (hne c), sub_add_cancel]
    have hne' : vdeg O z (a i) ≠ 0 := by
      unfold vdeg
      exact Finset.prod_ne_zero_iff.mpr fun c _ => zpow_ne_zero _ (hne c)
    have h0 : vdeg O z (0 : K → ℤ) = 1 := by
      unfold vdeg
      simp
    rw [h0, mul_one]
    apply mul_right_cancel₀ hne'
    rw [hv, e]
  unfold inum at hz0 ⊢
  convert hadd using 1
  rw [hz0, zero_add]

theorem inum_congr (h1 : PtDim) (h3 : UnitZero) {z : (Σ b, ι b) → Ω} {d : ℕ} (hz : IsPt k z d) (ht : fnField k z = ⊤)
    (a a' : Fin d → K → ℤ) (h : ∀ j, ValEq k z (a j) z (a' j)) : inum k z a = inum k z a' := by
  classical
  have key : ∀ s : Finset (Fin d), inum k z (fun j => if j ∈ s then a' j else a j) = inum k z a := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro i s hi ih
      rw [← ih]
      have e : (fun j => if j ∈ insert i s then a' j else a j) =
          Function.update (fun j => if j ∈ s then a' j else a j) i (a' i) := by
        funext j
        by_cases hj : j = i
        · subst hj
          simp
        · simp [hj]
      rw [e]
      apply inum_update h1 h3 hz ht
      simpa [hi] using (h i).symm
  simpa using (key Finset.univ).symm

theorem fnField_le_join_inl (y : (Σ b, ι b) → Ω) (y' : (Σ b, ι' b) → Ω) : fnField k y ≤ fnField k (joinPt y y') := by
  unfold fnField
  rw [IntermediateField.adjoin_le_iff]
  rintro t ⟨p, q, hpq, rfl⟩
  apply IntermediateField.subset_adjoin
  exact ⟨⟨Sum.inl p.1, p.2⟩, ⟨Sum.inl q.1, q.2⟩, congrArg Sum.inl hpq, rfl⟩

theorem finite_of_le {F F' : IntermediateField k Ω} (h : F ≤ F') [FiniteDimensional F Ω] : FiniteDimensional F' Ω := by
  letI := (IntermediateField.inclusion h).toRingHom.toAlgebra
  haveI : IsScalarTower F F' Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Module.Finite.of_restrictScalars_finite F F' Ω

theorem IsPt.join_inl {y : (Σ b, ι b) → Ω} {y' : (Σ b, ι' b) → Ω} {d : ℕ} (h : IsPt k y d) (h' : ∀ b, ∃ i, y' ⟨b, i⟩ ≠ 0) :
    IsPt k (joinPt y y') d := by
  obtain ⟨h0, hf, ht⟩ := h
  refine ⟨?_, ?_, ht⟩
  · rintro (b | b)
    · exact h0 b
    · exact h' b
  · haveI := hf
    exact finite_of_le (fnField_le_join_inl (k := k) y y')

theorem num_join_inl (h2 : NumPull) {y : (Σ b, ι b) → Ω} {y' : (Σ b, ι' b) → Ω} {d : ℕ} (h : IsPt k y d)
    (h' : ∀ b, ∃ i, y' ⟨b, i⟩ ≠ 0) (a : Fin d → K → ℤ) : num k (joinPt y y') (fun j => Sum.elim (a j) 0) = num k y a := by
  have hv : ReciprocityTheory.ChartRestriction.G.AI.I1.IsBlockMap (Sum.inl : K → K ⊕ K')
      (fun p : (Σ b, ι b) => (⟨Sum.inl p.1, p.2⟩ : Σ b, Sum.elim ι ι' b)) := by
    refine ⟨Sum.inl_injective, ?_, fun _ => rfl, ?_⟩
    · intro p q hpq
      obtain ⟨b, i⟩ := p
      obtain ⟨b', i'⟩ := q
      cases hpq
      rfl
    · rintro ⟨b, i⟩ ⟨c, rfl⟩
      exact ⟨⟨c, i⟩, rfl⟩
  have hp : ∀ j, ReciprocityTheory.ChartRestriction.G.AI.I1.pullDeg (Sum.inl : K → K ⊕ K') (a j) = Sum.elim (a j) (0 : K' → ℤ) := by
    intro j
    funext x
    cases x with
    | inl c => exact Sum.inl_injective.extend_apply (a j) 0 c
    | inr c =>
      show Function.extend Sum.inl (a j) 0 (Sum.inr c) = 0
      rw [Function.extend_apply' _ _ _ (by rintro ⟨c', hc⟩; cases hc)]
      rfl
  have := h2 k Ω K ι (K ⊕ K') (Sum.elim ι ι') Sum.inl _ (joinPt y y') d a hv (h.join_inl h') h
  simp only [hp] at this
  exact this

theorem num_join_inr (h2 : NumPull) {y : (Σ b, ι b) → Ω} {y' : (Σ b, ι' b) → Ω} {d : ℕ} (h : IsPt k y d) (h' : IsPt k y' d)
    (a : Fin d → K' → ℤ) : num k (joinPt y y') (fun j => Sum.elim 0 (a j)) = num k y' a := by
  have hv : ReciprocityTheory.ChartRestriction.G.AI.I1.IsBlockMap (Sum.inr : K' → K ⊕ K')
      (fun p : (Σ b, ι' b) => (⟨Sum.inr p.1, p.2⟩ : Σ b, Sum.elim ι ι' b)) := by
    refine ⟨Sum.inr_injective, ?_, fun _ => rfl, ?_⟩
    · intro p q hpq
      obtain ⟨b, i⟩ := p
      obtain ⟨b', i'⟩ := q
      cases hpq
      rfl
    · rintro ⟨b, i⟩ ⟨c, rfl⟩
      exact ⟨⟨c, i⟩, rfl⟩
  have hp : ∀ j, ReciprocityTheory.ChartRestriction.G.AI.I1.pullDeg (Sum.inr : K' → K ⊕ K') (a j) = Sum.elim (0 : K → ℤ) (a j) := by
    intro j
    funext x
    cases x with
    | inr c => exact Sum.inr_injective.extend_apply (a j) 0 c
    | inl c =>
      show Function.extend Sum.inr (a j) 0 (Sum.inl c) = 0
      rw [Function.extend_apply' _ _ _ (by rintro ⟨c', hc⟩; cases hc)]
      rfl
  have := h2 k Ω K' ι' (K ⊕ K') (Sum.elim ι ι') Sum.inr _ (joinPt y y') d a hv (h.join_inl h'.1) h'
  simp only [hp] at this
  exact this

theorem exists_top (y : (Σ b, ι b) → Ω) [FiniteDimensional (fnField k y) Ω] :
    ∃ (m : ℕ) (w : (Σ _ : Unit, Option (Fin m)) → Ω), (∀ b, ∃ i, w ⟨b, i⟩ ≠ 0) ∧ fnField k (joinPt y w) = ⊤ := by
  let B := Module.finBasis (fnField k y) Ω
  refine ⟨_, fun x => x.2.elim 1 B, fun _ => ⟨none, one_ne_zero⟩, eq_top_iff.2 fun t _ => ?_⟩
  rw [← B.sum_repr t]
  refine sum_mem fun i _ => ?_
  rw [Algebra.smul_def]
  refine mul_mem (fnField_le_join_inl y _ (B.repr t i).2) (IntermediateField.subset_adjoin _ _ ?_)
  exact ⟨⟨.inr (), some i⟩, ⟨.inr (), none⟩, rfl, (div_one _).symm⟩

theorem numEq : PtDim → NumPull → UnitZero → NumEq := by
  intro h1 h2 h3 k _ Ω _ _ K _ ι _ K' _ ι' _ y y' d a a' hy hy' h
  have hj := hy.join_inl hy'.1
  haveI := hj.2.1
  obtain ⟨m, w, hw, ht⟩ := exists_top (k := k) (joinPt y y')
  rw [← num_join_inl h2 hy hy'.1, ← num_join_inr h2 hy hy', ← num_join_inl h2 hj hw, ← num_join_inl h2 hj hw]
  unfold num
  congr 1
  refine inum_congr h1 h3 (hj.join_inl hw) ht _ _ fun j => ?_
  exact ((ValEq.join_inl _ w _).trans (ValEq.join_inl y y' _)).trans
    ((h j).trans ((ValEq.join_inl _ w _).trans (ValEq.join_inr y y' _)).symm)

end SheetDecomposition
end
end

