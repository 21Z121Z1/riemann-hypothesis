import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.LengthCommensurableMapIffOfInjective

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RelLengthSpanEqAddValDet
section
namespace GlobalTheory.RelativeLengthSpanDet

open IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in

theorem addVal_prod (s : Finset ι) (c : ι → R) :
    addVal R (∏ i ∈ s, c i) = ∑ i ∈ s, addVal R (c i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, addVal_mul, ih]

theorem length_self_eq_top : Module.length R R = ⊤ := by
  by_contra h
  rw [← ne_eq, Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian] at h
  have : IsArtinianRing R := h.2
  exact IsDiscreteValuationRing.not_isField R (IsArtinianRing.isField_of_isDomain R)

theorem length_coker_of_det_eq_zero (P : Matrix ι ι R) (h : P.det = 0) :
    Module.length R ((ι → R) ⧸ LinearMap.range P.mulVecLin) = ⊤ := by
  obtain ⟨w, hw, hwP⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hw
  have hk' : w k ≠ 0 := hk
  let g : R →ₗ[R] (ι → R) ⧸ LinearMap.range P.mulVecLin :=
    (LinearMap.range P.mulVecLin).mkQ ∘ₗ LinearMap.single R (fun _ : ι => R) k
  have hg : Function.Injective g := by
    rw [injective_iff_map_eq_zero]
    intro r hr
    have hr' : (Pi.single k r : ι → R) ∈ LinearMap.range P.mulVecLin :=
      (Submodule.Quotient.mk_eq_zero _).mp hr
    obtain ⟨x, hx⟩ := hr'
    have h1 : w ⬝ᵥ P.mulVec x = 0 := by
      rw [Matrix.dotProduct_mulVec, hwP, zero_dotProduct]
    rw [Matrix.mulVecLin_apply] at hx
    rw [hx, dotProduct_single] at h1
    exact (mul_eq_zero.mp h1).resolve_left hk'
  exact top_le_iff.mp (length_self_eq_top (R := R) ▸ Module.length_le_of_injective g hg)

theorem length_coker_of_injective {M : Type*} [AddCommGroup M] [Module R M]
    (b : Module.Basis ι R M) (f : M →ₗ[R] M) (hf : Function.Injective f) :
    Module.length R (M ⧸ LinearMap.range f) = addVal R (LinearMap.det f) := by
  have hr : Module.finrank R (LinearMap.range f) = Module.finrank R M :=
    LinearMap.finrank_range_of_inj hf
  set c := Submodule.smithNormalFormCoeffs b hr with hc
  set bt := Submodule.smithNormalFormTopBasis b hr with hbt
  set bb := Submodule.smithNormalFormBotBasis b hr with hbb
  have hdef : ∀ i, (bb i : M) = c i • bt i := Submodule.smithNormalFormBotBasis_def b hr
  have h1 : Module.length R (M ⧸ LinearMap.range f) = ∑ i, addVal R (c i) := by
    rw [(Submodule.quotientEquivPiSpan _ b hr).length_eq, Module.length_pi_of_fintype]
    exact Finset.sum_congr rfl fun i _ => Ring.ord_eq_addVal (c i)
  have h2 := LinearMap.associated_det_comp_equiv (LinearMap.range f).subtype
    (LinearEquiv.ofInjective f hf) (bt.equiv bb (Equiv.refl ι))
  have h3 : (LinearMap.range f).subtype ∘ₗ (LinearEquiv.ofInjective f hf : M →ₗ[R] _) = f := by
    ext x
    rfl
  have h4 : LinearMap.det ((LinearMap.range f).subtype ∘ₗ
      (bt.equiv bb (Equiv.refl ι) : M →ₗ[R] LinearMap.range f)) = ∏ i, c i := by
    rw [← LinearMap.det_toMatrix bt, ← Matrix.det_diagonal]
    congr 1
    ext i j
    rw [LinearMap.toMatrix_apply]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.equiv_apply,
      Equiv.refl_apply, Submodule.subtype_apply, hdef, map_smul, Module.Basis.repr_self,
      Finsupp.smul_apply, Finsupp.single_apply, Matrix.diagonal_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij, Ne.symm hij]
  rw [h3, h4] at h2
  rw [h1, (addVal_eq_iff_associated _ _).mpr h2, addVal_prod]

theorem length_coker (P : Matrix ι ι R) :
    Module.length R ((ι → R) ⧸ LinearMap.range P.mulVecLin) = addVal R P.det := by
  by_cases h : P.det = 0
  · rw [length_coker_of_det_eq_zero P h, h, addVal_zero]
  · have hinj : Function.Injective P.mulVecLin := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      by_contra hx0
      exact h (Matrix.exists_mulVec_eq_zero_iff.mp ⟨x, hx0, hx⟩)
    rw [length_coker_of_injective (Pi.basisFun R ι) _ hinj, ← Matrix.toLin'_apply',
      LinearMap.det_toLin']

theorem relLength_span_eq_addVal_det {V : Type*} [AddCommGroup V] [Module R V] {a v : ι → V}
    (ha : LinearIndependent R a) (P : Matrix ι ι R) (hv : ∀ j, v j = ∑ i, P i j • a i) :
    relLength (Submodule.span R (Set.range a)) (Submodule.span R (Set.range v)) =
      addVal R P.det := by
  have hinj : Function.Injective (Fintype.linearCombination R a) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    funext i
    exact Fintype.linearIndependent_iff.mp ha x (by rwa [Fintype.linearCombination_apply] at hx) i
  have hA : Submodule.span R (Set.range a) =
      (⊤ : Submodule R (ι → R)).map (Fintype.linearCombination R a) := by
    rw [Submodule.map_top, Fintype.range_linearCombination]
  have hcomp : Fintype.linearCombination R a ∘ₗ P.mulVecLin = Fintype.linearCombination R v := by
    refine LinearMap.pi_ext' fun j => LinearMap.ext_ring ?_
    simp [Fintype.linearCombination_apply, hv, Pi.single_apply]
  have hB : Submodule.span R (Set.range v) =
      (LinearMap.range P.mulVecLin).map (Fintype.linearCombination R a) := by
    rw [← LinearMap.range_comp, hcomp, Fintype.range_linearCombination]
  rw [hA, hB, relLength_map_of_injective _ hinj, relLength_top_left, length_coker]

universe u_1 u_2 u_3 in

theorem relLength_span_eq {R : Type u_1} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {V : Type u_2} [AddCommGroup V] [Module R V] {ι : Type u_3} [Fintype ι] [DecidableEq ι]
    {a v : ι → V} (ha : LinearIndependent R a) (P : Matrix ι ι R)
    (hv : ∀ j, v j = ∑ i, P i j • a i) :
    relLength (Submodule.span R (Set.range a)) (Submodule.span R (Set.range v)) =
      (addVal R : R → ℕ∞) P.det :=
  relLength_span_eq_addVal_det ha P hv

end GlobalTheory.RelativeLengthSpanDet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RelLengthSpanMatrix
section
universe u_1 u_2 u_3 u_4

namespace GlobalTheory.SignedLengthTower

theorem relLength_tower {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]
    {A B C : Submodule R V} (hBA : B ≤ A) (hCB : C ≤ B) :
    relLength A C = relLength B C + relLength A B := by
  have hle : C.submoduleOf A ≤ B.submoduleOf A := Submodule.comap_mono hCB
  rw [← relLength_submoduleOf hBA C, relLength_eq_length_map_mkQ (B.submoduleOf A),
    relLength_def, relLength_def]
  refine Module.length_eq_add_of_exact (Submodule.subtype _) (Submodule.factor hle)
    (Submodule.injective_subtype _) (Submodule.factor_surjective _) ?_
  intro y
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ y
  constructor
  · intro h
    have hx : x ∈ B.submoduleOf A := by
      simpa [Submodule.factor_mk] using h
    exact ⟨⟨_, x, hx, rfl⟩, rfl⟩
  · rintro ⟨⟨_, z, hz, rfl⟩, h⟩
    have h' : (C.submoduleOf A).mkQ z = (C.submoduleOf A).mkQ x := h
    rw [← h']
    simpa [Submodule.factor_mk] using hz

theorem ord_prod {R ι : Type*} [CommRing R] [IsDomain R] (s : Finset ι) (d : ι → R)
    (hd : ∀ i, d i ≠ 0) : Ring.ord R (∏ i ∈ s, d i) = ∑ i ∈ s, Ring.ord R (d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Ring.ord_one]
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      Ring.ord_mul' R (mem_nonZeroDivisors_of_ne_zero (hd i)), ih]

theorem length_coker {R ι : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [Fintype ι] (f : (ι → R) →ₗ[R] (ι → R)) (hf : Function.Injective f) :
    Module.length R ((ι → R) ⧸ LinearMap.range f) = Ring.ord R (LinearMap.det f) := by
  classical
  have h : Module.finrank R (LinearMap.range f) = Module.finrank R (ι → R) :=
    LinearMap.finrank_range_of_inj hf
  set e := Pi.basisFun R ι
  set d := Submodule.smithNormalFormCoeffs e h with hd
  set top := Submodule.smithNormalFormTopBasis e h with htop
  set bot := Submodule.smithNormalFormBotBasis e h with hbot
  have hass := LinearMap.associated_det_comp_equiv (LinearMap.range f).subtype
    (LinearEquiv.ofInjective f hf) (top.equiv bot (Equiv.refl ι))
  have h1 : (LinearMap.range f).subtype ∘ₗ (LinearEquiv.ofInjective f hf).toLinearMap = f := by
    ext1 i
    ext1
    rfl
  have h2 : LinearMap.det ((LinearMap.range f).subtype ∘ₗ
      (top.equiv bot (Equiv.refl ι)).toLinearMap) = ∏ i, d i := by
    rw [← LinearMap.det_toMatrix top, ← Matrix.det_diagonal]
    congr 1
    ext i j
    have := Submodule.smithNormalFormBotBasis_def e h j
    rw [← hd, ← htop, ← hbot] at this
    rw [LinearMap.toMatrix_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      Module.Basis.equiv_apply, Equiv.refl_apply, Submodule.subtype_apply, this]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Finsupp.single_apply, Ne.symm hij]
  rw [h1, h2] at hass
  obtain ⟨v, hv⟩ := hass.symm
  rw [(Submodule.quotientEquivPiSpan _ e h).length_eq, Module.length_pi_of_fintype, ← hv,
    Ring.ord_mul R (v.isUnit.mem_nonZeroDivisors), Ring.ord_of_isUnit v.isUnit, add_zero,
    ord_prod _ _ (Submodule.smithNormalFormCoeffs_ne_zero e h)]
  rfl

theorem relLength_span_matrix {R V ι : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [AddCommGroup V] [Module R V] [Fintype ι] [DecidableEq ι] {a c : ι → V}
    (ha : LinearIndependent R a) (M : Matrix ι ι R) (hM : M.det ≠ 0)
    (hc : ∀ j, c j = ∑ i, M i j • a i) :
    relLength (Submodule.span R (Set.range a)) (Submodule.span R (Set.range c)) =
      Ring.ord R M.det := by
  let φ := Fintype.linearCombination R a
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    funext i
    exact Fintype.linearIndependent_iff.mp ha x (by simpa [φ, Fintype.linearCombination_apply] using hx) i
  have hf : Function.Injective (Matrix.toLin' M) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    exact Matrix.eq_zero_of_mulVec_eq_zero hM (by simpa using hx)
  have hA : Submodule.span R (Set.range a) = Submodule.map φ ⊤ := by
    rw [Submodule.map_top, Fintype.range_linearCombination]
  have hC : Submodule.span R (Set.range c) =
      Submodule.map φ (LinearMap.range (Matrix.toLin' M)) := by
    rw [Matrix.range_toLin', Submodule.map_span, ← Set.range_comp]
    congr 2
    funext j
    simp [φ, Fintype.linearCombination_apply, hc]
  rw [hA, hC, relLength_map_of_injective φ hφ, relLength_top_left, length_coker _ hf,
    LinearMap.det_toLin']

theorem signedLength_span_eq {R : Type u_1} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type u_2} [Field K] [Algebra R K] [IsFractionRing R K]
    {V : Type u_3} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    {ι : Type u_4} [Fintype ι] [DecidableEq ι] {a b : ι → V} (ha : LinearIndependent K a)
    (g : Matrix ι ι K) (hb : ∀ j, b j = ∑ i, g i j • a i) {ϖ : R} (hϖ : Irreducible ϖ)
    (u : Rˣ) (n : ℤ) (hdet : g.det = algebraMap R K (u : R) * algebraMap R K ϖ ^ n) :
    signedLength (Submodule.span R (Set.range a)) (Submodule.span R (Set.range b)) = n := by
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hϖK : algebraMap R K ϖ ≠ 0 := (map_ne_zero_iff _ hinj).mpr hϖ.ne_zero
  have hg : g.det ≠ 0 := by
    rw [hdet]
    exact mul_ne_zero ((map_ne_zero_iff _ hinj).mpr u.ne_zero) (zpow_ne_zero _ hϖK)
  have hbK : LinearIndependent K b := by
    rw [Fintype.linearIndependent_iff] at ha ⊢
    intro x hx
    have h0 : g.mulVec x = 0 := by
      funext i
      refine ha (g.mulVec x) ?_ i
      rw [← hx]
      simp only [hb, Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp only [mul_comm]
    exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero hg h0)
  have hres : ∀ {v : ι → V}, LinearIndependent K v → LinearIndependent R v := fun hv =>
    hv.restrict_scalars (by simpa [← Algebra.algebraMap_eq_smul_one] using hinj)
  obtain ⟨⟨t, ht⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R)
    (fun p : ι × ι => g p.1 p.2)
  choose m hm using hint
  let M : Matrix ι ι R := Matrix.of fun i j => m (i, j)
  have hM : (algebraMap R K).mapMatrix M = algebraMap R K t • g := by
    ext i j
    simp [M, hm, Algebra.smul_def]
  let D : Matrix ι ι R := Matrix.diagonal fun _ => t
  have hD : D.det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun _ _ => nonZeroDivisors.ne_zero ht
  have hMD : algebraMap R K M.det = algebraMap R K D.det * g.det := by
    rw [RingHom.map_det, hM, Matrix.det_smul, Matrix.det_diagonal]
    simp
  have hM0 : M.det ≠ 0 := by
    rw [← map_ne_zero_iff _ hinj, hMD]
    exact mul_ne_zero ((map_ne_zero_iff _ hinj).mpr hD) hg
  let c : ι → V := fun j => t • b j
  have hca : ∀ j, c j = ∑ i, M i j • a i := by
    intro j
    simp only [c, hb, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← smul_assoc, ← hm (i, j), algebraMap_smul]
    rfl
  have hcb : ∀ j, c j = ∑ i, D i j • b i := by
    intro j
    simp [c, D, Matrix.diagonal_apply, ite_smul]
  have hle : ∀ {v : ι → V} {N : Matrix ι ι R}, (∀ j, c j = ∑ i, N i j • v i) →
      Submodule.span R (Set.range c) ≤ Submodule.span R (Set.range v) := by
    intro v N hN
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [hN]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have h1 := relLength_span_matrix (hres ha) M hM0 hca
  have h2 := relLength_span_matrix (hres hbK) D hD hcb
  have hC := le_inf (hle hca) (hle hcb)
  rw [relLength_tower inf_le_left hC, relLength_inf_right] at h1
  rw [relLength_tower inf_le_right hC, relLength_inf_right'] at h2
  have hord : Ring.ord R ϖ = 1 := by
    have := PrincipalIdealRing.isMaximal_of_irreducible hϖ
    have h := relLength_top_of_isMaximal (Ideal.span {ϖ})
    rw [relLength_top_left] at h
    exact h
  obtain ⟨p, q, rfl⟩ : ∃ p q : ℕ, n = (p : ℤ) - q := ⟨n.toNat, (-n).toNat, by omega⟩
  have hR : M.det * ϖ ^ q = D.det * (u * ϖ ^ p) := by
    apply hinj
    rw [map_mul, map_mul, map_mul, map_pow, map_pow, hMD, hdet, zpow_sub₀ hϖK, zpow_natCast,
      zpow_natCast]
    field_simp
  have hϖ0 : ϖ ∈ nonZeroDivisors R := mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero
  have hlen := congrArg (Ring.ord R) hR
  rw [Ring.ord_mul R (pow_mem hϖ0 q), Ring.ord_mul' R (mem_nonZeroDivisors_of_ne_zero hD),
    Ring.ord_mul R (pow_mem hϖ0 p), Ring.ord_of_isUnit u.isUnit, Ring.ord_pow hϖ0,
    Ring.ord_pow hϖ0, hord, ← h1, ← h2] at hlen
  have f1 := Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hM0)
  have f2 := Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hD)
  rw [← h1] at f1
  rw [← h2] at f2
  obtain ⟨x, hx⟩ := ENat.ne_top_iff_exists.mp (WithTop.add_ne_top.mp f1).1
  obtain ⟨y, hy⟩ := ENat.ne_top_iff_exists.mp (WithTop.add_ne_top.mp f1).2
  obtain ⟨z, hz⟩ := ENat.ne_top_iff_exists.mp (WithTop.add_ne_top.mp f2).2
  rw [signedLength_eq_of_relLength_eq hy.symm hz.symm]
  rw [← hx, ← hy, ← hz, nsmul_one, nsmul_one, zero_add] at hlen
  have : x + y + q = x + z + p := by exact_mod_cast hlen
  omega

end GlobalTheory.SignedLengthTower
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SignedLengthOfCommonLower
section
universe u_1 u_2

namespace GlobalTheory.RelativeLengthAdditivity

open GlobalTheory

section
variable {S : Type u_1} {V : Type u_2} [Ring S] [AddCommGroup V] [Module S V]

theorem relLength_bot_add {A D : Submodule S V} (h : D ≤ A) :
    relLength A ⊥ = relLength A D + relLength D ⊥ := by
  let N : Submodule S A := D.submoduleOf A
  have hex := Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
    (LinearMap.exact_subtype_mkQ N)
  have hN : Module.length S N = relLength D ⊥ := by
    have := relLength_submoduleOf h (⊥ : Submodule S V)
    have hb : (⊥ : Submodule S V).submoduleOf A = ⊥ := by
      ext x; simp [Submodule.submoduleOf]
    rw [hb, relLength_bot_right] at this
    exact this
  rw [relLength_bot_right, hex, hN, add_comm]
  rfl

theorem relLength_add {A C D : Submodule S V} (hCD : C ≤ D) (hDA : D ≤ A) :
    relLength A C = relLength A D + relLength D C := by
  have hb : C.map C.mkQ = ⊥ := Submodule.mkQ_map_self C
  rw [← relLength_map_mkQ le_rfl A, ← relLength_map_mkQ hCD A, ← relLength_map_mkQ le_rfl D, hb]
  exact relLength_bot_add (Submodule.map_mono hDA)

theorem signedLength_of_common_lower : ∀ {S : Type u_1} {V : Type u_2} [inst : Ring S] [inst_1 : AddCommGroup V]
    [inst_2 : Module S V] {A B C : Submodule S V}, C ≤ A → C ≤ B → ∀ {m n : ℕ},
    GlobalTheory.relLength A C = (↑m : ℕ∞) → GlobalTheory.relLength B C = (↑n : ℕ∞) →
    GlobalTheory.LengthCommensurable A B ∧ GlobalTheory.signedLength A B = (↑m : ℤ) - (↑n : ℤ) := by
  intro S V _ _ _ A B C hCA hCB m n hm hn
  have hCD : C ≤ A ⊓ B := le_inf hCA hCB
  have h1 := relLength_add hCD (inf_le_left : A ⊓ B ≤ A)
  have h2 := relLength_add hCD (inf_le_right : A ⊓ B ≤ B)
  rw [relLength_inf_right] at h1
  rw [relLength_inf_right'] at h2
  rw [hm] at h1
  rw [hn] at h2
  have ha : relLength A B ≠ ⊤ := fun h => by simp [h] at h1
  have hb : relLength B A ≠ ⊤ := fun h => by simp [h] at h2
  have hk : relLength (A ⊓ B) C ≠ ⊤ := fun h => by simp [h] at h1
  refine ⟨⟨ha, hb⟩, ?_⟩
  obtain ⟨a, ha'⟩ := ENat.ne_top_iff_exists.mp ha
  obtain ⟨b, hb'⟩ := ENat.ne_top_iff_exists.mp hb
  obtain ⟨k, hk'⟩ := ENat.ne_top_iff_exists.mp hk
  rw [← ha', ← hk'] at h1
  rw [← hb', ← hk'] at h2
  have e1 : m = a + k := by exact_mod_cast h1
  have e2 : n = b + k := by exact_mod_cast h2
  rw [signedLength_eq_of_relLength_eq ha'.symm hb'.symm, e1, e2]
  push_cast
  ring
end

end GlobalTheory.RelativeLengthAdditivity

example : ∀ {S : Type u_1} {V : Type u_2} [inst : Ring S] [inst_1 : AddCommGroup V] [inst_2 : Module S V] {A B C : Submodule S V}, C ≤ A → C ≤ B → ∀ {m n : ℕ}, GlobalTheory.relLength A C = (↑m : ℕ∞) → GlobalTheory.relLength B C = (↑n : ℕ∞) → GlobalTheory.LengthCommensurable A B ∧ GlobalTheory.signedLength A B = (↑m : ℤ) - (↑n : ℤ) := @GlobalTheory.RelativeLengthAdditivity.signedLength_of_common_lower
end

