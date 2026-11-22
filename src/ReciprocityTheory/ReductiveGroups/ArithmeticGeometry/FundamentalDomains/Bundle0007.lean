import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0005

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowFixesComplementOfIsotropic
section
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace Data

variable {r : ℕ} (X : Data E r)

section onetau

variable (ξ : Fin r → E) (τ : X.Ψ)

private theorem flowMat_mulVec' (s : ℂ) (v : Fin r → ℂ) :
    Matrix.mulVec (X.flowMat ξ τ s) v =
      v - (I * X.c τ * s * hermC τ.1 X.Gm v (emb τ.1 ξ)) • emb τ.1 ξ := by
  ext a
  simp only [Matrix.mulVec, dotProduct, flowMat, Matrix.of_apply, sub_mul, Finset.sum_sub_distrib,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hermC, emb]
  congr 1
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => ?_
  ring

private theorem hermC_sub_const_smul_left (σ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (v e w : Fin r → ℂ) (k : ℂ) :
    hermC σ G (v - k • e) w = hermC σ G v w - k * hermC σ G e w := by
  simp only [hermC, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

private theorem hermC_sub_const_smul_right (σ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (w v e : Fin r → ℂ) (k : ℂ) :
    hermC σ G w (v - k • e) = hermC σ G w v - conj k * hermC σ G w e := by
  simp only [hermC, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul]
  ring

lemma hC_flow_e (hiso : hermC τ.1 X.Gm (emb τ.1 ξ) (emb τ.1 ξ) = 0) (s : ℂ) (v : Fin r → ℂ) :
    hermC τ.1 X.Gm (Matrix.mulVec (X.flowMat ξ τ s) v) (emb τ.1 ξ) = hermC τ.1 X.Gm v (emb τ.1 ξ) := by
  rw [flowMat_mulVec', hermC_sub_const_smul_left, hiso, mul_zero, sub_zero]

lemma flow_fix (s : ℂ) (v : Fin r → ℂ) (hv : hermC τ.1 X.Gm v (emb τ.1 ξ) = 0) :
    Matrix.mulVec (X.flowMat ξ τ s) v = v := by
  rw [flowMat_mulVec', hv, mul_zero, zero_smul, sub_zero]

lemma hC_right_flow (s : ℂ) (y v : Fin r → ℂ) (hy : hermC τ.1 X.Gm y (emb τ.1 ξ) = 0) :
    hermC τ.1 X.Gm y (Matrix.mulVec (X.flowMat ξ τ s) v) = hermC τ.1 X.Gm y v := by
  rw [flowMat_mulVec', hermC_sub_const_smul_right, hy, mul_zero, sub_zero]

lemma col_flow (s : X.Ψ → ℂ) (x : Frame X.Ψ r) (a : Fin r) :
    col (mat (X.flow ξ s x) τ) a = Matrix.mulVec (X.flowMat ξ τ (s τ)) (col (mat x τ) a) := by
  ext k
  rfl

lemma mulVec_lin (M : Matrix (Fin r) (Fin r) ℂ) {n : ℕ} (β : Fin n → ℂ) (v : Fin n → Fin r → ℂ) :
    Matrix.mulVec M (∑ a, β a • v a) = ∑ a, β a • Matrix.mulVec M (v a) := by
  simp [Matrix.mulVec_sum, Matrix.mulVec_smul]

lemma ppos_flow {x : Frame X.Ψ r} (hx : x ∈ X.dom) (s : X.Ψ → ℂ) (hxs : X.flow ξ s x ∈ X.dom)
    (u : Fin r → ℂ) (hu : hermC τ.1 X.Gm u (emb τ.1 ξ) = 0)
    (hp : hermC τ.1 X.Gm (X.ppos x τ u) (emb τ.1 ξ) = 0) :
    X.ppos (X.flow ξ s x) τ u = X.ppos x τ u := by
  set α : Fin X.p0 → ℂ := fun a => ∑ b, hermC τ.1 X.Gm u (col (mat x τ) (Fin.castLE X.p0_le b)) *
    (X.gramPos x τ)⁻¹ b a with hα
  have hpx : X.ppos x τ u = ∑ a, α a • col (mat x τ) (Fin.castLE X.p0_le a) := rfl
  have hT : ∑ a, α a • col (mat (X.flow ξ s x) τ) (Fin.castLE X.p0_le a) = X.ppos x τ u := by
    simp only [col_flow]
    rw [← mulVec_lin, ← hpx, flow_fix X ξ τ _ _ hp]
  rw [← hT]
  apply ppos_eq_of X (X.flow ξ s x) τ (gramPos_det_ne X hxs τ) u α
  intro b
  rw [hT, col_flow, hC_right_flow]
  · exact ppos_orth X x τ (gramPos_det_ne X hx τ) u b
  · rw [hC_sub_left, hu, hp, sub_zero]

private theorem hermC_sum_const_smul_left {n : ℕ} (σ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (cf : Fin n → ℂ) (w : Fin n → Fin r → ℂ) (e : Fin r → ℂ) :
    hermC σ G (∑ a, cf a • w a) e = ∑ a, cf a * hermC σ G (w a) e := by
  have hadd : ∀ u u' : Fin r → ℂ, hermC σ G (u + u') e = hermC σ G u e + hermC σ G u' e := by
    intro u u'
    simp only [hermC, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  have hsm : ∀ (k : ℂ) (u : Fin r → ℂ), hermC σ G (k • u) e = k * hermC σ G u e := by
    intro k u
    simp only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  have h0 : hermC σ G 0 e = 0 := by simp [hermC]
  suffices H : ∀ s : Finset (Fin n),
      hermC σ G (∑ a ∈ s, cf a • w a) e = ∑ a ∈ s, cf a * hermC σ G (w a) e from H _
  intro s
  refine Finset.induction_on s ?_ ?_
  · simpa using h0
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, hsm, ih]

lemma hC_ppos_e (x : Frame X.Ψ r) (v : Fin r → ℂ) :
    hermC τ.1 X.Gm (X.ppos x τ v) (emb τ.1 ξ) =
      dotProduct (fun b => hermC τ.1 X.Gm v (col (mat x τ) (Fin.castLE X.p0_le b)))
        (Matrix.mulVec (X.gramPos x τ)⁻¹
          (fun a => hermC τ.1 X.Gm (col (mat x τ) (Fin.castLE X.p0_le a)) (emb τ.1 ξ))) := by
  unfold Data.ppos
  rw [hermC_sum_const_smul_left]
  simp only [dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  ring

lemma Hf_scale (hiso : hermC τ.1 X.Gm (emb τ.1 ξ) (emb τ.1 ξ) = 0) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) (s : X.Ψ → ℂ) (hxs : X.flow ξ s x ∈ X.dom) :
    ∃ k : ℂ, k ≠ 0 ∧ ∀ v : Fin r → ℂ, hermC τ.1 X.Gm v (emb τ.1 ξ) = 0 →
      X.Hf x τ v (emb τ.1 ξ) = k * X.Hf (X.flow ξ s x) τ v (emb τ.1 ξ) := by
  set e := emb τ.1 ξ with he
  set T := X.flowMat ξ τ (s τ) with hTdef
  set β : ℂ := -(I * X.c τ * s τ) with hβ
  set A := X.gramPos x τ with hAdef
  set A' := X.gramPos (X.flow ξ s x) τ with hA'def
  set l : Fin X.p0 → ℂ := fun a => hermC τ.1 X.Gm (col (mat x τ) (Fin.castLE X.p0_le a)) e with hl
  have hAdet := gramPos_det_ne X hx τ
  have hA'det := gramPos_det_ne X hxs τ
  have hsymm : ∀ v w, hermC τ.1 X.Gm v w = conj (hermC τ.1 X.Gm w v) := fun v w =>
    hC_symm τ.1 X.Gm X.Gm_herm w v

  have hA' : ∀ a b, A' a b = A a b + (β + conj β) * l a * conj (l b) := by
    intro a b
    have h1 : A' a b = hermC τ.1 X.Gm (Matrix.mulVec T (col (mat x τ) (Fin.castLE X.p0_le a)))
        (Matrix.mulVec T (col (mat x τ) (Fin.castLE X.p0_le b))) := by
      simp only [hA'def, gramPos, gram, Matrix.submatrix_apply, Matrix.of_apply, col_flow, hTdef]
    rw [h1, flowMat_mulVec, flowMat_mulVec, hC_add_left, hC_add_right, hC_add_right, hC_smul_left,
      hC_smul_left, hC_smul_right, hC_smul_right, hiso, hsymm e (col (mat x τ) (Fin.castLE X.p0_le b))]
    simp only [hAdef, gramPos, gram, Matrix.submatrix_apply, Matrix.of_apply, hl, hβ, map_mul]
    ring

  have hA'mul : ∀ y : Fin X.p0 → ℂ, Matrix.mulVec A' y =
      Matrix.mulVec A y + ((β + conj β) * dotProduct (fun b => conj (l b)) y) • l := by
    intro y
    funext a
    simp only [Matrix.mulVec, dotProduct, hA', Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul,
      Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  set y := Matrix.mulVec A⁻¹ l with hy
  have hAy : Matrix.mulVec A y = l := by
    rw [hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (Ne.isUnit hAdet), Matrix.one_mulVec]
  set k : ℂ := 1 + (β + conj β) * dotProduct (fun b => conj (l b)) y with hk
  have hA'y : Matrix.mulVec A' y = k • l := by
    rw [hA'mul, hAy, hk, add_smul, one_smul]
  have hk0 : k ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hA'y
    have hy0 : y = 0 := by
      have := congrArg (Matrix.mulVec A'⁻¹) hA'y
      rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (Ne.isUnit hA'det), Matrix.one_mulVec,
        Matrix.mulVec_zero] at this
    have hl0 : l = 0 := by rw [← hAy, hy0, Matrix.mulVec_zero]
    rw [hk] at h0
    simp [hy0] at h0
  have hyk : y = k • Matrix.mulVec A'⁻¹ l := by
    have := congrArg (Matrix.mulVec A'⁻¹) hA'y
    rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (Ne.isUnit hA'det), Matrix.one_mulVec,
      Matrix.mulVec_smul] at this
  refine ⟨k, hk0, fun v hv => ?_⟩
  have hcv : (fun b => hermC τ.1 X.Gm v (col (mat (X.flow ξ s x) τ) (Fin.castLE X.p0_le b))) =
      fun b => hermC τ.1 X.Gm v (col (mat x τ) (Fin.castLE X.p0_le b)) := by
    funext b; rw [col_flow, hC_right_flow X ξ τ _ _ _ hv]
  have hlT : (fun a => hermC τ.1 X.Gm (col (mat (X.flow ξ s x) τ) (Fin.castLE X.p0_le a)) e) = l := by
    funext a; rw [col_flow, hC_flow_e X ξ τ hiso]
  simp only [Hf]
  rw [hC_sub_left, hC_sub_left, hC_smul_left, hC_smul_left, hv, sub_zero, sub_zero,
    hC_ppos_e, hC_ppos_e, hcv, hlT]
  rw [show Matrix.mulVec (X.gramPos x τ)⁻¹ (fun a => hermC τ.1 X.Gm (col (mat x τ)
      (Fin.castLE X.p0_le a)) e) = y from rfl, hyk, dotProduct_smul, smul_eq_mul]
  ring

end onetau

end Data

end ReciprocityTheory.ChartRestriction.G.FD
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HermEqZeroOfTraceFormVanish
section
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

lemma mem_orthogonal_lattice_iff {r : ℕ} (X : Data E r) (ξ v : Fin r → E) :
    v ∈ X.Λp ξ ↔ v ∈ X.Λ ∧ herm X.Gm v ξ = 0 := by first | exact Iff.rfl | simp [Data.Λp, Data.hermL]

lemma integer_smul_eq_coe_smul {r : ℕ} (β : 𝓞 E) (v : Fin r → E) : β • v = (β : E) • v := by
  first
    | rfl
    | (funext i; simp [Algebra.smul_def])

lemma trace_form_integer_smul {r : ℕ} (ξ0 : E) (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E)
    (β : 𝓞 E) :
    EFf ξ0 G x (β • y) = Algebra.trace ℚ E (cc (β : E) * (-ξ0 * herm G x y)) := by
  unfold EFf herm
  rw [integer_smul_eq_coe_smul]
  congr 1
  simp only [Pi.smul_apply, smul_eq_mul, cc, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma herm_eq_zero_of_trace_form_vanish {r : ℕ} (ξ0 : E) (hξ0 : ξ0 ≠ 0) (G : Matrix (Fin r) (Fin r) E)
    (x y : Fin r → E) (h : ∀ β : 𝓞 E, EFf ξ0 G x (β • y) = 0) : herm G x y = 0 := by
  have hb : ∀ β : 𝓞 E, Algebra.trace ℚ E (cc (β : E) * (-ξ0 * herm G x y)) = 0 := fun β =>
    (trace_form_integer_smul ξ0 G x y β).symm.trans (h β)
  have hinv : ∀ a : E, cc (cc a) = a := by
    have h2 := pow_orderOf_eq_one (NumberField.IsCMField.complexConj E)
    rw [NumberField.IsCMField.orderOf_complexConj, pow_two] at h2
    intro a
    have := congrArg (fun σ => σ a) h2
    simpa [cc] using this
  have hw : ∀ w : E, Algebra.trace ℚ E (w * (-ξ0 * herm G x y)) = 0 := by
    intro w
    rw [← hinv w, ← (NumberField.integralBasis E).sum_repr (cc w)]
    simp only [cc, map_sum, map_rat_smul, Finset.sum_mul, smul_mul_assoc, LinearMap.map_smul]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [NumberField.integralBasis_apply]
    have := hb ((NumberField.RingOfIntegers.basis E) i)
    simp only [cc] at this
    rw [smul_eq_zero]
    exact Or.inr this
  have hz : -ξ0 * herm G x y = 0 := by
    have hnd := traceForm_nondegenerate ℚ E
    have hw' : ∀ w : E, Algebra.traceForm ℚ E (-ξ0 * herm G x y) w = 0 := fun w => by
      rw [Algebra.traceForm_apply, mul_comm]
      exact hw w
    first
      | exact hnd _ hw'
      | exact hnd.1 _ hw'
  rcases mul_eq_zero.1 hz with h1 | h1
  · exact absurd (neg_eq_zero.1 h1) hξ0
  · exact h1

theorem hermitian_dual_lattice_identity : PerfectPairingQuotient (E := E) := by
  intro r X ξ hξ
  obtain ⟨hξΛ, hξξ, hξ0⟩ := hξ
  have hsm : ∀ (β : 𝓞 E) v, v ∈ X.Λp ξ → β • v ∈ X.Λp ξ := by
    intro β v hv
    rw [mem_orthogonal_lattice_iff] at hv ⊢
    refine ⟨X.Λ.smul_mem β hv.1, ?_⟩
    rw [integer_smul_eq_coe_smul, herm_smul_left, hv.2, mul_zero]
  have hξp : ξ ∈ X.Λp ξ := (mem_orthogonal_lattice_iff _ _ _).mpr ⟨hξΛ, hξξ⟩
  constructor
  · intro φ hφ
    have : Module.Finite (𝓞 E) ↥X.Λ := Module.Finite.iff_fg.mpr X.Λ_fg
    have : Module.Finite ℤ ↥X.Λ := Module.Finite.trans (𝓞 E) ↥X.Λ
    let f : ↥X.Λ →ₗ[ℤ] E := ((X.hermL ξ).comp X.Λ.subtype.toAddMonoidHom).toIntLinearMap
    have hf : ∀ m : ↥X.Λ, f m = herm X.Gm (m : Fin r → E) ξ := fun m => rfl
    let P := LinearMap.ker f
    have : Module.IsTorsionFree ℤ (↥X.Λ ⧸ P) := by
      rw [Module.isTorsionFree_iff_smul_eq_zero]
      intro n q hq
      obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective P q
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, LinearMap.mem_ker,
        map_zsmul] at hq
      rcases smul_eq_zero.mp hq with h | h
      · exact Or.inl h
      · exact Or.inr ((Submodule.Quotient.mk_eq_zero P).mpr (LinearMap.mem_ker.mpr h))
    obtain ⟨s, hs⟩ := Module.projective_lifting_property P.mkQ LinearMap.id P.mkQ_surjective
    have hsq : ∀ q, P.mkQ (s q) = q := fun q => LinearMap.congr_fun hs q
    have hρ : ∀ m : ↥X.Λ, m - s (P.mkQ m) ∈ P := by
      intro m
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub]
      change P.mkQ m - P.mkQ (s (P.mkQ m)) = 0
      rw [hsq, sub_self]
    let ψ : ↥X.Λ →+ ℤ :=
      { toFun := fun m => φ ⟨((m - s (P.mkQ m) : ↥X.Λ) : Fin r → E),
          (mem_orthogonal_lattice_iff _ _ _).mpr ⟨(m - s (P.mkQ m)).2, LinearMap.mem_ker.mp (hρ m)⟩⟩
        map_zero' := by
          rw [← map_zero φ]; congr 1; ext1; simp
        map_add' := by
          intro a b
          rw [← map_add φ]; congr 1; ext1
          simp only [map_add]
          push_cast
          abel }
    obtain ⟨x, hxΛ, hx⟩ := X.EF_perf ψ
    have hval : ∀ ν : X.Λp ξ, (φ ν : ℚ) = EFf X.ξ0 X.Gm x ν := by
      intro ν
      have hν := (mem_orthogonal_lattice_iff _ _ _).mp ν.2
      have hP : (⟨ν, hν.1⟩ : ↥X.Λ) ∈ P := by rw [LinearMap.mem_ker, hf]; exact hν.2
      have hmk : P.mkQ (⟨ν, hν.1⟩ : ↥X.Λ) = 0 := (Submodule.Quotient.mk_eq_zero P).mpr hP
      have hψ : ψ ⟨ν, hν.1⟩ = φ ν := by
        show φ _ = φ ν
        congr 1; ext1
        simp [hmk]
      rw [← hψ]; exact hx ⟨ν, hν.1⟩
    have hxξ : herm X.Gm x ξ = 0 := by
      apply herm_eq_zero_of_trace_form_vanish X.ξ0 X.ξ0_ne
      intro β
      have hmem := hsm β ξ hξp
      have h0 := hφ ⟨β • ξ, hmem⟩ ⟨(β : E), integer_smul_eq_coe_smul β ξ⟩
      have h1 := hval ⟨β • ξ, hmem⟩
      rw [h0] at h1
      simpa using h1.symm
    exact ⟨⟨x, (mem_orthogonal_lattice_iff _ _ _).mpr ⟨hxΛ, hxξ⟩⟩, hval⟩
  · intro μ hμ
    apply exists_eq_smul_of_herm X.Gm X.Gm_det X.Gm_herm ξ μ hξ0
    intro y hy
    have horth : ∀ ν ∈ X.Λp ξ, herm X.Gm μ ν = 0 := by
      intro ν hν
      apply herm_eq_zero_of_trace_form_vanish X.ξ0 X.ξ0_ne
      intro β
      exact hμ ⟨β • ν, hsm β ν hν⟩
    obtain ⟨d, hd, hdy⟩ := exists_smul_mem (F := E) X.Λ (x := y)
      (by rw [X.Λ_span]; exact Submodule.mem_top)
    have hdyp : d • y ∈ X.Λp ξ := by
      rw [mem_orthogonal_lattice_iff]
      refine ⟨hdy, ?_⟩
      rw [integer_smul_eq_coe_smul, herm_smul_left, hy, mul_zero]
    have h2 := horth _ hdyp
    rw [integer_smul_eq_coe_smul, herm_smul_right] at h2
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h (by simpa using hd)
    · exact h

end ReciprocityTheory.ChartRestriction.G.FD
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCoefficientSplitting
section
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex Metric
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace Data

variable {r : ℕ} (X : Data E r)

def IsOrtho (x : Frame X.Ψ r) : Prop :=
  ∀ τ : X.Ψ, gram τ.1 X.Gm (mat x τ) = Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)

abbrev Coord : Type := X.Ψ → Fin (r - X.p0) → Fin X.p0 → ℂ

def lowBlock (Z : X.Coord) (τ : X.Ψ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun a b => (if a = b then 1 else 0) +
    if h : X.p0 ≤ (a : ℕ) ∧ (b : ℕ) < X.p0 then
      Z τ ⟨(a : ℕ) - X.p0, by have := a.isLt; omega⟩ ⟨b, h.2⟩ else 0

def xZ (x : Frame X.Ψ r) (Z : X.Coord) : Frame X.Ψ r :=
  fun τ => (mat x τ * X.lowBlock Z τ : Matrix (Fin r) (Fin r) ℂ)

def opN {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) : ℝ :=
  sSup {t | ∃ v : Fin n → ℂ, v ≠ 0 ∧
    t = Real.sqrt (∑ i, ‖Matrix.mulVec A v i‖ ^ 2) / Real.sqrt (∑ j, ‖v j‖ ^ 2)}

def zN (Z : X.Coord) : ℝ := ⨆ τ : X.Ψ, opN (Matrix.of (Z τ))

end Data

def OrthonormalFlagTranslate : Prop :=
  ∀ (r : ℕ) (X : Data E r),
    (∀ x ∈ X.dom, ∃ b ∈ Bor X.Ψ r, X.IsOrtho (rmul x b)) ∧
    (∀ (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ),
      (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, P (rmul x b) = bchar la b * P x) →
      ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, X.pnorm la P (rmul x b) = X.pnorm la P x) ∧
    ∀ x ∈ X.dom, ∀ x' ∈ X.dom, X.SameFlag x x' → (∀ ξ : Fin r → E,
      X.Jz x = X.Jz x' ∧ X.Uz x ξ = X.Uz x' ξ ∧ X.aproj x ξ = X.aproj x' ξ) ∧ X.maj x = X.maj x'

def OrthonormalChartNormControl : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x : Frame X.Ψ r), x ∈ X.dom → X.IsOrtho x → ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 / 10 →
    (∀ Z : X.Coord, X.zN Z ≤ ρ →
      X.xZ x Z ∈ X.dom ∧
      (∀ (la : Wt X.Ψ r) (w : ℝ), (∑ τ, X.spread la τ) ≤ w →
        |Real.log (X.nfac la (X.xZ x Z)) - Real.log (X.nfac la x)| ≤ 4 * w * r * X.zN Z ^ 2) ∧
      ∀ τ v, (1 - ρ) / (1 + ρ) * X.maj x τ v ≤ X.maj (X.xZ x Z) τ v ∧
        X.maj (X.xZ x Z) τ v ≤ (1 + ρ) / (1 - ρ) * X.maj x τ v) ∧
    ∀ G : Frame X.Ψ r → ℂ, DifferentiableOn ℂ G X.dom →
      DifferentiableOn ℂ (fun Z : X.Coord => G (X.xZ x Z)) {Z | X.zN Z < ρ}

def NearSupremumTransference : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E) (ν : X.Ψ → ℝ)
    (c1 w : ℝ) (z0 : Frame X.Ψ r), ShortVectorHypotheses X la P ξ ν c1 w z0 →
    ∀ x' ∈ X.dom, (∀ τ, (1 - d6rh c1 w) / (1 + d6rh c1 w) ≤ X.tt ξ x' τ ∧
      X.tt ξ x' τ ≤ (1 + d6rh c1 w) / (1 - d6rh c1 w)) →
    X.hatN la (X.fj la ξ ν P) x' ≤
      Real.exp 2 * sSup {t | ∃ y ∈ X.FramesOverBasis ξ, t = X.hatN la (X.fj la ξ ν P) y}

def SchwarzLemmaBall : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (γ : V → ℂ) (ρ S : ℝ), 0 < ρ →
    DifferentiableOn ℂ γ (closedBall 0 ρ) → (∀ Z ∈ closedBall (0 : V) ρ, ‖γ Z‖ ≤ Real.exp (9 / 4) * S) →
    S / 2 < ‖γ 0‖ → ‖γ 0‖ ≤ S → ∀ Z ∈ ball (0 : V) (ρ / 21), γ Z ≠ 0

def SplitData {r : ℕ} (X : DataX E r) (ξ : Fin r → E) (La : ℝ) (z : Frame X.Ψ r)
    (lam : Fin (r - 2) → Fin r → E) : Prop :=
  (∀ j, lam j ∈ X.L' ∧ herm X.Gm (lam j) ξ = 0) ∧
  LinearIndependent E (Fin.cons ξ lam : Fin (r - 2 + 1) → Fin r → E) ∧
  (∀ j k : Fin (r - 2), (j : ℕ) < X.p0 - 1 → X.p0 - 1 ≤ (k : ℕ) → herm X.Gm (lam j) (lam k) = 0) ∧
  (∀ j : Fin (r - 2), (j : ℕ) < X.p0 - 1 → (∀ τ : X.Ψ, 0 < (τ.1 (herm X.Gm (lam j) (lam j))).re) ∧
    X.Jz z (X.ucomp z ξ (X.embV (lam j))) = I • X.ucomp z ξ (X.embV (lam j))) ∧
  (∀ j : Fin (r - 2), X.p0 - 1 ≤ (j : ℕ) → (∀ τ : X.Ψ, (τ.1 (herm X.Gm (lam j) (lam j))).re < 0) ∧
    X.Jz z (X.ucomp z ξ (X.embV (lam j))) = -(I • X.ucomp z ξ (X.embV (lam j)))) ∧
  ∀ j (τ : X.Ψ), ‖τ.1 (herm X.Gm (lam j) (lam j))‖ ≤ La ^ 2

def OrthonormalShortVectorBound : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E) (ν : X.Ψ → ℝ)
    (c1 w : ℝ) (z0 : Frame X.Ψ r), ShortVectorHypotheses X la P ξ ν c1 w z0 →
    ∀ x0 ∈ X.dom, X.IsOrtho x0 → X.SameFlag z0 x0 →
    ∃ (lam : Fin (r - 2) → Fin r → E) (h1 : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (Z1 : X.Coord),
      X.IsUnitaryC h1 ∧
      (∀ s t : X.Ψ → ℂ, X.applyV h1 (X.lineV ξ s + X.Jz z0 (X.lineV ξ t)) =
        X.lineV ξ s + X.Jz z0 (X.lineV ξ t)) ∧
      (∀ u ∈ X.Uz z0 ξ, X.applyV h1 u ∈ X.Uz z0 ξ) ∧
      SplitData X ξ (d6La r X.p0 (fdeg E) (dE E) (flowEpsilonBound X.g (dE E) (fdeg E) X.NA X.NC c1 w) (d6rh c1 w))
        (X.lmulC h1 z0) lam ∧
      X.SameFlag (X.lmulC h1 z0) (X.xZ x0 Z1) ∧ X.zN Z1 ≤ d6rh c1 w / 100

def IsotropicCoefficientSplitting : Prop :=
  ∀ (r : ℕ) (X : Data E r) (ξ : Fin r → E), X.IsIso ξ →
    ∃ f : (Fin r → E) → E, (∀ μ ∈ X.Λp ξ, f μ • ξ ∈ X.Λ) ∧
      (∀ μ ∈ X.Λp ξ, ∀ μ' ∈ X.Λp ξ, f (μ + μ') = f μ + f μ') ∧
      (∀ (α : 𝓞 E), ∀ μ ∈ X.Λp ξ, f ((α : E) • μ) = α * f μ) ∧
      ∀ e : E, e • ξ ∈ X.Λ → f (e • ξ) = e

def NoShortVectorLowerBound : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (ξ : Fin r → E) (ep0 : ℝ), X.IsIso ξ → 0 < ep0 → ∀ z ∈ X.FramesOverBasis ξ,
    (∀ x ∈ X.L', herm X.Gm x ξ = 0 → (∀ e : E, x ≠ e • ξ) →
      ∃ τ : X.Ψ, ep0 ≤ X.maj z τ (X.ucomp z ξ (X.embV x) τ)) →
    ∀ δ : X.Ψ → (Fin r → ℂ) →ₗ[ℂ] ℂ, ∃ μ ∈ X.Λp ξ, ∀ u ∈ X.Uz z ξ, ∀ τ : X.Ψ,
      X.maj z τ ((δ τ (u τ) - (dE E : ℂ) * (-τ.1 X.ξ0) *
          hermC τ.1 X.Gm (u τ) (X.ucomp z ξ (X.embV μ) τ)) • Data.emb τ.1 ξ) ≤
        frameIndexBound r (fdeg E) (dE E) (rdE E) X.NA X.NC ep0 ^ 2 * X.maj z τ (u τ)

def UnitaryUnipotentMove : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E) (ν : X.Ψ → ℝ)
    (c1 w : ℝ) (z0 : Frame X.Ψ r), ShortVectorHypotheses X la P ξ ν c1 w z0 →
    ∀ x0 ∈ X.dom, X.IsOrtho x0 → X.SameFlag z0 x0 →
    ∀ (lam : Fin (r - 2) → Fin r → E) (h1 : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (Z1 : X.Coord),
      X.IsUnitaryC h1 →
      (∀ s t : X.Ψ → ℂ, X.applyV h1 (X.lineV ξ s + X.Jz z0 (X.lineV ξ t)) =
        X.lineV ξ s + X.Jz z0 (X.lineV ξ t)) →
      (∀ u ∈ X.Uz z0 ξ, X.applyV h1 u ∈ X.Uz z0 ξ) →
      SplitData X ξ (d6La r X.p0 (fdeg E) (dE E) (flowEpsilonBound X.g (dE E) (fdeg E) X.NA X.NC c1 w) (d6rh c1 w))
        (X.lmulC h1 z0) lam →
      X.SameFlag (X.lmulC h1 z0) (X.xZ x0 Z1) → X.zN Z1 ≤ d6rh c1 w / 100 →
      ∀ n' : ℕ, 1000 * frameIndexBound r (fdeg E) (dE E) (rdE E) X.NA X.NC
          (flowEpsilonBound X.g (dE E) (fdeg E) X.NA X.NC c1 w) / d6rh c1 w ≤ n' →
      ∃ (n : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (Z : X.Coord),
        X.IsUnitaryC n ∧ (∀ τ, Matrix.mulVec (n τ) (Data.emb τ.1 ξ) = Data.emb τ.1 ξ) ∧
        (∀ μ ∈ X.Λp ξ, ∃ e : E, e • ξ ∈ X.Λ ∧
          (n' : ℂ) • X.aproj (X.lmulC n (X.lmulC h1 z0)) ξ (X.embV μ) = X.embV (e • ξ)) ∧
        SplitData X ξ (d6La r X.p0 (fdeg E) (dE E) (flowEpsilonBound X.g (dE E) (fdeg E) X.NA X.NC c1 w)
          (d6rh c1 w)) (X.lmulC n (X.lmulC h1 z0)) lam ∧
        X.SameFlag (X.lmulC n (X.lmulC h1 z0)) (X.xZ x0 Z) ∧ X.zN Z < d6rh c1 w / 21

end

end ReciprocityTheory.ChartRestriction.G.FD
end

