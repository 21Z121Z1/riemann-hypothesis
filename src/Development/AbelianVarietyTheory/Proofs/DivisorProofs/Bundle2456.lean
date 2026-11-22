import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2373
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2362
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2374
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0022
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmDeRhamEigenspaceCorankLeTwo
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.RealMultEigen

theorem diagonalizable_corank_le_two {V : Type*} {κ : Type} [AddCommGroup V] [Module ℂ V] (b : Module.Basis κ ℂ V) (S : Module.End ℂ V) (ν : κ → ℂ)
    (hS : ∀ k, S (b k) = ν k • b k) (k₁ k₂ : κ) (hν : ∀ k, ν k = 0 → k = k₁ ∨ k = k₂) :
    Module.rank ℂ (V ⧸ LinearMap.range S) ≤ 2 ∧ Disjoint (LinearMap.ker S) (LinearMap.range S) := by
  classical
  have hr : ∀ k x, b.repr (S x) k = ν k * b.repr x k := fun k x => by
    have : (b.coord k) ∘ₗ S = ν k • b.coord k := b.ext fun l => by
      by_cases h : l = k
      · subst h; simp [hS]
      · simp [hS, Finsupp.single_apply, h]
    simpa using LinearMap.congr_fun this x
  constructor
  · let q := (LinearMap.range S).mkQ
    have htop : Submodule.span ℂ (({q (b k₁), q (b k₂)} : Finset _) : Set (V ⧸ LinearMap.range S)) = ⊤ := by
      rw [eq_top_iff, ← (LinearMap.range S).range_mkQ, LinearMap.range_eq_map (Submodule.mkQ _), ← b.span_eq, Submodule.map_span,
        Submodule.span_le]
      rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
      by_cases h : ν k = 0
      · apply Submodule.subset_span
        rcases hν k h with rfl | rfl <;> simp [q]
      · have : (LinearMap.range S).mkQ (b k) = 0 := by
          rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
          exact ⟨(ν k)⁻¹ • b k, by rw [map_smul, hS, smul_smul, inv_mul_cancel₀ h, one_smul]⟩
        rw [this]
        exact Submodule.zero_mem _
    rw [← rank_top, ← htop]
    refine (rank_span_finset_le _).trans ?_
    exact_mod_cast Finset.card_le_two
  · rw [Submodule.disjoint_def]
    rintro _ hx ⟨y, rfl⟩
    rw [LinearMap.mem_ker] at hx
    apply b.repr.injective
    ext k
    have h := hr k (S y)
    rw [hx, hr] at h
    rw [hr]
    simp only [map_zero, Finsupp.zero_apply] at h ⊢
    rcases mul_eq_zero.1 h.symm with h | h
    · rw [h, zero_mul]
    · exact h

theorem exists_eigenbasis {V : Type*} [AddCommGroup V] [Module ℂ V] {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    (full : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) (P : Λ →+ V) (hspan : Submodule.span ℂ (Set.range P) = ⊤)
    (hdim : Module.finrank ℂ V = 2 * g) (T : Module.End ℂ V) (r : Fin g → ℝ)
    (hT : ∀ x : Λ, ∃ x' : Λ, (x' : Fin g → ℂ) = (fun j => (r j : ℂ) * (x : Fin g → ℂ) j) ∧ T (P x) = P x') :
    ∃ b : Module.Basis (Fin g × Bool) ℂ V, ∀ k, T (b k) = (r k.1 : ℂ) • b k := by
  classical
  haveI : IsZLattice ℝ Λ := ⟨full⟩
  letI : Module ℝ V := Module.compHom V (algebraMap ℝ ℂ)
  haveI : IsScalarTower ℝ ℂ V := ⟨fun a c v => by
    change (a • c) • v = (algebraMap ℝ ℂ a) • c • v
    rw [smul_smul, Algebra.smul_def]⟩
  let bZ := Module.Free.chooseBasis ℤ Λ
  let bR := bZ.ofZLatticeBasis ℝ Λ
  let Q : (Fin g → ℂ) →ₗ[ℝ] V := bR.constr ℝ fun k => P (bZ k)
  have hQ : ∀ x : Λ, Q x = P x := fun x => by
    have : (Q.toAddMonoidHom.toIntLinearMap ∘ₗ Λ.subtype) = P.toIntLinearMap := bZ.ext fun k => by
      have := bR.constr_basis ℝ (fun k => P (bZ k)) k
      simpa [bR, Q] using this
    exact LinearMap.congr_fun this x
  let M : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) :=
    { toFun := fun w j => (r j : ℂ) * w j
      map_add' := fun w w' => by funext j; simp [mul_add]
      map_smul' := fun c w => by funext j; simp; ring }
  have hTQ : ∀ w, T (Q w) = Q (M w) := fun w => by
    have : (T.restrictScalars ℝ) ∘ₗ Q = Q ∘ₗ M := bR.ext fun k => by
      obtain ⟨x', h1, h2⟩ := hT (bZ k)
      have e : bR k = bZ k := by simp [bR]
      simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, e]
      rw [hQ, h2, ← hQ, h1]
      rfl
    exact LinearMap.congr_fun this w
  let v : Fin g × Bool → V := fun k => Q (Pi.single k.1 (if k.2 then Complex.I else 1))
  have hv : ⊤ ≤ Submodule.span ℂ (Set.range v) := by
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    rw [← hQ]
    generalize (x : Fin g → ℂ) = w
    have hw : w = ∑ j, ((w j).re • (Pi.single j 1 : Fin g → ℂ) + (w j).im • (Pi.single j Complex.I : Fin g → ℂ)) := by
      funext l
      simp [Finset.sum_apply, Pi.single_apply, Finset.sum_add_distrib]
    rw [hw, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [map_add, map_smul, map_smul]
    refine Submodule.add_mem _ ?_ ?_
    · exact Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨(j, false), rfl⟩)
    · exact Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨(j, true), rfl⟩)
  refine ⟨basisOfTopLeSpanOfCardEqFinrank v hv (by rw [hdim]; simp [mul_comm]), fun k => ?_⟩
  rw [coe_basisOfTopLeSpanOfCardEqFinrank]
  have : M (Pi.single k.1 (if k.2 then Complex.I else 1)) =
      r k.1 • (Pi.single k.1 (if k.2 then Complex.I else 1) : Fin g → ℂ) := by
    funext l
    by_cases h : l = k.1
    · subst h; simp [M]
    · simp [M, Pi.single_apply, h]
  simp only [v]
  rw [hTQ, this, map_smul]
  rfl

theorem rank_coker_le_two : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (L : Set E)
      (𝔠 : FracId (FR E)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ L 0 X), IsCMType φ →
    ∀ (i : I) (b₀ : 𝓞 (FR E)), (∀ j : I, φ j ((b₀ : FR E) : E) = φ i ((b₀ : FR E) : E) → j = i) →
      Module.rank ℂ (HdR X.A ⧸ LinearMap.range (act (dp0 ℂ) (𝟙 _) X.rm b₀ - φ i ((b₀ : FR E) : E) • 1)) ≤ 2 ∧
      Disjoint (LinearMap.ker (act (dp0 ℂ) (𝟙 _) X.rm b₀ - φ i ((b₀ : FR E) : E) • 1))
        (LinearMap.range (act (dp0 ℂ) (𝟙 _) X.rm b₀ - φ i ((b₀ : FR E) : E) • 1)) := by
  intro hPC _ E _ _ _ I _ φ L 𝔠 X U _ i b₀ hsep
  obtain ⟨ε, hε⟩ := hPC
  obtain ⟨P, hspan, hdim, -, hend, -⟩ :=
    hε X.A (Module.finrank ℚ (FR E)) X.ab X.dim (X.diag U.c) (LB.isLB_pull (X.isLB _) _) U.u
  have hreal : ∀ j, (((φ j ((b₀ : FR E) : E)).re : ℝ) : ℂ) = φ j ((b₀ : FR E) : E) := fun j =>
    Complex.conj_eq_iff_re.1 ((b₀ : FR E).2 (φ j))
  let M : (Fin (Module.finrank ℚ (FR E)) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℚ (FR E)) → ℂ) :=
    { toFun := fun w j => φ (U.e j) ((b₀ : FR E) : E) * w j
      map_add' := fun w w' => by funext j; simp [mul_add]
      map_smul' := fun r w => by funext j; simp; ring }
  haveI := U.u.discrete
  obtain ⟨b, hb⟩ := exists_eigenbasis U.u.Λ U.u.full P hspan hdim (act (dp0 ℂ) (𝟙 _) X.rm b₀)
    (fun j => (φ (U.e j) ((b₀ : FR E) : E)).re) (fun x => by
      have hx : M x ∈ U.u.Λ := by
        rw [← U.u.ker]
        refine (U.act b₀ x).trans ?_
        rw [(U.u.ker x).2 x.2]
        haveI := X.rm.hom b₀
        exact MonObj.one_comp _
      refine ⟨⟨M x, hx⟩, ?_, ?_⟩
      · funext j
        rw [hreal]
        rfl
      · haveI := X.rm.hom b₀
        exact hend (X.rm.act b₀) M (U.act b₀) x ⟨M x, hx⟩ rfl)
  refine diagonalizable_corank_le_two b _ (fun k => φ (U.e k.1) ((b₀ : FR E) : E) - φ i ((b₀ : FR E) : E)) (fun k => ?_)
    (U.e.symm i, false) (U.e.symm i, true) (fun k hk => ?_)
  · rw [LinearMap.sub_apply, hb, hreal, sub_smul]
    rfl
  · obtain ⟨j, c⟩ := k
    have : j = U.e.symm i := by rw [← hsep _ (sub_eq_zero.1 hk)]; simp
    subst this
    cases c <;> simp

end GlobalTheory.RealMultEigen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmLatticeDualIntegralImage
section
open NumberField GlobalTheory.CMVal GlobalTheory.LatJet GlobalTheory.RealMult
open GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex (latMod polMod dualLat TrInt bar)

namespace GlobalTheory.CxDescent

noncomputable def imForm (n : ℕ) (ρ : ℝ) : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun v u => (∑ j, (ρ : ℂ) * v j * starRingEnd ℂ (u j)).im)
    (by intro v v' u; simp [add_mul, mul_add, Finset.sum_add_distrib])
    (by intro c v u; simp [Finset.mul_sum, Complex.mul_im, Complex.mul_re]; exact Finset.sum_congr rfl (fun i _ => by ring))
    (by intro v u u'; simp [add_mul, mul_add, Finset.sum_add_distrib])
    (by intro c v u; simp [Finset.mul_sum, Complex.mul_im, Complex.mul_re]; exact Finset.sum_congr rfl (fun i _ => by ring))

theorem imForm_apply (n : ℕ) (ρ : ℝ) (v u : Fin n → ℂ) :
    imForm n ρ v u = (∑ j, (ρ : ℂ) * v j * starRingEnd ℂ (u j)).im := rfl

theorem imForm_nondeg (n : ℕ) (ρ : ℝ) (hρ : ρ ≠ 0) (v : Fin n → ℂ)
    (h : ∀ u, imForm n ρ v u = 0) : v = 0 := by
  have h1 := h (Complex.I • v)
  rw [imForm_apply, Complex.im_sum] at h1
  have hterm : ∀ j, ((ρ : ℂ) * v j * starRingEnd ℂ ((Complex.I • v) j)).im = -ρ * Complex.normSq (v j) := by
    intro j
    simp [Complex.mul_im, Complex.mul_re, Complex.normSq_apply]; ring
  simp_rw [hterm, ← Finset.mul_sum] at h1
  have hs : ∑ j, Complex.normSq (v j) = 0 := by
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd (neg_eq_zero.mp h2) hρ
    · exact h2
  funext j
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Complex.normSq_nonneg (v i))).mp hs j (Finset.mem_univ _)
  simpa using this

theorem mem_range_of_int_pairing (E : Type) [Field E] [NumberField E] (n : ℕ)
    (Φ : E →ₗ[ℚ] (Fin n → ℂ)) (L : Set E) (ρ : ℝ) (hρ : ρ ≠ 0)
    (hspan : Submodule.span ℝ (Φ '' L) = ⊤)
    (hrat : ∀ x y : E, ∃ q : ℚ, (∑ j, (ρ : ℂ) * Φ x j * starRingEnd ℂ (Φ y j)).im = q)
    (w : Fin n → ℂ)
    (hw : ∀ x ∈ L, ∃ m : ℤ, (∑ j, (ρ : ℂ) * w j * starRingEnd ℂ (Φ x j)).im = m) :
    ∃ x : E, w = Φ x := by
  set B := imForm n ρ with hB
  obtain ⟨t, htsub, htspan, htli⟩ := exists_linearIndependent ℝ (Φ '' L)
  have htfin : t.Finite := htli.setFinite
  haveI : Fintype t := htfin.fintype
  have hts : Submodule.span ℝ t = ⊤ := htspan.trans hspan

  have hvan : ∀ v, (∀ k : t, B v k = 0) → v = 0 := by
    intro v hv
    apply imForm_nondeg n ρ hρ v
    intro u
    have hle : Submodule.span ℝ t ≤ LinearMap.ker (B v) :=
      Submodule.span_le.mpr (fun k hk => by simpa using hv ⟨k, hk⟩)
    have hu : u ∈ LinearMap.ker (B v) := hle (hts ▸ Submodule.mem_top)
    simpa using hu

  have hpre : ∀ k : t, ∃ x ∈ L, Φ x = k := fun k => htsub k.2
  choose xk hxkL hxk using hpre
  choose q hq using hrat
  let Q : Matrix t t ℚ := fun k j => q (xk k) (xk j)
  have hBQ : ∀ k j : t, B k j = (Q k j : ℝ) := by
    intro k j
    rw [hB, imForm_apply, ← hxk k, ← hxk j]; exact hq _ _
  choose m hm using fun j : t => hw (xk j) (hxkL j)
  have hBm : ∀ j : t, B w j = (m j : ℝ) := by
    intro j; rw [hB, imForm_apply, ← hxk j]; exact hm j

  have hinj : Function.Injective (Matrix.vecMulLinear Q) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    have hz : ∑ k, (c k : ℝ) • (k : Fin n → ℂ) = 0 := by
      apply hvan
      intro j
      have hj := congrFun hc j
      simp only [Matrix.vecMulLinear_apply, Matrix.vecMul, dotProduct, Pi.zero_apply] at hj
      rw [map_sum, LinearMap.sum_apply]
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hBQ]
      exact_mod_cast hj
    have := (Fintype.linearIndependent_iff.mp htli) (fun k => (c k : ℝ)) hz
    funext k; exact_mod_cast this k
  have hsurj := (LinearMap.injective_iff_surjective.mp hinj)
  obtain ⟨c, hc⟩ := hsurj (fun j => (m j : ℚ))
  refine ⟨∑ k, c k • xk k, ?_⟩
  rw [← sub_eq_zero]
  apply hvan
  intro j
  have hj := congrFun hc j
  simp only [Matrix.vecMulLinear_apply, Matrix.vecMul, dotProduct] at hj
  rw [map_sub, LinearMap.sub_apply, hBm, map_sum, map_sum, LinearMap.sum_apply]
  simp only [map_smul, ← Rat.cast_smul_eq_qsmul ℝ, hxk, map_smul, LinearMap.smul_apply, smul_eq_mul, hBQ]
  rw [sub_eq_zero]
  exact_mod_cast hj.symm

end GlobalTheory.CxDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmLatticeImageSpansReal
section
open NumberField GlobalTheory.CMVal GlobalTheory.LatJet GlobalTheory.RealMult
open GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex (latMod polMod dualLat TrInt bar)

namespace GlobalTheory.CMSpan

open ComplexConjugate

theorem functional_single {n : ℕ} (f : (Fin n → ℂ) →ₗ[ℝ] ℝ) (j : Fin n) (z : ℂ) :
    ((f (Pi.single j z) : ℝ) : ℂ) =
      (((f (Pi.single j 1) : ℂ) - Complex.I * (f (Pi.single j Complex.I) : ℂ)) / 2) * z +
      conj (((f (Pi.single j 1) : ℂ) - Complex.I * (f (Pi.single j Complex.I) : ℂ)) / 2) * conj z := by
  have hz : (Pi.single j z : Fin n → ℂ) =
      z.re • (Pi.single j (1:ℂ) : Fin n → ℂ) + z.im • (Pi.single j Complex.I : Fin n → ℂ) := by
    ext k
    by_cases h : k = j
    · subst h; simp [Complex.ext_iff]
    · simp [h]
  rw [hz, map_add, map_smul, map_smul]
  simp only [map_div₀, map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  apply Complex.ext <;> simp <;> ring

theorem conjugate_ne_self {E : Type} [Field E] [IsTotallyComplex E] (σ : E →+* ℂ) :
    ComplexEmbedding.conjugate σ ≠ σ := fun h =>
  IsTotallyComplex.complexEmbedding_not_isReal σ (ComplexEmbedding.isReal_iff.2 h)

end GlobalTheory.CMSpan

namespace GlobalTheory.CMSpan

open ComplexConjugate

theorem cmType_embeddings_injective {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type}
    (φ : I → E →+* ℂ) (hφ : IsCMType φ) :
    Function.Injective (Sum.elim φ (fun i => ComplexEmbedding.conjugate (φ i))) := by
  have hTC : IsTotallyComplex E := IsCMField.to_isTotallyComplex
  rintro (i | i) (j | j) h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
  · exact congrArg Sum.inl ((hφ (φ i)).unique (Or.inl rfl) (Or.inl h))
  · have hij : i = j := (hφ (φ i)).unique (Or.inl rfl) (Or.inr h)
    subst hij
    exact absurd h.symm (conjugate_ne_self (φ i))
  · have hij : j = i := (hφ (φ j)).unique (Or.inl rfl) (Or.inr h.symm)
    subst hij
    exact absurd h (conjugate_ne_self (φ j))
  · have h' : φ i = φ j := by
      refine RingHom.ext fun x => ?_
      have := congrArg (fun σ : E →+* ℂ => conj (σ x)) h
      simpa [ComplexEmbedding.conjugate_coe_eq] using this
    exact congrArg Sum.inr ((hφ (φ i)).unique (Or.inl rfl) (Or.inl h'))

theorem span_real_eq_top : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I]
    (φ : I → E →+* ℂ), IsCMType φ →
    ∀ (n : ℕ) (e : Fin n ≃ I) (L : Submodule (OF E) E),
      (∃ N : ℕ, 0 < N ∧ ∀ x : 𝓞 E, (N : E) * algebraMap (𝓞 E) E x ∈ L) →
    ∀ (Λ : Submodule ℤ (Fin n → ℂ)), (∀ w, w ∈ Λ ↔ ∃ x ∈ L, w = fun j ↦ φ (e j) x) →
      Submodule.span ℝ (Λ : Set (Fin n → ℂ)) = ⊤ := by
  intro E _ _ _ I _ φ hφ n e L hL Λ hΛ
  classical
  obtain ⟨N, hN, hNL⟩ := hL
  by_contra hne
  obtain ⟨f, hf0, hfk⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)

  have hkill : ∀ x : E, f (fun j ↦ φ (e j) x) = 0 := by
    intro x
    obtain ⟨y, hy0, hyint⟩ := exists_integral_multiples ℤ ℚ ({x} : Finset E)
    let z : 𝓞 E := ⟨y • x, hyint x (Finset.mem_singleton_self x)⟩
    have hmem : (fun j ↦ φ (e j) ((N : E) * algebraMap (𝓞 E) E z)) ∈ Λ :=
      (hΛ _).2 ⟨_, hNL z, rfl⟩
    have h0 := hfk (Submodule.subset_span hmem)
    rw [LinearMap.mem_ker] at h0
    have hsm : (fun j ↦ φ (e j) ((N : E) * algebraMap (𝓞 E) E z)) =
        ((N : ℝ) * (y : ℝ)) • (fun j ↦ φ (e j) x) := by
      ext j
      simp [z, zsmul_eq_mul, Complex.real_smul, mul_assoc]
    rw [hsm, map_smul, smul_eq_mul] at h0
    have hNy : (N : ℝ) * (y : ℝ) ≠ 0 :=
      mul_ne_zero (by exact_mod_cast hN.ne') (by exact_mod_cast hy0)
    exact (mul_eq_zero.1 h0).resolve_left hNy

  set c : Fin n → ℂ := fun j =>
    ((f (Pi.single j 1) : ℂ) - Complex.I * (f (Pi.single j Complex.I) : ℂ)) / 2 with hc
  have hexp : ∀ w : Fin n → ℂ, ((f w : ℝ) : ℂ) = ∑ j, (c j * w j + conj (c j) * conj (w j)) := by
    intro w
    conv_lhs => rw [← Finset.univ_sum_single w]
    rw [map_sum, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun j _ => functional_single f j (w j)

  let ψ : I ⊕ I → (E →* ℂ) := fun a => ((Sum.elim φ (fun i => ComplexEmbedding.conjugate (φ i)) a : E →+* ℂ) : E →* ℂ)
  have hψ : Function.Injective ψ := by
    intro a b h
    apply cmType_embeddings_injective φ hφ
    exact RingHom.ext fun x => DFunLike.congr_fun h x
  have hli := (linearIndependent_monoidHom E ℂ).comp ψ hψ
  let g : I ⊕ I → ℂ := Sum.elim (fun i => c (e.symm i)) (fun i => conj (c (e.symm i)))
  have hg : ∑ a, g a • (fun x => ψ a x) = 0 := by
    funext x
    have hx := hexp (fun j ↦ φ (e j) x)
    rw [hkill x, Complex.ofReal_zero] at hx
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Fintype.sum_sum_type,
      g, ψ, Sum.elim_inl, Sum.elim_inr, MonoidHom.coe_coe, ComplexEmbedding.conjugate_coe_eq]
    rw [← Finset.sum_add_distrib, ← e.sum_comp]
    simpa using hx.symm
  have hc0 : ∀ j, c j = 0 := by
    intro j
    have := Fintype.linearIndependent_iff.1 hli g hg (Sum.inl (e j))
    simpa [g] using this
  apply hf0
  refine LinearMap.ext fun w => ?_
  have hw := hexp w
  simp only [hc0, zero_mul, map_zero, add_zero, Finset.sum_const_zero] at hw
  simpa using hw

end GlobalTheory.CMSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmPeriodMatrixExists
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatModel

theorem surj_lattice : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
      IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = io) → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
      ∀ e : Fin (Module.finrank ℚ (FR E)) ≃ I,
      ∃ M : (Fin (Module.finrank ℚ (FR E)) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℚ (FR E)) → ℂ), Function.Surjective M ∧
        ∀ z, (∀ j, ∃ a b : ℤ, z j = a + b * io δ) → ∃ x ∈ lattice c y, M z = fun j ↦ φ (e j) x := by
  intro K _ _ d δ io hK hd hδ E _ _ _ _ I _ φ hφ hio c y hc e
  classical
  have hEK : Module.finrank K E = Module.finrank ℚ (FR E) := by
    have h1 : Module.finrank ℚ E = 2 * Module.finrank ℚ (FR E) := by
      rw [← Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E,
        Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E, mul_comm]
    have h2 : Module.finrank ℚ K * Module.finrank K E = Module.finrank ℚ E := Module.finrank_mul_finrank ℚ K E
    rw [hK, h1] at h2
    omega
  generalize Module.finrank ℚ (FR E) = f at e hEK ⊢
  let b := Module.finBasisOfFinrankEq K E hEK
  obtain ⟨m, hm0, hm⟩ := exists_integral_multiples ℤ ℚ (L := E) (Finset.univ.image b)
  obtain ⟨N, hN0, hNmem, -⟩ := GlobalTheory.CMVal.LatBound.lattice_between E c hc y

  have hint : ∀ j, IsIntegral ℤ (m • b j) := fun j => hm _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))
  have hδint : IsIntegral ℤ (algebraMap K E δ) := by
    refine ⟨Polynomial.X ^ 2 + Polynomial.C (d : ℤ), ?_, ?_⟩
    · exact Polynomial.monic_X_pow_add_C _ two_ne_zero
    · simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]
      rw [← map_pow, hδ]; simp
  let u : Fin f → 𝓞 E := fun j => ⟨m • b j, hint j⟩
  let v : Fin f → 𝓞 E := fun j => ⟨algebraMap K E δ * (m • b j), hδint.mul (hint j)⟩
  let w : Fin f → E := fun j => (N : E) * (m • b j)
  have hw : ∀ j, w j ∈ lattice c y := fun j => hNmem (u j)
  have hδw : ∀ j, algebraMap K E δ * w j ∈ lattice c y := fun j => by
    have := hNmem (v j)
    simpa [w, v, mul_left_comm] using this

  have hs : ∀ _j : Fin f, IsUnit ((N : K) * (m : K)) := fun _ => by
    refine IsUnit.mk0 _ (mul_ne_zero (by exact_mod_cast hN0.ne') (by exact_mod_cast hm0))
  let b' := b.isUnitSMul hs
  have hb' : ∀ j, b' j = w j := fun j => by
    simp only [b', Module.Basis.isUnitSMul_apply, w, Algebra.smul_def, zsmul_eq_mul, map_mul, map_natCast, map_intCast]
    simp only [algebraMap_int_eq, eq_intCast]
    ring
  let A : Matrix (Fin f) (Fin f) ℂ := fun i j => φ (e i) (w j)
  refine ⟨Matrix.mulVecLin A, ?_, ?_⟩
  ·
    show Function.Surjective A.mulVec
    rw [Matrix.mulVec_surjective_iff_isUnit, ← Matrix.linearIndependent_rows_iff_isUnit]
    have hinj : Function.Injective (fun i : Fin f => ((φ (e i) : E →+* ℂ) : E →* ℂ)) := by
      intro i i' h
      have h' : φ (e i) = φ (e i') := RingHom.ext fun x => DFunLike.congr_fun h x
      obtain ⟨k, -, hk⟩ := hφ (φ (e i))
      have a1 := hk (e i) (Or.inl rfl)
      have a2 := hk (e i') (Or.inl h')
      exact e.injective (a1.trans a2.symm)
    have li : LinearIndependent ℂ (fun i : Fin f => ((((φ (e i) : E →+* ℂ) : E →* ℂ)) : E → ℂ)) :=
      (linearIndependent_monoidHom E ℂ).comp _ hinj
    rw [Fintype.linearIndependent_iff] at li ⊢
    intro g hg i
    refine li g ?_ i
    funext x
    have hrow : ∀ j, ∑ i, g i * φ (e i) (w j) = 0 := fun j => by
      have := congrFun hg j
      simpa [Matrix.row, A, Finset.sum_apply] using this
    have hx : x = ∑ j, b'.repr x j • w j := by
      conv_lhs => rw [← b'.sum_repr x]
      simp only [hb']
    simp only [Finset.sum_apply, Pi.smul_apply, MonoidHom.coe_coe, smul_eq_mul, Pi.zero_apply]
    rw [hx]
    simp only [map_sum, Algebra.smul_def, map_mul]
    have hio' : ∀ i (k : K), φ (e i) (algebraMap K E k) = io k := fun i k => by
      rw [← hio (e i)]; rfl
    simp only [hio']
    calc ∑ i, g i * ∑ j, io (b'.repr x j) * φ (e i) (w j)
        = ∑ j, io (b'.repr x j) * ∑ i, g i * φ (e i) (w j) := by
          simp only [Finset.mul_sum]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
      _ = 0 := by simp [hrow]
  · intro z hz
    choose a a' ha using hz
    refine ⟨∑ j, ((a j : E) * w j + (a' j : E) * (algebraMap K E δ * w j)), ?_, ?_⟩
    · rw [← coe_latticeSub]
      refine AddSubgroup.sum_mem _ fun j _ => AddSubgroup.add_mem _ ?_ ?_
      · rw [← zsmul_eq_mul]; exact AddSubgroup.zsmul_mem _ (hw j) _
      · rw [← zsmul_eq_mul]; exact AddSubgroup.zsmul_mem _ (hδw j) _
    · funext i
      have hio' : φ (e i) (algebraMap K E δ) = io δ := by rw [← hio (e i)]; rfl
      show A.mulVec z i = φ (e i) _
      simp only [Matrix.mulVec, dotProduct, A, map_sum, map_add, map_mul, map_intCast, hio', ha]
      refine Finset.sum_congr rfl fun j _ => by ring

end GlobalTheory.LatModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingEqOneTrivialOnAxisStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commutatorPairing_eq_one_trivial_on_axis : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x₀ : Sp k ⟶ S) (m : ℕ), (m : k) ≠ 0 → ∀ (a b : Over.mk x₀ ⟶ A), a ^ m = 1 → b ^ m = 1 → (∃ t : (P.pull (lift (snd A (Over.mk x₀) ≫ a ^ 2) (fst A (Over.mk x₀))).left).Gen, t.IsGen) → ∀ c : Γ((Over.mk x₀).left, ⊤)ˣ, Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) (m : ℤ) a b c → c = 1 := by
  first | (exact @GlobalTheory.WeilSqKer.weilIs_eq_one) | (exact GlobalTheory.WeilSqKer.weilIs_eq_one) | (intros; apply GlobalTheory.WeilSqKer.weilIs_eq_one  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatibleReductionSystemMapImmersionStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compatibleReductionSystem_map_immersion : ∀ (R : Type) [CommRing R] (I : Ideal R) (W W' : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)) (π : W' ⟶ W), IsSeparated f → IsImmersion π → ∀ t : ℕ → W'.IdealSheafData, IsSystem (π ≫ f) I t → (∀ e, IsProper ((t e).subschemeι ≫ π ≫ f)) → IsSystem f I (fun e => (t e).map π) ∧ (∀ e, IsProper (((t e).map π).subschemeι ≫ f)) ∧ ∀ e, ((t e).map π).comap π = t e := by
  first | exact @GlobalTheory.FormalAlg.mapSystem | exact GlobalTheory.FormalAlg.mapSystem | (intros; apply GlobalTheory.FormalAlg.mapSystem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentDegreesSumLeTotalDegreeStatement
section
open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.componentDegrees_sum_le_total_degree : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r), IsComplexData U V dict → ∀ G : WTZ D.host.E, GoodW U (xiR D) V dict G → rankW U G = ∑ᶠ Z : Comp Xo c, rankOn U Z G ∧ (∑ᶠ Z : Comp Xo c, degOn U (xiR D) V dict Z G) ≤ degW U (xiR D) V dict G := by
  first | exact @GlobalTheory.Proof.componentDegrees_sum_le_total_degree.degOn_sum_le | exact GlobalTheory.Proof.componentDegrees_sum_le_total_degree.degOn_sum_le | (intros; apply GlobalTheory.Proof.componentDegrees_sum_le_total_degree.degOn_sum_le <;> assumption)
end

